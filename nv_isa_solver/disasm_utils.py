import subprocess
import tempfile
try:
    import tqdm
except Exception:
    class _TqdmDummy:
        @staticmethod
        def tqdm(x, *a, **k):
            return x

    tqdm = _TqdmDummy()
import os
import multiprocessing
import logging
import re
import threading
from collections import Counter

from .parser import InstructionParser

NVDISASM_TIMEOUT_SEC = int(os.environ.get("NV_ISA_SOLVER_NVDISASM_TIMEOUT_SEC", "30"))
FAMILY_KEY_DELIM = "__fam__"


def _process_dump(dump):
    lines = dump.split("\n")
    result = []
    for line in lines:
        if "/*" not in line:
            continue
        result.append(line[line.find("*/") + 2 :].strip())
    return "\n".join(result).strip()


def _has_decoded_asm(asm):
    if not asm or not isinstance(asm, str):
        return False
    return any(line.strip() for line in asm.splitlines())


def _has_placeholder_asm(asm):
    if not _has_decoded_asm(asm):
        return False
    upper = asm.upper()
    return ("???" in asm) or ("INVALID" in upper)


def _should_persist_disasm(returncode, asm):
    return returncode == 0 and _has_decoded_asm(asm) and not _has_placeholder_asm(asm)


def _cache_base_name_from_key(parsed_key):
    try:
        if not isinstance(parsed_key, str) or not parsed_key:
            return None
        base_name, _sep, _rest = parsed_key.partition("_")
        base_name = base_name.strip()
        return base_name if base_name else None
    except Exception:
        return None


def _add_to_cache_index(disassembler, inst_bytes, asm, parsed_key=None):
    """将 (inst_bytes, asm) 加入 cache_by_key 索引。

    若传入 parsed_key 则直接使用；否则从 asm 最后一行解析。
    解析失败时用助记符+opcode 做 fallback 索引，避免指令从 find_uniques 中丢失。
    """
    if not _has_decoded_asm(asm):
        return
    if parsed_key is None:
        try:
            lines = [l for l in asm.splitlines() if l.strip()]
            if not lines:
                return
            parsed = InstructionParser.parseInstruction(lines[-1])
            parsed_key = parsed.get_key()
        except Exception:
            try:
                lines = [l for l in asm.splitlines() if l.strip()]
                if lines:
                    toks = lines[-1].strip().split()
                    mnemonic = (toks[1] if len(toks) > 1 and toks[0].startswith("@") else (toks[0] if toks else "UNKNOWN"))
                    opcode = get_bit_range(inst_bytes, 0, 12)
                    parsed_key = f"{mnemonic}_PARSE_FALLBACK_{opcode}"
                else:
                    return
            except Exception:
                return
    if parsed_key not in disassembler.cache_by_key:
        disassembler.cache_by_key[parsed_key] = []
    disassembler.cache_by_key[parsed_key].append((inst_bytes, asm))
    base_name = _cache_base_name_from_key(parsed_key)
    if base_name:
        if base_name not in disassembler.cache_keys_by_base:
            disassembler.cache_keys_by_base[base_name] = {}
        disassembler.cache_keys_by_base[base_name][parsed_key] = None


def _norm_tokens(tokens):
    out = []
    for tok in tokens or []:
        if not isinstance(tok, str):
            continue
        clean = tok.rstrip(".").strip()
        if not clean:
            continue
        if "???" in clean or "INVALID" in clean.upper():
            continue
        out.append(clean)
    return tuple(sorted(Counter(out).items()))


def _parsed_surface_signature(parsed):
    """提取用于 distill 的“表面语义签名”。

    目的:
    - 允许清零 operand 数值位；
    - 允许清零 instruction modifier 位（RZ/RM/RP 等），以便得到 canonical baseline
      供 enumerate_modifiers 从 0 开始枚举；若保留 modifier 位则 baseline 会卡在
      某值（如 RZ=3），无法正确枚举全部取值；
    - 禁止把 operand modifier / predicate 蒸馏丢失。
    """
    try:
        key = parsed.get_key()
    except Exception:
        key = None
    try:
        pred = getattr(parsed, "predicate", None)
    except Exception:
        pred = None
    # 不包含 instruction modifiers：允许 distill 将 RZ/RM/RP 等 modifier 位归零，
    # 得到干净的 canonical baseline 供枚举使用。
    op_mods = []
    try:
        ops = parsed.get_flat_operands()
    except Exception:
        ops = []
    for op in ops:
        try:
            reg_type = getattr(op, "reg_type", None)
            op_key = op.get_operand_key() if hasattr(op, "get_operand_key") else type(op).__name__
            om = _norm_tokens(getattr(op, "modifiers", []) or [])
        except Exception:
            reg_type = None
            op_key = type(op).__name__
            om = tuple()
        op_mods.append((reg_type, op_key, om))
    return (key, pred, tuple(op_mods))


class Disassembler:
    def __init__(self, arch, nvdisasm="nvdisasm", batch_size=None):
        self.cache = {}
        # 运行期 memo：包含持久化 cache 和本轮 nvdisasm 失败/空输出结果，
        # 用于避免重复调用 nvdisasm。
        self._runtime_memo = {}
        # 按 parsed key 索引的 cache：key -> [(inst_bytes, asm), ...]
        # 用于按 key 快速查找同指令不同编码的候选，避免每次遍历整个 cache（数十万条）
        self.cache_by_key = {}
        # 按 base_name 索引 parsed key：base_name -> {parsed_key: None, ...}
        # 用于占位符回退时按 base 局部检索，而不是快照全量 keys 再做前缀筛选。
        self.cache_keys_by_base = {}
        # 蒸馏结果缓存：raw inst bytes -> distilled bytes
        self._distill_cache = {}
        # Sanitize arch string: prefer tokens like 'SM100a', 'SM90a', etc.
        try:
            matches = re.findall(r"(SM\d{2,3}[a-z]?)", arch, flags=re.IGNORECASE)
            if matches:
                self.arch = matches[-1]
            else:
                logging.debug("arch string '%s' does not match expected pattern; using as-is", arch)
                self.arch = arch
        except Exception:
            self.arch = arch
        self.nvdisasm = nvdisasm
        if batch_size is None:
            batch_size = min(multiprocessing.cpu_count(), 32)
        self.batch_size = batch_size
        try:
            max_parallel = int(
                os.environ.get(
                    "NV_ISA_SOLVER_MAX_NVDISASM_PROCS",
                    str(max(1, self.batch_size)),
                )
            )
        except Exception:
            max_parallel = max(1, self.batch_size)
        self.max_parallel_disasm = max(1, max_parallel)
        self._nvdisasm_semaphore = threading.BoundedSemaphore(
            self.max_parallel_disasm
        )
        self._cache_lock = threading.RLock()

    def _get_cached_result(self, inst):
        inst_b = bytes(inst)
        with self._cache_lock:
            if inst_b in self.cache:
                return self.cache[inst_b]
            return self._runtime_memo.get(inst_b)

    def _store_disasm_result(self, inst, asm, returncode=None):
        inst_b = bytes(inst)
        with self._cache_lock:
            self._runtime_memo[inst_b] = asm
            if returncode is None or _should_persist_disasm(returncode, asm):
                self.cache[inst_b] = asm
                _add_to_cache_index(self, inst_b, asm)

    def get_cache_items(self):
        with self._cache_lock:
            return tuple(self.cache.items())

    def get_cache_keys_for_base(self, base_name):
        with self._cache_lock:
            return tuple(self.cache_keys_by_base.get(base_name, {}).keys())

    def get_cache_index_items(self):
        with self._cache_lock:
            return tuple((key, list(candidates)) for key, candidates in self.cache_by_key.items())

    def load_cache(self, filename):
        """加载 disasm cache 文件。cache 格式：每行 "asm --- hex"。

        加载时同时构建 cache_by_key 索引，供 get_cache_candidates 和 find_uniques_from_cache 使用。
        """
        with self._cache_lock:
            self._distill_cache.clear()
            self.cache_by_key.clear()
            self.cache_keys_by_base.clear()
        try:
            with open(filename) as file:
                for line in file:
                    if "---" not in line:
                        continue
                    parts = line.split("---")
                    if len(parts) < 2:
                        continue
                    asm = parts[0].strip()
                    inst = parts[1].strip()
                    hexstr = re.sub(r"[^0-9a-fA-F]", "", inst)
                    if len(hexstr) == 0:
                        continue
                    if len(hexstr) % 2 != 0:
                        continue
                    try:
                        inst_bytes = bytes.fromhex(hexstr)
                        if not _has_decoded_asm(asm):
                            continue
                        parsed_key = None
                        # 同时索引到 cache_by_key
                        try:
                            lines = [l for l in asm.splitlines() if l.strip()]
                            if lines:
                                parsed_key = InstructionParser.parseInstruction(lines[-1]).get_key()
                        except Exception:
                            # 解析失败时用助记符+opcode 做 fallback 索引，避免 cache 中存在的指令从 find_uniques 中丢失
                            try:
                                last_line = [l for l in asm.splitlines() if l.strip()]
                                if last_line:
                                    toks = last_line[-1].strip().split()
                                    mnemonic = (toks[1] if len(toks) > 1 and toks[0].startswith("@") else (toks[0] if toks else "UNKNOWN"))
                                    opcode = get_bit_range(inst_bytes, 0, 12)
                                    parsed_key = f"{mnemonic}_PARSE_FALLBACK_{opcode}"
                            except Exception:
                                pass
                        with self._cache_lock:
                            self.cache[inst_bytes] = asm
                            if parsed_key is not None:
                                _add_to_cache_index(self, inst_bytes, asm, parsed_key=parsed_key)
                    except ValueError:
                        continue
        except FileNotFoundError:
            logging.debug("Cache could not be loaded: %s", filename)
            pass

    def dump_cache(self, filename):
        cache_items = self.get_cache_items()
        with open(filename, "w") as file:
            for inst, disasm in cache_items:
                if not _should_persist_disasm(0, disasm):
                    continue
                file.write(disasm + " --- " + inst.hex() + "\n")

    def get_cache_candidates(self, key):
        """按 parsed key 返回同 key 的 cache 候选列表。

        返回 [(inst_bytes, asm), ...]，若无则返回空列表。
        用于替代遍历整个 cache 的 O(n) 查找，直接 O(1) 索引。
        """
        with self._cache_lock:
            return list(self.cache_by_key.get(key, ()))

    # Find unique instruction signatures from the cache.
    def find_uniques_from_cache(self):
        """基于 cache_by_key 选每个 parsed_key 的代表编码。

        代表编码优先级（高 -> 低）：
        1) 反汇编文本不含占位符（??? / INVALID）
        2) concrete token 数更多（parsed.modifiers + operand.modifiers）
        3) 占位符 token 数更少
        4) 控制码之外的语义位更丰富（避免选到过度稀疏的 canonical seed）
        """
        def _rank_candidate(asm: str):
            if not isinstance(asm, str) or not asm:
                return (0, -1, -9999)
            upper = asm.upper()
            has_placeholder_text = ("???" in asm) or ("INVALID" in upper)
            concrete = 0
            placeholders = 0
            try:
                lines = [l for l in asm.splitlines() if l.strip()]
                if lines:
                    parsed = InstructionParser.parseInstruction(lines[-1])
                    for token in (getattr(parsed, "modifiers", []) or []):
                        if isinstance(token, str) and token:
                            if ("???" in token) or ("INVALID" in token.upper()):
                                placeholders += 1
                            else:
                                concrete += 1
                    for op in parsed.get_flat_operands():
                        for token in (getattr(op, "modifiers", []) or []):
                            if isinstance(token, str) and token:
                                if ("???" in token) or ("INVALID" in token.upper()):
                                    placeholders += 1
                                else:
                                    concrete += 1
            except Exception:
                pass
            clean = 0 if has_placeholder_text else 1
            return (clean, concrete, -placeholders)

        def _semantic_inst_popcount(inst_bytes):
            try:
                data = bytes(inst_bytes)
            except Exception:
                return 0
            semantic_prefix = data[:13]
            try:
                return sum(byte.bit_count() for byte in semantic_prefix)
            except Exception:
                return sum(bin(byte).count("1") for byte in semantic_prefix)

        keys = {}
        for parsed_key, candidates in self.get_cache_index_items():
            # 去掉“多 family”拆分：同一 parsed_key + opcode 下只保留 1 个
            # 代表编码（后续由 pipeline 推断 modifier/flag 表覆盖更多 token）。
            best_per_opcode = {}
            for inst_bytes, asm in candidates:
                if not asm:
                    continue
                opcode = get_bit_range(inst_bytes, 0, 12)
                full_key = f"{opcode}.{parsed_key}"
                rank = _rank_candidate(asm) + (_semantic_inst_popcount(inst_bytes),)
                prev = best_per_opcode.get(full_key)
                if prev is None or rank > prev[0]:
                    best_per_opcode[full_key] = (rank, inst_bytes)
            for opcode_key, (_rank, inst_bytes) in best_per_opcode.items():
                keys[opcode_key] = inst_bytes
        return keys

    def disassemble(self, inst):
        inst = bytes(inst)
        cached = self._get_cached_result(inst)
        if cached is not None:
            return cached

        tmp = tempfile.NamedTemporaryFile(delete=False)
        tmp.write(inst)
        tmp.close()
        self._nvdisasm_semaphore.acquire()
        try:
            result = subprocess.run(
                [self.nvdisasm, tmp.name, "--binary", self.arch],
                capture_output=True,
                timeout=NVDISASM_TIMEOUT_SEC,
            )
            asm = _process_dump(result.stdout.decode("ascii", errors="ignore"))
        finally:
            self._nvdisasm_semaphore.release()
            os.remove(tmp.name)
        self._store_disasm_result(inst, asm, result.returncode)
        return asm

    def disassemble_parallel(self, array, disable_cache=False, force_sequential=False):
        """批量反汇编。force_sequential=True 时串行执行，避免主流程并行时进程数过多。"""
        if not disable_cache:
            result = [None] * len(array)
            idxes = []
            new_array = []
            for i, inst in enumerate(array):
                inst = bytes(inst)
                cached = self._get_cached_result(inst)
                if cached is not None:
                    result[i] = cached
                    continue
                idxes.append(i)
                new_array.append(inst)
            uncached_results = self.disassemble_parallel(
                new_array, disable_cache=True, force_sequential=force_sequential
            )
            for i, asm in zip(idxes, uncached_results):
                result[i] = asm
            return result

        if force_sequential:
            return [self.disassemble(inst) for inst in array]

        if len(array) > self.batch_size:
            result = []
            for i in tqdm.tqdm(range(0, len(array), self.batch_size)):
                result += self.disassemble_parallel(
                    array[i : i + self.batch_size],
                    disable_cache=True,
                    force_sequential=force_sequential,
                )
            assert len(result) == len(array)
            return result

        results = []
        returncodes = []
        cursor = 0
        while cursor < len(array):
            chunk = []
            acquired = 0
            self._nvdisasm_semaphore.acquire()
            acquired += 1
            chunk.append(array[cursor])
            cursor += 1
            while cursor < len(array) and acquired < self.max_parallel_disasm:
                if not self._nvdisasm_semaphore.acquire(blocking=False):
                    break
                acquired += 1
                chunk.append(array[cursor])
                cursor += 1

            processes = []
            tmp_files = []
            try:
                for inst in chunk:
                    tmp = tempfile.NamedTemporaryFile(delete=False)
                    tmp_files.append(tmp)
                    tmp.write(inst)
                    name = tmp.name
                    tmp.close()

                    process = subprocess.Popen(
                        [self.nvdisasm, name, "--binary", self.arch],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                    )
                    processes.append(process)

                for process in processes:
                    try:
                        stdout, _stderr = process.communicate(timeout=NVDISASM_TIMEOUT_SEC)
                    except subprocess.TimeoutExpired as exc:
                        process.kill()
                        process.communicate()
                        raise RuntimeError(
                            f"nvdisasm timeout after {NVDISASM_TIMEOUT_SEC}s"
                        ) from exc
                    results.append(_process_dump(stdout.decode("ascii", errors="ignore")))
                    returncodes.append(process.returncode)
            finally:
                for tmp in tmp_files:
                    try:
                        os.remove(tmp.name)
                    except FileNotFoundError:
                        pass
                for _ in range(acquired):
                    self._nvdisasm_semaphore.release()

        for inst, disasm, returncode in zip(array, results, returncodes):
            self._store_disasm_result(inst, disasm, returncode)

        return results

    def distill_instruction(self, inst, use_parallel=True):
        inst_key = bytes(inst)
        with self._cache_lock:
            cached = self._distill_cache.get(inst_key)
        if cached is not None:
            return cached

        original_asm = self.disassemble(inst)
        orig_lines = [l for l in original_asm.splitlines() if l.strip()]
        orig_line = orig_lines[-1] if orig_lines else original_asm
        original_parsed = InstructionParser.parseInstruction(orig_line)
        original_signature = _parsed_surface_signature(original_parsed)

        distilled = bytes(inst)
        max_bit = len(inst) * 8 - 1
        batch_size_bits = 8

        # 固定点蒸馏：
        # 每次成功清零 1 个 bit 后，从高位重新扫描，直到整轮无变化。
        # 这样不会漏掉“同批里更高位本可在下一状态继续清零”的位。
        changed = True
        while changed:
            changed = False
            i = max_bit
            while i >= 0:
                # 收集本批（最多 8 个）待尝试的 bit 索引与候选指令
                batch_bits = []
                batch_candidates = []
                j = i
                while j >= 0 and len(batch_bits) < batch_size_bits:
                    byte_idx = j // 8
                    if byte_idx < len(distilled) and (distilled[byte_idx] >> (j % 8)) & 1 == 1:
                        inst_ = bytearray(bytes(distilled))
                        inst_[byte_idx] = inst_[byte_idx] & ~(1 << (j % 8))
                        batch_bits.append(j)
                        batch_candidates.append(bytes(inst_))
                    j -= 1

                if not batch_candidates:
                    i = j
                    continue

                # 批量反汇编（主流程并行时 use_parallel=False 避免进程数过多）
                batch_asms = self.disassemble_parallel(
                    batch_candidates, force_sequential=not use_parallel
                )

                # 按 bit 从高到低处理，只应用第一个成功的
                applied = False
                applied_idx = -1
                for bit_idx, (_bit_pos, asm) in enumerate(zip(batch_bits, batch_asms)):
                    if not asm:
                        continue
                    if re.search(r"\?+\d*", asm) or re.search(
                        r"INVALID\w*", asm, flags=re.IGNORECASE
                    ):
                        continue
                    try:
                        lines = [l for l in asm.splitlines() if l.strip()]
                        line = lines[-1] if lines else asm
                        distill_parsed = InstructionParser.parseInstruction(line)
                    except Exception:
                        continue
                    if original_parsed.get_key() != distill_parsed.get_key():
                        continue
                    # 保 key、predicate、operand-modifier；不保 instruction modifier，
                    # 以便 modifier 位可归零得到 canonical baseline 供枚举。
                    if _parsed_surface_signature(distill_parsed) != original_signature:
                        continue
                    distilled = batch_candidates[bit_idx]
                    applied = True
                    applied_idx = bit_idx
                    changed = True
                    break

                if applied and applied_idx >= 0:
                    # 应用一次后从最高位重新扫，保证固定点。
                    i = max_bit
                else:
                    i = j
        distilled_b = bytes(distilled)
        with self._cache_lock:
            self._distill_cache[inst_key] = distilled_b
        return distilled_b


    def mutate_inst(self, inst, start=0, end=16 * 8, use_parallel=True):
        idxes = []
        insts = []
        # Ensure we have enough bytes to flip bits up to `end` by zero-extending.
        needed_bytes = (end + 7) // 8
        for i in range(start, end):
            inst_ = bytearray(bytes(inst))
            if len(inst_) < needed_bytes:
                inst_.extend(b"\x00" * (needed_bytes - len(inst_)))
            inst_[i // 8] = inst_[i // 8] ^ (1 << (i % 8))
            insts.append(inst_)
            idxes.append(i)
        return zip(idxes, insts, self.disassemble_parallel(insts, force_sequential=not use_parallel))

    def inst_disasm_range(self, base, bit_start, bit_end):
        instructions = []
        needed_bytes = (bit_end + 7) // 8
        for i in range(pow(2, bit_end - bit_start + 1)):
            inst_bytes = bytearray(bytes(base))
            if len(inst_bytes) < needed_bytes:
                inst_bytes.extend(b"\x00" * (needed_bytes - len(inst_bytes)))
            set_bit_range(inst_bytes, bit_start, bit_end, i)
            instructions.append(inst_bytes)
        return zip(instructions, self.disassemble_parallel(instructions))


def set_bit_range(byte_array, start_bit, end_bit, value):
    for i in range(start_bit, end_bit):
        mask = 1 << (i % 8)
        if value & (1 << (i - start_bit)):
            byte_array[i // 8] |= mask
        else:
            byte_array[i // 8] &= ~mask


def get_bit_range(byte_array, start_bit, end_bit):
    result = 0
    for i in range(start_bit, end_bit):
        v = (byte_array[i // 8] >> (i % 8)) & 1
        result |= v << (i - start_bit)
    return result


def get_bit_range_sparse(byte_array, bit_positions):
    """从指定位位置读取值，bit_positions[0] 对应最低位。"""
    result = 0
    for i, pos in enumerate(bit_positions):
        v = (byte_array[pos // 8] >> (pos % 8)) & 1
        result |= v << i
    return result


def set_bit_range_sparse(byte_array, bit_positions, value):
    """向指定位位置写入值，保留其他位不变。"""
    for i, pos in enumerate(bit_positions):
        mask = 1 << (pos % 8)
        if (value >> i) & 1:
            byte_array[pos // 8] |= mask
        else:
            byte_array[pos // 8] &= ~mask
