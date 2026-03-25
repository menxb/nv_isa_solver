"""英伟达指令编码分析器 (instruction_solver)

【模块职责】
从反汇编（disasm）缓存（cache）中分析指令编码布局，推断：
- 操作数（operand）的位段（range）
- 修饰符（modifier）的位段（range）与取值表
- 标志（flag）、常量位（CONSTANT）等

【核心流程】
1. 加载反汇编（disasm）缓存（cache） -> find_uniques_from_cache 获取唯一指令
2. 对每条指令：mutate 逐位翻转 -> 解析反汇编（disasm）差异 -> 归类到 opcode/操作数（operand）/修饰符（modifier）/谓词（predicate）等位集合
3. 多轮 analysis 固定点迭代：消歧标志（flag）与修饰符（modifier）、扩展修饰符组、压缩常量位等
4. 输出 isa.json 和 HTML 位图（bitmap）
"""
from __future__ import annotations

import ast
import atexit
import contextlib
import json
from enum import Enum
from typing import List
from collections import Counter, defaultdict
from itertools import product, combinations
import os
import logging
import re
import sys
import threading
import time

from .disasm_utils import Disassembler, set_bit_range, get_bit_range, FAMILY_KEY_DELIM
from .solver_support import (
    extract_mnemonic_head_from_disasm as _extract_mnemonic_head_from_disasm,
    extract_opcode_from_analysis_key as _extract_opcode_from_analysis_key,
    extract_parsed_key_from_analysis_key as _extract_parsed_key_from_analysis_key_base,
    rank_cache_candidate_for_exact as _rank_cache_candidate_for_exact_base,
    recover_operand_spec_from_cache as _recover_operand_spec_from_cache_base,
    safe_flat_operand_count as _safe_flat_operand_count_base,
    safe_operand_range_count as _safe_operand_range_count_base,
    safe_parsed_key as _safe_parsed_key,
    semantic_inst_popcount as _semantic_inst_popcount,
    select_instruction_by_exact_key as _select_instruction_by_exact_key_base,
    coverage_profile_is_superset,
    spec_coverage_fold_signature,
    spec_coverage_profile,
    spec_coverage_quality_score,
    spec_family_merge_signature,
    spec_structural_fingerprint,
)
from .solver_workflow import (
    apply_diagnostic_feedback_hints as _apply_diagnostic_feedback_hints_base,
    build_diagnostic_feedback_hints as _build_diagnostic_feedback_hints_base,
    build_key_miss_entry as _build_key_miss_entry_base,
    diagnostic_entry_has_feedback as _diagnostic_entry_has_feedback_base,
    diagnostic_entry_score as _diagnostic_entry_score_base,
    diagnose_missing_tokens_for_key as _diagnose_missing_tokens_for_key_base,
    diagnostic_token_location as _diagnostic_token_location_base,
    diagnose_operand_token_is_value_alias as _diagnose_operand_token_is_value_alias_base,
    flat_operand_signature as _flat_operand_signature_base,
    load_diagnostic_feedback_hints as _load_diagnostic_feedback_hints_base,
    normalized_token_counter_from_parsed as _normalized_token_counter_from_parsed_base,
    operand_instance_fingerprint as _operand_instance_fingerprint_base,
    prepare_spec_for_html as _prepare_spec_for_html_base,
    select_feedback_seed_instruction as _select_feedback_seed_instruction_base,
    set_diagnostic_feedback_hints as _set_diagnostic_feedback_hints_base,
    token_in_parsed as _token_in_parsed_base,
    variable_operand_indices_for_analysis_key as _variable_operand_indices_for_analysis_key_base,
    visible_tokens_from_spec as _visible_tokens_from_spec_base,
    write_diagnostic_report as _write_diagnostic_report_base,
    InstructionSolverDriver,
    build_arg_parser,
)
from .modifier_domain import (
    backfill_modifier_tables_from_ranges as _backfill_modifier_tables_from_ranges_base,
    chosen_display_from_rows as _chosen_display_from_rows_base,
    compress_modifier_constant_bits as _compress_modifier_constant_bits_base,
    concrete_modifier_names as _concrete_modifier_names_base,
    clean_modifier_row_name as _clean_modifier_row_name_base,
    emit_modifier_constant_segments as _emit_modifier_constant_segments_base,
    factorize_operand_modifier_groups_from_rows as _factorize_operand_modifier_groups_from_rows_base,
    factorize_modifier_groups_from_rows as _factorize_modifier_groups_from_rows_base,
    filter_non_placeholder_modifiers as _filter_non_placeholder_modifiers_base,
    get_operand_modifier_rows as _get_operand_modifier_rows_base,
    has_placeholder_modifier as _has_placeholder_modifier_base,
    is_diagnose_noise_token as _is_diagnose_noise_token_base,
    is_placeholder_modifier as _is_placeholder_modifier_base,
    normalize_modifier_rows as _normalize_modifier_rows_base,
    sanitize_disasm as _sanitize_disasm_base,
    sanitize_modifier_display_name as _sanitize_modifier_display_name_base,
    split_token_parts as _split_token_parts_base,
    try_split_modifier_groups as _try_split_modifier_groups_base,
    unify_spec_modifiers as _unify_spec_modifiers_base,
    attach_half_pair_overlay_operand_modifiers as _attach_half_pair_overlay_operand_modifiers_base,
)
from .encoding_model import (
    EncodingRange,
    EncodingRanges,
    EncodingRangeType,
    OPERAND_MODIFIER_ENUM_MAX,
    analyse_modifiers,
    find_modifier_difference,
    generate_modifier_table,
    operand_colors,
)
from . import table_utils
from . import parser
from .parser import InstructionParser, Instruction
from .life_range import analyse_live_ranges, get_interaction_ranges, InteractionType

# 缓存（cache）回退仅用于“同 key 干净编码替换”，不做无证据 token 合成。
ENABLE_CACHE_FALLBACK = True
# 与 orign 保持一致：主动 mutation 仅覆盖 bit 0..109。
MUTATION_ANALYSIS_END_BIT = 14 * 8 - 2
# 多修饰符（modifier）位段（range）联合枚举上限（用于 cross-range 证据提取）。
MODIFIER_CARTESIAN_MAX_ENUM = 32768
OPERAND_MODIFIER_RECLASSIFY_MAX_BITS = max(
    1, int(OPERAND_MODIFIER_ENUM_MAX).bit_length() - 1
)
# 缓存（cache）差分补位的样本上限，避免重 key 在固定点里反复全量扫描导致超时。
CACHE_AUGMENT_MAX_SAMPLES = int(
    os.environ.get("NV_ISA_SOLVER_CACHE_AUGMENT_MAX_SAMPLES", "1024")
)
# 控制码字段起点（按当前实现：第 14 字节 bit1，即 bit105）。
# 这些位不应被操作数（operand）/修饰符（modifier）解析逻辑“误认”为 operand_modi 等语义位。
CONTROL_CODE_START_BIT = 13 * 8 + 1
# stall(4) + y(1) + r-bar(3) + w-bar(3) + b-mask(6) + reuse(4) = 21 位
CONTROL_CODE_KNOWN_BITS = 21
CONTROL_CODE_END_BIT = CONTROL_CODE_START_BIT + CONTROL_CODE_KNOWN_BITS


class _SolverProfiler:
    def __init__(self):
        raw = os.environ.get("NV_ISA_SOLVER_PROFILE", "").strip().lower()
        self.enabled = raw not in ("", "0", "false", "no", "off")
        self.output_path = os.environ.get("NV_ISA_SOLVER_PROFILE_OUT", "").strip()
        self._lock = threading.RLock()
        self._stats = {}
        self._registered = False
        if self.enabled:
            self._register_atexit()

    def _register_atexit(self):
        if self._registered:
            return
        atexit.register(self._emit_summary)
        self._registered = True

    @contextlib.contextmanager
    def section(self, name: str):
        if not self.enabled:
            yield
            return
        started = time.perf_counter()
        try:
            yield
        finally:
            elapsed = time.perf_counter() - started
            self.record(name, elapsed)

    def record(self, name: str, elapsed_sec: float):
        if not self.enabled:
            return
        with self._lock:
            bucket = self._stats.setdefault(
                name,
                {
                    "count": 0,
                    "total_sec": 0.0,
                    "max_sec": 0.0,
                },
            )
            bucket["count"] += 1
            bucket["total_sec"] += float(elapsed_sec)
            if elapsed_sec > bucket["max_sec"]:
                bucket["max_sec"] = float(elapsed_sec)

    def _emit_summary(self):
        if not self.enabled:
            return
        with self._lock:
            if not self._stats:
                return
            summary = {
                "type": "nv_isa_solver_profile",
                "sections": [],
            }
            for name, stats in sorted(
                self._stats.items(),
                key=lambda item: item[1]["total_sec"],
                reverse=True,
            ):
                count = int(stats["count"])
                total_sec = float(stats["total_sec"])
                avg_sec = (total_sec / count) if count else 0.0
                summary["sections"].append(
                    {
                        "name": name,
                        "count": count,
                        "total_sec": round(total_sec, 6),
                        "avg_sec": round(avg_sec, 6),
                        "max_sec": round(float(stats["max_sec"]), 6),
                    }
                )
        payload = json.dumps(summary, ensure_ascii=False)
        try:
            if self.output_path:
                with open(self.output_path, "w", encoding="utf-8") as f:
                    f.write(payload + "\n")
            else:
                sys.stderr.write(payload + "\n")
                sys.stderr.flush()
        except Exception:
            pass


_SOLVER_PROFILER = _SolverProfiler()


def _profile_section(name: str):
    return _SOLVER_PROFILER.section(name)


def _should_reclassify_modifier_range_as_operand_modifier(rng) -> bool:
    try:
        return int(getattr(rng, "length", 0) or 0) <= OPERAND_MODIFIER_RECLASSIFY_MAX_BITS
    except Exception:
        return False


def _warn_skipped_operand_modifier_reclassification(rng, analysis_key, mapped_idx, group):
    try:
        preview = []
        for _value, name in list(group or []):
            if not name or not isinstance(name, str):
                continue
            clean = name.rstrip(".")
            if clean and clean not in preview:
                preview.append(clean)
            if len(preview) >= 4:
                break
        sys.stderr.write(
            "[nv_isa_solver] skipped operand modifier reclassification: "
            f"analysis_key={analysis_key or '<unknown>'} "
            f"operand_index={mapped_idx} "
            f"start={getattr(rng, 'start', None)} "
            f"length={getattr(rng, 'length', None)} "
            f"max_bits={OPERAND_MODIFIER_RECLASSIFY_MAX_BITS} "
            f"names={preview}\n"
        )
        sys.stderr.flush()
    except Exception:
        pass


def _is_control_code_bit(bit_index: int) -> bool:
    try:
        return CONTROL_CODE_START_BIT <= int(bit_index) < CONTROL_CODE_END_BIT
    except Exception:
        return False


def _cache_iter(disassembler):
    """遍历全部缓存（cache）（兜底路径）。常规路径优先用按 key 索引。"""
    if not ENABLE_CACHE_FALLBACK:
        return tuple()
    try:
        return tuple(disassembler.get_cache_items())
    except Exception:
        try:
            return tuple(disassembler.cache.items())
        except Exception:
            return tuple(list(disassembler.cache.items()))


def _cache_iter_by_key(disassembler, target_key):
    """按 parsed key 获取缓存（cache）候选。索引缺失时退化为全表过滤。"""
    if not ENABLE_CACHE_FALLBACK or not target_key:
        return tuple()
    candidates = disassembler.get_cache_candidates(target_key)
    if candidates:
        return tuple(candidates)
    # 回退：cache_by_key 可能因解析差异未索引该 key，遍历缓存（cache）按 key 过滤
    result = []
    for inst_b, asm_text in _cache_iter(disassembler):
        try:
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if not lines:
                continue
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() == target_key:
                result.append((inst_b, asm_text))
        except Exception:
            continue
    return tuple(result)


def _verified_disasm_line_for_inst(
    disassembler,
    inst_bytes,
    *,
    expected_key=None,
    expected_family_head=None,
):
    """对最终编码做一次当前 arch 的真实反汇编校验。"""
    try:
        out = disassembler.disassemble(inst_bytes)
    except Exception:
        return None
    if not out:
        return None

    try:
        lines = [line for line in str(out).splitlines() if line.strip()]
        asm_line = lines[-1] if lines else str(out)
        asm_line = sanitize_disasm(asm_line)
        parsed = InstructionParser.parseInstruction(asm_line)
    except Exception:
        return None

    if expected_key is not None:
        try:
            if parsed.get_key() != expected_key:
                return None
        except Exception:
            return None

    if expected_family_head is not None:
        try:
            family_head = _extract_mnemonic_head_from_disasm(asm_line)
        except Exception:
            family_head = None
        if family_head != expected_family_head:
            expected_text = str(expected_family_head)
            if "." in expected_text:
                return None
            actual_base = family_head.split(".", 1)[0] if isinstance(family_head, str) else None
            if actual_base != expected_text:
                return None

    return asm_line, parsed


def _refresh_spec_display_from_inst(spec, disassembler, *, expected_family_head=None):
    """用 spec 当前编码的真实反汇编刷新展示文本。"""
    try:
        expected_key = spec.parsed.get_key()
    except Exception:
        expected_key = None
    if expected_family_head is None:
        try:
            expected_family_head = getattr(spec.parsed, "base_name", None)
        except Exception:
            expected_family_head = None

    verified = _verified_disasm_line_for_inst(
        disassembler,
        spec.ranges.inst,
        expected_key=expected_key,
        expected_family_head=expected_family_head,
    )
    if verified is None:
        return False

    asm_line, parsed = verified
    spec.disasm = asm_line
    spec.parsed = parsed
    try:
        spec.opcode_modis = spec._get_opcode_modis()
    except Exception:
        pass
    try:
        parsed_mods = [
            m.rstrip(".")
            for m in (getattr(spec.parsed, "modifiers", []) or [])
            if isinstance(m, str) and m and not is_placeholder_modifier(m)
        ]
        if parsed_mods:
            spec.canonical_name = ".".join([spec.parsed.base_name] + parsed_mods)
        else:
            spec.canonical_name = ".".join(
                [spec.parsed.base_name] + (getattr(spec, "opcode_modis", []) or [])
            )
    except Exception:
        pass
    return True


def _get_spec_disasm_modifier_context(spec):
    try:
        disasm_mod_list = [
            m.rstrip(".")
            for m in (getattr(spec.parsed, "modifiers", []) or [])
            if isinstance(m, str) and m and not is_placeholder_modifier(m)
        ]
    except Exception:
        disasm_mod_list = []
    return disasm_mod_list, set(disasm_mod_list)


def _sync_spec_parsed_modifiers(spec, original_parser_modifiers=None):
    try:
        disasm_mod_list, disasm_mods = _get_spec_disasm_modifier_context(spec)

        new_parsed_mods = []
        for grp in getattr(spec, "modifiers", []) or []:
            if grp and len(grp) > 0:
                nm = grp[0][1]
                if isinstance(nm, str):
                    nm = nm.rstrip(".")
                if nm and not is_placeholder_modifier(nm):
                    new_parsed_mods.append(nm)

        opcode_clean = []
        try:
            for m in getattr(spec, "opcode_modis", []) or []:
                if (
                    isinstance(m, str)
                    and not is_placeholder_modifier(m)
                    and (not disasm_mods or m in disasm_mods)
                ):
                    opcode_clean.append(m)
        except Exception:
            opcode_clean = []

        if disasm_mods:
            new_parsed_mods = [m for m in new_parsed_mods if m in disasm_mods]

        evidence = set()
        try:
            for mr in spec.ranges._find(EncodingRangeType.MODIFIER):
                if mr.name and isinstance(mr.name, str) and not is_placeholder_modifier(mr.name):
                    evidence.add(mr.name.rstrip("."))
        except Exception:
            pass
        try:
            for grp in getattr(spec, "modifiers", []) or []:
                for _, name in grp:
                    if isinstance(name, str) and not is_placeholder_modifier(name):
                        evidence.add(name.rstrip("."))
        except Exception:
            pass

        cleaned = []
        for token in opcode_clean + new_parsed_mods + disasm_mod_list:
            if not isinstance(token, str):
                continue
            t = token.rstrip(".")
            if not t or is_placeholder_modifier(t):
                continue
            if disasm_mods and t not in disasm_mods:
                continue
            if t not in cleaned:
                cleaned.append(t)
        for token in original_parser_modifiers or []:
            if not isinstance(token, str):
                continue
            t = token.rstrip(".")
            if not t or is_placeholder_modifier(t):
                continue
            if disasm_mods and t not in disasm_mods:
                continue
            if t not in cleaned:
                cleaned.append(t)

        if cleaned:
            spec.parsed.modifiers = cleaned
        elif disasm_mods:
            spec.parsed.modifiers = sorted(disasm_mods)
        elif evidence:
            spec.parsed.modifiers = sorted(evidence)
    except Exception:
        pass


def _disasm_text_is_unclean(text):
    try:
        return (not text) or ("???" in text) or (".." in text) or re.search(
            r'(?<!\w)INVALID(?!\w)', text, flags=re.IGNORECASE
        )
    except Exception:
        return True


def _try_repair_spec_disasm(
    spec,
    disassembler,
    *,
    target_key=None,
    expected_family_head=None,
    evidence_bits=None,
):
    """当 spec 当前编码反汇编结果不干净时，尝试用 cache/枚举修补。"""
    try:
        final_asm = disassembler.disassemble(spec.ranges.inst)
    except Exception:
        final_asm = None
    if not _disasm_text_is_unclean(final_asm):
        return True

    if target_key is None:
        try:
            target_key = spec.parsed.get_key()
        except Exception:
            target_key = None
    if expected_family_head is None:
        try:
            expected_family_head = getattr(spec.parsed, "base_name", None)
        except Exception:
            expected_family_head = None

    def _adopt_clean_inst(clean_inst, asm_line, parsed):
        try:
            spec.disasm = sanitize_disasm(asm_line)
            spec.parsed = parsed
            spec.ranges = EncodingRanges(spec.ranges.ranges, bytes(clean_inst))
        except Exception:
            return False
        try:
            unify_spec_modifiers(spec)
        except Exception:
            pass
        return True

    try:
        for inst_b, asm_text in _cache_iter_by_key(disassembler, target_key):
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if not lines:
                continue
            asm_line = lines[-1]
            if _disasm_text_is_unclean(asm_line):
                continue
            try:
                parsed = InstructionParser.parseInstruction(asm_line)
            except Exception:
                continue
            if parsed.get_key() != target_key:
                continue
            if expected_family_head:
                try:
                    family_head = _extract_mnemonic_head_from_disasm(asm_line)
                except Exception:
                    family_head = None
                if family_head != expected_family_head and (
                    not isinstance(family_head, str)
                    or family_head.split(".", 1)[0] != str(expected_family_head)
                ):
                    continue
            try:
                clean_inst = disassembler.distill_instruction(inst_b)
            except Exception:
                clean_inst = inst_b
            if _adopt_clean_inst(clean_inst, asm_line, parsed):
                return True
    except Exception:
        pass

    try:
        found = enumerate_all_combinations(
            spec.ranges,
            disassembler,
            max_enum=4096,
            target_key=target_key,
            evidence_bits=evidence_bits,
        )
        if found:
            clean_inst = found if isinstance(found, (bytes, bytearray)) else bytes(found)
            asm_text = disassembler.disassemble(clean_inst)
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if lines:
                asm_line = lines[-1]
                if not _disasm_text_is_unclean(asm_line):
                    try:
                        parsed = InstructionParser.parseInstruction(asm_line)
                    except Exception:
                        parsed = None
                    if parsed is not None and parsed.get_key() == target_key:
                        try:
                            clean_inst = disassembler.distill_instruction(clean_inst)
                        except Exception:
                            pass
                        if _adopt_clean_inst(clean_inst, asm_line, parsed):
                            return True
    except Exception:
        pass

    return False




def _spec_final_consistent(spec, disassembler):
    """校验 spec 一致性：反汇编（disasm）无占位符，且 parsed.modifiers 有位证据。"""
    try:
        with _profile_section("final_consistency"):
            if not _refresh_spec_display_from_inst(spec, disassembler):
                return False
            # _refresh_spec_display_from_inst 已确保 spec.disasm 来自当前 arch 的真实反汇编。
            out = getattr(spec, "disasm", None)
            if (not out) or ("???" in out) or (".." in out) or re.search(r'(?<!\w)INVALID(?!\w)', out, flags=re.IGNORECASE):
                return False

            # 从位段（range）与 spec.modifiers 收集可作为证据的名称
            evidence = set()
            try:
                for mr in spec.ranges._find(EncodingRangeType.MODIFIER):
                    if mr.name and isinstance(mr.name, str) and not is_placeholder_modifier(mr.name):
                        evidence.add(mr.name.rstrip('.'))
            except Exception:
                pass
            try:
                for grp in getattr(spec, 'modifiers', []) or []:
                    for _, name in grp:
                        if isinstance(name, str) and not is_placeholder_modifier(name):
                            evidence.add(name.rstrip('.'))
            except Exception:
                pass

            # 每个非占位符 parsed 修饰符（modifier）都必须能被证据表示
            try:
                parsed_now = getattr(spec.parsed, 'modifiers', []) or []
                for pm in parsed_now:
                    try:
                        if is_placeholder_modifier(pm):
                            continue
                    except Exception:
                        continue
                    if pm not in evidence:
                        return False
            except Exception:
                return False

            return True
    except Exception:
        return False


def enumerate_all_combinations(ranges, disassembler, max_enum=32768, target_key=None, evidence_bits=None):
    """有界穷举修饰符（modifier）组合，返回第一个“可稳定反汇编（disasm）”的候选编码（encoding）。

    伪代码:
        1) 构造候选编码迭代器 inst_bytes_iter()
           - 若 evidence_bits 非空：只在这些 bit 上做 0/1 笛卡尔积
              - 否则：对所有 MODIFIER 位段（range）的取值空间做笛卡尔积
        2) 对每个候选字节序列:
              - disassemble -> 取最后一行反汇编（disasm）指令
           - parseInstruction
           - 若 target_key 指定且 key 不匹配则跳过
              - 若修饰符（modifier）含占位符则跳过
           - 返回 distill_instruction(inst_bytes)；若失败返回原始 inst_bytes
        3) 枚举耗尽或异常则返回 None

    数据结构:
        - ranges: EncodingRanges，提供 _find()/encode()/inst/operand_count()
        - evidence_bits: 可迭代 bit 下标（会转成 list）
        - domains: list[range]，给 itertools.product 做取值域
        - tried: int，跨迭代器与外层共享的枚举计数上限
        - 返回值: Optional[bytes]

    复杂语法:
        - 嵌套生成器 + nonlocal（inst_bytes_iter 修改外层 tried）
        - itertools.product(*domains) 做多维枚举
        - any(is_placeholder_modifier(...)) 做占位符过滤
        - set_bit_range 对 bytearray 指定位段（range）写值
    """
    try:
        from itertools import product
        tried = 0

        # 构建候选 inst_bytes 的迭代器
        def inst_bytes_iter():
            """按两种模式产生候选编码（encoding）字节流（惰性生成）。

            伪代码:
                if evidence_bits:
                    bit_list = list(evidence_bits)
                    for combo in product([0,1]^len(bit_list)):
                        若 tried 超上限则 break
                        在 ranges.inst 拷贝上逐位 set_bit_range
                        yield bytes(inst_arr)
                else:
                    mod_ranges = ranges._find(MODIFIER)
                    domains = [range(2**r.length) ...]
                    operand_values = [0] * ranges.operand_count()
                    for combo in product(*domains):
                        若 tried 超上限则 break
                        yield ranges.encode(operand_values, combo)

            数据结构:
                - bit_list: list[int]
                - inst_arr: bytearray（每次组合独立拷贝）
                - mod_ranges: list[EncodingRange]（修饰符位段）
                - operand_values: list[int]（仅提供默认零值）

            复杂语法:
                - 生成器函数 `yield`
                - `product(*domains)` 的可变参数展开
                - `zip(combo, bit_list)` 同步遍历值和 bit 位置
            """
            nonlocal tried
            if evidence_bits:
                bit_list = list(evidence_bits)
                domains = [range(2) for _ in bit_list]
                for combo in product(*domains):
                    tried += 1
                    if tried > max_enum:
                        break
                    try:
                        inst_arr = bytearray(ranges.inst)
                        for v, bit in zip(combo, bit_list):
                            set_bit_range(inst_arr, bit, bit + 1, v)
                        yield bytes(inst_arr)
                    except Exception:
                        continue
            else:
                mod_ranges = ranges._find(EncodingRangeType.MODIFIER)
                if not mod_ranges:
                    return
                domains = [range(2 ** r.length) for r in mod_ranges]
                operand_count = ranges.operand_count()
                operand_values = [0] * operand_count
                for combo in product(*domains):
                    tried += 1
                    if tried > max_enum:
                        break
                    try:
                        yield ranges.encode(operand_values, list(combo))
                    except Exception:
                        continue

        for inst_bytes in inst_bytes_iter():
            try:
                asm = disassembler.disassemble(inst_bytes)
                lines = [l for l in asm.splitlines() if l.strip()]
                if not lines:
                    continue
                asm_line = lines[-1]
                parsed = InstructionParser.parseInstruction(asm_line)
                if target_key and parsed.get_key() != target_key:
                    continue
                # 跳过包含占位符的修饰符（modifier）解析结果
                if has_placeholder_modifier(getattr(parsed, 'modifiers', [])):
                    continue
                # 找到候选
                try:
                    return disassembler.distill_instruction(inst_bytes)
                except Exception:
                    return inst_bytes
            except Exception:
                continue
        return None
    except Exception:
        return None


def _find_clean_cache_candidate(disassembler, parsed_inst):
    """从缓存（cache）中挑选“同 key 且无占位符”的干净样本，不做额外枚举验证。

    伪代码:
        1) target_key = parsed_inst.get_key()
        2) 先调用 _try_candidates([target_key])
        3) 若失败且 parsed_inst.modifiers（修饰符）含占位符:
           - 取 base_name
           - 从 base_name 索引中获取同 base 的 key 列表
           - 再调用 _try_candidates(all_keys)
        4) 成功返回 (parsed_cand, groups, clean_inst_bytes, clean_asm_line)
           失败返回 None

    数据结构:
        - all_keys: list[str]（同 base 的候选 key）
        - groups: list[list[tuple[int, str]]]，与修饰符（modifier）组结构兼容
        - 返回: Optional[tuple[Instruction, list, bytes, str]]

    复杂语法:
        - 内部函数封装搜索策略，复用同一筛选逻辑
        - 列表推导筛 key 前缀
        - `any(is_placeholder_modifier(...))` 占位符检测
    """
    try:
        if not ENABLE_CACHE_FALLBACK:
            return None
        try:
            target_key = parsed_inst.get_key()
        except Exception:
            return None

        def _try_candidates(keys_to_try):
            """按给定 key 列表顺序查找首个可用干净样本。

            伪代码:
                for tk in keys_to_try:
                    for (inst_b, asm_text) in cache_by_key[tk]:
                        parse 最后一行
                        若 key 不一致或 modifiers 含占位符 -> continue
                        构造 groups（每个修饰符 modifier 一组）
                        return parsed_cand, groups, bytes(inst_b), asm_line
                return None

            数据结构:
                - keys_to_try: Iterable[str]
                - cand_mods: list[str]
                - groups: list[list[tuple[int, str]]]

            复杂语法:
                - 双层循环短路返回（first-hit）
                - 容错返回策略：组构造失败时降级为空 groups
            """
            for tk in keys_to_try:
                for inst_b, asm_text in _cache_iter_by_key(disassembler, tk):
                    try:
                        if not asm_text or not isinstance(asm_text, str):
                            continue
                        lines = [l for l in asm_text.splitlines() if l.strip()]
                        if not lines:
                            continue
                        parsed_cand = InstructionParser.parseInstruction(lines[-1])
                        if parsed_cand.get_key() != tk:
                            continue
                        cand_mods = getattr(parsed_cand, 'modifiers', []) or []
                        if has_placeholder_modifier(cand_mods):
                            continue
                        groups = []
                        try:
                            for m in cand_mods:
                                if not m:
                                    groups.append([(0, "")])
                                else:
                                    groups.append([(0, m + '.')])
                            clean_asm = lines[-1]
                            return parsed_cand, groups, bytes(inst_b), clean_asm
                        except Exception:
                            return parsed_cand, [], bytes(inst_b), lines[-1] if lines else ""
                    except Exception:
                        continue
            return None

        # 先尝试同 key
        res = _try_candidates([target_key])
        if res:
            return res

        # 回退：若目标含占位符，尝试同 base 的候选
        # （例如 UTCSHIFT.???0 -> 尝试 UTCSHIFT.DOWN、UTCSHIFT.2CTA.DOWN）
        try:
            parsed_mods = getattr(parsed_inst, 'modifiers', []) or []
            if has_placeholder_modifier(parsed_mods):
                base = getattr(parsed_inst, 'base_name', None)
                if base:
                    all_keys = disassembler.get_cache_keys_for_base(base)
                    if all_keys:
                        res = _try_candidates(all_keys)
                        if res:
                            return res
        except Exception:
            pass
        return None
    except Exception:
        return None


def _collect_modifier_evidence_bits(mutation_set):
    try:
        if mutation_set is not None and getattr(mutation_set, "modifier_bits", None):
            return set(mutation_set.modifier_bits)
    except Exception:
        pass
    return None


def _has_concrete_modifier_names(modifier_values, operand_modifier_values=None):
    try:
        for group in modifier_values or []:
            for _, name in group or []:
                if name and not is_placeholder_modifier(name):
                    return True
    except Exception:
        pass
    try:
        for rows in (operand_modifier_values or {}).values():
            for _, name in rows or []:
                if name and not is_placeholder_modifier(name):
                    return True
    except Exception:
        pass
    return False


def _recover_placeholder_modifier_state(disassembler, parsed_inst, ranges, mutation_set):
    try:
        rem = _find_clean_cache_candidate(disassembler, parsed_inst)
        if rem:
            parsed_inst, modifier_values, clean_inst, clean_asm = rem
            return {
                "parsed_inst": parsed_inst,
                "modifier_values": modifier_values,
                "ranges": EncodingRanges(ranges.ranges, clean_inst),
                "asm": clean_asm,
                "reanalysis_inst": bytes(clean_inst),
            }
    except Exception:
        return None

    try:
        target_key = parsed_inst.get_key()
    except Exception:
        return None

    found = enumerate_all_combinations(
        ranges,
        disassembler,
        max_enum=4096,
        target_key=target_key,
        evidence_bits=_collect_modifier_evidence_bits(mutation_set),
    )
    if not found:
        return None

    try:
        inst_bytes = found if isinstance(found, (bytes, bytearray)) else bytes(found)
        asm_text = disassembler.disassemble(inst_bytes)
        lines = [l for l in asm_text.splitlines() if l.strip()]
        if not lines:
            return None
        parsed_cand = InstructionParser.parseInstruction(lines[-1])
        groups = []
        for mod_name in getattr(parsed_cand, "modifiers", []) or []:
            if not mod_name:
                groups.append([(0, "")])
            else:
                groups.append([(0, mod_name + ".")])
        return {
            "parsed_inst": parsed_cand,
            "modifier_values": groups,
            "ranges": ranges,
            "asm": asm_text,
            "reanalysis_inst": bytes(inst_bytes),
        }
    except Exception:
        return None


def _augment_predicate_bits_from_cache(disassembler, target_key, predicate_bits_set):
    """利用缓存（cache）差分补充谓词（predicate）控制位。

    伪代码:
          1) 先按“非谓词（predicate）语义面”分桶：
           surface_sig = (base_name, modifiers, flat_operands_signature)
          2) 每个桶内记录 pred -> inst_hex（同语义、不同谓词 predicate）
          3) 对桶内不同谓词（predicate）样本两两异或:
           - 对每个 byte 计算 xor = b1 ^ b2
           - 展开 xor 的每个置位 bit
           - 跳过 control code 区间位
              - 其余位加入 predicate_bits_set（谓词位）

    数据结构:
        - grouped: dict[surface_sig, dict[predicate, hex_str]]
        - surface_sig: tuple[str, tuple[str], tuple[operand_sig]]
        - predicate_bits_set: set[int]（谓词 predicate 位集合，就地更新）

    复杂语法:
        - 嵌套局部函数构造操作数（operand）/谓词（predicate）签名
        - 分片 `h[j:j+2]` + `int(..., 16)` 做十六进制字节解码
        - 位运算 `xor >> k & 1` 提取 bit 变化
    """
    def _operand_surface_signature(op):
        try:
            return (
                type(op).__name__,
                getattr(op, "reg_type", None),
                getattr(op, "ident", None),
                getattr(op, "constant", None),
                tuple(getattr(op, "modifiers", []) or []),
            )
        except Exception:
            return (type(op).__name__, repr(op))

    def _predicate_surface_signature(parsed):
        try:
            operands = tuple(
                _operand_surface_signature(op)
                for op in (parsed.get_flat_operands() or [])
            )
        except Exception:
            operands = tuple()
        try:
            modifiers = tuple(getattr(parsed, "modifiers", []) or [])
        except Exception:
            modifiers = tuple()
        return (
            getattr(parsed, "base_name", None),
            modifiers,
            operands,
        )

    try:
        grouped = defaultdict(dict)
        for inst_b, asm_text in _cache_iter_by_key(disassembler, target_key):
            try:
                if not asm_text or not isinstance(asm_text, str):
                    continue
                lines = [l for l in asm_text.splitlines() if l.strip()]
                if not lines:
                    continue
                parsed = InstructionParser.parseInstruction(lines[-1])
                if parsed.get_key() != target_key:
                    continue
                pred = getattr(parsed, "predicate", None) or ""
                surface_sig = _predicate_surface_signature(parsed)
                bucket = grouped.setdefault(surface_sig, {})
                if pred not in bucket:
                    bucket[pred] = inst_b.hex()
            except Exception:
                continue

        for pred_to_hex in grouped.values():
            preds = list(pred_to_hex.items())
            if len(preds) < 2:
                continue
            for i, (p1, h1) in enumerate(preds):
                for p2, h2 in preds[i + 1 :]:
                    if p1 == p2 or len(h1) != len(h2):
                        continue
                    for j in range(0, len(h1), 2):
                        b1 = int(h1[j : j + 2], 16)
                        b2 = int(h2[j : j + 2], 16)
                        xor = b1 ^ b2
                        for k in range(8):
                            if (xor >> k) & 1:
                                bit_off = (j // 2) * 8 + k
                                if _is_control_code_bit(bit_off):
                                    continue
                                predicate_bits_set.add(bit_off)
    except Exception:
        pass


def _augment_operand_bits_from_cache(disassembler, parsed_inst, mutation_set):
    """在“同修饰符（modifier）/不同操作数（operand）”样本间做差分，补齐操作数位证据。

    伪代码:
        1) target_key = parsed_inst.get_key()
        2) 收集 sig_to_hex[(mod_sig, op_sig)] = inst_hex
              - mod_sig = (predicate, modifiers)
              - op_sig 由 flat_operands 的 ident/repr 组成（操作数签名）
           - 对 TMEM 等难区分场景，退化为 asm operand 片段签名
        3) 对 sig_to_hex 两两比较:
           - 只比较 mod_sig 相同且 op_sig 不同的样本
              - 按字节 xor，提取变化 bit -> operand_bits（操作数位）
        4) 将 operand_bits 注入 mutation_set:
           - mutation_set.operand_value_bits.update(...)
           - mutation_set.bit_to_operand[bit] = 0
              - 重新 compute_encoding_ranges
          5) 若出现 OPERAND 位段（range），返回 (ranges, parsed_inst, mutation_set)，否则 None

    数据结构:
        - sig_to_hex: dict[(mod_sig, op_sig), hex_str]
        - mod_sig: tuple[str, tuple[str]]
        - op_sig: tuple[str, ...]
        - operand_bits: set[int]
        - bit_to_op: dict[int, int]

    复杂语法:
        - 复合键 dict（tuple 嵌 tuple）做样本索引
        - 生成式构建 op_sig，并带条件 fallback
        - 双重 pairwise 比较 + 位级 xor 提取
    """
    if not ENABLE_CACHE_FALLBACK:
        return None
    try:
        target_key = parsed_inst.get_key()
    except Exception:
        return None

    # 收集 (modifier_sig, operand_sig) -> inst_hex，只 diff 同一修饰符（modifier）下不同操作数（operand）的编码
    sig_to_hex = {}
    for inst_b, asm_text in _cache_iter_by_key(disassembler, target_key):
        try:
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if not lines:
                continue
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() != target_key:
                continue
            if has_placeholder_modifier(getattr(parsed, "modifiers", [])):
                continue
            pred = getattr(parsed, "predicate", None) or ""
            mods = tuple(getattr(parsed, "modifiers", []) or [])
            try:
                ops = parsed.get_flat_operands()
                if ops:
                    op_sig = tuple(
                        str(getattr(o, "ident", o)) if getattr(o, "ident", None) is not None
                        else repr(o)  # AddressOperand/tmem 等 ident 为 None，用 repr 区分
                        for o in ops
                    )
                    # 若仍无法区分（如全为 TMEM_），用 asm 中操作数字段（operand）部分
                    if all(s == "None" or "TMEM_" in s for s in op_sig):
                        asm_line = lines[-1]
                        op_sig = (asm_line.split(";")[0].strip(),)
                else:
                    op_sig = ()
            except Exception:
                op_sig = ()
            mod_sig = (pred, mods)
            if (mod_sig, op_sig) not in sig_to_hex:
                sig_to_hex[(mod_sig, op_sig)] = inst_b.hex()
        except Exception:
            continue

    # 对同一 mod_sig 下不同 op_sig 的编码做 diff
    operand_bits = set()
    bit_to_op = {}
    for (mod_sig, op_sig1), h1 in sig_to_hex.items():
        for (mod_sig2, op_sig2), h2 in sig_to_hex.items():
            if mod_sig != mod_sig2 or op_sig1 == op_sig2 or len(h1) != len(h2):
                continue
            for j in range(0, len(h1), 2):
                b1 = int(h1[j : j + 2], 16)
                b2 = int(h2[j : j + 2], 16)
                xor = b1 ^ b2
                for k in range(8):
                    if (xor >> k) & 1:
                        bit_off = (j // 2) * 8 + k
                        operand_bits.add(bit_off)
                        bit_to_op[bit_off] = 0  # 单 operand 时默认 0

    if not operand_bits:
        return None

    # 注入到 mutation_set 并重新计算位段（range）
    mutation_set.operand_value_bits.update(operand_bits)
    for b, oi in bit_to_op.items():
        mutation_set.bit_to_operand[b] = oi
    ranges = mutation_set.compute_encoding_ranges()
    try:
        setattr(ranges, "_analysis_key", analysis_key or parsed_inst.get_key())
    except Exception:
        pass
    operand_ranges = ranges._find(EncodingRangeType.OPERAND)
    if operand_ranges:
        return ranges, parsed_inst, mutation_set
    return None


def _refine_operand_ranges_from_cache(disassembler: Disassembler, parsed_inst):
    """当当前样本缺少操作数（operand）位段（range）时，改用同 key 缓存（cache）样本重新跑完整分析链。

    伪代码:
        1) target_key = parsed_inst.get_key()
          2) 遍历最多 max_candidates 个同 key 缓存（cache）样本
        3) 对每个样本:
           - distill + disassemble + mutate_inst
           - 构造 InstructionMutationSet
              - 依次运行多个 fixedpoint analysis（flags/operand/fimm/modifier...）
           - compute_encoding_ranges
              - 若得到 OPERAND 位段（range）：返回 (ranges, parsed_cand, mset)
        4) 全部失败返回 None

    数据结构:
        - mutations: list[tuple[int, bytes, str]]（由 disassembler 产生）
        - mset: InstructionMutationSet
        - ranges: EncodingRanges
        - 返回: Optional[tuple[EncodingRanges, Instruction, InstructionMutationSet]]

    复杂语法:
        - 分阶段 fixedpoint 调度（同一 mset 多次迭代）
        - try/except 局部降级：distill 失败时回退原始 bytes
        - 早停策略：首个可生成操作数位段（operand range）的候选立即返回
    """
    try:
        target_key = parsed_inst.get_key()
    except Exception:
        return None

    # 若禁用基于缓存（cache）的回退，则不执行任何操作。
    if not ENABLE_CACHE_FALLBACK:
        return None

    tried = 0
    max_candidates = 128
    # 按 key 索引直接查候选，避免遍历整个缓存（cache）
    for inst_b, asm_text in _cache_iter_by_key(disassembler, target_key):
        if tried >= max_candidates:
            break
        try:
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if not lines:
                continue
            asm_line = lines[-1]
            try:
                p = InstructionParser.parseInstruction(asm_line)
            except Exception:
                continue
            if p.get_key() != target_key:
                continue
            tried += 1

            # 对该候选编码重新执行一次 mutation 分析。
            try:
                clean_inst = disassembler.distill_instruction(inst_b)
            except Exception:
                clean_inst = inst_b
            base_asm = disassembler.disassemble(clean_inst)
            mutations = disassembler.mutate_inst(clean_inst, end=MUTATION_ANALYSIS_END_BIT)
            mset = InstructionMutationSet(clean_inst, base_asm, mutations, disassembler)

            analysis_run_fixedpoint(disassembler, mset, analysis_disambiguate_flags)
            analysis_run_fixedpoint(disassembler, mset, analysis_promote_known_flags)
            analysis_run_fixedpoint(disassembler, mset, analysis_operand_fix)
            analysis_run_fixedpoint(disassembler, mset, analysis_merge_mutually_exclusive_operand_flags)
            analysis_run_fixedpoint(disassembler, mset, analysis_disambiguate_operand_flags)
            analysis_run_fixedpoint(disassembler, mset, analysis_fimm_bridge_constants)
            analysis_run_fixedpoint(disassembler, mset, analysis_augment_modifier_bits_from_cache)
            analysis_run_fixedpoint(disassembler, mset, analysis_extend_modifiers)
            analysis_run_fixedpoint(disassembler, mset, analysis_modifier_splitting)
            ranges = mset.compute_encoding_ranges()

            try:
                operand_ranges = ranges._find(EncodingRangeType.OPERAND)
            except Exception:
                operand_ranges = []
            if operand_ranges:
                # 使用与该编码对应的 parsed 候选
                # 作为新的 parsed_inst 基线。
                try:
                    base_lines = [l for l in base_asm.splitlines() if l.strip()]
                    base_line = base_lines[-1] if base_lines else base_asm
                    parsed_cand = InstructionParser.parseInstruction(base_line)
                except Exception:
                    parsed_cand = p
                return ranges, parsed_cand, mset
        except Exception:
            continue

    return None



def _recover_operand_spec_from_cache(disassembler, target_key, arch_code, max_candidates=256):
    return _recover_operand_spec_from_cache_base(
        disassembler=disassembler,
        target_key=target_key,
        arch_code=arch_code,
        enable_cache_fallback=ENABLE_CACHE_FALLBACK,
        cache_iter_by_key=_cache_iter_by_key,
        instruction_analysis_pipeline=instruction_analysis_pipeline,
        encoding_range_type=EncodingRangeType,
        max_candidates=max_candidates,
    )


def _safe_operand_range_count(spec):
    return _safe_operand_range_count_base(spec, EncodingRangeType)


def _safe_flat_operand_count(spec):
    return _safe_flat_operand_count_base(spec)


def _extract_parsed_key_from_analysis_key(analysis_key: str):
    return _extract_parsed_key_from_analysis_key_base(analysis_key, FAMILY_KEY_DELIM)


def _rank_cache_candidate_for_exact(asm_text: str):
    return _rank_cache_candidate_for_exact_base(
        asm_text,
        instruction_parser=InstructionParser,
        is_placeholder_modifier=is_placeholder_modifier,
    )


def _select_instruction_by_exact_key(disassembler: Disassembler, exact_key: str):
    return _select_instruction_by_exact_key_base(
        disassembler=disassembler,
        exact_key=exact_key,
        family_key_delim=FAMILY_KEY_DELIM,
        cache_iter_by_key=_cache_iter_by_key,
        get_bit_range=get_bit_range,
        extract_mnemonic_head_from_disasm_fn=_extract_mnemonic_head_from_disasm,
        rank_cache_candidate_for_exact_fn=_rank_cache_candidate_for_exact,
        semantic_inst_popcount_fn=_semantic_inst_popcount,
    )

def _flat_operand_signature(parsed_inst):
    return _flat_operand_signature_base(parsed_inst)


def _operand_instance_fingerprint(op):
    return _operand_instance_fingerprint_base(op)


def _variable_operand_indices_for_analysis_key(
    disassembler: Disassembler,
    analysis_key: str,
    parsed_inst=None,
    max_samples: int = 1024,
):
    return _variable_operand_indices_for_analysis_key_base(
        disassembler=disassembler,
        analysis_key=analysis_key,
        parsed_inst=parsed_inst,
        max_samples=max_samples,
        extract_parsed_key_from_analysis_key_fn=_extract_parsed_key_from_analysis_key,
        extract_opcode_from_analysis_key_fn=_extract_opcode_from_analysis_key,
        cache_iter_by_key_fn=_cache_iter_by_key,
        get_bit_range_fn=get_bit_range,
    )


def _normalized_token_counter_from_parsed(parsed_inst):
    return _normalized_token_counter_from_parsed_base(
        parsed_inst,
        split_token_parts_fn=_split_token_parts,
    )


def _split_token_parts(token: str):
    return _split_token_parts_base(token, is_placeholder_modifier)


def _diagnostic_token_location(raw_asm: str, token: str):
    return _diagnostic_token_location_base(
        raw_asm,
        token,
        split_token_parts_fn=_split_token_parts,
    )


def _build_diagnostic_feedback_hints(payload):
    return _build_diagnostic_feedback_hints_base(
        payload,
        diagnostic_token_location_fn=_diagnostic_token_location,
        extract_opcode_from_analysis_key_fn=_extract_opcode_from_analysis_key,
        get_bit_range_fn=get_bit_range,
    )


def _load_diagnostic_feedback_hints(report_path: str):
    return _load_diagnostic_feedback_hints_base(
        report_path,
        diagnostic_token_location_fn=_diagnostic_token_location,
        extract_opcode_from_analysis_key_fn=_extract_opcode_from_analysis_key,
        get_bit_range_fn=get_bit_range,
    )


def _set_diagnostic_feedback_hints(hints):
    return _set_diagnostic_feedback_hints_base(hints)


class InstructionSolverCoreApi:
    def __init__(self):
        self.FAMILY_KEY_DELIM = FAMILY_KEY_DELIM
        self.ENABLE_CACHE_FALLBACK = ENABLE_CACHE_FALLBACK
        self.EncodingRangeType = EncodingRangeType
        self.INSTRUCTION_DESC_HEADER = INSTRUCTION_DESC_HEADER
        self.INSTVIZ_HEADER = table_utils.INSTVIZ_HEADER

    def create_disassembler(self, arch, nvdisasm):
        return Disassembler(arch, nvdisasm=nvdisasm)

    @staticmethod
    def load_diagnostic_feedback_hints(report_path):
        return _load_diagnostic_feedback_hints(report_path)

    @staticmethod
    def set_diagnostic_feedback_hints(hints):
        return _set_diagnostic_feedback_hints(hints)

    @staticmethod
    def select_instruction_by_exact_key(disassembler, exact_key):
        return _select_instruction_by_exact_key(disassembler, exact_key)

    @staticmethod
    def extract_parsed_key_from_analysis_key(analysis_key):
        return _extract_parsed_key_from_analysis_key(analysis_key)

    @staticmethod
    def extract_mnemonic_head_from_disasm(disasm_text):
        return _extract_mnemonic_head_from_disasm(disasm_text)

    @staticmethod
    def build_key_miss_entry(*args, **kwargs):
        return _build_key_miss_entry(*args, **kwargs)

    @staticmethod
    def write_diagnostic_report(report_path, report_entries):
        return _write_diagnostic_report(report_path, report_entries)

    @staticmethod
    def prepare_spec_for_html(spec):
        return _prepare_spec_for_html_base(
            spec,
            is_placeholder_modifier=is_placeholder_modifier,
            get_bit_range_fn=get_bit_range,
            encoding_range_type=EncodingRangeType,
            encoding_range_cls=EncodingRange,
            generate_modifier_table_fn=generate_modifier_table,
            get_operand_modifier_rows_fn=_get_operand_modifier_rows,
        )

    @staticmethod
    def render_spec_html(spec):
        return spec.generate_html()

    @staticmethod
    def instruction_analysis_pipeline(*args, **kwargs):
        return instruction_analysis_pipeline(*args, **kwargs)

    @staticmethod
    def diagnostic_entry_score(diag_entry):
        return _diagnostic_entry_score(diag_entry)

    @staticmethod
    def diagnostic_entry_has_feedback(diag_entry):
        return _diagnostic_entry_has_feedback(diag_entry)

    @staticmethod
    def build_diagnostic_feedback_hints(payload):
        return _build_diagnostic_feedback_hints(payload)

    @staticmethod
    def select_feedback_seed_instruction(diag_entry, current_inst, expected_family_head=None):
        return _select_feedback_seed_instruction(
            diag_entry,
            current_inst,
            expected_family_head=expected_family_head,
        )

    @staticmethod
    def recover_operand_spec_from_cache(disassembler, target_key, arch_code, max_candidates=256):
        return _recover_operand_spec_from_cache(
            disassembler,
            target_key,
            arch_code,
            max_candidates=max_candidates,
        )

    @staticmethod
    def backfill_modifier_tables_from_ranges(spec, disassembler):
        return _backfill_modifier_tables_from_ranges(spec, disassembler)

    @staticmethod
    def safe_flat_operand_count(spec):
        return _safe_flat_operand_count(spec)

    @staticmethod
    def safe_operand_range_count(spec):
        return _safe_operand_range_count(spec)

    @staticmethod
    def safe_parsed_key(spec):
        return _safe_parsed_key(spec)

    @staticmethod
    def variable_operand_indices_for_analysis_key(disassembler, key, parsed_inst=None):
        return _variable_operand_indices_for_analysis_key(
            disassembler,
            key,
            parsed_inst=parsed_inst,
        )

    @staticmethod
    def find_clean_cache_candidate(disassembler, parsed_inst):
        return _find_clean_cache_candidate(disassembler, parsed_inst)

    @staticmethod
    def spec_structural_fingerprint(spec):
        return spec_structural_fingerprint(
            spec,
            is_placeholder_modifier=is_placeholder_modifier,
        )

    @staticmethod
    def spec_family_merge_signature(spec):
        return spec_family_merge_signature(
            spec,
            safe_parsed_key=_safe_parsed_key,
            extract_mnemonic_head_from_disasm=_extract_mnemonic_head_from_disasm,
            is_placeholder_modifier=is_placeholder_modifier,
        )

    @staticmethod
    def spec_coverage_quality_score(spec):
        return spec_coverage_quality_score(
            spec,
            is_placeholder_modifier=is_placeholder_modifier,
        )

    @staticmethod
    def spec_coverage_fold_signature(spec):
        return spec_coverage_fold_signature(
            spec,
            is_placeholder_modifier=is_placeholder_modifier,
        )

    @staticmethod
    def spec_coverage_profile(spec):
        return spec_coverage_profile(
            spec,
            is_placeholder_modifier=is_placeholder_modifier,
        )

    @staticmethod
    def coverage_profile_is_superset(candidate, target):
        return coverage_profile_is_superset(candidate, target)

    @staticmethod
    def is_placeholder_modifier(modifier):
        return is_placeholder_modifier(modifier)

    @staticmethod
    def has_placeholder_modifier(modifiers):
        return has_placeholder_modifier(modifiers)

    @staticmethod
    def filter_non_placeholder_modifiers(modifiers):
        return filter_non_placeholder_modifiers(modifiers)


def _apply_diagnostic_feedback_hints(
    mutation_set,
    parsed_key: str,
    analysis_key: str | None = None,
    feedback_hints=None,
):
    return _apply_diagnostic_feedback_hints_base(
        mutation_set,
        parsed_key,
        mutation_analysis_end_bit=MUTATION_ANALYSIS_END_BIT,
        is_control_code_bit_fn=_is_control_code_bit,
        is_placeholder_modifier_fn=is_placeholder_modifier,
        analysis_key=analysis_key,
        feedback_hints=feedback_hints,
    )


def _write_diagnostic_report(report_path: str, report_entries):
    return _write_diagnostic_report_base(report_path, report_entries)


def _diagnostic_entry_score(diag_entry):
    return _diagnostic_entry_score_base(diag_entry)


def _diagnostic_entry_has_feedback(diag_entry):
    return _diagnostic_entry_has_feedback_base(
        diag_entry,
        diagnostic_token_location_fn=_diagnostic_token_location,
    )


def _select_feedback_seed_instruction(diag_entry, current_inst, expected_family_head=None):
    return _select_feedback_seed_instruction_base(
        diag_entry,
        current_inst,
        diagnostic_token_location_fn=_diagnostic_token_location,
        extract_mnemonic_head_from_disasm_fn=_extract_mnemonic_head_from_disasm,
        expected_family_head=expected_family_head,
    )


def _build_key_miss_entry(
    disassembler: Disassembler,
    analysis_key: str,
    spec,
    *,
    max_tokens: int,
    pair_budget: int,
    max_cache_samples: int,
    family_heads=None,
):
    return _build_key_miss_entry_base(
        disassembler,
        analysis_key,
        spec,
        max_tokens=max_tokens,
        pair_budget=pair_budget,
        max_cache_samples=max_cache_samples,
        extract_parsed_key_from_analysis_key_fn=_extract_parsed_key_from_analysis_key,
        extract_opcode_from_analysis_key_fn=_extract_opcode_from_analysis_key,
        get_bit_range_fn=get_bit_range,
        visible_tokens_from_spec_fn=_visible_tokens_from_spec,
        diagnose_missing_tokens_for_key_fn=_diagnose_missing_tokens_for_key,
        family_heads=family_heads,
    )


def _operand_value_changed_for_diagnose(base_parsed, mutated_parsed):
    try:
        lhs = base_parsed.get_flat_operands()
        rhs = mutated_parsed.get_flat_operands()
        for a, b in zip(lhs, rhs):
            if isinstance(a, (parser.IntIMMOperand, parser.FloatIMMOperand)) and isinstance(
                b, (parser.IntIMMOperand, parser.FloatIMMOperand)
            ):
                if a.compare(b) or _imm_constants_abs_equal(a, b):
                    continue
                return True
            if isinstance(a, parser.RegOperand) and isinstance(b, parser.RegOperand):
                if (
                    getattr(a, "reg_type", None) == "SNOWFLAKE"
                    and getattr(b, "reg_type", None) == "SNOWFLAKE"
                ):
                    if not a.compare(b):
                        return True
                    if tuple(getattr(a, "modifiers", []) or []) != tuple(
                        getattr(b, "modifiers", []) or []
                    ):
                        return True
                    continue
            if not a.compare(b):
                return True
        return False
    except Exception:
        return False


def _diagnose_missing_tokens_for_key(
    disassembler: Disassembler,
    parsed_key: str,
    visible_tokens,
    max_tokens: int = 12,
    pair_budget: int = 256,
    max_cache_samples: int = 4000,
    family_heads=None,
    opcode_value=None,
):
    return _diagnose_missing_tokens_for_key_base(
        disassembler,
        parsed_key,
        visible_tokens,
        max_tokens=max_tokens,
        pair_budget=pair_budget,
        max_cache_samples=max_cache_samples,
        family_heads=family_heads,
        opcode_value=opcode_value,
        cache_iter_by_key_fn=_cache_iter_by_key,
        extract_mnemonic_head_from_disasm_fn=_extract_mnemonic_head_from_disasm,
        parse_instruction_fn=InstructionParser.parseInstruction,
        get_bit_range_fn=get_bit_range,
        has_placeholder_modifier_fn=has_placeholder_modifier,
        split_token_parts_fn=_split_token_parts,
        is_diagnose_noise_token_fn=_is_diagnose_noise_token,
        diagnose_operand_token_is_value_alias_fn=_diagnose_operand_token_is_value_alias,
        token_in_parsed_fn=_token_in_parsed,
        set_bit_fn=set_bit,
        mutation_analysis_end_bit=MUTATION_ANALYSIS_END_BIT,
        operand_value_changed_fn=_operand_value_changed_for_diagnose,
        parser_module=parser,
    )


def diagnose_missing_tokens_for_key(
    disassembler: Disassembler,
    parsed_key: str,
    visible_tokens,
    max_tokens: int = 12,
    pair_budget: int = 256,
    max_cache_samples: int = 4000,
    family_heads=None,
    opcode_value=None,
):
    """公开兼容入口；实际诊断实现已迁移到 solver_workflow.py。"""
    return _diagnose_missing_tokens_for_key(
        disassembler,
        parsed_key,
        visible_tokens,
        max_tokens=max_tokens,
        pair_budget=pair_budget,
        max_cache_samples=max_cache_samples,
        family_heads=family_heads,
        opcode_value=opcode_value,
    )


def _is_diagnose_noise_token(token: str):
    return _is_diagnose_noise_token_base(
        token,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def _diagnose_operand_token_is_value_alias(operand, token: str):
    return _diagnose_operand_token_is_value_alias_base(operand, token, parser)


def _token_in_parsed(parsed, token: str):
    return _token_in_parsed_base(
        parsed,
        token,
        split_token_parts_fn=_split_token_parts,
    )


def _visible_tokens_from_spec(spec):
    return _visible_tokens_from_spec_base(
        spec,
        split_token_parts_fn=_split_token_parts,
        parser_module=parser,
        encoding_range_type=EncodingRangeType,
    )


def attach_half_pair_overlay_operand_modifiers(spec, disassembler):
    return _attach_half_pair_overlay_operand_modifiers_base(
        spec,
        disassembler,
        encoding_range_type=EncodingRangeType,
        set_bit_range_fn=set_bit_range,
        parse_instruction_fn=InstructionParser.parseInstruction,
        split_token_parts_fn=_split_token_parts,
        clean_modifier_row_name_fn=_clean_name_for_row,
        get_operand_modifier_rows_fn=_get_operand_modifier_rows,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def detect_overlay_operand_modifiers_generic(spec, disassembler):
    """公开兼容入口；保留工具脚本依赖的通用 overlay 检测。"""
    result = []
    try:
        key = spec.parsed.get_key()
    except Exception:
        return result
    try:
        inst_base = getattr(spec.ranges, "inst", None)
        if inst_base is None:
            return result
        inst_base = bytearray(inst_base)
    except Exception:
        return result

    opmod_2bit = [
        rng
        for rng in spec.ranges._find(EncodingRangeType.OPERAND_MODIFIER)
        if int(getattr(rng, "length", 0) or 0) == 2
    ]
    flag_1bit = [
        rng
        for rng in spec.ranges._find(EncodingRangeType.OPERAND_FLAG)
        if int(getattr(rng, "length", 0) or 0) == 1
    ]
    opmod_1bit = [
        rng
        for rng in spec.ranges._find(EncodingRangeType.OPERAND_MODIFIER)
        if int(getattr(rng, "length", 0) or 0) == 1
    ]
    for rng in opmod_1bit:
        if getattr(rng, "operand_index", None) is not None:
            flag_1bit.append(rng)

    def _extract_operand_modifier_tokens_all(inst_bytes, op_idx):
        asm = disassembler.disassemble(inst_bytes)
        if not asm:
            return None, None
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            return asm, None
        if parsed.get_key() != spec.parsed.get_key():
            return asm, None
        try:
            ops = parsed.get_flat_operands()
        except Exception:
            return asm, None
        if op_idx < 0 or op_idx >= len(ops):
            return asm, None
        tokens = set()
        try:
            for raw in getattr(ops[op_idx], "modifiers", []) or []:
                for tok in _split_token_parts(raw):
                    if tok and not is_placeholder_modifier(tok):
                        tokens.add(tok)
        except Exception:
            return asm, None
        return asm, tokens

    for main_rng in opmod_2bit:
        op_idx = getattr(main_rng, "operand_index", None)
        if op_idx is None:
            continue
        main_start = main_rng.start
        main_end = main_rng.start + main_rng.length

        for flag_rng in flag_1bit:
            if getattr(flag_rng, "operand_index", None) != op_idx:
                continue
            if main_start <= flag_rng.start < main_end:
                continue
            flag_start = flag_rng.start

            t00 = t01 = t11 = t21 = t31 = None
            for main_val in range(4):
                for overlay in (0, 1):
                    inst_b = bytearray(inst_base)
                    set_bit_range(inst_b, main_start, main_end, main_val)
                    set_bit_range(inst_b, flag_start, flag_start + 1, overlay)
                    asm, tokens = _extract_operand_modifier_tokens_all(bytes(inst_b), op_idx)
                    if asm and "INVALID" in asm:
                        tokens = set()
                    if tokens is None:
                        tokens = set()
                    if main_val == 0 and overlay == 0:
                        t00 = tokens
                    elif main_val == 0 and overlay == 1:
                        t01 = tokens
                    elif main_val == 1 and overlay == 1:
                        t11 = tokens
                    elif main_val == 2 and overlay == 1:
                        t21 = tokens
                    elif main_val == 3 and overlay == 1:
                        t31 = tokens

            if t01 is None:
                t01 = set()
            if t00 is None:
                t00 = set()
            for token in t01:
                if token in t00:
                    continue
                if token in (t11 or set()):
                    continue
                if token in (t21 or set()):
                    continue
                if token in (t31 or set()):
                    continue
                result.append(
                    {
                        "key": key,
                        "operand_index": op_idx,
                        "overlay_token": token,
                        "main_start": main_start,
                        "flag_start": flag_start,
                    }
                )

    return result


def is_placeholder_modifier(m: str) -> bool:
    return _is_placeholder_modifier_base(m)


def _sanitize_modifier_display_name(name):
    return _sanitize_modifier_display_name_base(
        name,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def _get_operand_modifier_rows(operand_modifiers, op_idx, rng=None):
    return _get_operand_modifier_rows_base(operand_modifiers, op_idx, rng=rng)


def filter_non_placeholder_modifiers(mods):
    return _filter_non_placeholder_modifiers_base(
        mods,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def has_placeholder_modifier(mods):
    return _has_placeholder_modifier_base(
        mods,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def _chosen_display_from_rows(rows, encoded_val):
    return _chosen_display_from_rows_base(
        rows,
        encoded_val,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def sanitize_disasm(d: str) -> str:
    return _sanitize_disasm_base(d)


def _normalize_modifier_token(token):
    try:
        if not isinstance(token, str):
            return ""
        clean = token.rstrip(".").strip()
        if not clean or clean == "headerflags" or is_placeholder_modifier(clean):
            return ""
        return clean
    except Exception:
        return ""


def _modifier_tokens_from_name(name):
    tokens = []
    seen = set()
    try:
        parts = _split_token_parts(name)
    except Exception:
        parts = [name]
    for part in parts or []:
        clean = _normalize_modifier_token(part)
        if clean and clean not in seen:
            tokens.append(clean)
            seen.add(clean)
    return tokens


def _modifier_tokens_from_parsed_modifiers(modifiers):
    tokens = []
    seen = set()
    for modifier in modifiers or []:
        for token in _modifier_tokens_from_name(modifier):
            if token not in seen:
                tokens.append(token)
                seen.add(token)
    return tokens


def _collect_modifier_interactions(
    disassembler: Disassembler,
    parsed_inst: Instruction,
    ranges: EncodingRanges,
    modifier_values,
):
    try:
        modifier_ranges = ranges._find(EncodingRangeType.MODIFIER)
    except Exception:
        return []
    if len(modifier_ranges) < 2:
        return []

    domains = []
    total_combos = 1
    try:
        for rng in modifier_ranges:
            domain = range(2 ** int(getattr(rng, "length", 0) or 0))
            domains.append(domain)
            total_combos *= len(domain)
    except Exception:
        return []
    if total_combos <= 0 or total_combos > MODIFIER_CARTESIAN_MAX_ENUM:
        return []

    try:
        operand_values = [0] * ranges.operand_count()
        for rng in ranges._find(EncodingRangeType.OPERAND):
            idx = getattr(rng, "operand_index", None)
            if idx is None or idx < 0 or idx >= len(operand_values):
                continue
            operand_values[idx] = get_bit_range(
                ranges.inst, rng.start, rng.start + rng.length
            )
    except Exception:
        operand_values = []

    try:
        expected_key = parsed_inst.get_key()
    except Exception:
        expected_key = None

    row_tokens = defaultdict(set)
    for group_idx, group in enumerate(modifier_values or []):
        for value, name in group or []:
            try:
                norm_value = int(value)
            except Exception:
                continue
            for token in _modifier_tokens_from_name(name):
                row_tokens[(group_idx, norm_value)].add(token)

    all_combos = list(product(*domains))
    combo_insts = []
    for combo in all_combos:
        try:
            combo_insts.append(ranges.encode(operand_values, list(combo)))
        except Exception:
            combo_insts.append(None)

    disasm_inputs = [inst_bytes for inst_bytes in combo_insts if inst_bytes is not None]
    if not disasm_inputs:
        return []

    try:
        disasm_outputs = disassembler.disassemble_parallel(disasm_inputs)
    except Exception:
        return []
    disasm_iter = iter(disasm_outputs)

    valid_records = []
    observed_values = defaultdict(set)
    for combo, inst_bytes in zip(all_combos, combo_insts):
        if inst_bytes is None:
            continue
        asm = next(disasm_iter, "")
        lines = [line for line in (asm or "").splitlines() if line.strip()]
        if not lines:
            continue
        try:
            combo_parsed = InstructionParser.parseInstruction(lines[-1])
        except Exception:
            continue
        try:
            if expected_key is not None and combo_parsed.get_key() != expected_key:
                continue
        except Exception:
            continue

        combo_tokens = set(
            _modifier_tokens_from_parsed_modifiers(
                getattr(combo_parsed, "modifiers", []) or []
            )
        )
        single_group_tokens = set()
        for group_idx, value in enumerate(combo):
            single_group_tokens.update(row_tokens.get((group_idx, int(value)), set()))
            observed_values[group_idx].add(int(value))
        residual_tokens = tuple(sorted(combo_tokens - single_group_tokens))
        valid_records.append(
            {
                "combo": tuple(int(v) for v in combo),
                "tokens": residual_tokens,
            }
        )

    if not valid_records:
        return []

    token_support = defaultdict(set)
    for record_idx, record in enumerate(valid_records):
        for token in record["tokens"]:
            token_support[token].add(record_idx)

    pair_combo_cache = {}

    def _pair_combo_sets(group_a, group_b):
        key = (group_a, group_b)
        cached = pair_combo_cache.get(key)
        if cached is not None:
            return cached
        mapping = defaultdict(set)
        for record_idx, record in enumerate(valid_records):
            combo = record["combo"]
            mapping[(combo[group_a], combo[group_b])].add(record_idx)
        pair_combo_cache[key] = mapping
        return mapping

    grouped = {}
    for token, support_ids in token_support.items():
        if not support_ids:
            continue
        best = None
        for group_a, group_b in combinations(range(len(modifier_ranges)), 2):
            if len(observed_values.get(group_a, set())) < 2:
                continue
            if len(observed_values.get(group_b, set())) < 2:
                continue
            for pair_vals, combo_ids in _pair_combo_sets(group_a, group_b).items():
                if combo_ids != support_ids:
                    continue
                rank = (len(combo_ids), group_a, group_b, pair_vals[0], pair_vals[1])
                if best is None or rank < best[0]:
                    best = (rank, group_a, group_b, pair_vals)
        if best is None:
            continue
        _rank, group_a, group_b, pair_vals = best
        bucket_key = (group_a, group_b, int(pair_vals[0]), int(pair_vals[1]))
        bucket = grouped.setdefault(
            bucket_key,
            {
                "groups": [group_a, group_b],
                "values": [int(pair_vals[0]), int(pair_vals[1])],
                "tokens": [],
            },
        )
        if token not in bucket["tokens"]:
            bucket["tokens"].append(token)

    interactions = list(grouped.values())
    for entry in interactions:
        entry["tokens"] = sorted(entry["tokens"])
    interactions.sort(
        key=lambda entry: (
            tuple(entry.get("groups", [])),
            tuple(entry.get("values", [])),
            tuple(entry.get("tokens", [])),
        )
    )
    return interactions


def unify_spec_modifiers(spec: "InstructionSpec"):
    return _unify_spec_modifiers_base(
        spec,
        encoding_range_type=EncodingRangeType,
        get_bit_range_fn=get_bit_range,
        is_placeholder_modifier_fn=is_placeholder_modifier,
        filter_non_placeholder_modifiers_fn=filter_non_placeholder_modifiers,
    )


def _normalize_modifier_rows(rows):
    return _normalize_modifier_rows_base(
        rows,
        sanitize_modifier_display_name_fn=_sanitize_modifier_display_name,
    )


def _concrete_modifier_names(rows):
    return _concrete_modifier_names_base(
        rows,
        sanitize_modifier_display_name_fn=_sanitize_modifier_display_name,
    )


def _backfill_modifier_tables_from_ranges(spec: "InstructionSpec", disassembler):
    return _backfill_modifier_tables_from_ranges_base(
        spec,
        disassembler,
        encoding_range_type=EncodingRangeType,
        unify_spec_modifiers_fn=unify_spec_modifiers,
        normalize_modifier_rows_fn=_normalize_modifier_rows,
        concrete_modifier_names_fn=_concrete_modifier_names,
        filter_non_placeholder_modifiers_fn=filter_non_placeholder_modifiers,
    )


def try_split_modifier_groups(
    disassembler: Disassembler, ranges: EncodingRanges, modifier_values
):
    return _try_split_modifier_groups_base(
        disassembler,
        ranges,
        modifier_values,
        encoding_range_type=EncodingRangeType,
        encoding_range_cls=EncodingRange,
        get_bit_range_fn=get_bit_range,
        instruction_parser=InstructionParser,
        filter_non_placeholder_modifiers_fn=filter_non_placeholder_modifiers,
        is_placeholder_modifier_fn=is_placeholder_modifier,
        find_modifier_difference_fn=find_modifier_difference,
    )


def _emit_modifier_constant_segments(
    ranges,
    rng,
    group,
    meaningful_vals,
    bit_kinds,
    new_ranges_list,
    new_modifier_values,
):
    return _emit_modifier_constant_segments_base(
        ranges,
        rng,
        group,
        meaningful_vals,
        bit_kinds,
        new_ranges_list,
        new_modifier_values,
        encoding_range_type=EncodingRangeType,
        encoding_range_cls=EncodingRange,
        get_bit_range_fn=get_bit_range,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def factorize_modifier_groups_from_rows(ranges: EncodingRanges, modifier_values):
    return _factorize_modifier_groups_from_rows_base(
        ranges,
        modifier_values,
        encoding_range_type=EncodingRangeType,
        encoding_range_cls=EncodingRange,
        get_bit_range_fn=get_bit_range,
        is_placeholder_modifier_fn=is_placeholder_modifier,
        find_modifier_difference_fn=find_modifier_difference,
    )


def compress_modifier_constant_bits(ranges: EncodingRanges, modifier_values):
    return _compress_modifier_constant_bits_base(
        ranges,
        modifier_values,
        encoding_range_type=EncodingRangeType,
        encoding_range_cls=EncodingRange,
        get_bit_range_fn=get_bit_range,
        emit_modifier_constant_segments_fn=_emit_modifier_constant_segments,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def analysis_merge_mutually_exclusive_instruction_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """把互斥的 F16/BF16 双 flag 合并为同一 2-bit modifier 组。"""
    flag_map = dict(getattr(mset, "instruction_modifier_bit_flag", {}) or {})
    bits = sorted(flag_map.keys())
    if len(bits) < 2:
        return False

    try:
        base_mods = set(getattr(mset.parsed, "modifiers", []) or [])
    except Exception:
        base_mods = set()

    changed = False
    consumed = set()

    def _probe_mods(flip_bits):
        arr = bytearray(mset.inst)
        for b in flip_bits:
            set_bit(arr, b)
        asm = disassembler.disassemble(arr)
        if not asm:
            return None
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            return None
        if parsed.get_key() != mset.key:
            return None
        mods = set(getattr(parsed, "modifiers", []) or [])
        if any(isinstance(tok, str) and is_placeholder_modifier(tok) for tok in mods):
            return None
        return mods

    for bit in bits:
        adj = bit + 1
        if bit in consumed or adj in consumed:
            continue
        if adj not in flag_map:
            continue

        name_a = flag_map.get(bit)
        name_b = flag_map.get(adj)
        pair = {name_a, name_b}
        # 只处理已证实会互斥的 F16/BF16，避免误合并其他 flag。
        if pair != {"F16", "BF16"}:
            continue

        mods_a = _probe_mods([bit])
        mods_b = _probe_mods([adj])
        if mods_a is None or mods_b is None:
            continue

        a_toggled = (name_a in mods_a) != (name_a in base_mods)
        b_unchanged_in_a = (name_b in mods_a) == (name_b in base_mods)
        b_toggled = (name_b in mods_b) != (name_b in base_mods)
        a_unchanged_in_b = (name_a in mods_b) == (name_a in base_mods)
        if not (a_toggled and b_unchanged_in_a and b_toggled and a_unchanged_in_b):
            continue

        mods_ab = _probe_mods([bit, adj])
        # 若双翻转后两者可同时成立，则它们是独立 flag，不合并。
        if mods_ab is not None and (name_a in mods_ab and name_b in mods_ab):
            continue

        # 合并：从 flag 映射移除，并强制这两位成为同一个 modifier group。
        mset.instruction_modifier_bit_flag.pop(bit, None)
        mset.instruction_modifier_bit_flag.pop(adj, None)
        mset.modifier_bits.add(bit)
        mset.modifier_bits.add(adj)
        start = min(bit, adj)
        # 00 -> 默认空；01 -> F16；10 -> BF16；11 非法/未命名。
        mset.forced_modifier_rows_by_range[(start, 2)] = [
            (0, ""),
            (1, "F16."),
            (2, "BF16."),
        ]
        next_gid = max([0] + list((getattr(mset, "modifier_groups", {}) or {}).values())) + 1
        mset.modifier_groups[bit] = next_gid
        mset.modifier_groups[adj] = next_gid
        mset.protected_modifier_split_bits.add(bit)
        mset.protected_modifier_split_bits.add(adj)
        consumed.add(bit)
        consumed.add(adj)
        changed = True

    return changed


def _imm_constants_abs_equal(lhs, rhs):
    """判断两个立即数 operand 的“绝对值文本/数值”是否相等。"""
    if type(lhs) is not type(rhs):
        return False
    try:
        if isinstance(lhs, parser.IntIMMOperand):
            return abs(int(lhs.constant)) == abs(int(rhs.constant))
        if isinstance(lhs, parser.FloatIMMOperand):
            left = str(lhs.constant).strip()
            right = str(rhs.constant).strip()
            if left.startswith(("+", "-")):
                left = left[1:]
            if right.startswith(("+", "-")):
                right = right[1:]
            return left == right
    except Exception:
        return False
    return False


def _optional_predicate_operand_cnot_toggle(base_parsed, mutated_parsed):
    try:
        if getattr(base_parsed, "base_name", None) != getattr(mutated_parsed, "base_name", None):
            return None
        if tuple(getattr(base_parsed, "modifiers", []) or []) != tuple(
            getattr(mutated_parsed, "modifiers", []) or []
        ):
            return None
        base_ops = list(base_parsed.get_flat_operands() or [])
        mutated_ops = list(mutated_parsed.get_flat_operands() or [])
    except Exception:
        return None

    def _match_prefix(longer, shorter):
        if len(longer) != len(shorter) + 1:
            return None
        try:
            tail = longer[-1]
            if not isinstance(tail, parser.RegOperand):
                return None
            if getattr(tail, "reg_type", None) not in {"UP", "P"}:
                return None
            tail_mods = tuple(getattr(tail, "modifiers", []) or [])
            if "cNOT" not in tail_mods:
                return None
            for a, b in zip(longer[:-1], shorter):
                if type(a) is not type(b):
                    return None
                if not a.compare(b):
                    return None
                if tuple(getattr(a, "modifiers", []) or []) != tuple(
                    getattr(b, "modifiers", []) or []
                ):
                    return None
            return len(longer) - 1
        except Exception:
            return None

    idx = _match_prefix(base_ops, mutated_ops)
    if idx is not None:
        return idx
    idx = _match_prefix(mutated_ops, base_ops)
    if idx is not None:
        return idx
    return None


class InstructionMutationSet:
    """指令变异集合：对 inst 逐位翻转得到 mutations，分析差异归类到 opcode/operand/modifier/predicate 等位集合。"""

    def __init__(self, inst, disasm: str, mutations, disassembler):
        # 规范化指令字节并确保长度至少为 16 字节。
        """初始化对象状态并建立后续流程所需字段。
        
        伪代码:
            1. 执行赋值与状态更新。
            2. 根据条件走不同分支并选择返回/继续路径。
            3. 初始化或更新 disasm_lines。
            4. 初始化或更新 disasm_to_parse。
        数据结构:
            - 输入: inst, disasm, mutations, disassembler。
            - 局部: disasm_lines, disasm_to_parse, has_bad。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 推导式, 生成器表达式, try/except 容错。
        """
        self.inst = bytes(inst)
        if len(self.inst) < 16:
            self.inst = self.inst + b"\x00" * (16 - len(self.inst))
        self.disasm = disasm
        # 清洗 disasm：nvdisasm 可能在真实指令前包含头部行。
        # 解析时使用最后一条非空行作为指令文本。
        disasm_lines = [l for l in self.disasm.splitlines() if l.strip()]
        disasm_to_parse = disasm_lines[-1] if len(disasm_lines) > 0 else self.disasm
        self.parsed = InstructionParser.parseInstruction(disasm_to_parse)

        # 提前挂接 disassembler，便于在构建 mutation 基线时访问其 cache。
        self.disassembler = disassembler

        # 若 parsed modifiers 含占位符（???、INVALID），尝试在
        # disassembler cache 中寻找同 key 且操作数一致、并具有具体
        # modifier 名称的干净变体。若找到，则可作为基线以避免本实例
        # 的高开销枚举。
        try:
            has_bad = has_placeholder_modifier(self.parsed.modifiers)
        except Exception:
            has_bad = False

        # 注意：已禁用基于 cache 的“干净变体”回退。
        # 历史上我们会在 parsed 指令含占位符时，尝试替换为 cache 中
        # 具有具体 modifier 名称的反汇编结果。该行为会从外部数据
        # 合成名称，可能引入无证据支撑的名称。为保证输出严格基于
        # 位证据（mutation/enumeration），这里不查询 disassembler cache。
        # 保持 `self.parsed` 为当前指令真实反汇编的解析结果，并依赖枚举。

        self.mutations = mutations

        self.operand_type_bits = set()
        self.opcode_bits = set()
        self.operand_value_bits = set()
        self.operand_modifier_bits = set()
        self.operand_modifier_bit_flag = {}
        self.instruction_modifier_bit_flag = {}
        self.bit_to_operand = {}
        self.predicate_bits = set()

        self.modifier_bits = set()
        self.modifier_groups = {}
        # 某些位模式可直接给出稳定 modifier 映射（由位翻转证据确定）。
        # 键: (start_bit, length)，值: [(encoded_value, name_with_dot), ...]
        self.forced_modifier_rows_by_range = {}
        # 由 FloatIMM 纠偏提升得到的 modifier 位，后续禁止拆分，避免把函数字段误切成多个 1-bit 组。
        self.protected_modifier_split_bits = set()

        self._analyse()

    def reset_modifier_groups(self):
        """清空 modifier_groups，下次 compute_encoding_ranges 会重新 canonicalize。
        
        伪代码:
            1. 执行赋值与状态更新。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.modifier_groups = {}

    def canonicalize_modifier_groups(self):
        """规范化 modifier 组：为无组的连续位序列分配 group_id，并重新编号为 1,2,3...。
        
        伪代码:
            1. 初始化或更新 max_group_id。
            2. 初始化或更新 fill_mode。
            3. 初始化或更新 fill_id。
            4. 初始化或更新 bits。
            5. 遍历输入集合并在循环内执行条件判断与累积。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: max_group_id, fill_mode, fill_id, bits, max_num。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """

        # 步骤 1：为每个 range 分配编号。
        max_group_id = None
        fill_mode = False
        fill_id = None

        bits = sorted(list(self.modifier_bits))
        for i, bit in enumerate(bits):
            if bit in self.modifier_groups:
                continue
                # 当出现不连续时，应切换 group_id
            if fill_mode and i != 0 and bits[i - 1] != bit - 1:
                fill_mode = False

            if not fill_mode:
                max_group_id = max([0] + list(self.modifier_groups.values()))
                fill_mode = True
                fill_id = max_group_id + 1
                max_group_id = fill_id
            self.modifier_groups[bit] = fill_id

        # 步骤 2：重排编号
        max_num = 0
        num_map = {}
        bits = sorted(list(self.modifier_bits))
        for bit in bits:
            gid = self.modifier_groups[bit]
            if gid not in num_map:
                num_map[gid] = max_num + 1
                max_num += 1
            self.modifier_groups[bit] = num_map[gid]

    def _analyse(self):
        """遍历 mutations，根据反汇编差异将每位归类到 opcode/operand/modifier/predicate 等集合。
        
        伪代码:
            1. 初始化或更新 parsed_operands。
            2. 执行赋值与状态更新。
            3. 遍历输入集合并在循环内执行条件判断与累积。
            4. 优先走主路径，异常时执行兜底分支。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: parsed_operands, asm, mutated_parsed, optional_cnot_operand, mutated_operands。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 try/except 容错, f-string。
        """
        parsed_operands = self.parsed.get_flat_operands()
        self.key = self.parsed.get_key()
        for i_bit, inst, asm in self.mutations:
            # 控制码字段（stall/y/barrier/reuse）不应参与语义位归因：
            # 它们通常不会改变 parsed_key，但可能改变 disasm 表面 token
            #（例如出现/消失 .reuse），容易被误判成 operand_modi。
            if _is_control_code_bit(i_bit):
                continue
            # disassembler 拒绝解码该指令。
            asm = asm.strip()
            if len(asm) == 0:
                self.opcode_bits.add(i_bit)
                continue

            try:
                mutated_parsed = InstructionParser.parseInstruction(asm)
            except Exception:
                # 解析失败则静默跳过本次 mutation。
                continue
            if self.parsed.get_key() != mutated_parsed.get_key():
                optional_cnot_operand = _optional_predicate_operand_cnot_toggle(
                    self.parsed, mutated_parsed
                )
                if optional_cnot_operand is not None:
                    self.bit_to_operand[i_bit] = optional_cnot_operand
                    self.operand_modifier_bits.add(i_bit)
                    self.operand_modifier_bit_flag[i_bit] = "cNOT"
                    continue
                # 注意：是否仅在基线指令不同的情况下才判定为 opcode bit。
                self.opcode_bits.add(i_bit)
                continue

            # 即使 parsed key 不变，也将低位 opcode 区段判为 opcode。
            # 否则某些指令（如 BMOV+SNOWFLAKE）会把 opcode 位错误泄漏到
            # operand/operand-modifier 分类中。
            if i_bit < 12:
                self.opcode_bits.add(i_bit)
                continue

            mutated_operands = mutated_parsed.get_flat_operands()

            if self.parsed.predicate != mutated_parsed.predicate:
                self.predicate_bits.add(i_bit)

            operand_effected = False
            non_float_operand_effected = False
            # 分析 operand 值与 operand modifiers。
            for i, (a, b) in enumerate(zip(mutated_operands, parsed_operands)):
                # 对立即数：先判断 modifier 差异，再判断值差异。
                # 这样 cNEG/cABS 等语义位不会因为 compare() 的值变化被吞进 operand_value。
                if isinstance(b, (parser.IntIMMOperand, parser.FloatIMMOperand)):
                    effected, flag = analyse_modifiers(b.modifiers, a.modifiers)
                    if effected:
                        self.bit_to_operand[i_bit] = i
                        self.operand_modifier_bits.add(i_bit)
                        operand_effected = True
                        if not isinstance(b, parser.FloatIMMOperand):
                            non_float_operand_effected = True
                        if flag:
                            self.operand_modifier_bit_flag[i_bit] = flag
                        continue

                    same_value = a.compare(b) or _imm_constants_abs_equal(a, b)
                    if not same_value:
                        self.operand_value_bits.add(i_bit)
                        self.bit_to_operand[i_bit] = i
                        operand_effected = True
                        if not isinstance(b, parser.FloatIMMOperand):
                            non_float_operand_effected = True
                    continue

                if not a.compare(b):
                    self.operand_value_bits.add(i_bit)
                    self.bit_to_operand[i_bit] = i
                    operand_effected = True
                    if not isinstance(b, parser.FloatIMMOperand):
                        non_float_operand_effected = True
                else:
                    effected, flag = analyse_modifiers(b.modifiers, a.modifiers)
                    if effected:
                        # SNOWFLAKE 风格寄存器枚举在 operand 槽中编码语义值；
                        # parser 可能将别名暴露为 operand modifiers，
                        # 但按位看这些属于 value bits。
                        if (
                            isinstance(b, parser.RegOperand)
                            and getattr(b, "reg_type", None) == "SNOWFLAKE"
                        ):
                            self.operand_value_bits.add(i_bit)
                            self.bit_to_operand[i_bit] = i
                            operand_effected = True
                            non_float_operand_effected = True
                        else:
                            self.bit_to_operand[i_bit] = i
                            self.operand_modifier_bits.add(i_bit)
                            operand_effected = True
                            if not isinstance(b, parser.FloatIMMOperand):
                                non_float_operand_effected = True
                    if flag:
                        self.operand_modifier_bit_flag[i_bit] = flag
            if operand_effected:
                # FIMM 指令可能存在函数选择位，同时改变 parsed FloatIMM 的表面文本；
                # 当仅影响 FloatIMM 操作数时，优先将这些位归类为 instruction modifiers。
                if not non_float_operand_effected:
                    inst_effected, inst_flag = analyse_modifiers(
                        self.parsed.modifiers, mutated_parsed.modifiers
                    )
                    if inst_effected:
                        self.modifier_bits.add(i_bit)
                        self.operand_value_bits.discard(i_bit)
                        self.operand_modifier_bits.discard(i_bit)
                        self.operand_modifier_bit_flag.pop(i_bit, None)
                        self.bit_to_operand.pop(i_bit, None)
                        self.protected_modifier_split_bits.add(i_bit)
                        if inst_flag:
                            self.instruction_modifier_bit_flag[i_bit] = inst_flag
                continue

            # 不在 opcode 区段中查找 modifiers。
            # 否则会把它当成不同指令。
            if i_bit > 12:
                # 分析 instruction modifiers。
                effected, flag = analyse_modifiers(
                    self.parsed.modifiers, mutated_parsed.modifiers
                )
                if effected:
                    self.modifier_bits.add(i_bit)
                if flag:
                    self.instruction_modifier_bit_flag[i_bit] = flag

        # 诊断日志：报告检测到的 modifier 位与分组
        try:
            import logging
            logger = logging.getLogger(__name__)
            logger.info(f"InstructionMutationSet._analyse: detected modifier_bits={sorted(self.modifier_bits)}")
            logger.info(f"InstructionMutationSet._analyse: instruction_modifier_bit_flag={self.instruction_modifier_bit_flag}")
            logger.info(f"InstructionMutationSet._analyse: operand_modifier_bits={sorted(self.operand_modifier_bits)}")
        except Exception:
            pass

    def compute_encoding_ranges(self):
        """从 mutation 分析结果构造 EncodingRanges：按位顺序输出 OPERAND/FLAG/MODIFIER/CONSTANT 等 range。
        
        伪代码:
            1. 初始化或更新 result。
            2. 初始化或更新 current_range。
            3. 执行表达式调用以推进流程。
            4. 定义内部辅助函数 `_push` 并在后续流程中调用。
            5. 遍历输入集合并在循环内执行条件判断与累积。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: result, current_range, i, new_range, control_code_ranges。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, 位运算, try/except 容错, 内嵌函数/闭包。
        """
        result = []
        current_range = None
        self.canonicalize_modifier_groups()

        def _push():
            """函数 `_push` 的实现说明。
            
            伪代码:
                1. 执行顺序语句并更新中间状态。
                2. 根据条件走不同分支并选择返回/继续路径。
                3. 初始化或更新 current_range。
            数据结构:
                - 输入: 无显式位置参数。
                - 局部: current_range。
                - 输出: 主要通过就地更新外部容器/对象状态。
            复杂语法:
                - 使用 条件分支与循环控制。
            """
            nonlocal current_range
            if current_range:
                result.append(current_range)
            current_range = None

        # 显示口径与 orign 保持一致：位图构造始终覆盖 0..127 全部位。
        # 即使主动 mutation 只覆盖到 bit 109，后续位也会在这里按控制码/常量归类并渲染。
        for i in range(0, 8 * 16):
            new_range = None
            # 控制码字段优先：无论该字段当前取值是否为 0，都应以控制码类型呈现，
            # 并且必须覆盖掉任何来自 mutation 的误分类（例如把 y/reuse 误认成 operand_modi）。
            if _is_control_code_bit(i):
                control_code_ranges = [
                    (EncodingRangeType.STALL_CYCLES, 4),
                    (EncodingRangeType.YIELD_FLAG, 1),
                    (EncodingRangeType.READ_BARRIER, 3),
                    (EncodingRangeType.WRITE_BARRIER, 3),
                    (EncodingRangeType.BARRIER_MASK, 6),
                    (EncodingRangeType.REUSE_MASK, 4),
                ]
                offset = CONTROL_CODE_START_BIT
                for rtype, length in control_code_ranges:
                    if i >= offset and i < offset + length:
                        new_range = EncodingRange(rtype, i, 1)
                        break
                    offset += length

                # 落在“已知控制码段”之外（例如 bit126..127）的尾部位，保持后续逻辑处理
                # 为 CONSTANT，这样位图仍能显示真实 bit 值。
            if new_range is None and i in self.modifier_bits:
                if i in self.instruction_modifier_bit_flag:
                    _push()
                    current_range = EncodingRange(
                        EncodingRangeType.FLAG,
                        i,
                        1,
                        name=self.instruction_modifier_bit_flag[i],
                    )
                    _push()
                    continue
                else:
                    new_range = EncodingRange(
                        EncodingRangeType.MODIFIER,
                        i,
                        1,
                        group_id=self.modifier_groups[i],
                    )
            elif new_range is None and i in self.predicate_bits:
                new_range = EncodingRange(EncodingRangeType.PREDICATE, i, 1)
            elif new_range is None and i in self.operand_modifier_bits:
                operand_index = self.bit_to_operand[i]
                # 是否为 flag
                if i in self.operand_modifier_bit_flag:
                    # 无论如何先冲刷当前单元。
                    _push()
                    current_range = EncodingRange(
                        EncodingRangeType.OPERAND_FLAG,
                        i,
                        1,
                        operand_index=operand_index,
                        name=self.operand_modifier_bit_flag[i],
                    )
                    _push()
                    continue
                else:
                    new_range = EncodingRange(
                        EncodingRangeType.OPERAND_MODIFIER,
                        i,
                        1,
                        operand_index=operand_index,
                    )
            elif new_range is None and i in self.operand_value_bits:
                new_range = EncodingRange(
                    EncodingRangeType.OPERAND,
                    i,
                    1,
                    operand_index=self.bit_to_operand[i],
                )

            if new_range is None:
                new_range = EncodingRange(EncodingRangeType.CONSTANT, i, 1, constant=0)
            # 决定是否扩展当前 range。
            if (
                current_range
                and new_range.type == current_range.type
                and new_range.operand_index == current_range.operand_index
                and (new_range.type != EncodingRangeType.CONSTANT or i != 8 * 8)
                and (
                    new_range.group_id is None
                    or new_range.group_id == current_range.group_id
                )
            ):
                current_range.length += 1
            else:
                # 推入当前 range
                _push()
                current_range = new_range

            if current_range.type == EncodingRangeType.CONSTANT:
                current_range.constant |= ((self.inst[i // 8] >> (i % 8)) & 1) << (
                    current_range.length - 1
                )

        _push()

        # 后处理 ranges：对 FloatIMM 操作数，凡被归类为 OPERAND_MODIFIER
        # 的位实际属于立即数值本体，应改为 OPERAND 位，避免在 FIMM
        # 中出现伪“operand modi”字段。
        try:
            flat_ops = self.parsed.get_flat_operands()
            for rng in result:
                try:
                    if (
                        rng.type == EncodingRangeType.OPERAND_MODIFIER
                        and rng.operand_index is not None
                        and 0 <= rng.operand_index < len(flat_ops)
                        and isinstance(flat_ops[rng.operand_index], parser.FloatIMMOperand)
                    ):
                        rng.type = EncodingRangeType.OPERAND
                        rng.group_id = None
                        # 立即数字段的 name 不具备语义
                        rng.name = None
                except Exception:
                    continue
        except Exception:
            pass

        # 诊断信息：在非 debug 运行中抑制，保持分析稳定。
        try:
            operand_ranges = [r for r in result if r.type in (EncodingRangeType.OPERAND, EncodingRangeType.OPERAND_MODIFIER, EncodingRangeType.OPERAND_FLAG)]
            try:
                _ = self.parsed.get_flat_operands()
            except Exception:
                pass
        except Exception:
            pass

        # 后处理后（例如把 FloatIMM operand modifiers 重分类为 operand bits），
        # 某些 operand 可能被多个相邻且语义相同的 range 表示。将其重新合并，
        # 保证位图中一个 operand 渲染为一个连续块（例如 FIMM 的 operand 1
        # 不应显示为多个“operand 1”切片）。
        try:
            if result:
                merged = [result[0]]
                for rng in result[1:]:
                    prev = merged[-1]
                    if (
                        # 同类 range（但忽略 CONSTANT，其有额外值管理与行拆分规则）
                        rng.type == prev.type
                        and rng.type
                        not in (
                            EncodingRangeType.CONSTANT,
                            EncodingRangeType.FLAG,
                            EncodingRangeType.OPERAND_FLAG,
                        )
                        # operand / group / name 语义一致
                        and rng.operand_index == prev.operand_index
                        and rng.group_id == prev.group_id
                        and rng.name == prev.name
                        # 且在位空间上紧邻
                        and rng.start == prev.start + prev.length
                    ):
                        prev.length += rng.length
                    else:
                        merged.append(rng)
                result = merged
        except Exception:
            pass

        return EncodingRanges(result, self.inst)


def set_bit(array: bytearray, i):
    """翻转单个 bit（越界或负数直接忽略）。"""
    if i < 0:
        return
    byte_index = i // 8
    if byte_index >= len(array):
        # 越界 bit 翻转：忽略，避免分析中触发 IndexError
        return
    bit_offset = i % 8
    array[byte_index] ^= 1 << bit_offset


def analysis_disambiguate_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """二次消歧 FLAG：邻位翻转后若 token 证据不稳定，则回退为 modifier。"""
    modifier_mutations = []

    for bit in mset.instruction_modifier_bit_flag:
        inst_ = bytearray(mset.inst)
        set_bit(inst_, bit)
        set_bit(inst_, bit + 1)
        modifier_mutations.append((inst_, bit, bit + 1))

        if bit - 1 not in mset.instruction_modifier_bit_flag:
            inst_ = bytearray(mset.inst)
            set_bit(inst_, bit)
            set_bit(inst_, bit - 1)
            modifier_mutations.append((inst_, bit, bit - 1))
    if len(modifier_mutations) == 0:
        return False
    instructions, offsets, adj_offsets = zip(*modifier_mutations)

    disassembled = mset.disassembler.disassemble_parallel(instructions)
    changed = False
    try:
        base_inst_mods = set(getattr(mset.parsed, "modifiers", []) or [])
    except Exception:
        base_inst_mods = set()
    for disasm, bit, adj in zip(disassembled, offsets, adj_offsets):
        if bit not in mset.instruction_modifier_bit_flag:
            continue  # Already eleminated.
        flag_name = mset.instruction_modifier_bit_flag[bit]
        if not disasm:
            continue
        try:
            parsed = InstructionParser.parseInstruction(disasm)
        except Exception:
            continue
        if parsed.get_key() != mset.key:
            continue
        # 对于真实 flag，翻转 bit 后应相对基线“状态翻转”；
        # 不能假定基线一定是 flag=0（否则像基线已带 flag 的情形会误判）。
        base_has_flag = flag_name in base_inst_mods
        mutated_has_flag = flag_name in (getattr(parsed, "modifiers", []) or [])
        if mutated_has_flag == base_has_flag:
            changed = True
            mset.modifier_bits.add(adj)
            del mset.instruction_modifier_bit_flag[bit]
            if adj in mset.instruction_modifier_bit_flag:
                del mset.instruction_modifier_bit_flag[adj]
            mset.reset_modifier_groups()

    return changed


def analysis_merge_placeholder_backed_instruction_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """把“同名连续 flag + 占位符单 bit 差分”回退为同一 multi-bit modifier 组。

    典型场景：基线带 `.RZ`，但 3 个 bit 分别单独翻转后只会得到
    `.???1/.???2/.???8` 这类局部占位符。_analyse 会把每个位都看成
    “RZ 被移除”的单 bit flag；实际上它们是同一 3-bit modifier domain
    的局部证据，应保留为一个 modifier range 供后续枚举。
    """
    flag_map = dict(getattr(mset, "instruction_modifier_bit_flag", {}) or {})
    bits = sorted(flag_map.keys())
    if len(bits) < 2:
        return False

    def _normalize_token(name):
        if not name or not isinstance(name, str):
            return None
        clean = name.rstrip(".").strip()
        return clean or None

    try:
        base_mods = list(getattr(mset.parsed, "modifiers", []) or [])
    except Exception:
        base_mods = []
    base_counter = Counter(base_mods)
    base_names = {_normalize_token(name) for name in base_mods}

    def _probe_bit(bit: int):
        inst = bytearray(mset.inst)
        set_bit(inst, bit)
        asm = disassembler.disassemble(inst)
        if not asm:
            return None
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            return None
        if parsed.get_key() != mset.key:
            return None

        diff = Counter(getattr(parsed, "modifiers", []) or [])
        diff.subtract(base_counter)
        raw_nonzero = [(name, count) for name, count in diff.items() if count != 0]
        if not raw_nonzero:
            return None

        saw_placeholder = False
        visible = []
        for name, count in raw_nonzero:
            normalized = _normalize_token(name)
            if normalized is None:
                continue
            if is_placeholder_modifier(normalized):
                saw_placeholder = True
                continue
            visible.append((normalized, count))
        return visible, saw_placeholder

    changed = False
    next_gid = max([0] + list((getattr(mset, "modifier_groups", {}) or {}).values())) + 1
    idx = 0
    while idx < len(bits):
        start_bit = bits[idx]
        flag_name = _normalize_token(flag_map.get(start_bit))
        run = [start_bit]
        idx += 1
        while (
            idx < len(bits)
            and bits[idx] == run[-1] + 1
            and _normalize_token(flag_map.get(bits[idx])) == flag_name
        ):
            run.append(bits[idx])
            idx += 1

        if len(run) < 2 or not flag_name or flag_name not in base_names:
            continue

        group_bits = list(run)
        saw_placeholder = False
        mergeable = True
        for bit in run:
            probe = _probe_bit(bit)
            if probe is None:
                mergeable = False
                break
            visible, saw_placeholder_bit = probe
            saw_placeholder = saw_placeholder or saw_placeholder_bit

            if len(visible) != 1:
                mergeable = False
                break
            visible_name, visible_count = visible[0]
            if visible_name != flag_name or abs(visible_count) != 1:
                mergeable = False
                break

        def _extend_with_placeholder_only(adj_bit: int) -> bool:
            nonlocal saw_placeholder
            if adj_bit < 0:
                return False
            if adj_bit not in getattr(mset, "modifier_bits", set()):
                return False
            if adj_bit in flag_map:
                return False
            probe = _probe_bit(adj_bit)
            if probe is None:
                return False
            visible, saw_placeholder_bit = probe
            if not saw_placeholder_bit or visible:
                return False
            saw_placeholder = True
            return True

        left = run[0] - 1
        while mergeable and _extend_with_placeholder_only(left):
            group_bits.insert(0, left)
            left -= 1

        right = run[-1] + 1
        while mergeable and _extend_with_placeholder_only(right):
            group_bits.append(right)
            right += 1

        if not mergeable or not saw_placeholder:
            continue

        for bit in group_bits:
            mset.instruction_modifier_bit_flag.pop(bit, None)
            mset.modifier_bits.add(bit)
            mset.modifier_groups[bit] = next_gid
            mset.protected_modifier_split_bits.add(bit)
        next_gid += 1
        changed = True

    return changed


# 仅提升“已知布尔开关”到 FLAG，避免把多 bit 互斥字段误拆为多个开关。
# 例如 U64<->S64、RN/RM/RP/RZ 这类有替换关系的字段应保留在 modifier group。
KNOWN_INSTRUCTION_FLAGS = frozenset({"NTZ", "FTZ", "B", "R"})


def analysis_promote_known_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """将“单 bit 已知布尔 token 开关”的位提升为 FLAG。

    对布尔开关而言，基线可能已经带有该 token；因此既接受“翻位后新增”，
    也接受“翻位后移除”，只要差分中恰好只有这一个已知 token。
    """
    changed = False
    for bit in list(mset.modifier_bits):
        if bit in mset.instruction_modifier_bit_flag:
            continue
        inst = bytearray(mset.inst)
        set_bit(inst, bit)
        asm = disassembler.disassemble(inst)
        if not asm:
            continue
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            continue
        if parsed.get_key() != mset.key:
            continue
        diff = Counter(parsed.modifiers)
        diff.subtract(Counter(mset.parsed.modifiers))
        added = [n for n, c in diff.items() if c > 0]
        removed = [n for n, c in diff.items() if c < 0]
        flag_candidates = {n.rstrip(".") for n in added + removed if isinstance(n, str) and n}
        if len(flag_candidates) == 1:
            flag_name = next(iter(flag_candidates))
            if flag_name in KNOWN_INSTRUCTION_FLAGS:
                mset.instruction_modifier_bit_flag[bit] = flag_name
                changed = True
    return changed


def analysis_merge_mutually_exclusive_operand_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """把同一 operand 上相邻且互斥的「单 bit flag + 单 bit modifier」合并为同一 2-bit modifier 组。

    例如 H0_H0（当前被标成 operand flag）与 H1_H1（operand modifier）实为同一 2-bit 编码的
    不同取值，应合并为一个 modi 组，避免一个进 OPERAND_FLAG、一个进 OPERAND_MODIFIER。

    H0_NH1 miss 根因：若两 bit 未合并，则 enumerate_operand_modifiers 只对单个 OPERAND_MODIFIER
    range 枚举 0/1，不会与 OPERAND_FLAG 位做笛卡尔积，故 00（对应 H0_NH1）从未被枚举到。
    若反汇编在「两 bit 均为 1」时同时输出 H0_H0 与 H1_H1，原逻辑会认为非互斥而跳过合并；
    对半对族（H0_H0/H1_H1/H0_NH1）仍应合并，以便 2-bit 枚举得到 00→H0_NH1 等。
    """
    flag_map = dict(getattr(mset, "operand_modifier_bit_flag", {}) or {})
    if not flag_map:
        return False
    try:
        base_operands = mset.parsed.get_flat_operands()
    except Exception:
        return False

    def _operand_mods(inst_bytes, op_idx):
        asm = disassembler.disassemble(inst_bytes)
        if not asm:
            return None
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            return None
        if parsed.get_key() != getattr(mset, "key", None):
            return None
        ops = parsed.get_flat_operands()
        if op_idx is None or op_idx < 0 or op_idx >= len(ops):
            return None
        return set(getattr(ops[op_idx], "modifiers", []) or [])

    changed = False
    consumed = set()
    for bit in sorted(flag_map.keys()):
        if bit in consumed:
            continue
        op_idx = mset.bit_to_operand.get(bit)
        if op_idx is None:
            continue
        name_a = flag_map.get(bit)
        if not name_a:
            continue
        for adj in (bit + 1, bit - 1):
            if adj < 0 or adj in consumed:
                continue
            if adj not in mset.operand_modifier_bits and adj not in flag_map:
                continue
            if mset.bit_to_operand.get(adj) != op_idx:
                continue
            base_mods = _operand_mods(mset.inst, op_idx)
            if base_mods is None:
                continue
            inst_a = bytearray(mset.inst)
            set_bit(inst_a, bit)
            inst_adj = bytearray(mset.inst)
            set_bit(inst_adj, adj)
            inst_ab = bytearray(mset.inst)
            set_bit(inst_ab, bit)
            set_bit(inst_ab, adj)
            mods_a = _operand_mods(bytes(inst_a), op_idx)
            mods_adj = _operand_mods(bytes(inst_adj), op_idx)
            mods_ab = _operand_mods(bytes(inst_ab), op_idx)
            if mods_a is None or mods_adj is None or mods_ab is None:
                continue
            name_b = flag_map.get(adj)
            if not name_b:
                added = list(mods_adj - base_mods) if base_mods else list(mods_adj)
                if len(added) != 1:
                    continue
                name_b = (added[0].rstrip(".") if isinstance(added[0], str) else None) or ""
                if not name_b or is_placeholder_modifier(name_b):
                    continue
            a_toggled = (name_a in mods_a) != (name_a in base_mods)
            b_toggled = (name_b in mods_adj) != (name_b in base_mods)
            if not a_toggled or not b_toggled:
                continue
            # 两 bit 均为 1 时反汇编若同时带 H0_H0 与 H1_H1，原逻辑会跳过合并，导致
            # 两 bit 保持为 OPERAND_FLAG + OPERAND_MODIFIER，枚举只做单 range 0/1，漏掉 00→H0_NH1。
            # 半对族已知为同一 2-bit 编码的多种取值，此处仍合并，由 2-bit 枚举发现 H0_NH1。
            half_pair = {"H0_H0", "H1_H1", "H0_NH1"}
            both_in_ab = name_a in mods_ab and name_b in mods_ab
            if both_in_ab and not (name_a in half_pair and name_b in half_pair):
                continue
            mset.operand_modifier_bit_flag.pop(bit, None)
            mset.operand_modifier_bit_flag.pop(adj, None)
            # 合并后的两 bit 应作为同一 OPERAND_MODIFIER 参与 compute_encoding_ranges，
            # 否则会落入 CONSTANT 导致位图重复/混乱。
            mset.operand_modifier_bits.add(bit)
            mset.operand_modifier_bits.add(adj)
            consumed.add(bit)
            consumed.add(adj)
            changed = True
            break
    return changed


def analysis_disambiguate_operand_flags(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """消歧 operand flag：位翻转后 token 不再绑定该 operand 时，降级为普通 modifier。"""
    modifier_mutations = []
    for bit in mset.operand_modifier_bit_flag:
        inst_ = bytearray(mset.inst)
        set_bit(inst_, bit)
        set_bit(inst_, bit + 1)
        modifier_mutations.append((inst_, bit, bit + 1))
        if bit - 1 not in mset.operand_modifier_bit_flag:
            inst_ = bytearray(mset.inst)
            set_bit(inst_, bit)
            set_bit(inst_, bit - 1)
            modifier_mutations.append((inst_, bit, bit - 1))
    if len(modifier_mutations) == 0:
        return False

    instructions, offsets, adj_offsets = zip(*modifier_mutations)
    disassembled = mset.disassembler.disassemble_parallel(instructions)
    changed = False
    try:
        base_operands = mset.parsed.get_flat_operands()
    except Exception:
        base_operands = []
    for disasm, bit, adj in zip(disassembled, offsets, adj_offsets):
        if bit not in mset.operand_modifier_bit_flag:
            continue
        flag_name = mset.operand_modifier_bit_flag[bit]
        if not disasm:
            continue
        try:
            parsed = InstructionParser.parseInstruction(disasm)
        except Exception:
            continue
        if parsed.get_key() != mset.key:
            continue
        op_idx = mset.bit_to_operand.get(bit)
        if op_idx is None or op_idx < 0 or op_idx >= len(base_operands):
            continue
        mutated_operands = parsed.get_flat_operands()
        if op_idx >= len(mutated_operands):
            continue
        try:
            if not base_operands[op_idx].compare(mutated_operands[op_idx]):
                continue
        except Exception:
            continue
        base_mods = getattr(base_operands[op_idx], "modifiers", []) or []
        mutated_mods = getattr(mutated_operands[op_idx], "modifiers", []) or []
        # 与 instruction-level 同理：检查“相对基线是否翻转”，而不是
        # 强制要求翻转后一定包含该 flag（基线可能本来就包含它）。
        base_has_flag = flag_name in base_mods
        mutated_has_flag = flag_name in mutated_mods
        if mutated_has_flag == base_has_flag:
            changed = True
            del mset.operand_modifier_bit_flag[bit]
            if adj in mset.operand_modifier_bit_flag:
                del mset.operand_modifier_bit_flag[adj]
    return changed


def analysis_operand_fix(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """修复 operand 边界：对 [UR10+0x1] 这类，IMM 为 0 时 distillation 可能不删，导致 operand 边界不连续。
    
    伪代码:
        1. 初始化或更新 operands。
        2. 定义内部辅助函数 `mutate_test` 并在后续流程中调用。
        3. 初始化或更新 ranges。
        4. 初始化或更新 operand_ranges。
        5. 遍历输入集合并在循环内执行条件判断与累积。
    数据结构:
        - 输入: disassembler, mset。
        - 局部: operands, inst, asm, parsed, mutated_operands。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 try/except 容错, 内嵌函数/闭包。
    """

    operands = mset.parsed.get_flat_operands()

    def mutate_test(operand_index, idx, adj):
        """函数 `mutate_test` 的实现说明。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
            2. 初始化或更新 inst。
            3. 执行表达式调用以推进流程。
            4. 初始化或更新 asm。
        数据结构:
            - 输入: operand_index, idx, adj。
            - 局部: inst, asm, parsed, mutated_operands。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 try/except 容错。
        """
        try:
            if idx in getattr(mset, "operand_modifier_bits", set()) or idx in getattr(
                mset, "modifier_bits", set()
            ):
                return
        except Exception:
            pass
        inst = bytearray(mset.inst)
        set_bit(inst, idx)
        set_bit(inst, adj)
        asm = disassembler.disassemble(inst)
        if len(asm) == 0:
            return
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            return
        if parsed.get_key() != mset.key:
            return
        mutated_operands = parsed.get_flat_operands()
        if operands[operand_index] == mutated_operands[operand_index]:
            return
        mset.operand_value_bits.add(idx)
        mset.bit_to_operand[idx] = operand_index

    ranges = mset.compute_encoding_ranges()
    operand_ranges = ranges._find(EncodingRangeType.OPERAND)

    for i, rng in enumerate(operand_ranges):
        operand = operands[rng.operand_index]
        if not isinstance(operand, parser.Operand) and not (
            isinstance(operand, parser.IntIMMOperand)
            and isinstance(operand.parent, parser.AddressOperand)
        ):
            continue
        # 此处仍有边界不确定性：若 bit 恰好跨字节边界可能需进一步验证。
        if rng.start % 8 != 0:
            mutate_test(rng.operand_index, rng.start - 1, rng.start)
        elif rng.length % 8 != 0:
            mutate_test(rng.operand_index, rng.start + rng.length, rng.start)


def analysis_fimm_bridge_constants(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """桥接 FIMM 内部的常量位间隙：OPERAND/CONSTANT/OPERAND 模式 -> 中间 CONSTANT 归入 operand。
    
    伪代码:
        1. 初始化或更新 changed。
        2. 优先走主路径，异常时执行兜底分支。
        3. 根据条件走不同分支并选择返回/继续路径。
        4. 返回本函数最终结果。
    数据结构:
        - 输入: disassembler, mset。
        - 局部: changed, ranges, operands, i, prev_rng。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 try/except 容错。
    """
    changed = False
    try:
        ranges = mset.compute_encoding_ranges()
        operands = mset.parsed.get_flat_operands()
    except Exception:
        return False

    try:
        for i in range(1, len(ranges.ranges) - 1):
            try:
                prev_rng = ranges.ranges[i - 1]
                mid_rng = ranges.ranges[i]
                next_rng = ranges.ranges[i + 1]
            except Exception:
                continue

            # 只处理 FloatIMMOperand 上出现的 OPERAND / CONSTANT / OPERAND 模式
            if (
                prev_rng.type == EncodingRangeType.OPERAND
                and next_rng.type == EncodingRangeType.OPERAND
                and prev_rng.operand_index == next_rng.operand_index
                and mid_rng.type == EncodingRangeType.CONSTANT
            ):
                op_idx = prev_rng.operand_index
                try:
                    operand = operands[op_idx]
                except Exception:
                    continue
                if not isinstance(operand, parser.FloatIMMOperand):
                    continue

                # 把中间 constant 段上的每一位都当成这个 FIMM operand 的取值位
                for bit in range(mid_rng.start, mid_rng.start + mid_rng.length):
                    try:
                        mset.operand_value_bits.add(bit)
                        mset.bit_to_operand[bit] = op_idx
                        changed = True
                    except Exception:
                        continue
    except Exception:
        return False

    if changed:
        # 结构发生变化，需要重新 canonicalize 分组
        mset.reset_modifier_groups()
    return changed


def analysis_augment_modifier_bits_from_cache(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """从 cache 的同 key 样本差分补充 modifier_bits（不仅限 rounding token）。
    
    伪代码:
        1. 根据条件走不同分支并选择返回/继续路径。
        2. 优先走主路径，异常时执行兜底分支。
    数据结构:
        - 输入: disassembler, mset。
        - 局部: target_key, base_opcode, base_predicate, base_operand_sig, forbidden_bits。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 推导式, 生成器表达式, 位运算, try/except 容错。
    """
    if not ENABLE_CACHE_FALLBACK:
        return False
    try:
        target_key = mset.key
    except Exception:
        return False
    if not target_key:
        return False

    try:
        base_opcode = get_bit_range(mset.inst, 0, 12)
    except Exception:
        base_opcode = None
    try:
        base_predicate = getattr(mset.parsed, "predicate", None)
    except Exception:
        base_predicate = None
    base_operand_sig = _flat_operand_signature(mset.parsed)

    # 不允许覆盖已归因为其它语义的位。
    forbidden_bits = set()
    forbidden_bits.update(getattr(mset, "operand_value_bits", set()) or set())
    forbidden_bits.update(getattr(mset, "predicate_bits", set()) or set())
    forbidden_bits.update(getattr(mset, "operand_modifier_bits", set()) or set())
    forbidden_bits.update(getattr(mset, "opcode_bits", set()) or set())

    # token_sig -> distilled_inst_bytes 映射。
    samples = {}

    def _add_sample(inst_bytes, parsed):
        token_counter = _normalized_token_counter_from_parsed(parsed)
        token_sig = tuple(sorted(token_counter.items()))
        # 同一 token 签名只保留一个样本；先去重，再做 distill，
        # 避免重 key 在重复签名样本上反复 distill。
        if token_sig in samples:
            return
        try:
            distilled = disassembler.distill_instruction(inst_bytes)
        except Exception:
            distilled = bytes(inst_bytes)
        samples[token_sig] = bytes(distilled)

    try:
        _add_sample(mset.inst, mset.parsed)
    except Exception:
        pass

    sampled = 0
    for inst_b, asm_text in _cache_iter_by_key(disassembler, target_key):
        if CACHE_AUGMENT_MAX_SAMPLES > 0 and sampled >= CACHE_AUGMENT_MAX_SAMPLES:
            break
        try:
            if base_opcode is not None and get_bit_range(inst_b, 0, 12) != base_opcode:
                continue
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [l for l in asm_text.splitlines() if l.strip()]
            if not lines:
                continue
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() != target_key:
                continue
            if getattr(parsed, "predicate", None) != base_predicate:
                continue
            if _flat_operand_signature(parsed) != base_operand_sig:
                continue
            # 只用 concrete token 样本做位证据，避免占位符噪音。
            if any(
                is_placeholder_modifier(m)
                for m in (getattr(parsed, "modifiers", []) or [])
            ):
                continue
            sampled += 1
            _add_sample(inst_b, parsed)
        except Exception:
            continue

    sample_items = list(samples.values())
    if len(sample_items) < 2:
        return False

    discovered = set()
    anchor_inst = sample_items[0]
    for inst_b in sample_items[1:]:
        max_len = max(len(anchor_inst), len(inst_b))
        for byte_i in range(max_len):
            a = anchor_inst[byte_i] if byte_i < len(anchor_inst) else 0
            b = inst_b[byte_i] if byte_i < len(inst_b) else 0
            xor = a ^ b
            if xor == 0:
                continue
            for bit_off in range(8):
                if ((xor >> bit_off) & 1) == 0:
                    continue
                bit = byte_i * 8 + bit_off
                if bit >= MUTATION_ANALYSIS_END_BIT:
                    continue
                if bit in forbidden_bits:
                    continue
                discovered.add(bit)

    if not discovered:
        return False

    changed = False
    for bit in discovered:
        if bit not in mset.modifier_bits:
            changed = True
            mset.modifier_bits.add(bit)
    if changed:
        mset.reset_modifier_groups()
    return changed


def analysis_extend_modifiers(
    disassembler: Disassembler, mset: InstructionMutationSet
) -> bool:
    """扩展 modifier 相邻位：若翻转 bit±1 时 modifier 变化，将相邻位加入 modifier_bits。
    
    伪代码:
        1. 初始化或更新 ranges。
        2. 初始化或更新 modifier_ranges。
        3. 初始化或更新 changed。
        4. 定义内部辅助函数 `analyse_adj` 并在后续流程中调用。
        5. 遍历输入集合并在循环内执行条件判断与累积。
    数据结构:
        - 输入: disassembler, mset。
        - 局部: ranges, modifier_ranges, changed, array, original_asm。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 try/except 容错, 内嵌函数/闭包。
    """
    ranges = mset.compute_encoding_ranges()
    modifier_ranges = ranges._find(EncodingRangeType.MODIFIER)
    changed = False

    def analyse_adj(modi_bit, adj):
        """函数 `analyse_adj` 的实现说明。
        
        伪代码:
            1. 执行顺序语句并更新中间状态。
            2. 根据条件走不同分支并选择返回/继续路径。
            3. 初始化或更新 array。
            4. 执行表达式调用以推进流程。
            5. 初始化或更新 original_asm。
        数据结构:
            - 输入: modi_bit, adj。
            - 局部: array, original_asm, original_parsed, modi_asm, modi_parsed。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 try/except 容错。
        """
        nonlocal changed
        # 注意：这里尚不完全确定。也许在具备“枚举后 modifier 拆分”后可移除。
        if adj in mset.instruction_modifier_bit_flag:
            return

        array = bytearray(mset.inst)
        set_bit(array, modi_bit)
        original_asm = disassembler.disassemble(array)
        if len(original_asm) == 0:
            return
        original_parsed = InstructionParser.parseInstruction(original_asm)

        set_bit(array, adj)
        modi_asm = disassembler.disassemble(array)
        if len(modi_asm) == 0:
            return
        try:
            modi_parsed = InstructionParser.parseInstruction(modi_asm)
        except Exception:
            return

        if modi_parsed.get_key() != original_parsed.get_key():
            return
        # 检查 modifiers 是否存在差异。
        if modi_parsed.modifiers != original_parsed.modifiers:
            # 相邻 bit 属于 modifier 的一部分

            changed = changed or (adj not in mset.modifier_bits)
            mset.modifier_bits.add(adj)
            if adj in mset.instruction_modifier_bit_flag:
                del mset.instruction_modifier_bit_flag[adj]

    for rng in modifier_ranges:
        # 经验上 1 0 0 0 1 这种探测顺序通常更稳。
        analyse_adj(rng.start, rng.start - 1)
        # 备选探测：analyse_adj(rng.start + rng.length // 2, rng.start - 1)
        analyse_adj(rng.start, rng.start + rng.length)
        # 备选探测：analyse_adj(rng.start + rng.length // 2, rng.start + rng.length)
    if changed:
        mset.reset_modifier_groups()
    return changed


def analysis_modifier_splitting(
    disassembler: Disassembler, mset: InstructionMutationSet
):
    """拆分 modifier：若相邻位独立控制不同 modifier，则拆成多个 modifier 组。
    
    伪代码:
        1. 初始化或更新 ranges。
        2. 初始化或更新 modifier_ranges。
        3. 定义内部辅助函数 `_norm_counter` 并在后续流程中调用。
        4. 定义内部辅助函数 `_single_toggle` 并在后续流程中调用。
        5. 定义内部辅助函数 `analyse_adj` 并在后续流程中调用。
    数据结构:
        - 输入: disassembler, mset。
        - 局部: ranges, modifier_ranges, out, token, clean。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 推导式, 生成器表达式, try/except 容错, 内嵌函数/闭包。
    """
    ranges = mset.compute_encoding_ranges()
    modifier_ranges = ranges._find(EncodingRangeType.MODIFIER)

    def _norm_counter(tokens):
        out = Counter()
        for token in tokens or []:
            if not isinstance(token, str):
                continue
            clean = token.rstrip(".").strip()
            if not clean or is_placeholder_modifier(clean):
                continue
            out[clean] += 1
        return out

    def _single_toggle(counter_a: Counter, counter_b: Counter):
        diff = Counter(counter_b)
        diff.subtract(counter_a)
        added = [(name, cnt) for name, cnt in diff.items() if cnt > 0]
        removed = [(name, -cnt) for name, cnt in diff.items() if cnt < 0]
        if len(added) == 1 and len(removed) == 0:
            name, cnt = added[0]
            return name if cnt == 1 else None
        if len(removed) == 1 and len(added) == 0:
            name, cnt = removed[0]
            return name if cnt == 1 else None
        if len(added) == 1 and len(removed) == 1:
            add_name, add_cnt = added[0]
            rem_name, rem_cnt = removed[0]
            if add_name == rem_name and add_cnt == 1 and rem_cnt == 1:
                return add_name
        return None

    def analyse_adj(modi_bit, adj):
        # 四态一致性校验（00/10/01/11）：
        # 仅当两个 bit 都体现为互相独立的单 token 开关时，才允许拆分。
        base = bytearray(mset.inst)
        mod_only = bytearray(base)
        set_bit(mod_only, modi_bit)
        adj_only = bytearray(base)
        set_bit(adj_only, adj)
        both = bytearray(mod_only)
        set_bit(both, adj)

        disasms = disassembler.disassemble_parallel([base, mod_only, adj_only, both])
        if any((not asm) for asm in disasms):
            return False
        try:
            p00, p10, p01, p11 = [InstructionParser.parseInstruction(asm) for asm in disasms]
        except Exception:
            return False
        if len({p00.get_key(), p10.get_key(), p01.get_key(), p11.get_key()}) != 1:
            return False

        c00 = _norm_counter(getattr(p00, "modifiers", []) or [])
        c10 = _norm_counter(getattr(p10, "modifiers", []) or [])
        c01 = _norm_counter(getattr(p01, "modifiers", []) or [])
        c11 = _norm_counter(getattr(p11, "modifiers", []) or [])

        tok_m0 = _single_toggle(c00, c10)
        tok_m1 = _single_toggle(c01, c11)
        tok_a0 = _single_toggle(c00, c01)
        tok_a1 = _single_toggle(c10, c11)
        if not tok_m0 or not tok_m1 or not tok_a0 or not tok_a1:
            return False
        if tok_m0 != tok_m1:
            return False
        if tok_a0 != tok_a1:
            return False
        if tok_m0 == tok_a0:
            return False
        return True

    def split_range(rng, i):
        """函数 `split_range` 的实现说明。
        
        伪代码:
            1. 初始化或更新 next_group_id。
            2. 遍历输入集合并在循环内执行条件判断与累积。
        数据结构:
            - 输入: rng, i。
            - 局部: next_group_id, i。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        next_group_id = max([0] + list(mset.modifier_groups.values())) + 1
        for i in range(i, rng.length):
            mset.modifier_groups[rng.start + i] = next_group_id

    for rng in modifier_ranges:
        protected = set(getattr(mset, "protected_modifier_split_bits", set()) or set())
        if any((rng.start + off) in protected for off in range(rng.length)):
            continue
        for i in range(1, rng.length):
            if (
                analyse_adj(rng.start, rng.start + i)
                or analyse_adj(rng.start + i - 1, rng.start + i)
                or analyse_adj(rng.start, rng.start + i)
            ):
                split_range(rng, i)
                return True

    return False


INSTRUCTION_DESC_HEADER = """
    <style>
        .instruction-desc {
            font-weight: bold;
            padding: 5px;
            margin-top: 15px;
            margin-bottom: 15px;
        }

        .flat-operand-section {
            padding: 2px;
            margin: 2px;
            border-radius: 5px;
        }
    </style>
"""


class InstructionDescGenerator:
    def generate(self, instruction: Instruction, full_name: str):
        """函数 `generate` 的实现说明。
        
        伪代码:
            1. 执行赋值与状态更新。
            2. 执行增量更新。
            3. 初始化或更新 flat_op_i。
            4. 遍历输入集合并在循环内执行条件判断与累积。
        数据结构:
            - 输入: instruction, full_name。
            - 局部: flat_op_i, op, sop。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 f-string。
        """
        self.result = '<div class="instruction-desc">'
        self.result += f'<span class="base-name">{full_name}</span>'

        # 为子操作数分配编号。
        flat_op_i = 0
        for op in instruction.operands:
            for sop in op.flatten():
                sop.flat_operand_index = flat_op_i
                flat_op_i += 1

        self.result += '<span class="operands"> &nbsp; '
        for i, op in enumerate(instruction.operands):
            if i != 0:
                self.result += ","
            self.result += " "
            self.visit(op)
        self.result += "</span>"

        self.result += "</div>"
        return self.result

    def visit(self, op: parser.Operand):
        """函数 `visit` 的实现说明。
        
        伪代码:
            1. 根据条件走不同分支并选择返回/继续路径。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        if isinstance(op, parser.DescOperand):
            self.visitDescOperand(op)
        elif isinstance(op, parser.ConstantMemOperand):
            self.visitConstantMemOperand(op)
        elif isinstance(op, parser.IntIMMOperand):
            self.visitIntIMMOperand(op)
        elif isinstance(op, parser.FloatIMMOperand):
            self.visitFloatIMMOperand(op)
        elif isinstance(op, parser.AddressOperand):
            self.visitAddressOperand(op)
        elif isinstance(op, parser.RegOperand):
            self.visitRegOperand(op)
        elif isinstance(op, parser.AttributeOperand):
            self.visitAttributeOperand(op)

    def begin_section(self, op: parser.Operand):
        # 当 flat_operand_index 缺失或非法时，使用安全默认色。
        """函数 `begin_section` 的实现说明。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
            2. 执行增量更新。
        数据结构:
            - 输入: op。
            - 局部: color。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 try/except 容错, f-string。
        """
        try:
            color = operand_colors[op.flat_operand_index]
        except Exception:
            color = "#EEEEEE"
        self.result += f"<span class='flat-operand-section' style='background-color:{color}'>"

    def end_section(self):
        """函数 `end_section` 的实现说明。
        
        伪代码:
            1. 执行增量更新。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.result += "</span>"

    def visitAttributeOperand(self, op):
        """函数 `visitAttributeOperand` 的实现说明。
        
        伪代码:
            1. 执行增量更新。
            2. 执行表达式调用以推进流程。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.result += "a"
        self.visit(op.sub_operands[0])

    def visitDescOperand(self, op):
        """函数 `visitDescOperand` 的实现说明。
        
        伪代码:
            1. 执行增量更新。
            2. 执行表达式调用以推进流程。
            3. 根据条件走不同分支并选择返回/继续路径。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.result += "g" if op.g else ""
        self.result += "desc["
        self.visit(op.sub_operands[0])
        self.result += "]"
        if len(op.sub_operands) > 1:
            self.visit(op.sub_operands[1])

    def visitConstantMemOperand(self, op):
        # 优先将整个 constant-memory operand 渲染为单个高亮区段，
        # 即便 bit->operand 映射不完整也能保持可见。展示时使用
        # 解析后的 operand key，得到简洁且更易读的形式（如 c[R0][0x0]）。
        """函数 `visitConstantMemOperand` 的实现说明。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 try/except 容错。
        """
        try:
            self.begin_section(op)
            # 显示时使用 get_operand_key（稳定且不包含 modifiers）
            self.result += op.get_operand_key()
            self.end_section()
        except Exception:
            # 尽力回退到之前的详细渲染路径
            self.result += "cx" if op.cx else "c"
            self.result += "["
            self.visit(op.sub_operands[0])
            self.result += "]"
            self.visit(op.sub_operands[1])

    def visitIntIMMOperand(self, op):
        """函数 `visitIntIMMOperand` 的实现说明。
        
        伪代码:
            1. 执行表达式调用以推进流程。
            2. 执行增量更新。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.begin_section(op)
        self.result += "INT_IMM"
        self.end_section()

    def visitFloatIMMOperand(self, op):
        """函数 `visitFloatIMMOperand` 的实现说明。
        
        伪代码:
            1. 执行表达式调用以推进流程。
            2. 执行增量更新。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.begin_section(op)
        self.result += "FIMM"
        self.end_section()

    def visitAddressOperand(self, op):
        """函数 `visitAddressOperand` 的实现说明。
        
        伪代码:
            1. 执行增量更新。
            2. 遍历输入集合并在循环内执行条件判断与累积。
        数据结构:
            - 输入: op。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.result += "["
        for i, sop in enumerate(op.sub_operands):
            if i != 0:
                self.result += "+"
            self.visit(sop)
        self.result += "]"

    def visitRegOperand(self, op):
        # 若 parser 产出回退 RegOperand("UNKNOWN", raw_token)，
        # 且 raw token 实际包含 constant-memory 形态（如 `c[...]` 或 `cx[...]`），
        # 则优先渲染该表面文本，让 UI 显示 constant-memory 引用而不是 `UNKNOWN`。
        """函数 `visitRegOperand` 的实现说明。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
            2. 执行表达式调用以推进流程。
            3. 执行增量更新。
        数据结构:
            - 输入: op。
            - 局部: raw。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 try/except 容错。
        """
        try:
            if getattr(op, "reg_type", None) == "UNKNOWN" and isinstance(
                getattr(op, "ident", None), str
            ):
                raw = op.ident
                if "c[" in raw:
                    self.begin_section(op)
                    # 将 raw token 作为尽力的人类可读表面文本
                    # （通常本身已是 c[...] 或 cx[...] 字符串）。
                    self.result += raw
                    self.end_section()
                    return
        except Exception:
            # 吞掉异常并继续走默认渲染路径
            pass

        self.begin_section(op)
        self.result += op.get_operand_key()
        self.end_section()


def counter_remove_zeros(counts: Counter):
    """从 Counter 中移除 count 为 0 的项。
    
    伪代码:
        1. 遍历输入集合并在循环内执行条件判断与累积。
    数据结构:
        - 输入: counts。
        - 局部: 以临时表达式为主。
        - 输出: 主要通过就地更新外部容器/对象状态。
    复杂语法:
        - 使用 条件分支与循环控制。
    """
    for name, count in list(counts.items()):
        if count == 0:
            del counts[name]


def factorize_operand_modifier_groups_from_rows(ranges: EncodingRanges, operand_modifier_values):
    return _factorize_operand_modifier_groups_from_rows_base(
        ranges,
        operand_modifier_values,
        encoding_range_type=EncodingRangeType,
        encoding_range_cls=EncodingRange,
        get_bit_range_fn=get_bit_range,
        is_placeholder_modifier_fn=is_placeholder_modifier,
        find_modifier_difference_fn=find_modifier_difference,
    )


def _clean_name_for_row(name):
    return _clean_modifier_row_name_base(
        name,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


def _modifier_token_set_from_rows(rows):
    tokens = set()
    try:
        for _value, name in rows or []:
            clean = _normalize_modifier_token(name)
            if clean:
                tokens.add(clean)
    except Exception:
        return tokens
    return tokens


class InstructionSpec:
    """指令规格：包含 disasm、parsed、ranges、modifiers、operand_modifiers 等，用于生成 HTML 和 isa.json。"""

    def __init__(
        self,
        disasm: str,
        parsed: Instruction,
        ranges: 'EncodingRanges',
        modifiers,
        operand_modifiers,
        modifier_interactions=None,
        operand_interactions=None,
        operand_modifier_composites=None,
        force_modifier_bits=None,
    ):
        """初始化对象状态并建立后续流程所需字段。
        
        伪代码:
            1. 执行赋值与状态更新。
        数据结构:
            - 输入: disasm, parsed, ranges, modifiers, operand_modifiers, operand_interactions, force_modifier_bits。
            - 局部: flat_ops, parsed_reg_tokens, op, normalized_mods, entries。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, 生成器表达式, try/except 容错, f-string。
        """
        self.disasm = disasm
        self.parsed = parsed
        self.ranges = ranges
        self.modifiers = modifiers
        self.operand_modifiers = operand_modifiers
        normalized_modifier_interactions = []
        for entry in modifier_interactions or []:
            try:
                groups = [int(group) for group in list(entry.get("groups") or [])]
                values = [int(value) for value in list(entry.get("values") or [])]
            except Exception:
                continue
            if not groups or len(groups) != len(values):
                continue
            seen_tokens = set()
            tokens = []
            for token in list(entry.get("tokens") or []):
                clean = _normalize_modifier_token(token)
                if clean and clean not in seen_tokens:
                    tokens.append(clean)
                    seen_tokens.add(clean)
            if not tokens:
                continue
            normalized_modifier_interactions.append(
                {
                    "groups": groups,
                    "values": values,
                    "tokens": tokens,
                }
            )
        self.modifier_interactions = normalized_modifier_interactions
        self.operand_interactions = operand_interactions
        normalized_operand_modifier_composites = []
        for entry in operand_modifier_composites or []:
            try:
                operand_index = int(entry.get("operand_index"))
                group_id = int(entry.get("group_id"))
                main_width = int(entry.get("main_width"))
                overlay_width = int(entry.get("overlay_width"))
            except Exception:
                continue
            rows = []
            seen_rows = set()
            for row in list(entry.get("rows") or []):
                try:
                    main_value = int(row.get("main_value"))
                    overlay_value = int(row.get("overlay_value"))
                except Exception:
                    continue
                seen_tokens = set()
                tokens = []
                for token in list(row.get("tokens") or []):
                    clean = _normalize_modifier_token(token)
                    if clean and clean not in seen_tokens:
                        tokens.append(clean)
                        seen_tokens.add(clean)
                row_key = (main_value, overlay_value, tuple(tokens))
                if row_key in seen_rows:
                    continue
                rows.append(
                    {
                        "main_value": main_value,
                        "overlay_value": overlay_value,
                        "tokens": tokens,
                    }
                )
                seen_rows.add(row_key)
            if not rows:
                continue
            normalized_operand_modifier_composites.append(
                {
                    "operand_index": operand_index,
                    "group_id": group_id,
                    "main_width": main_width,
                    "overlay_width": overlay_width,
                    "rows": rows,
                }
            )
        self.operand_modifier_composites = normalized_operand_modifier_composites
        # 记录由 mutation 证据得到的强制保留位：即便枚举结果
        # 只有空/占位候选，也要保留对应 modifier 组。
        try:
            self.force_modifier_bits = set(force_modifier_bits) if force_modifier_bits else set()
        except Exception:
            self.force_modifier_bits = set()
        self.empty_value = []
        self.all_modifiers = []
        # 预计算 parsed flat operand 标识，供寄存器匹配使用。
        flat_ops = self.parsed.get_flat_operands()
        parsed_reg_tokens = set()
        for op in flat_ops:
            try:
                if hasattr(op, 'reg_type') and hasattr(op, 'ident') and op.ident is not None:
                    parsed_reg_tokens.add(f"{op.reg_type}{op.ident}")
            except Exception:
                pass

        # 将传入 modifiers 规范化为 list-of-(value, name) 分组结构。
        normalized_mods = []
        for i, modifier_range in enumerate(modifiers):
            entries = []

            def _normalize_modifier_name(raw_name):
                if isinstance(raw_name, str):
                    clean_nm = raw_name.strip()
                    if clean_nm in ("", "."):
                        return ""
                    return raw_name if raw_name.endswith('.') else raw_name + '.'
                return str(raw_name) + '.'

            try:
                if len(modifier_range) > 0 and isinstance(modifier_range[0], str):
                    for v_idx, nm in enumerate(modifier_range):
                        name = _normalize_modifier_name(nm)
                        entries.append((v_idx, name))
                else:
                    # 认为已是 pair 列表格式
                    entries = [
                        (value, _normalize_modifier_name(name))
                        for value, name in list(modifier_range)
                    ]
            except Exception:
                try:
                    entries = [
                        (value, _normalize_modifier_name(name))
                        for value, name in list(modifier_range)
                    ]
                except Exception:
                    entries = []
            normalized_mods.append(entries)
            for value, name in entries:
                group_name = name[:-1]
                # 若该 modifier 组仅由类寄存器 token 组成，且这些 token
                # 对应到 parsed operands，则跳过将其作为 modifier 组处理
                # （更可能是 operand 映射）。
                tokens = [t for t in group_name.split('.') if len(t) != 0]
                if len(tokens) > 0 and all(
                    t.isalnum() and (t.startswith('R') or t.startswith('UR') or t.startswith('P') or t.startswith('UP') or t.startswith('SR'))
                    for t in tokens
                ):
                    # 检查 token 是否映射到 parsed operand token，如 'R0' -> reg_type='R', ident='0'
                    if all(t in parsed_reg_tokens for t in tokens):
                        # 跳过将该组加入 modifier 候选
                        continue
                self.all_modifiers.append((group_name, i, value))

        # 用规范化后的形式替换 modifiers，供后续流程使用
        self.modifiers = normalized_mods
        # 后处理 modifier 组：若某组解析为与 parsed flat operands 匹配的
        # 类寄存器 token，则把对应位段从 MODIFIER 重分类为 OPERAND_MODIFIER，
        # 并绑定到 operand 索引，避免把寄存器 token 误当作 instruction modifier。
        try:
            flat_ops = self.parsed.get_flat_operands()
            parsed_token_to_idx = {}
            for idx, op in enumerate(flat_ops):
                try:
                    if hasattr(op, 'reg_type') and hasattr(op, 'ident') and op.ident is not None:
                        parsed_token_to_idx[f"{op.reg_type}{op.ident}"] = idx
                except Exception:
                    continue

            # 按当前 modifier range 出现顺序与 self.modifiers 对齐；
            # 这里不能依赖 group_id，因为它在上游是 1-based，且后处理后
            # 也可能不再与枚举组索引稳定对应。
            mod_ranges = [
                rng for rng in self.ranges.ranges
                if rng.type == EncodingRangeType.MODIFIER
            ]

            # 记录 modifier group id -> operand index 的重映射，
            # 以保持 `self.operand_modifiers` 与 ranges 同步。
            remapped_groups = {}

            # 对每个 modifier 组，检查其名称是否映射到单一 operand
            for gid, modi_group in enumerate(self.modifiers):
                mapped_idx = None
                ambiguous = False
                for value, name in modi_group:
                    # 枚举结果中的 name 通常以 '.' 结尾
                    group_name = name[:-1] if name.endswith('.') else name
                    if len(group_name) == 0:
                        continue
                    tokens = [t for t in group_name.split('.') if len(t) != 0]
                    for tok in tokens:
                        # 类寄存器 token 检测：R123、UR12、P3、UP2、SR0
                        if tok.startswith(('R', 'UR', 'P', 'UP', 'SR')) and tok in parsed_token_to_idx:
                            idx = parsed_token_to_idx[tok]
                            if mapped_idx is None:
                                mapped_idx = idx
                            elif mapped_idx != idx:
                                ambiguous = True
                                break
                        else:
                            ambiguous = True
                            break
                    if ambiguous:
                        break
                if mapped_idx is not None and not ambiguous and gid < len(mod_ranges):
                    # 重分类 ranges 并记录映射，便于后续更新
                    # operand modifier 表与 ranges.operand_index 对齐。
                    rng = mod_ranges[gid]
                    if not _should_reclassify_modifier_range_as_operand_modifier(rng):
                        _warn_skipped_operand_modifier_reclassification(
                            rng,
                            getattr(self.ranges, "_analysis_key", None)
                            or self.parsed.get_key(),
                            mapped_idx,
                            modi_group,
                        )
                        continue
                    rng.type = EncodingRangeType.OPERAND_MODIFIER
                    rng.operand_index = mapped_idx
                    remapped_groups[gid] = (mapped_idx, rng.start, rng.length)
                    rng.group_id = None

            # 确保 operand_modifiers 字典反映所有重映射的 modifier 组。
            # 按 (operand_index, start, length) 存储，与 enumerate 一致。
            try:
                for gid, range_key in remapped_groups.items():
                    if gid < len(self.modifiers):
                        group = self.modifiers[gid]
                        if group and isinstance(group, list):
                            existing = self.operand_modifiers.get(range_key, [])
                            if existing != group:
                                self.operand_modifiers[range_key] = group
            except Exception:
                pass
        except Exception:
            # 尽力而为；此处失败不应中止 spec 构建。
            pass

        # 最终裁剪：移除仅含占位符或空名称的 modifier 组，避免在 HTML 中生成空表。
        def _meaningful(n):
            """函数 `_meaningful` 的实现说明。
            
            伪代码:
                1. 优先走主路径，异常时执行兜底分支。
            数据结构:
                - 输入: n。
                - 局部: nm。
                - 输出: 通过 return 返回计算结果。
            复杂语法:
                - 使用 try/except 容错。
            """
            try:
                if not n or not isinstance(n, str):
                    return False
                nm = n.rstrip(".").strip()
                if not nm:
                    return False
                if is_placeholder_modifier(nm):
                    return False
                return True
            except Exception:
                return False

        try:
            # 按出现顺序构建稳定的 modifier ranges 视图，保证
            # modifier 组索引（来自枚举）与对应 EncodingRange 条目对齐。
            # 原 group_id 是 mutation 分析内部编号，后处理后未必与
            # 枚举索引一致。
            mod_ranges = [rng for rng in self.ranges.ranges if rng.type == EncodingRangeType.MODIFIER]

            # 依据 modifier range 的实际位跨度确定哪些组对应强制位，
            # 不依赖不透明的 group_id。
            forced_group_ids = set()
            if self.force_modifier_bits and mod_ranges:
                for gid, rng in enumerate(mod_ranges):
                    try:
                        for b in range(rng.start, rng.start + rng.length):
                            if b in self.force_modifier_bits:
                                forced_group_ids.add(gid)
                                break
                    except Exception:
                        continue

            # 保留 modifier 组索引：对要丢弃的组填空列表而非压缩列表，
            # 以保持枚举索引与 mod_ranges 顺序对齐。
            new_mods = []
            for gid, group in enumerate(self.modifiers):
                # 若该组有 mutation 证据支撑，即使看起来无意义也保留。
                if gid in forced_group_ids:
                    new_mods.append(group)
                    continue
                keep = False
                for _, name in group:
                    if _meaningful(name):
                        keep = True
                        break
                if keep:
                    new_mods.append(group)
                else:
                    new_mods.append([])
            self.modifiers = new_mods
        except Exception:
            pass
        try:
            # 将“有意义选项 <=1”的组转成 CONSTANT range：
            # 按出现顺序将组索引映射到 modifier ranges，
            # 而不是比较 range.group_id。
            mod_ranges = [rng for rng in self.ranges.ranges if rng.type == EncodingRangeType.MODIFIER]
            for gid, group in enumerate(self.modifiers):
                meaningful = [name for _, name in group if _meaningful(name)]
                unique_names = set((n or "").rstrip(".").strip() for n in meaningful)
                redundant = len(meaningful) > 1 and len(unique_names) <= 1
                # 满足以下条件转成 CONSTANT：
                # (1) 无有意义选项，或
                # (2) 冗余——所有取值同名（该位不影响 modifier）。
                # 对 (1) 需尊重 force_modifier_bits；对 (2) 一律转换。
                if len(meaningful) == 0 and hasattr(self, 'force_modifier_bits') and self.force_modifier_bits:
                    try:
                        if gid in forced_group_ids:
                            continue
                    except Exception:
                        pass
                if (len(meaningful) == 0 or redundant) and gid < len(mod_ranges):
                    rng = mod_ranges[gid]
                    try:
                        bit_val = get_bit_range(self.ranges.inst, rng.start, rng.start + rng.length)
                    except Exception:
                        bit_val = 0
                    rng.type = EncodingRangeType.CONSTANT
                    rng.constant = bit_val
                    rng.group_id = None
                    rng.name = None  # bitmap shows bits, not modifier name
        except Exception:
            # 尽力处理；出现异常也不让 spec 构建失败。
            pass

        try:
            # 某些 single-bit 翻转会在早期被误提升成 instruction FLAG，
            # 但后续 modifier/interactions 已经给出了更强证据。
            # 这类“假 flag”会导致位图同时出现同名 FLAG 与 modi/interactions，
            # 如 F2FP 的 UNPACK_B、STTM 的 16dp128bit。这里统一回收为 CONSTANT。
            instruction_modifier_tokens = set()
            for group in self.modifiers or []:
                instruction_modifier_tokens.update(_modifier_token_set_from_rows(group))
            for entry in self.modifier_interactions or []:
                for token in entry.get("tokens") or []:
                    clean = _normalize_modifier_token(token)
                    if clean:
                        instruction_modifier_tokens.add(clean)

            if instruction_modifier_tokens:
                for rng in self.ranges.ranges:
                    if rng.type != EncodingRangeType.FLAG:
                        continue
                    clean = _normalize_modifier_token(getattr(rng, "name", None))
                    if not clean or clean not in instruction_modifier_tokens:
                        continue
                    try:
                        bit_val = get_bit_range(self.ranges.inst, rng.start, rng.start + rng.length)
                    except Exception:
                        bit_val = 0
                    rng.type = EncodingRangeType.CONSTANT
                    rng.constant = bit_val
                    rng.name = None
                    rng.group_id = None
        except Exception:
            pass

        # 所有 modifier 重分类/裁剪完成后，再计算 opcode_modis 和
        # canonical_name，避免保留过期的 instruction-level 结果。
        self.opcode_modis = self._get_opcode_modis()
        try:
            parsed_mods = getattr(self.parsed, "modifiers", []) or []
            if parsed_mods and not has_placeholder_modifier(parsed_mods):
                self.canonical_name = ".".join([self.parsed.base_name] + parsed_mods)
            else:
                self.canonical_name = ".".join([self.parsed.base_name] + self.opcode_modis)
        except Exception:
            self.canonical_name = ".".join([self.parsed.base_name] + self.opcode_modis)

        # 注意：已移除激进的可视化回退（合成 operand ranges）。
        # 在已有/应有 distillation/mutation 数据作为事实来源时，
        # 人工合成任意 operand 位布局是不正确的。若缺少 operand ranges，
        # 更可能是 disassembler/探测失败，应通过诊断处理而非臆造位位置。
    def to_json_obj(self):
        """导出 JSON 可序列化对象（dict）。
        
        伪代码:
            1. 返回本函数最终结果。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: 以临时表达式为主。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        # JSON 键必须是字符串；tuple 键 (op_idx, start, length) 转为 str 以便还原。
        om_ser = {}
        for k, v in (self.operand_modifiers or {}).items():
            key_str = str(k) if isinstance(k, tuple) else k
            om_ser[key_str] = v
        return {
            "disasm": self.disasm,
            "parsed": self.parsed.to_json_obj(),
            "ranges": self.ranges.to_json_obj(),
            "modifiers": self.modifiers,
            "operand_modifiers": om_ser,
            "modifier_interactions": self.modifier_interactions,
            "operand_interactions": self.operand_interactions,
            "operand_modifier_composites": self.operand_modifier_composites,
            "opcode_modis": self.opcode_modis,
            "canonical_name": self.canonical_name,
        }

    def _get_opcode_modis(self) -> str:
        # 基于 ENCODED 值构建规范 modifier 列表，而非 parsed.modifiers。
        # 这样可确保互斥 modifier（如 TLD4 R|G|B|A 通道）只展示
        # 实际编码值，而不是暗示可共存的并集。
        """函数 `_get_opcode_modis` 的实现说明。
        
        伪代码:
            1. 初始化或更新 resolved。
            2. 优先走主路径，异常时执行兜底分支。
            3. 初始化或更新 all_group_names。
            4. 遍历输入集合并在循环内执行条件判断与累积。
            5. 初始化或更新 inst_modifiers。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: resolved, mod_ranges, val, chosen, all_group_names。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, try/except 容错。
        """
        resolved = []
        try:
            mod_ranges = self.ranges._find(EncodingRangeType.MODIFIER)
            for idx, rng in enumerate(mod_ranges):
                try:
                    val = get_bit_range(self.ranges.inst, rng.start, rng.start + rng.length)
                except Exception:
                    val = 0
                chosen = None
                saw_encoded_row = False
                if self.modifiers and idx < len(self.modifiers):
                    for v, n in self.modifiers[idx]:
                        if v != val:
                            continue
                        saw_encoded_row = True
                        if isinstance(n, str) and not is_placeholder_modifier(n):
                            chosen = n.rstrip('.')
                        break
                    if (not chosen) and (not saw_encoded_row):
                        for v, n in self.modifiers[idx]:
                            if isinstance(n, str) and not is_placeholder_modifier(n) and n.strip():
                                chosen = n.rstrip('.')
                                break
                if chosen:
                    resolved.append(chosen)
        except Exception:
            pass

        # 补充 opcode 级 modifiers：即 parsed.modifiers 中不属于任何
        # modifier 组的项（如提升为 FLAG 的 NTZ、FTZ）。
        all_group_names = set()
        for grp in (self.modifiers or []):
            for _v, n in grp:
                if isinstance(n, str) and n and not is_placeholder_modifier(n):
                    all_group_names.add(n.rstrip('.'))
        inst_modifiers = set(self.parsed.modifiers)
        for m in all_group_names:
            inst_modifiers.discard(m)
        opcode_level = [m for m in filter_non_placeholder_modifiers(self.parsed.modifiers) if m in inst_modifiers]
        # 保序：先 resolved（来自编码值），后 opcode-level
        seen = set(resolved)
        for m in opcode_level:
            if m not in seen:
                resolved.append(m)
                seen.add(m)
        return resolved

    @classmethod
    def from_json_obj(cls, obj):
        """从 JSON 对象（dict）恢复实例。
        
        伪代码:
            1. 返回本函数最终结果。
        数据结构:
            - 输入: obj。
            - 局部: 以临时表达式为主。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        om_raw = obj.get("operand_modifiers") or {}
        operand_modifiers = {}
        for k, v in om_raw.items():
            try:
                if isinstance(k, str) and k.startswith("(") and ")" in k:
                    key = ast.literal_eval(k)
                else:
                    key = int(k) if isinstance(k, str) and k.isdigit() else k
                operand_modifiers[key] = v
            except Exception:
                operand_modifiers[k] = v
        return cls(
            obj["disasm"],
            Instruction.from_json_obj(obj["parsed"]),
            EncodingRanges.from_json_obj(obj["ranges"]),
            obj["modifiers"],
            operand_modifiers,
            modifier_interactions=obj.get("modifier_interactions"),
            operand_interactions=obj["operand_interactions"],
            operand_modifier_composites=obj.get("operand_modifier_composites"),
        )

    def get_modifier_values(self, modifiers):
        # 贪心算法选择正确的 modifier 值。
        # 先清洗输入 modifier token：忽略占位符与 headerflags
        """读取并返回 `modifier_values` 相关结果。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
            2. 初始化或更新 counts。
            3. 遍历输入集合并在循环内执行条件判断与累积。
            4. 定义内部辅助函数 `score_match` 并在后续流程中调用。
            5. 初始化或更新 used_modis。
        数据结构:
            - 输入: modifiers。
            - 局部: modifiers, counts, modi, _counts, match。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, try/except 容错, 内嵌函数/闭包, Counter 计数。
        """
        try:
            modifiers = [m for m in modifiers if m and not (is_placeholder_modifier(str(m)) or str(m) == "headerflags")]
        except Exception:
            pass
        counts = Counter(modifiers)

        for modi in self.opcode_modis:
            counts[modi] -= 1
            if counts[modi] < 0:
                return None

        def score_match(modifier_group):
            """函数 `score_match` 的实现说明。
            
            伪代码:
                1. 初始化或更新 _counts。
                2. 初始化或更新 match。
                3. 遍历输入集合并在循环内执行条件判断与累积。
                4. 根据条件走不同分支并选择返回/继续路径。
            数据结构:
                - 输入: modifier_group。
                - 局部: _counts, match, modifier, score。
                - 输出: 通过 return 返回计算结果。
            复杂语法:
                - 使用 Counter 计数。
            """
            _counts = Counter(counts)
            match = True
            for modifier in modifier_group:
                if len(modifier) == 0:
                    continue
                if modifier not in counts:
                    match = False
                    break
            if not match:
                return 0
            for modifier in modifier_group:
                _counts[modifier] -= 1
                if _counts[modifier] < 0:
                    return 0
                counter_remove_zeros(_counts)
            score = sum(counts.values()) - sum(_counts.values())
            return score

        used_modis = set()
        # 确保 modi_values 长度足够：前序裁剪可能缩短 `self.modifiers`，
        # 但 `self.all_modifiers` 仍引用原组索引。按需扩容以避免 IndexError。
        max_idx = -1
        try:
            max_idx = max([i for _, i, _ in self.all_modifiers])
        except Exception:
            max_idx = -1
        base_len = max(0, len(self.modifiers))
        required_len = max(base_len, max_idx + 1)
        modi_values = [0] * required_len

        def _ensure_modi_len(idx):
            """函数 `_ensure_modi_len` 的实现说明。
            
            伪代码:
                1. 执行顺序语句并更新中间状态。
                2. 根据条件走不同分支并选择返回/继续路径。
            数据结构:
                - 输入: idx。
                - 局部: 以临时表达式为主。
                - 输出: 主要通过就地更新外部容器/对象状态。
            复杂语法:
                - 使用 条件分支与循环控制。
            """
            nonlocal modi_values
            if idx >= len(modi_values):
                modi_values.extend([0] * (idx - len(modi_values) + 1))
        change = True
        while len(counts) != 0 and change:
            change = False
            best_i = -1
            best_value = -1
            best_modi_group = None
            best_match = 0
            for modifier_group, i, value in self.all_modifiers:
                if i in used_modis:
                    continue
                modifier_group = [
                    operand
                    for operand in modifier_group.split(".")
                    if len(operand) != 0
                ]
                score = score_match(modifier_group)
                if score > best_match:
                    best_i = i
                    best_value = value
                    best_match = score
                    best_modi_group = modifier_group
            if best_match != 0:
                change = True
                if best_i >= 0:
                    _ensure_modi_len(best_i)
                    modi_values[best_i] = best_value
                    used_modis.add(best_i)
                for modifier in best_modi_group:
                    counts[modifier] -= 1
                    counter_remove_zeros(counts)

        flags = self.ranges.get_flags()
        used_flags = set()
        for name in counts:
            if name in flags:
                used_flags.add(name)
                counts[name] -= 1
        counter_remove_zeros(counts)

        if len(counts) != 0:
            return None

        for operand_group, i, value in self.all_modifiers:
            # 跳过已分配的 modifier 组
            if i in used_modis:
                continue
            if len(operand_group) != 0:
                continue
            _ensure_modi_len(i)
            modi_values[i] = value
        return modi_values, used_flags

    def get_minimal_modifiers(self) -> List[str]:
        """读取并返回 `minimal_modifiers` 相关结果。
        
        伪代码:
            1. 初始化或更新 modifiers。
            2. 遍历输入集合并在循环内执行条件判断与累积。
            3. 返回本函数最终结果。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: modifiers, modi_group, modis。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式。
        """
        modifiers = list(self.opcode_modis)
        for modi_group in self.modifiers:
            if len(modi_group) == 0:
                # 理论上不应发生，但确实可能出现。
                continue

            if "" in [modi[1] for modi in modi_group]:
                continue
            modis = modi_group[0][1][:-1].split(".")
            modifiers += modis
        return modifiers

    def encode_for_life_range(self, modifiers=[]) -> bytearray:
        """函数 `encode_for_life_range` 的实现说明。
        
        伪代码:
            1. 初始化或更新 operands。
            2. 初始化或更新 operand_values。
            3. 初始化或更新 reg_count。
            4. 初始化或更新 ureg_count。
            5. 初始化或更新 pred_count。
        数据结构:
            - 输入: modifiers。
            - 局部: operands, operand_values, reg_count, ureg_count, pred_count。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        operands = self.parsed.get_flat_operands()
        operand_values = [0] * len(operands)
        reg_count = 0
        ureg_count = 0
        pred_count = 1
        upred_count = 1

        modifiers, flags = self.get_modifier_values(modifiers)
        if modifiers is None:
            return None, None
        registers = []
        predicates = []
        upredicates = []
        uregisters = []
        for i, operand in enumerate(operands):
            if isinstance(operand, parser.RegOperand):
                if operand.reg_type == "R":
                    operand_values[i] = reg_count * 16 + 16
                    registers.append((i, operand_values[i]))
                    reg_count += 1
                elif operand.reg_type == "P":
                    operand_values[i] = pred_count * 2
                    predicates.append((i, operand_values[i]))
                    pred_count += 1
                elif operand.reg_type == "UP":
                    operand_values[i] = upred_count * 2
                    upredicates.append((i, operand_values[i]))
                    upred_count += 1
                elif operand.reg_type == "UR":
                    operand_values[i] = ureg_count * 4 + 4
                    uregisters.append((i, operand_values[i]))
                    ureg_count += 1
        reg_files = {
            "GPR": registers,
            "PRED": predicates,
            "UPRED": upredicates,
            "UGPR": uregisters,
        }
        encoded = self.ranges.encode(
            operand_values, modifiers, yield_flag=False, read_barrier=0, write_barrier=0
        )
        return (reg_files, encoded)

    def encode(
        self,
        operand_values,
        operand_modifiers=None,
        operand_flags=None,
        modifiers=None,
        predicate=None,
        stall_cycles=None,
        yield_flag=None,
        read_barrier=None,
        write_barrier=None,
        barrier_mask=None,
        reuse_mask=None,
    ) -> bytearray:
        """函数 `encode` 的实现说明。
        
        伪代码:
            1. 根据条件走不同分支并选择返回/继续路径。
            2. 初始化或更新 modifiers, flags。
            3. 返回本函数最终结果。
        数据结构:
            - 输入: operand_values, operand_modifiers, operand_flags, modifiers, predicate, stall_cycles, yield_flag, read_barrier, write_barrier, barrier_mask, reuse_mask。
            - 局部: modifiers, operand_modifiers, flags。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        if modifiers is None:
            modifiers = []
        if operand_modifiers is None:
            operand_modifiers = {}
        modifiers, flags = self.get_modifier_values(modifiers)
        if modifiers is None:
            return None

        return self.ranges.encode(
            operand_values,
            modifiers=modifiers,
            flags=flags,
            operand_modifiers=operand_modifiers,
            operand_flags=operand_flags,
            predicate=predicate,
            stall_cycles=stall_cycles,
            yield_flag=yield_flag,
            read_barrier=read_barrier,
            write_barrier=write_barrier,
            barrier_mask=barrier_mask,
            reuse_mask=reuse_mask,
        )

    def analyse_operand_interactions(self, arch_code, nvdisasm):
        """函数 `analyse_operand_interactions` 的实现说明。
        
        伪代码:
            1. 优先走主路径，异常时执行兜底分支。
            2. 根据条件走不同分支并选择返回/继续路径。
            3. 初始化或更新 result。
            4. 遍历输入集合并在循环内执行条件判断与累积。
            5. 执行赋值与状态更新。
        数据结构:
            - 输入: arch_code, nvdisasm。
            - 局部: reg_files, encoded, interaction_data, interaction_ranges, result。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, try/except 容错。
        """
        try:
            reg_files, encoded = self.encode_for_life_range(
                self.get_minimal_modifiers()
            )
            if encoded is None:
                return
            interaction_data, self.operand_interaction_raw = analyse_live_ranges(
                encoded, arch_code, nvdisasm=nvdisasm
            )
            interaction_ranges = get_interaction_ranges(interaction_data)
        except Exception:
            return
        if interaction_ranges is None:
            return
        result = {}
        for file_name, reg_ranges in interaction_ranges.items():
            range_to_operand = {begin: opx for opx, begin in reg_files[file_name]}
            result[file_name] = []
            for rng in reg_ranges:
                if rng[1] == "USED":
                    continue
                if rng[0] not in range_to_operand:
                    continue
                sub_operand_idx = range_to_operand[rng[0]]
                result[file_name].append((sub_operand_idx, rng[1], rng[2]))
        self.operand_interactions = result

    def generate_html(self):
        """生成该指令的 HTML：指令描述 + 位图 + modifier 表格。
        
        伪代码:
            1. 初始化或更新 desc_generator。
            2. 初始化或更新 html_result。
            3. 优先走主路径，异常时执行兜底分支。
            4. 初始化或更新 interaction_type_names。
        数据结构:
            - 输入: 无显式位置参数。
            - 局部: desc_generator, html_result, inst_hex, interaction_type_names, operand_interactions。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式, 生成器表达式, try/except 容错, f-string。
        """
        desc_generator = InstructionDescGenerator()
        html_result = desc_generator.generate(self.parsed, self.canonical_name)
        # 嵌入精确 16B 编码，便于基于 HTML 的校验可通过 nvdisasm 回环，
        # 无需依赖 isa.json/pipeline 回退。
        try:
            inst_hex = self.ranges.inst.hex()
        except Exception:
            inst_hex = ""
        html_result = f'<div class="spec" data-inst-hex="{inst_hex}">' + html_result
        interaction_type_names = {
            InteractionType.READ: "READ",
            InteractionType.WRITE: "WRITE",
            InteractionType.READWRITE: "READ_WRITE",
        }
        if self.operand_interactions:
            operand_interactions = []
            operands = self.parsed.get_flat_operands()
            for file, file_usages in self.operand_interactions.items():
                for usg in file_usages:
                    op = operands[usg[0]]
                    operand_interactions.append((op, usg[1], usg[2]))
            operand_interactions = sorted(
                operand_interactions, key=lambda x: x[0].flat_operand_index
            )

            for i, operand_int in enumerate(operand_interactions):
                color = operand_colors[operand_int[0].flat_operand_index]
                html_result += f"""
                    <span class="flat-operand-section" style="background-color:{color}">
                    {interaction_type_names[operand_int[1]]} {operand_int[0].reg_type} ({operand_int[2]} slots)
                    </span>
                """
        html_result += f"<p> distilled: {self.disasm}</p>"
        # 构建可安全展示的 key。若 parser 产出的 key 含 UNKNOWN
        # （如回退 RegOperand 导致），优先用 parsed operands 重建 key，
        # 并回退到包含 constant-memory 形态（c[...] / cx[...]）的 raw token，
        # 使 UI 展示更友好的 c[...] 表面而非 UNKNOWN。
        try:
            basic_key = self.parsed.get_key()
        except Exception:
            basic_key = None

        key = basic_key
        if not key or "UNKNOWN" in (key or ""):
            parts = [self.parsed.base_name]
            try:
                flat_ops = self.parsed.get_flat_operands()
                for op in flat_ops:
                    try:
                        k = op.get_operand_key()
                    except Exception:
                        k = None
                    # 若 operand key 为 UNKNOWN（多见于 RegOperand 回退），
                    # 但 raw token 含 c[...] 形态，则用该 raw token 构造 key。
                    if (not k or k == "UNKNOWN") and hasattr(op, "ident") and isinstance(
                        getattr(op, "ident", None), str
                    ) and "c[" in op.ident:
                        k = op.ident
                    if not k:
                        k = "UNKNOWN"
                    parts.append(k)
                key = "_".join(parts)
            except Exception:
                # 重建失败则保留 basic_key
                key = basic_key

        html_result += f"<p> key: {key}</p>"
        html_result += self.ranges.generate_html_table()
        for frag in getattr(self, "_html_table_fragments", []) or []:
            html_result += frag
        return html_result + "</div>"


def analysis_run_fixedpoint(
    disassembler: Disassembler, mset: InstructionMutationSet, fn
):
    """对 mset 反复执行 fn 直到不再变化（固定点迭代）。"""
    change = True
    while change:
        change = fn(disassembler, mset)


# 固定点分析阶段顺序：正确性相关（消歧/合并/扩展/拆分等）
_ANALYSIS_PHASES = [
    analysis_disambiguate_flags,
    analysis_merge_placeholder_backed_instruction_flags,
    analysis_promote_known_flags,
    analysis_merge_mutually_exclusive_instruction_flags,
    analysis_operand_fix,
    analysis_merge_mutually_exclusive_operand_flags,
    analysis_disambiguate_operand_flags,
    analysis_fimm_bridge_constants,
    analysis_augment_modifier_bits_from_cache,
    analysis_extend_modifiers,
    analysis_modifier_splitting,
]


def instruction_analysis_pipeline(
    inst,
    disassembler,
    arch_code,
    force_exhaustive=False,
    exhaustive_max=32768,
    expected_family_head=None,
    allow_expensive_cache_recovery=True,
    enable_operand_interactions=False,
    lightweight_diagnose=False,
    analysis_key=None,
    remediation_depth=0,
    diagnostic_feedback_hints=None,
    skip_distill=False,
    skip_attach_half_pair=False,
):
    """单条指令的完整分析流水线：distill -> mutate -> 多轮 analysis -> 枚举 modifier -> 构建 InstructionSpec。
    
    伪代码:
        1. 初始化或更新 raw_inst。
        2. 初始化或更新 inst。
        3. 初始化或更新 asm。
        4. 根据条件走不同分支并选择返回/继续路径。
        5. 优先走主路径，异常时执行兜底分支。
    数据结构:
        - 输入: inst, disassembler, arch_code, force_exhaustive, exhaustive_max, expected_family_head, allow_expensive_cache_recovery, enable_operand_interactions, lightweight_diagnose, analysis_key, remediation_depth。
        - 局部: raw_inst, inst, asm, distilled_head, raw_asm。
        - 输出: 通过 return 返回计算结果。
    复杂语法:
        - 使用 推导式, 生成器表达式, 位运算, try/except 容错。
    """
    with _profile_section("instruction_analysis_pipeline.total"):
        raw_inst = bytes(inst) if isinstance(inst, (bytes, bytearray)) else inst
        if skip_distill:
            inst = raw_inst
            with _profile_section("instruction_analysis_pipeline.disassemble_baseline"):
                asm = disassembler.disassemble(inst)
        else:
            with _profile_section("instruction_analysis_pipeline.distill"):
                inst = disassembler.distill_instruction(inst)
            with _profile_section("instruction_analysis_pipeline.disassemble_baseline"):
                asm = disassembler.disassemble(inst)
    # 在 exact-family 模式下，distillation 不能漂移到其他助记符 family
    #（例如请求 MUFU.COS，却蒸馏成 MUFU.RSQ）。
    if expected_family_head:
        try:
            distilled_head = _extract_mnemonic_head_from_disasm(asm)
        except Exception:
            distilled_head = None
        if distilled_head != expected_family_head:
            try:
                raw_asm = disassembler.disassemble(raw_inst)
                raw_head = _extract_mnemonic_head_from_disasm(raw_asm)
            except Exception:
                raw_asm = None
                raw_head = None
            if raw_head == expected_family_head:
                inst = raw_inst
                asm = raw_asm
    # 在任何基于 cache 的清理前记录原始 parsed 指令，
    # 以检测原始 disasm 是否包含占位符 modifiers（如 '???'），
    # 并丢弃那些无法通过 mutation/enumeration 得到具体替代的变体。
    try:
        orig_lines = [l for l in asm.splitlines() if l.strip()]
        orig_line = orig_lines[-1] if orig_lines else asm
        orig_parsed = InstructionParser.parseInstruction(orig_line)
        orig_has_placeholders = has_placeholder_modifier(getattr(orig_parsed, 'modifiers', []))
    except Exception:
        orig_parsed = None
        orig_has_placeholders = False

    # 与 orign 一致：主动 mutation 只覆盖 bit 0..109。
    # 110..127 位会在 compute_encoding_ranges 阶段参与渲染，默认作为常量或控制码字段显示。
    with _profile_section("instruction_analysis_pipeline.mutate_inst"):
        mutations = disassembler.mutate_inst(inst, end=MUTATION_ANALYSIS_END_BIT)
    with _profile_section("instruction_analysis_pipeline.build_mutation_set"):
        mutation_set = InstructionMutationSet(inst, asm, mutations, disassembler)
    # 使用 mutation set 中可能已清理的 parsed 基线，
    # 让后续分析/回退都基于合理的 parsed 指令执行。
    parsed_inst = mutation_set.parsed
    try:
        original_parser_modifiers = [
            m.rstrip(".")
            for m in (getattr(parsed_inst, "modifiers", []) or [])
            if isinstance(m, str) and m and not is_placeholder_modifier(m)
        ]
    except Exception:
        original_parser_modifiers = []

    for phase_fn in _ANALYSIS_PHASES:
        with _profile_section(f"analysis_phase.{phase_fn.__name__}"):
            analysis_run_fixedpoint(disassembler, mutation_set, phase_fn)
    try:
        if _apply_diagnostic_feedback_hints(
            mutation_set,
            parsed_inst.get_key(),
            analysis_key=analysis_key,
            feedback_hints=diagnostic_feedback_hints,
        ):
            with _profile_section("analysis_phase.feedback_extend_modifiers"):
                analysis_run_fixedpoint(disassembler, mutation_set, analysis_extend_modifiers)
            with _profile_section("analysis_phase.feedback_modifier_splitting"):
                analysis_run_fixedpoint(disassembler, mutation_set, analysis_modifier_splitting)
    except Exception:
        pass
    with _profile_section("instruction_analysis_pipeline.compute_encoding_ranges"):
        ranges = mutation_set.compute_encoding_ranges()

    # 通用 cache 回退：若对明显有 operands 的指令仍推断不出 operand ranges，
    # 尝试同 key 的其他 cache 编码并重新运行 mutation 分析以恢复 operand ranges。
    # 这与旧版 SM100a pipeline 的行为一致：有时会选到更适合 mutation 的编码。
    try:
        operand_ranges = ranges._find(EncodingRangeType.OPERAND)
    except Exception:
        operand_ranges = []
    try:
        parsed_ops = parsed_inst.get_flat_operands() if hasattr(parsed_inst, "get_flat_operands") else []
    except Exception:
        parsed_ops = []
    if (not operand_ranges) and parsed_ops:
        try:
            refined = _refine_operand_ranges_from_cache(disassembler, parsed_inst)
        except Exception:
            refined = None
        if refined is not None:
            new_ranges, new_parsed, new_mset = refined
            try:
                new_operand_ranges = new_ranges._find(EncodingRangeType.OPERAND)
            except Exception:
                new_operand_ranges = []
            if new_operand_ranges:
                ranges = new_ranges
                parsed_inst = new_parsed
                mutation_set = new_mset
        else:
            # 最后手段：基于 cache 差分合成 operand bits（如 ARRIVES [UR0] vs [UR4]）
            try:
                augmented = _augment_operand_bits_from_cache(
                    disassembler, parsed_inst, mutation_set
                )
            except Exception:
                augmented = None
            if augmented is not None:
                new_ranges, new_parsed, new_mset = augmented
                try:
                    new_operand_ranges = new_ranges._find(EncodingRangeType.OPERAND)
                except Exception:
                    new_operand_ranges = []
                if new_operand_ranges:
                    ranges = new_ranges
                    parsed_inst = new_parsed
                    mutation_set = new_mset

    # 若调用方要求，尝试对已发现 modifier ranges 做有界穷举，
    # 以寻找同 key 的干净编码。
    if force_exhaustive:
        try:
            clean_candidate = enumerate_all_combinations(ranges, disassembler, exhaustive_max, target_key=parsed_inst.get_key())
            if clean_candidate:
                try:
                    return instruction_analysis_pipeline(
                        clean_candidate,
                        disassembler,
                        arch_code,
                        force_exhaustive=False,
                        expected_family_head=expected_family_head,
                        allow_expensive_cache_recovery=allow_expensive_cache_recovery,
                        enable_operand_interactions=enable_operand_interactions,
                        lightweight_diagnose=lightweight_diagnose,
                        analysis_key=analysis_key,
                    )
                except Exception:
                    pass
        except Exception:
            pass

    if lightweight_diagnose:
        simple_modifier_values = []
        try:
            seen = set()
            for modifier in getattr(parsed_inst, "modifiers", []) or []:
                if not isinstance(modifier, str):
                    continue
                clean = modifier.rstrip(".").strip()
                if not clean or is_placeholder_modifier(clean) or clean in seen:
                    continue
                seen.add(clean)
                simple_modifier_values.append([(0, clean + ".")])
        except Exception:
            simple_modifier_values = []
        simple_operand_modifiers = {}
        try:
            for idx, operand in enumerate(parsed_inst.get_flat_operands()):
                rows = []
                seen_rows = set()
                for modifier in getattr(operand, "modifiers", []) or []:
                    if not isinstance(modifier, str):
                        continue
                    clean = modifier.rstrip(".").strip()
                    if not clean or is_placeholder_modifier(clean):
                        continue
                    if isinstance(operand, parser.IntIMMOperand) and clean not in {"cNEG", "cABS"}:
                        continue
                    if isinstance(operand, parser.FloatIMMOperand):
                        continue
                    if clean in seen_rows:
                        continue
                    seen_rows.add(clean)
                    rows.append((0, clean + "."))
                if rows:
                    simple_operand_modifiers[idx] = rows
        except Exception:
            simple_operand_modifiers = {}
        asm2 = sanitize_disasm(asm)
        return InstructionSpec(
            asm2,
            parsed_inst,
            ranges,
            simple_modifier_values,
            simple_operand_modifiers,
            force_modifier_bits=getattr(mutation_set, "modifier_bits", None),
        )

    # 若未检测到 modifier bits，尝试在 disassembler cache 中寻找干净变体，
    # 并在该编码上重跑分析，从而在不做穷举的前提下获得可用于高亮的
    # 正确编码 ranges。
    # 当 skip_distill 为 True（remediation 轮）时禁止此回退，否则会用同 key 的
    # 其他候选替换当前指令，可能选到不含 F32/RELU 等 token 的样本，导致再次丢失。
    if (
        len(mutation_set.modifier_bits) == 0
        and not (getattr(mutation_set, "operand_modifier_bits", None) or set())
        and not (getattr(mutation_set, "operand_modifier_bit_flag", None) or {})
        and allow_expensive_cache_recovery
        and not skip_distill
    ):
        try:
            # 从 disassembler cache 尝试多个干净候选，直到找到一个能通过
            # 同步探测得到具体 modifier ranges 的编码。这样比只依赖
            # 单一候选更稳健。
            key = parsed_inst.get_key()
            candidates = []
            # 按 key 索引直接查候选，避免遍历整个 cache
            for inst_b, asm_text in _cache_iter_by_key(disassembler, key):
                lines = [l for l in asm_text.splitlines() if l.strip()]
                if not lines:
                    continue
                asm_line = lines[-1]
                if expected_family_head:
                    try:
                        if _extract_mnemonic_head_from_disasm(asm_line) != expected_family_head:
                            continue
                    except Exception:
                        continue
                try:
                    p = InstructionParser.parseInstruction(asm_line)
                except Exception:
                    continue
                if p.get_key() != key:
                    continue
                bad = False
                for m in p.modifiers:
                    if is_placeholder_modifier(m):
                        bad = True
                        break
                if bad:
                    continue
                candidates.append((inst_b, asm_line))
                if len(candidates) >= 128:
                    break

            import math

            for clean_bytes, clean_asm in candidates:
                clean_inst = bytes(clean_bytes)
                base_asm = disassembler.disassemble(clean_inst)
                base_lines = [l for l in base_asm.splitlines() if l.strip()]
                base_line = base_lines[-1] if base_lines else base_asm
                try:
                    base_parsed = InstructionParser.parseInstruction(base_line)
                except Exception:
                    continue

                probe = InstructionMutationSet.__new__(InstructionMutationSet)
                probe.inst = clean_inst
                probe.disasm = base_line
                probe.parsed = base_parsed
                probe.mutations = []
                probe.disassembler = disassembler

                probe.operand_type_bits = set()
                probe.opcode_bits = set()
                probe.operand_value_bits = set()
                probe.operand_modifier_bits = set()
                probe.operand_modifier_bit_flag = {}
                probe.instruction_modifier_bit_flag = {}
                probe.bit_to_operand = {}
                probe.predicate_bits = set()

                probe.modifier_bits = set()
                probe.modifier_groups = {}

                parsed_operands = base_parsed.get_flat_operands()

                probe_insts = []
                for i_bit in range(0, MUTATION_ANALYSIS_END_BIT):
                    inst_arr = bytearray(clean_inst)
                    inst_arr[i_bit // 8] ^= (1 << (i_bit % 8))
                    probe_insts.append(bytes(inst_arr))
                probe_disasms = disassembler.disassemble_parallel(probe_insts)

                for i_bit, asm_txt in enumerate(probe_disasms):
                    asm_lines = [l for l in asm_txt.splitlines() if l.strip()]
                    if not asm_lines:
                        continue
                    try:
                        mutated = InstructionParser.parseInstruction(asm_lines[-1])
                    except Exception:
                        continue
                    if base_parsed.get_key() != mutated.get_key():
                        probe.opcode_bits.add(i_bit)
                        continue
                    if base_parsed.predicate != mutated.predicate:
                        probe.predicate_bits.add(i_bit)
                    # 操作数
                    for oi, (a, b) in enumerate(zip(mutated.get_flat_operands(), parsed_operands)):
                        if not a.compare(b):
                            probe.operand_value_bits.add(i_bit)
                            probe.bit_to_operand[i_bit] = oi
                            break
                    else:
                        # 回退：若 modifiers 不同，则标记为 modifier bit
                        if mutated.modifiers != base_parsed.modifiers:
                            probe.modifier_bits.add(i_bit)

                _augment_predicate_bits_from_cache(disassembler, key, probe.predicate_bits)

                # 构建 ranges 并尝试枚举
                probe_ranges = probe.compute_encoding_ranges()
                try:
                    setattr(probe_ranges, "_analysis_key", analysis_key or key)
                except Exception:
                    pass
                modifier_values = probe_ranges.enumerate_modifiers(disassembler)
                operand_modifier_values = probe_ranges.enumerate_operand_modifiers(disassembler)

                if modifier_values:
                    candidate_parsed_inst = InstructionParser.parseInstruction(clean_asm)
                    # 确保 parsed 指令与枚举出的 modifier 名称均不含
                    # 占位符 token（???、INVALID 或 '.0'）。
                    parsed_has_placeholders = any(isinstance(m, str) and is_placeholder_modifier(m) for m in getattr(candidate_parsed_inst, 'modifiers', []))
                    enum_has_placeholders = any(isinstance(name, str) and is_placeholder_modifier(name) for group in modifier_values for (_, name) in group)
                    if parsed_has_placeholders or enum_has_placeholders:
                        # 跳过该候选并尝试下一个干净 cache 条目
                        continue
                    clean_asm2 = sanitize_disasm(clean_asm)
                    spec = InstructionSpec(
                        clean_asm2,
                        candidate_parsed_inst,
                        probe_ranges,
                        modifier_values,
                        operand_modifier_values,
                        force_modifier_bits=getattr(probe, "modifier_bits", None),
                    )
                    try:
                        unify_spec_modifiers(spec)
                    except Exception:
                        pass
                    try:
                        _backfill_modifier_tables_from_ranges(spec, disassembler)
                    except Exception:
                        pass
                    # 用从 spec.modifiers 派生的具体名称替换 parsed modifiers
                    try:
                        new_parsed_mods = []
                        for grp in getattr(spec, 'modifiers', []):
                            if grp and len(grp) > 0:
                                nm = grp[0][1]
                                if isinstance(nm, str):
                                    nm = nm.rstrip('.')
                                if not is_placeholder_modifier(nm):
                                    new_parsed_mods.append(nm)
                        # 将 opcode 级 modifiers（opcode_modis）合并进 parsed.modifiers
                        try:
                            disasm_mod_list = []
                            disasm_mods = set()
                            try:
                                dlines = [l for l in str(getattr(spec, "disasm", "")).splitlines() if l.strip()]
                                if dlines:
                                    dparsed = InstructionParser.parseInstruction(dlines[-1])
                                    disasm_mod_list = [
                                        m.rstrip(".")
                                        for m in (getattr(dparsed, "modifiers", []) or [])
                                        if isinstance(m, str) and m and not is_placeholder_modifier(m)
                                    ]
                                    disasm_mods = set(disasm_mod_list)
                            except Exception:
                                disasm_mod_list = []
                                disasm_mods = set()
                            opcode_mods = getattr(spec, 'opcode_modis', []) or []
                            opcode_clean = [
                                m
                                for m in opcode_mods
                                if isinstance(m, str)
                                and not is_placeholder_modifier(m)
                                and (not disasm_mods or m in disasm_mods)
                            ]
                        except Exception:
                            opcode_clean = []
                        # 仅保留在最终反汇编中出现的逐 range 投影 modifiers；
                        # 避免把 cache/噪声 token（如默认别名）带入 parsed.modifiers。
                        if disasm_mods:
                            new_parsed_mods = [m for m in new_parsed_mods if m in disasm_mods]
                        # 组合最终 modifiers：先 opcode 级，再逐 range 解析结果。
                        # 若解析为空，则保留 parser 观察到的 modifiers
                        #（如 CALL.REL.NOINC 在未发现 modifier ranges 时）。
                        merged = []
                        for m in opcode_clean + new_parsed_mods:
                            if m and m not in merged:
                                merged.append(m)
                        for m in disasm_mod_list:
                            if m and m not in merged:
                                merged.append(m)
                        if not merged:
                            try:
                                for m in getattr(spec.parsed, "modifiers", []) or []:
                                    if isinstance(m, str):
                                        mm = m.rstrip(".")
                                        if (
                                            mm
                                            and not is_placeholder_modifier(mm)
                                            and (not disasm_mods or mm in disasm_mods)
                                            and mm not in merged
                                        ):
                                            merged.append(mm)
                            except Exception:
                                pass
                        if hasattr(spec.parsed, 'modifiers'):
                            spec.parsed.modifiers = merged
                        else:
                            setattr(spec.parsed, 'modifiers', merged)
                    except Exception:
                        pass
                    # 用选中名称标注 modifier ranges，提升可读性
                    try:
                        mod_ranges = spec.ranges._find(EncodingRangeType.MODIFIER)
                        if mod_ranges:
                            # 标注 range 时，若 parser 提供的具体 modifier 名出现在
                            # 该 range 的枚举候选中，则优先使用它。这样可避免在 parser
                            # 已识别该编码槽为另一 modifier（如 E5M2/E2M3）时，
                            # 误分配到其他组 token（如 F16/BF16）。
                            parsed_tokens = filter_non_placeholder_modifiers(getattr(spec.parsed, 'modifiers', []))
                            for idx, mr in enumerate(mod_ranges):
                                try:
                                    if getattr(spec, 'modifiers', None) and idx < len(spec.modifiers):
                                        grp = spec.modifiers[idx]
                                        if grp and len(grp) > 0:
                                            # 本组候选名称（无尾随点）
                                            cand = [n.rstrip('.') for (_v, n) in grp if isinstance(n, str) and n]
                                            chosen = None
                                            # 选取首个出现在候选中的 parser token
                                            for pt in parsed_tokens:
                                                if pt in cand:
                                                    chosen = pt
                                                    break
                                            # 否则优先编码值对应候选
                                            if chosen is None:
                                                nm = grp[0][1]
                                                if isinstance(nm, str):
                                                    chosen = nm.rstrip('.')
                                            if chosen is not None:
                                                mr.name = chosen
                                except Exception:
                                    continue
                    except Exception:
                        pass
                    # 在可行时，用 operand_modifier_values 更新 operand modifiers
                    try:
                        op_ranges = spec.ranges._find(EncodingRangeType.OPERAND_MODIFIER)
                        if op_ranges:
                            flat_ops = spec.parsed.get_flat_operands()
                            for rng in op_ranges:
                                try:
                                    val = get_bit_range(spec.ranges.inst, rng.start, rng.start + rng.length)
                                except Exception:
                                    val = 0
                                op_idx = getattr(rng, 'operand_index', None)
                                rows = _get_operand_modifier_rows(operand_modifier_values, op_idx, rng)
                                chosen = _chosen_display_from_rows(rows, val)
                                if chosen is not None and op_idx is not None and op_idx < len(flat_ops):
                                    op = flat_ops[op_idx]
                                    try:
                                        existing = filter_non_placeholder_modifiers(getattr(op, 'modifiers', []) or [])
                                        existing.append(chosen)
                                        op.modifiers = existing
                                    except Exception:
                                        pass
                                    try:
                                        # 用选中名称标注 operand_modifier range
                                        rng.name = chosen
                                    except Exception:
                                        pass
                    except Exception:
                        pass
                    try:
                        key = spec.parsed.get_key()
                        evidence_bits = (
                            set(probe.modifier_bits)
                            if getattr(probe, "modifier_bits", None)
                            else None
                        )
                        if not _try_repair_spec_disasm(
                            spec,
                            disassembler,
                            target_key=key,
                            expected_family_head=getattr(spec.parsed, "base_name", None),
                            evidence_bits=evidence_bits,
                        ):
                            spec.filtered = True

                        if enable_operand_interactions:
                            try:
                                spec.analyse_operand_interactions(arch_code, disassembler.nvdisasm)
                            except Exception:
                                pass
                    except Exception:
                        pass
                    # 最后关口：候选被接受前，必须通过集中式最终一致性检查。
                    if _spec_final_consistent(spec, disassembler):
                        return spec
                    # 该 cache 候选不一致时，不应整条指令直接失败；
                    # 放弃当前候选并继续尝试下一个，若都失败再回到主流程。
                    continue

            # 若执行到此，同步探测未产出 modifier ranges。
            # 当禁用 cache 回退时，不查询 disassembler cache 来合成
            # modifier 名称。按用户要求，凡 parsed 反汇编含占位符且
            # 无法经枚举/mutation 解析的变体应被丢弃。
            if not ENABLE_CACHE_FALLBACK:
                return None

        except Exception:
            # 确保外层探测 try 块平衡；候选探测中出现任何异常时，
            # 视为未找到候选并继续主流程。
            pass

    # 枚举 instruction-level modifier 取值。
    try:
        with _profile_section("instruction_analysis_pipeline.enumerate_modifiers"):
            modifier_values = ranges.enumerate_modifiers(disassembler)
    except Exception:
        modifier_values = []

    # 回退：若 modifier 枚举失败（常由 nvdisasm 报错导致），
    # 则从 disassembler cache 收集同指令 key 的干净 modifier 名称列表，
    # 填充一个简化 modifier 分组，使 HTML 在缺少 bit->name 映射时
    # 仍可展示候选名称。
    if not modifier_values:
        try:
            seen = []
            key = parsed_inst.get_key()
            for inst_b, asm_text in _cache_iter_by_key(disassembler, key):
                lines = [l for l in asm_text.splitlines() if l.strip()]
                if not lines:
                    continue
                asm_line = lines[-1]
                try:
                    p = InstructionParser.parseInstruction(asm_line)
                except Exception:
                    continue
                bad = False
                for m in p.modifiers:
                    if not m or m.startswith("???") or m.startswith("INVALID"):
                        bad = True
                        break
                if bad:
                    continue
                # 记录 modifier 元组
                tup = tuple(p.modifiers)
                if tup in seen:
                    continue
                seen.append(tup)
                modifier_values.append(
                    [
                        (idx, m if m.endswith(".") else m + ".")
                        for idx, m in enumerate(tup)
                        if isinstance(m, str) and m
                    ]
                )
        except Exception:
            pass

    try:
        with _profile_section("instruction_analysis_pipeline.enumerate_operand_modifiers.initial"):
            operand_modifier_values = ranges.enumerate_operand_modifiers(disassembler)
    except Exception:
        operand_modifier_values = {}
    # 清洗 modifier 名称：将空名称替换为可读占位
    try:
        sanitized = []
        for group in modifier_values:
            # 分析阶段尽量保留占位符/INVALID 名称，避免在位推理和
            # 诊断前过早丢失证据；占位符清理推迟到 HTML/isa 输出阶段。
            remove_placeholders = False
            new_group = []
            for val, name in group:
                if not name or len(name.strip()) == 0:
                    # 此处不替换 parser-only modifier 名称；保持为空，
                    # 让后续裁剪移除缺少具体位证据的分组。
                    new_group.append((val, ""))
                else:
                    new_group.append((val, name))

            if remove_placeholders:
                filtered = [(v, n) for (v, n) in new_group if not is_placeholder_modifier(n)]
                # 若过滤后全空，则回退到原始 new_group
                if len(filtered) > 0:
                    new_group = filtered

            sanitized.append(new_group)
        modifier_values = sanitized
    except Exception:
        pass

    # 移除结构性空 modifier 组；即便名称全像占位符，也保留组结构，
    # 以便后续分析/诊断继续利用其数值分布。
    try:
        # 移除完全空的组。
        modifier_values = [
            g
            for g in modifier_values
            if g and len(g) > 0
        ]
    except Exception:
        modifier_values = modifier_values

    # 若裁剪后所有组都消失，尝试保守回退：
    # 优先使用 parsed 指令中的具体 modifiers（排除占位符），
    # 并以单组形式展示，让 UI 仍能显示候选。
    if not modifier_values:
        try:
            parsed_mods = [m for m in filter_non_placeholder_modifiers(parsed_inst.modifiers or []) if m]
            if parsed_mods:
                # 每个 parsed modifier 建一个单选组
                modifier_values = [[(0, name + ".")] for name in parsed_mods]
        except Exception:
            pass

    def _modifier_layout_signature(ranges_obj, modifier_rows):
        try:
            range_sig = tuple(
                (
                    getattr(getattr(rng, "type", None), "value", getattr(rng, "type", None)),
                    int(getattr(rng, "start", 0) or 0),
                    int(getattr(rng, "length", 0) or 0),
                    getattr(rng, "operand_index", None),
                    getattr(rng, "name", None),
                    getattr(rng, "constant", None),
                )
                for rng in getattr(ranges_obj, "ranges", []) or []
            )
        except Exception:
            range_sig = tuple()
        try:
            rows_sig = tuple(
                tuple((int(v), n if isinstance(n, str) else n) for v, n in (group or []))
                for group in (modifier_rows or [])
            )
        except Exception:
            rows_sig = tuple()
        return (range_sig, rows_sig)

    def _modifier_range_layout_signature(ranges_obj):
        try:
            return tuple(
                (
                    int(getattr(rng, "start", 0) or 0),
                    int(getattr(rng, "length", 0) or 0),
                    getattr(rng, "name", None),
                    getattr(rng, "constant", None),
                )
                for rng in ranges_obj._find(EncodingRangeType.MODIFIER)
            )
        except Exception:
            return tuple()

    def _apply_forced_modifier_rows(current_ranges, current_modifier_values):
        try:
            forced_rows = getattr(mutation_set, "forced_modifier_rows_by_range", {}) or {}
        except Exception:
            forced_rows = {}
        if not forced_rows or not current_modifier_values:
            return current_modifier_values
        try:
            mod_ranges = current_ranges._find(EncodingRangeType.MODIFIER)
        except Exception:
            return current_modifier_values
        patched = list(current_modifier_values)
        for idx, mr in enumerate(mod_ranges):
            if idx >= len(patched):
                break
            key = (mr.start, mr.length)
            if key in forced_rows:
                patched[idx] = list(forced_rows[key])
        return patched

    # 运行一个小型固定点循环，使新拆分的 ranges 在下一轮可继续被
    # 压缩/再拆分（如 ISETP：6 -> 1+5 -> 1+3+2）。
    for _modifier_split_pass in range(3):
        modifier_values = _apply_forced_modifier_rows(ranges, modifier_values)
        before_split_signature = _modifier_layout_signature(ranges, modifier_values)
        before_range_layout = _modifier_range_layout_signature(ranges)

        # 先切出常量位（前缀/后缀/内部）。当仅有 U32/S32（枚举中无 RZ）时，
        # 会得到 1+5(CONST)，从而避免错误展示“5-bit modi 2: 11010→RZ”。
        try:
            modifier_values, ranges = compress_modifier_constant_bits(ranges, modifier_values)
        except Exception:
            pass

        # 拆分复合 modifier ranges（如 UTMALDG ND+GATHER4、I2FP U32+RZ）。
        try:
            modifier_values, ranges = try_split_modifier_groups(disassembler, ranges, modifier_values)
        except Exception:
            pass
        modifier_values = _apply_forced_modifier_rows(ranges, modifier_values)

        # 第二次压缩：对 try_split 产出的 ranges 再切内部常量
        #（如 I2FP 4+2 -> 4-bit 段中 bit1-3 对 F32.S32 为常量 -> 1+3+2）。
        try:
            modifier_values, ranges = compress_modifier_constant_bits(ranges, modifier_values)
        except Exception:
            pass
        modifier_values = _apply_forced_modifier_rows(ranges, modifier_values)

        after_range_layout = _modifier_range_layout_signature(ranges)

        # 压缩后重新枚举：compress_modifier_constant_bits 中的投影可能碰撞
        #（多个原值映射到同一投影值），导致名称错误
        #（如 modi2 值 00 显示 "F32"，本应为空）。
        # 在切分后的 ranges 上重跑 enumerate_modifiers，可借助段隔离
        # 得到正确的分段名称。
        try:
            mod_ranges = ranges._find(EncodingRangeType.MODIFIER)
            if len(mod_ranges) >= 1 and after_range_layout != before_range_layout:
                re_enum = ranges.enumerate_modifiers(disassembler)
                if re_enum and len(re_enum) == len(mod_ranges):
                    modifier_values = re_enum
        except Exception:
            pass
        modifier_values = _apply_forced_modifier_rows(ranges, modifier_values)

        after_split_signature = _modifier_layout_signature(ranges, modifier_values)
        if after_split_signature == before_split_signature:
            break

    # 应用由位证据直接给出的强制映射（例如 MUFU 的 F16/BF16 互斥 2-bit 组），
    # 避免枚举阶段把其它组 token 错误投影到该组。
    modifier_values = _apply_forced_modifier_rows(ranges, modifier_values)

    # 尝试将看起来像“寄存器到 operand 映射”的 modifier 组重分类为
    # operand modifiers。用于处理 nvdisasm 枚举给出类寄存器 token
    #（或空名）但其本质并非 instruction-level modifier，而是 operand 选择编码。
    try:
        modifier_ranges = ranges._find(EncodingRangeType.MODIFIER)
        parsed_flat = parsed_inst.get_flat_operands() if parsed_inst else []
        parsed_token_to_idx = {}
        for idx, op in enumerate(parsed_flat):
            try:
                if hasattr(op, 'reg_type') and hasattr(op, 'ident') and op.ident is not None:
                    parsed_token_to_idx[f"{op.reg_type}{op.ident}"] = idx
            except Exception:
                continue

        new_operand_mods = dict(operand_modifier_values) if operand_modifier_values else {}
        keep_groups = []
        # 预计算 modifier ranges 的基线编码值，便于即使发生裁剪/重排
        # 也能稳健地把枚举组映射回 ranges。
        base_vals = [
            get_bit_range(ranges.inst, rng.start, rng.start + rng.length)
            for rng in modifier_ranges
        ]

        for i, group in enumerate(modifier_values):
            # 收集具体且非占位符名称
            names = [name for (_, name) in group if name and not is_placeholder_modifier(name)]
            if len(names) == 0:
                # 无可用映射信息 -> 保持原状（可能已在前面清洗过）
                keep_groups.append(group)
                continue

            mapped_idx = None
            ambiguous = False
            for name in names:
                gname = name[:-1] if name.endswith('.') else name
                tokens = [t for t in gname.split('.') if len(t) != 0]
                if len(tokens) == 0:
                    ambiguous = True
                    break
                for tok in tokens:
                    if not (tok.startswith('R') or tok.startswith('UR') or tok.startswith('P') or tok.startswith('UP') or tok.startswith('SR')):
                        ambiguous = True
                        break
                    if tok not in parsed_token_to_idx:
                        ambiguous = True
                        break
                    idx = parsed_token_to_idx[tok]
                    if mapped_idx is None:
                        mapped_idx = idx
                    elif mapped_idx != idx:
                        ambiguous = True
                        break
                if ambiguous:
                    break

            if not ambiguous and mapped_idx is not None:
                # 将对应 ranges 重分类为 OPERAND_MODIFIER，并得到 mr 用于 range_key。
                mr = None
                group_vals = set(v for (v, _) in group)
                for j, mrange in enumerate(modifier_ranges):
                    if base_vals[j] in group_vals:
                        mr = mrange
                        break
                if mr is None and i < len(modifier_ranges):
                    mr = modifier_ranges[i]
                if mr is not None:
                    if not _should_reclassify_modifier_range_as_operand_modifier(mr):
                        _warn_skipped_operand_modifier_reclassification(
                            mr,
                            getattr(ranges, "_analysis_key", None)
                            or (parsed_inst.get_key() if parsed_inst else None),
                            mapped_idx,
                            group,
                        )
                        keep_groups.append(group)
                        continue
                    range_key = (mapped_idx, mr.start, mr.length)
                    existing = new_operand_mods.get(range_key, [])
                    for val, name in group:
                        if (val, name) not in existing:
                            existing.append((val, name))
                    new_operand_mods[range_key] = existing
                    for rng in ranges.ranges:
                        if (
                            rng.type == EncodingRangeType.MODIFIER
                            and rng.start == mr.start
                            and rng.length == mr.length
                        ):
                            rng.type = EncodingRangeType.OPERAND_MODIFIER
                            rng.operand_index = mapped_idx
                            rng.group_id = None
                # 该组不再保留在 instruction-level modifiers 中
                continue

            keep_groups.append(group)

        modifier_values = keep_groups
        operand_modifier_values = new_operand_mods
    except Exception:
        # 尽力而为；即使重分类失败也继续
        pass

    # 这一阶段不直接替换为 cache 中的“干净编码”。
    # 占位符补救在后续 placeholder 处理分支统一执行。

    # 若已解析出 operands 但未检测到任何 operand ranges，不再在此阶段丢弃指令；
    # 仍继续构建 spec（operand 信息保留在 parsed 中），由输出阶段决定是否保留，
    # 避免 UTCIMMA/UTCQMMA 等复杂 operand 指令被整条丢弃。
    try:
        parsed_ops = parsed_inst.get_flat_operands()
        operand_ranges = ranges._find(EncodingRangeType.OPERAND)
        if len(parsed_ops) > 0 and len(operand_ranges) == 0:
            pass  # 继续，不 return None
    except Exception:
        pass

    # 若 parsed 指令包含占位符 modifiers（???/INVALID/.0），
    # 且枚举未产出任何具体 modifier 名称，则执行以下策略（与备份运行时一致）：
    # 1) 先尝试同 key 的任意干净 cache 条目直接替换。
    # 2) 若失败，执行有界枚举，发现干净同 key 编码并采用其 parsed modifiers。
    # 3) 若仍失败，丢弃该变体。
    #
    # 当蒸馏字节反汇编后仍含占位符（如 ARRIVES.???0）时，
    # 优先使用干净 cache 编码，确保最终 spec 的 disasm 不含 ???。
    reanalysis_inst = None
    placeholder_recovery_cache = {}

    def _recover_placeholder_modifier_state_cached(current_parsed_inst, current_ranges):
        try:
            cache_key = (
                current_parsed_inst.get_key(),
                bytes(getattr(current_ranges, "inst", b"")),
                current_ranges._range_signature(),
            )
        except Exception:
            cache_key = None
        if cache_key is not None and cache_key in placeholder_recovery_cache:
            return placeholder_recovery_cache[cache_key]
        recovered = _recover_placeholder_modifier_state(
            disassembler, current_parsed_inst, current_ranges, mutation_set
        )
        if cache_key is not None:
            placeholder_recovery_cache[cache_key] = recovered
        return recovered

    try:
        parsed_mods = parsed_inst.modifiers if hasattr(parsed_inst, "modifiers") else []
        has_parsed_placeholders = any(isinstance(m, str) and is_placeholder_modifier(m) for m in parsed_mods)
        has_concrete_mod_names = _has_concrete_modifier_names(modifier_values)
        # 若 parsed 含占位符，先尝试干净 cache 替换，使 spec.ranges.inst
        # 可被干净反汇编（避免最终检查因 ??? 被拒绝）。
        if has_parsed_placeholders:
            try:
                rem = _find_clean_cache_candidate(disassembler, parsed_inst)
                if rem:
                    parsed_inst, modifier_values, clean_inst, clean_asm = rem
                    reanalysis_inst = bytes(clean_inst)
                    ranges = EncodingRanges(ranges.ranges, clean_inst)
                    asm = clean_asm
                    has_parsed_placeholders = False  # now clean
            except Exception:
                pass
        if has_parsed_placeholders and not has_concrete_mod_names:
            recovered = _recover_placeholder_modifier_state_cached(parsed_inst, ranges)
            if recovered is None:
                return None
            parsed_inst = recovered["parsed_inst"]
            modifier_values = recovered["modifier_values"]
            ranges = recovered["ranges"]
            asm = recovered["asm"]
            reanalysis_inst = recovered["reanalysis_inst"]
    except Exception:
        pass

    # 若原始 parsed 指令含占位符 modifiers，且 enumeration/mutation
    # 未产出任何具体 modifier 名称，则丢弃该变体
    #（用户要求不保留 parser-only 修复）。
    try:
        has_concrete_mod_names = _has_concrete_modifier_names(
            modifier_values, operand_modifier_values
        )
        if orig_has_placeholders and not has_concrete_mod_names:
            # 对含占位符的 parsed asm 未找到补救。
            # 仅在禁用 cache 回退时直接丢弃；否则允许基于 cache 的补救
            # 替换为干净同 key 编码。
            if not ENABLE_CACHE_FALLBACK:
                return None
            recovered = _recover_placeholder_modifier_state_cached(parsed_inst, ranges)
            if recovered is None:
                return None
            parsed_inst = recovered["parsed_inst"]
            modifier_values = recovered["modifier_values"]
            ranges = recovered["ranges"]
            asm = recovered["asm"]
            reanalysis_inst = recovered["reanalysis_inst"]
    except Exception:
        pass

    try:
        if (
            remediation_depth == 0
            and reanalysis_inst is not None
            and bytes(reanalysis_inst) != bytes(inst)
        ):
            return instruction_analysis_pipeline(
                reanalysis_inst,
                disassembler,
                arch_code,
                force_exhaustive,
                exhaustive_max,
                expected_family_head,
                allow_expensive_cache_recovery,
                enable_operand_interactions,
                lightweight_diagnose,
                analysis_key=analysis_key,
                remediation_depth=1,
            )
    except Exception:
        pass

    try:
        with _profile_section("instruction_analysis_pipeline.factorize_modifier_groups"):
            modifier_values, ranges = factorize_modifier_groups_from_rows(ranges, modifier_values)
        with _profile_section("instruction_analysis_pipeline.compress_modifier_constants.final"):
            modifier_values, ranges = compress_modifier_constant_bits(ranges, modifier_values)
    except Exception:
        pass

    modifier_interactions = []
    try:
        with _profile_section("instruction_analysis_pipeline.collect_modifier_interactions"):
            modifier_interactions = _collect_modifier_interactions(
                disassembler,
                parsed_inst,
                ranges,
                modifier_values,
            )
    except Exception:
        modifier_interactions = []

    # 在最终 ranges 上重新枚举 operand modifiers，保证 (op_idx, start, length) 与
    # spec.ranges 一致，否则 HTML 里按 range 查表会找不到行。
    try:
        def _operand_modifier_signature(rows):
            try:
                normalized = []
                for key, value in sorted((rows or {}).items()):
                    normalized.append((key, tuple(value)))
                return tuple(normalized)
            except Exception:
                return None

        refactored_operand_modifiers = False
        for _ in range(2):
            with _profile_section("instruction_analysis_pipeline.enumerate_operand_modifiers.refine"):
                operand_modifier_values = ranges.enumerate_operand_modifiers(disassembler)
            before_sig = (
                ranges._range_signature(),
                _operand_modifier_signature(operand_modifier_values),
            )
            with _profile_section("instruction_analysis_pipeline.factorize_operand_modifier_groups"):
                operand_modifier_values, ranges = factorize_operand_modifier_groups_from_rows(
                    ranges, operand_modifier_values
                )
            after_sig = (
                ranges._range_signature(),
                _operand_modifier_signature(operand_modifier_values),
            )
            if after_sig == before_sig:
                break
            refactored_operand_modifiers = True
        if refactored_operand_modifiers:
            with _profile_section("instruction_analysis_pipeline.enumerate_operand_modifiers.final"):
                operand_modifier_values = ranges.enumerate_operand_modifiers(disassembler)
    except Exception:
        pass

    try:
        verified = _verified_disasm_line_for_inst(
            disassembler,
            ranges.inst,
            expected_key=parsed_inst.get_key() if hasattr(parsed_inst, "get_key") else None,
            expected_family_head=expected_family_head or getattr(parsed_inst, "base_name", None),
        )
    except Exception:
        verified = None
    if verified is not None:
        asm, parsed_inst = verified
    asm2 = sanitize_disasm(asm)

    with _profile_section("instruction_analysis_pipeline.build_spec"):
        spec = InstructionSpec(
            asm2,
            parsed_inst,
            ranges,
            modifier_values,
            operand_modifier_values,
            modifier_interactions=modifier_interactions,
            force_modifier_bits=getattr(mutation_set, "modifier_bits", None),
        )
        try:
            unify_spec_modifiers(spec)
        except Exception:
            pass
        try:
            _backfill_modifier_tables_from_ranges(spec, disassembler)
        except Exception:
            pass
    # 用选中名称标注 modifier ranges，形成最终 spec
    try:
        mod_ranges = spec.ranges._find(EncodingRangeType.MODIFIER)
        if mod_ranges:
            for idx, mr in enumerate(mod_ranges):
                try:
                    if getattr(spec, 'modifiers', None) and idx < len(spec.modifiers):
                        grp = spec.modifiers[idx]
                        if grp and len(grp) > 0:
                            # 优先使用该 modifier range 实际编码值对应的名称；
                            # 若该名称为空则保持为空，以便 UI 展示隐式默认值。
                            try:
                                val = get_bit_range(spec.ranges.inst, mr.start, mr.start + mr.length)
                            except Exception:
                                val = None
                            chosen = None
                            matched_encoded = False
                            if val is not None:
                                for v, n in grp:
                                    if v == val:
                                        chosen = n
                                        matched_encoded = True
                                        break
                            if not matched_encoded:
                                # 回退：首个非占位符名称
                                for v, n in grp:
                                    if isinstance(n, str) and not is_placeholder_modifier(n) and n.strip() != "":
                                        chosen = n
                                        break
                            if isinstance(chosen, str):
                                mr.name = chosen.rstrip('.')
                            else:
                                # 显式空/默认项——保持 name 未设置或为空
                                mr.name = ""
                except Exception:
                    continue
    except Exception:
        pass
    try:
        op_ranges = spec.ranges._find(EncodingRangeType.OPERAND_MODIFIER)
        if op_ranges:
            flat_ops = spec.parsed.get_flat_operands()
            for rng in op_ranges:
                try:
                    val = get_bit_range(spec.ranges.inst, rng.start, rng.start + rng.length)
                except Exception:
                    val = 0
                op_idx = getattr(rng, 'operand_index', None)
                rows = _get_operand_modifier_rows(operand_modifier_values, op_idx, rng)
                chosen = _chosen_display_from_rows(rows, val)
                if chosen is not None and op_idx is not None and op_idx < len(flat_ops):
                    op = flat_ops[op_idx]
                    try:
                        existing = filter_non_placeholder_modifiers(getattr(op, 'modifiers', []) or [])
                        existing.append(chosen)
                        op.modifiers = existing
                    except Exception:
                        pass
                    try:
                        rng.name = chosen
                    except Exception:
                        pass
    except Exception:
        pass
    if enable_operand_interactions:
        try:
            spec.analyse_operand_interactions(arch_code, disassembler.nvdisasm)
        except Exception:
            pass
    if not skip_attach_half_pair:
        try:
            with _profile_section("instruction_analysis_pipeline.attach_half_pair_overlay"):
                attach_half_pair_overlay_operand_modifiers(spec, disassembler)
        except Exception:
            pass
    _sync_spec_parsed_modifiers(
        spec,
        original_parser_modifiers=original_parser_modifiers,
    )
    # Final consistency: only drop variants when opcode/modifier 本身仍含占位符。
    # 对仅出现在操作数字段里的占位片段（如 ???255）保留，避免误丢有效 family。
    try:
        with _profile_section("instruction_analysis_pipeline.final_placeholder_guard"):
            try:
                final_out = disassembler.disassemble(spec.ranges.inst)
            except Exception:
                final_out = None
            if not final_out:
                return None
            text_has_placeholder = (
                ("???" in final_out)
                or (".." in final_out)
                or re.search(r'(?<!\w)INVALID(?!\w)', final_out, flags=re.IGNORECASE)
            )
            if text_has_placeholder:
                lines = [line for line in final_out.splitlines() if line.strip()]
                asm_line = lines[-1] if lines else final_out
                try:
                    parsed_final = InstructionParser.parseInstruction(asm_line)
                except Exception:
                    return None
                bad_opcode_placeholder = False
                try:
                    base_name = getattr(parsed_final, "base_name", "")
                    if isinstance(base_name, str):
                        for part in base_name.split("."):
                            if is_placeholder_modifier(part):
                                bad_opcode_placeholder = True
                                break
                except Exception:
                    bad_opcode_placeholder = True
                if not bad_opcode_placeholder:
                    try:
                        for modifier in getattr(parsed_final, "modifiers", []) or []:
                            if is_placeholder_modifier(modifier):
                                bad_opcode_placeholder = True
                                break
                    except Exception:
                        bad_opcode_placeholder = True
                if bad_opcode_placeholder:
                    return None
    except Exception:
        return None
    return spec


class ISASpec:
    def __init__(self, instructions):
        """初始化对象状态并建立后续流程所需字段。
        
        伪代码:
            1. 执行赋值与状态更新。
        数据结构:
            - 输入: instructions。
            - 局部: 以临时表达式为主。
            - 输出: 主要通过就地更新外部容器/对象状态。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        self.instructions = instructions

    @classmethod
    def from_json_obj(cls, obj):
        """从 JSON 对象（dict）恢复实例。
        
        伪代码:
            1. 返回本函数最终结果。
        数据结构:
            - 输入: obj。
            - 局部: 以临时表达式为主。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 推导式。
        """
        return cls(
            {key: InstructionSpec.from_json_obj(value) for key, value in obj.items()}
        )

    @classmethod
    def from_json(cls, json_str):
        """从 JSON 字符串解析并恢复实例。
        
        伪代码:
            1. 返回本函数最终结果。
        数据结构:
            - 输入: json_str。
            - 局部: 以临时表达式为主。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        return ISASpec.from_json_obj(json.loads(json_str))

    @classmethod
    def from_file(cls, filename):
        """从文件加载 JSON 并构造实例。
        
        伪代码:
            1. 在上下文管理器中执行核心逻辑。
        数据结构:
            - 输入: filename。
            - 局部: 以临时表达式为主。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 条件分支与循环控制。
        """
        with open(filename) as file:
            return ISASpec.from_json(file.read())

    def find_instruction(self, target_key, modifiers=[]):
        """在 instructions 中找 parsed_key==target_key 且 modifier 匹配度最高的 spec。
        
        伪代码:
            1. 初始化或更新 modifiers。
            2. 初始化或更新 score。
            3. 初始化或更新 best。
            4. 遍历输入集合并在循环内执行条件判断与累积。
            5. 返回本函数最终结果。
        数据结构:
            - 输入: target_key, modifiers。
            - 局部: modifiers, score, best, signature_key, _modifiers。
            - 输出: 通过 return 返回计算结果。
        复杂语法:
            - 使用 Counter 计数。
        """
        modifiers = Counter(modifiers)

        score = -1
        best = None
        for key, inst in self.instructions.items():
            signature_key = inst.parsed.get_key()
            if signature_key != target_key:
                continue

            _modifiers = Counter(modifiers)
            match = True

            for modi in inst.opcode_modis:
                _modifiers[modi] -= 1
                if _modifiers[modi] < 0:
                    match = False
                    break
            if not match:
                continue

            new_score = sum(modifiers.values()) - sum(_modifiers.values())
            if new_score > score:
                best = inst
                score = new_score
        return best


def main():
    arguments = build_arg_parser().parse_args()
    InstructionSolverDriver(arguments, InstructionSolverCoreApi()).run()


if __name__ == "__main__":
    main()
