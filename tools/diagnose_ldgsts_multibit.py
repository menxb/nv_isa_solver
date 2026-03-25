#!/usr/bin/env python3
"""通过 cache 分析 LDGSTS 缺失 token 是否需多 bit 组合才能触发。

策略：仅用 cache 中已有编码，比较 base 与各候选的 bit 差异，推断每个 token 对应的位。
无需调用 nvdisasm，速度快。
"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser


def diff_bits(a: bytes, b: bytes) -> set:
    """返回 a、b 不同的位索引集合。"""
    out = set()
    for i in range(min(len(a), len(b)) * 8):
        if ((a[i // 8] ^ b[i // 8]) >> (i % 8)) & 1:
            out.add(i)
    return out


def main():
    d = Disassembler("SM100a")
    cache_file = os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt")
    if not os.path.exists(cache_file):
        print(f"Cache not found: {cache_file}")
        return 1
    d.load_cache(cache_file)
    d.find_uniques_from_cache()

    target_tokens = {"CONSTANT", "CTA", "EL", "EU", "GPU", "LTC256B", "LU", "MMIO", "NA", "PRIVATE", "SM"}
    target_key = "LDGSTS_RI_R_P"

    # 找 base 编码（EF，无 addrspace）
    base_inst = None
    base_asm = None
    for inst_b, asm_text in d.get_cache_candidates(target_key) or []:
        lines = [l for l in asm_text.splitlines() if l.strip()]
        if not lines:
            continue
        asm = lines[-1]
        try:
            p = InstructionParser.parseInstruction(asm)
            mods = set(getattr(p, "modifiers", []) or [])
            if "EF" in mods and not (target_tokens & mods):
                base_inst = bytes(inst_b)
                base_asm = asm
                break
        except Exception:
            continue

    if not base_inst:
        print("No base EF encoding found for LDGSTS_RI_R_P")
        return 1

    print(f"Base: {base_asm[:80]}...")
    print(f"Hex: {base_inst.hex()}")
    print()

    # 遍历 cache 中所有同 key 候选，收集 token -> diff_bits
    token_to_diffs = {t: [] for t in target_tokens}
    for inst_b, asm_text in d.get_cache_candidates(target_key) or []:
        lines = [l for l in asm_text.splitlines() if l.strip()]
        if not lines:
            continue
        try:
            p = InstructionParser.parseInstruction(lines[-1])
            if p.get_key() != target_key:
                continue
            mods = set(getattr(p, "modifiers", []) or [])
            hit = target_tokens & mods
            if not hit:
                continue
            diff = diff_bits(base_inst, bytes(inst_b))
            if not diff:
                continue
            for t in hit:
                token_to_diffs[t].append(diff)
        except Exception:
            continue

    # 分析：单 bit 可区分的 vs 需多 bit 组合的
    print("=== 从 cache 推断：token 与 base 的 bit 差异 ===")
    for t in sorted(target_tokens):
        diffs = token_to_diffs[t]
        if not diffs:
            print(f"  {t}: (cache 中无此 token 的样本)")
            continue
        # 取所有 diff 的交集：若某位在所有样本中都不同，则可能是该 token 的位
        common = set.intersection(*diffs) if len(diffs) > 1 else diffs[0]
        # 取所有 diff 的并集：该 token 可能涉及的位
        union = set.union(*diffs) if diffs else set()
        single_bit_samples = [d for d in diffs if len(d) == 1]
        if single_bit_samples:
            bits = sorted(set(b for d in single_bit_samples for b in d))
            print(f"  {t}: 有单 bit 样本, bits={bits} (共 {len(single_bit_samples)} 样本)")
        else:
            min_len = min(len(d) for d in diffs)
            samples = [sorted(d) for d in diffs if len(d) == min_len][:3]
            print(f"  {t}: 需多 bit 组合, 最少 {min_len} bit, 例 diff_bits={samples}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
