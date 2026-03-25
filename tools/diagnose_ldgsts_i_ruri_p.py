#!/usr/bin/env python3
"""诊断 LDGSTS_I_RURI_P 为何 addrspace 未解析。追踪 mutation 流程，对 addrspace 区 (72-86) 逐 bit 记录 flip 结果。"""
import os
import sys
import re

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler, get_bit_range
from nv_isa_solver.parser import InstructionParser


def main():
    d = Disassembler("SM100a")
    cache_file = os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt")
    if not os.path.exists(cache_file):
        print(f"Cache not found: {cache_file}")
        return 1

    d.load_cache(cache_file)
    uniques = d.find_uniques_from_cache()

    target_key = "LDGSTS_I_RURI_P"
    full_key = None
    base_inst = None
    for k, inst in uniques.items():
        if target_key in k:
            full_key = k
            base_inst = inst
            break

    if base_inst is None:
        print(f"find_uniques 中未找到 {target_key}")
        # 从 cache 取第一个
        cands = d.get_cache_candidates(target_key)
        if not cands:
            print("cache 中无此 key")
            return 1
        base_inst, _ = cands[0]
        print(f"从 cache 取第一个候选")

    print(f"=== Base 编码 ===")
    base_asm = d.disassemble(base_inst)
    lines = [l for l in base_asm.splitlines() if l.strip()]
    base_line = lines[-1] if lines else base_asm
    print(f"  {base_line[:100]}")
    print(f"  hex: {base_inst.hex()}")

    # Distill
    print(f"\n=== Distill 后 ===")
    distilled = d.distill_instruction(base_inst, use_parallel=False)
    dist_asm = d.disassemble(distilled)
    dist_lines = [l for l in dist_asm.splitlines() if l.strip()]
    dist_line = dist_lines[-1] if dist_lines else dist_asm
    print(f"  {dist_line[:100]}")
    print(f"  hex: {distilled.hex()}")

    # Mutation - 只测 addrspace 区 72-86
    ADDRSPACE_BITS = list(range(72, 87))
    mutations = d.mutate_inst(distilled, start=72, end=87, use_parallel=False)
    mut_list = list(mutations)

    try:
        base_parsed = InstructionParser.parseInstruction(dist_line)
        base_key = base_parsed.get_key()
        base_mods = set(getattr(base_parsed, "modifiers", []) or [])
        base_ops = base_parsed.get_flat_operands()
    except Exception as e:
        print(f"Parse base 失败: {e}")
        return 1

    print(f"\n=== Addrspace 区 (bits 72-86) 单 bit flip 结果 ===")
    print(f"  base_key={base_key}")
    print(f"  base_modifiers={sorted(base_mods)}")
    print()

    for i_bit, inst, asm in mut_list:
        asm = asm.strip()
        reason = None
        if len(asm) == 0:
            reason = "empty_asm"
        else:
            if re.search(r"\?+\d*", asm) or re.search(r"INVALID\w*", asm, flags=re.IGNORECASE):
                reason = "INVALID_or_??? "
            try:
                mut_parsed = InstructionParser.parseInstruction(asm)
            except Exception as e:
                reason = f"parse_fail({e})"
            if reason is None:
                mut_key = mut_parsed.get_key()
                if mut_key != base_key:
                    reason = f"key_change({base_key}->{mut_key})"
                else:
                    mut_ops = mut_parsed.get_flat_operands()
                    operand_effected = False
                    for a, b in zip(mut_ops, base_ops):
                        if not a.compare(b):
                            operand_effected = True
                            break
                    if operand_effected:
                        reason = "operand_change"
                    else:
                        mut_mods = set(getattr(mut_parsed, "modifiers", []) or [])
                        if mut_mods != base_mods:
                            added = mut_mods - base_mods
                            removed = base_mods - mut_mods
                            reason = f"modifier_change +{added} -{removed} -> WOULD_ADD_TO_modifier_bits"
                        else:
                            reason = "no_change(skip)"

        bit_val = get_bit_range(distilled, i_bit, i_bit + 1)
        flip_dir = "0->1" if bit_val == 0 else "1->0"
        asm_short = asm[:60] + "..." if len(asm) > 60 else asm
        print(f"  bit{i_bit:3d} ({flip_dir}): {reason}")
        if reason and "modifier_change" in reason:
            print(f"       asm: {asm_short}")

    # 统计
    reasons = []
    for i_bit, inst, asm in mut_list:
        asm = asm.strip()
        if len(asm) == 0:
            reasons.append("empty")
        elif re.search(r"\?+\d*", asm) or re.search(r"INVALID", asm, flags=re.IGNORECASE):
            reasons.append("invalid")
        else:
            try:
                p = InstructionParser.parseInstruction(asm)
                if p.get_key() != base_key:
                    reasons.append("key_change")
                else:
                    ops = p.get_flat_operands()
                    if any(not a.compare(b) for a, b in zip(ops, base_ops)):
                        reasons.append("operand_change")
                    else:
                        m = set(getattr(p, "modifiers", []) or [])
                        if m != base_mods:
                            reasons.append("modifier_ok")
                        else:
                            reasons.append("no_change")
            except Exception:
                reasons.append("parse_fail")

    from collections import Counter
    c = Counter(reasons)
    print(f"\n=== 汇总 (bits 72-86) ===")
    for r, n in c.most_common():
        print(f"  {r}: {n}")
    if c.get("modifier_ok", 0) > 0:
        print(f"\n  结论: 有 {c['modifier_ok']} 个 bit flip 应加入 modifier_bits，但 pipeline 可能因其他原因未发现")
    else:
        print(f"\n  结论: 无任何 bit flip 产生 modifier 变化。原因分布如上。")

    return 0


if __name__ == "__main__":
    sys.exit(main())
