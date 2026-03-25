#!/usr/bin/env python3
"""诊断指定 key 的 modifier 枚举：检查 enumerate_modifiers 是否返回空组。

用法: python3 tools/diagnose_modifier_enum.py F2FP_R_R_FI
"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.instruction_solver import instruction_analysis_pipeline
from nv_isa_solver.instruction_solver import EncodingRangeType
from nv_isa_solver.instruction_solver import is_placeholder_modifier


def main():
    target_key = sys.argv[1] if len(sys.argv) > 1 else "F2FP_R_R_FI"
    d = Disassembler("SM100a")
    cache_file = os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt")
    if not os.path.exists(cache_file):
        print(f"Cache not found: {cache_file}")
        return 1

    d.load_cache(cache_file)
    cands = d.get_cache_candidates(target_key)
    if not cands:
        print(f"No cache candidates for {target_key}")
        return 1

    # 取第一个候选
    inst_b, asm_text = cands[0]
    inst = bytes(inst_b)
    spec = instruction_analysis_pipeline(inst, d, "SM100a", in_parallel_context=True)
    if spec is None:
        print(f"Pipeline returned None for {target_key}")
        return 1

    ranges = spec.ranges
    modifiers = spec.modifiers
    mod_ranges = ranges._find(EncodingRangeType.MODIFIER)

    print(f"=== {target_key} modifier 枚举结果 ===")
    print(f"  MODIFIER ranges: {len(mod_ranges)}")
    print(f"  modifier_values groups: {len(modifiers or [])}")
    for i, (grp, rng) in enumerate(zip(modifiers or [], mod_ranges or [])):
        names = [n for _, n in (grp or []) if n and not is_placeholder_modifier(str(n))]
        status = "OK" if names else "EMPTY"
        print(f"  mod_range {i} start={rng.start} len={rng.length}: {status} names={names[:6]}...")
    return 0


if __name__ == "__main__":
    sys.exit(main())
