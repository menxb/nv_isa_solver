#!/usr/bin/env python3
"""Debug ST_desc ranges: 检查 encoding ranges 中是否有 MODIFIER/FLAG。"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.instruction_solver import (
    instruction_analysis_pipeline,
    EncodingRangeType,
)

CACHE = "disasm_cache_sm100a.merged.txt"
ARCH = "SM100a"


def main():
    d = Disassembler(ARCH, nvdisasm="nvdisasm")
    d.load_cache(CACHE)
    d.find_uniques_from_cache()

    for key in ["ST_desc[UR][RI]_R", "ST_desc[UR][R]_R"]:
        cands = d.get_cache_candidates(key)
        if not cands:
            print(f"[SKIP] {key}")
            continue

        inst = bytes(cands[0][0])
        # Check mutation_set before pipeline completes
        asm = d.disassemble(inst)
        muts = d.mutate_inst(inst, end=128)
        from nv_isa_solver.instruction_solver import (
            InstructionMutationSet,
            analysis_run_fixedpoint,
            analysis_disambiguate_flags,
            analysis_promote_known_flags,
            analysis_operand_fix,
            analysis_disambiguate_operand_flags,
            analysis_fimm_bridge_constants,
            analysis_extend_modifiers,
            analysis_modifier_splitting,
        )
        mset = InstructionMutationSet(inst, asm, muts, d)
        mset._merge_f16_rn_rz_flag_bits()
        analysis_run_fixedpoint(d, mset, analysis_disambiguate_flags)
        analysis_run_fixedpoint(d, mset, analysis_promote_known_flags)
        analysis_run_fixedpoint(d, mset, analysis_operand_fix)
        analysis_run_fixedpoint(d, mset, analysis_disambiguate_operand_flags)
        analysis_run_fixedpoint(d, mset, analysis_fimm_bridge_constants)
        analysis_run_fixedpoint(d, mset, analysis_extend_modifiers)
        analysis_run_fixedpoint(d, mset, analysis_modifier_splitting)
        ranges_pre = mset.compute_encoding_ranges()
        op_ranges_pre = ranges_pre._find(EncodingRangeType.OPERAND)
        print(f"\n=== {key} (before refinement) ===")
        print(f"  inst: {inst.hex()}")
        print(f"  modifier_bits: {sorted(mset.modifier_bits)}")
        print(f"  operand_ranges: {len(op_ranges_pre)}")
        mod_ranges_pre = ranges_pre._find(EncodingRangeType.MODIFIER)
        print(f"  MODIFIER ranges: {len(mod_ranges_pre)}")

        spec = instruction_analysis_pipeline(inst, d, 100)
        if not spec:
            print(f"[FAIL] {key}: pipeline returned None")
            continue

        print(f"\n=== {key} (final spec) ===")
        print(f"  inst: {spec.ranges.inst.hex()[:40]}...")
        for r in spec.ranges.ranges:
            rtype = r.type
            if rtype in (EncodingRangeType.MODIFIER, EncodingRangeType.OPERAND_MODIFIER,
                        EncodingRangeType.FLAG, EncodingRangeType.OPERAND_FLAG,
                        EncodingRangeType.STALL_CYCLES, EncodingRangeType.YIELD_FLAG,
                        EncodingRangeType.READ_BARRIER, EncodingRangeType.WRITE_BARRIER,
                        EncodingRangeType.BARRIER_MASK, EncodingRangeType.REUSE_MASK):
                print(f"  {rtype}: start={r.start} len={r.length} name={getattr(r,'name',None)}")


if __name__ == "__main__":
    main()
