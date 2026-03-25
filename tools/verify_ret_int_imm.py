#!/usr/bin/env python3
"""
Verify RET_R_I INT_IMM encoding by bit-flip + disassembly.
Reports which bits actually change the immediate value.
"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser, IntIMMOperand

ARCH = "SM100a"
CACHE_FILE = "disasm_cache_sm100a.merged.txt"


def get_int_imm_from_parsed(parsed):
    """Extract INT_IMM value from parsed instruction (last operand for RET_R_I)."""
    try:
        flat = parsed.get_flat_operands()
        for op in flat:
            if isinstance(op, IntIMMOperand):
                return op.constant
    except Exception:
        pass
    return None


def main():
    target_key = sys.argv[1] if len(sys.argv) > 1 else "RET_R_I"
    dis = Disassembler(ARCH, nvdisasm="nvdisasm")
    cache_path = os.path.join(PROJECT_ROOT, CACHE_FILE)
    dis.load_cache(cache_path)

    # Find instruction for key
    inst_bytes = None
    base_asm = None
    for ib, asm in dis.cache.items():
        if not asm:
            continue
        lines = [l for l in asm.splitlines() if l.strip()]
        if not lines:
            continue
        try:
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() == target_key:
                inst_bytes = bytes(ib)
                base_asm = lines[-1]
                break
        except Exception:
            continue

    if inst_bytes is None:
        print(f"[ERR] No cache entry for key {target_key}")
        return 1

    base_parsed = InstructionParser.parseInstruction(base_asm)
    base_imm = get_int_imm_from_parsed(base_parsed)
    print(f"Base: {base_asm}")
    print(f"Base INT_IMM: {base_imm}")
    print(f"Base hex: {inst_bytes.hex()}")
    print()

    # Flip each bit and check if INT_IMM changes
    bits_affecting_imm = []
    for bit in range(128):
        inst_mut = bytearray(inst_bytes)
        if len(inst_mut) < 16:
            inst_mut.extend(b"\x00" * (16 - len(inst_mut)))
        byte_idx = bit // 8
        if byte_idx >= len(inst_mut):
            continue
        inst_mut[byte_idx] ^= 1 << (bit % 8)

        asm = dis.disassemble(bytes(inst_mut))
        if not asm:
            continue
        lines = [l for l in asm.splitlines() if l.strip()]
        if not lines:
            continue
        try:
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() != target_key:
                continue
            imm = get_int_imm_from_parsed(parsed)
            if imm is not None and imm != base_imm:
                bits_affecting_imm.append(bit)
        except Exception:
            continue

    print(f"Bits that change INT_IMM (total {len(bits_affecting_imm)}):")
    print(bits_affecting_imm)
    print()

    if bits_affecting_imm:
        # Check contiguity
        min_b, max_b = min(bits_affecting_imm), max(bits_affecting_imm)
        expected_contiguous = set(range(min_b, max_b + 1))
        actual = set(bits_affecting_imm)
        gaps = expected_contiguous - actual
        if gaps:
            print(f"Gaps (non-contiguous): {sorted(gaps)}")
            print(f"INT_IMM is FRAGMENTED: bits span {min_b}-{max_b} but with gaps")
        else:
            print(f"INT_IMM is CONTIGUOUS: bits {min_b}-{max_b} ({len(bits_affecting_imm)} bits)")

    # Explicit check for bits 82, 83 (the two "0" between operand 2 segments in RET_P_R_I)
    if target_key == "RET_P_R_I" and inst_bytes:
        print("\n--- Check bits 82, 83 (the two '0' between operand 2 segments) ---")
        for bit in [82, 83]:
            inst_mut = bytearray(inst_bytes)
            if len(inst_mut) < 16:
                inst_mut.extend(b"\x00" * (16 - len(inst_mut)))
            inst_mut[bit // 8] ^= 1 << (bit % 8)
            asm = dis.disassemble(bytes(inst_mut))
            lines = [l for l in asm.splitlines() if l.strip()] if asm else []
            try:
                parsed = InstructionParser.parseInstruction(lines[-1]) if lines else None
                key = parsed.get_key() if parsed else "?"
                imm = get_int_imm_from_parsed(parsed) if parsed else None
                print(f"  Bit {bit} flip: key={key} imm={imm} (base={base_imm})  asm={lines[-1][:60] if lines else '?'}...")
            except Exception as e:
                print(f"  Bit {bit} flip: error {e}")


if __name__ == "__main__":
    sys.exit(main() or 0)
