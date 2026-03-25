#!/usr/bin/env python3
import re
import sys
from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser

MOD_DEBUG = 'output/mod_debug.txt'
DISASM_CACHE = 'disasm_cache.txt'

def find_range_for_key(key):
    with open(MOD_DEBUG) as f:
        data = f.read()
    # locate blocks starting with SANITIZE_BEFORE key=... or FINAL KEY
    pattern = re.compile(r"SANITIZE_BEFORE key=%s[\s\S]*?range 0: start=(\d+) len=(\d+) name=(\S+)" % re.escape(key))
    m = pattern.search(data)
    if m:
        return int(m.group(1)), int(m.group(2)), m.group(3)
    # fallback: search for 'FINAL KEY: key' then nearby 'range' lines
    pattern2 = re.compile(r"FINAL KEY: %s[\s\S]{0,200}?range 0: start=(\d+) len=(\d+) name=(\S+)" % re.escape(key))
    m2 = pattern2.search(data)
    if m2:
        return int(m2.group(1)), int(m2.group(2)), m2.group(3)
    raise RuntimeError('could not find range for key %s in %s' % (key, MOD_DEBUG))

def find_inst_for_key(d, key):
    d.load_cache(DISASM_CACHE)
    for inst, asm in d.cache.items():
        try:
            parsed = InstructionParser.parseInstruction(asm)
        except Exception:
            continue
        if parsed.get_key() == key:
            return inst, asm
    raise RuntimeError('no cache entry with key %s' % key)

def main():
    if len(sys.argv) < 2:
        print('usage: bitflip_verify.py <KEY>')
        return
    key = sys.argv[1]
    arch = 'SM103a3'
    d = Disassembler(arch)
    print('finding modifier range for', key)
    start, length, name = find_range_for_key(key)
    print('range start=%d len=%d name=%s' % (start, length, name))

    print('locating cache instruction for key', key)
    inst, asm = find_inst_for_key(d, key)
    print('original asm:', asm)
    print('original bytes:', inst.hex())

    # disassemble original (may be cached)
    orig = d.disassemble(inst)

    # flip each bit in the range and disassemble
    end = start + length
    results = []
    for bit in range(start, end):
        idx = bit
        inst2 = bytearray(bytes(inst))
        needed = (idx // 8) + 1
        if len(inst2) < needed:
            inst2.extend(b'\x00' * (needed - len(inst2)))
        inst2[idx // 8] ^= (1 << (idx % 8))
        flipped = d.disassemble(bytes(inst2))
        results.append((idx, inst2.hex(), flipped))

    print('\n=== Results ===')
    print('Original disasm:')
    print(orig)
    for idx, hexb, dis in results:
        print('\nFlipped bit %d -> bytes=%s' % (idx, hexb))
        print(dis)

if __name__ == '__main__':
    main()
