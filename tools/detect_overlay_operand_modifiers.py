#!/usr/bin/env python3
"""通用 overlay 检测：用「结构 + 8 次 probe」扫描 cache/分析结果，列出所有 (key, operand_index, overlay_token)。

不依赖 H0_NH1 等名称。对每条唯一指令跑一次 pipeline（skip_attach_half_pair=True），
再对 spec 做结构检测 + 8 次编码 probe，满足条件的记录 (key, operand_index, overlay_token)。
"""

import argparse
import json
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler  # noqa: E402
from nv_isa_solver.instruction_solver import (  # noqa: E402
    instruction_analysis_pipeline,
    detect_overlay_operand_modifiers_generic,
)


def main():
    p = argparse.ArgumentParser(
        description="Scan cache with structure+8-probe, list (key, operand_index, overlay_token)."
    )
    p.add_argument("--cache_file", default="disasm_cache.txt", help="Disasm cache file")
    p.add_argument("--arch", default="sm_100", help="Architecture (e.g. sm_100)")
    p.add_argument("--arch_code", type=int, default=None, help="Arch code (default inferred or 90)")
    p.add_argument("--output", "-o", default=None, help="Output JSON path (default: stdout)")
    p.add_argument("--limit", type=int, default=None, help="Max keys to process (for testing)")
    args = p.parse_args()

    cache_path = args.cache_file
    if not os.path.isfile(cache_path):
        cache_path = os.path.join(PROJECT_ROOT, cache_path)
    if not os.path.isfile(cache_path):
        print(f"[ERROR] Cache not found: {args.cache_file}", file=sys.stderr)
        return 1

    arch_code = args.arch_code
    if arch_code is None:
        import re
        m = re.search(r"(\d+)", str(args.arch))
        arch_code = int(m.group(1)) if m else 90

    disassembler = Disassembler(args.arch)
    disassembler.load_cache(cache_path)
    all_uniques = disassembler.find_uniques_from_cache()
    keys = list(all_uniques.items())
    if args.limit is not None:
        keys = keys[: args.limit]

    results = []
    for i, (key, inst) in enumerate(keys):
        if (i + 1) % 500 == 0 or i == 0:
            print(f"[scan] {i + 1}/{len(keys)} {key}", file=sys.stderr)
        try:
            spec = instruction_analysis_pipeline(
                inst,
                disassembler,
                arch_code,
                force_exhaustive=False,
                exhaustive_max=32768,
                expected_family_head=None,
                allow_expensive_cache_recovery=False,
                enable_operand_interactions=False,
                skip_distill=False,
                skip_attach_half_pair=True,
            )
        except Exception as e:
            print(f"[warn] pipeline failed for {key}: {e}", file=sys.stderr)
            continue
        if spec is None:
            continue
        try:
            hits = detect_overlay_operand_modifiers_generic(spec, disassembler)
        except Exception as e:
            print(f"[warn] detector failed for {key}: {e}", file=sys.stderr)
            continue
        for h in hits:
            results.append(h)

    # 输出至少包含 (key, operand_index, overlay_token)，可选 main_start, flag_start
    out = [
        {
            "key": r["key"],
            "operand_index": r["operand_index"],
            "overlay_token": r["overlay_token"],
            "main_start": r.get("main_start"),
            "flag_start": r.get("flag_start"),
        }
        for r in results
    ]
    json_str = json.dumps(out, indent=2, ensure_ascii=False)

    if args.output:
        os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(json_str)
        print(f"[OK] Wrote {len(out)} entries to {args.output}", file=sys.stderr)
    else:
        print(json_str)

    print(f"[SUMMARY] keys_scanned={len(keys)} hits={len(results)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
