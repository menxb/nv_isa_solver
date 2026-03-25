#!/usr/bin/env python3
"""验证 solver 输出（HTML/isa/pipeline）的编码正确性。

从 HTML/isa 中提取 inst 十六进制；
用 nvdisasm --binary SM100a <hex> 反汇编；
对比反汇编结果与 distilled 文本是否一致。

用法:
  # 从 HTML 提取 inst 与 distilled，用 nvdisasm 验证（推荐）
  python tools/verify_family_disasm.py --html output/F2FP.html

  # 从 isa.json 验证（需先运行 solver 生成完整 isa.json）
  python tools/verify_family_disasm.py --isa isa.json --key F2FP

  # 运行 pipeline 获取 specs 后验证（较慢）
  python tools/verify_family_disasm.py --pipeline --key F2FP

  # HTML 无 data-inst-hex 时，用 isa 或 pipeline 作为 inst 来源
  python tools/verify_family_disasm.py --html output/F2FP.html --isa isa.json --key F2FP

注意：--html 模式需 solver 生成的 HTML 含 data-inst-hex（每条 spec 一个）。若 HTML 较旧，请先重新生成：
  python -m nv_isa_solver.instruction_solver --arch SM100a --cache_file disasm_cache_sm100a.merged.txt --filter F2FP
"""
import argparse
import json
import os
import re
import subprocess
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)


def _normalize_asm(s: str) -> str:
    """规范化反汇编文本便于对比：去多余空白、统一分号后空格。"""
    if not s:
        return ""
    s = " ".join(s.split())
    return s.strip().rstrip(";")


def run_nvdisasm(inst_hex: str, arch: str = "SM100a", nvdisasm: str = "nvdisasm") -> str:
    """对 inst 十六进制运行 nvdisasm，返回最后一行反汇编。"""
    import tempfile
    try:
        inst_bytes = bytes.fromhex(inst_hex.replace(" ", ""))
    except ValueError:
        return ""
    with tempfile.NamedTemporaryFile(delete=False, suffix=".bin") as f:
        f.write(inst_bytes)
        path = f.name
    try:
        result = subprocess.run(
            [nvdisasm, path, "--binary", arch],
            capture_output=True,
            text=True,
            timeout=5,
        )
        out = result.stdout or ""
        # 取最后非空行（实际指令行），去掉 /* ... */ 注释
        lines = [l for l in out.splitlines() if l.strip()]
        if lines:
            last = lines[-1]
            if "*/" in last:
                last = last[last.rfind("*/") + 2 :].strip()
            return last.strip()
        return ""
    finally:
        try:
            os.unlink(path)
        except Exception:
            pass


def extract_from_isa(isa_path: str, key_pattern: str) -> list[tuple[str, str, str]]:
    """从 isa.json 提取 (inst_hex, expected_disasm, canonical_name) 列表。"""
    with open(isa_path) as f:
        data = json.load(f)
    results = []
    for k, obj in data.items():
        try:
            if key_pattern not in k:
                continue
        except Exception:
            continue
        try:
            inst = obj.get("ranges", {}).get("inst")
            disasm = obj.get("disasm", "")
            canon = obj.get("canonical_name", "")
            if inst:
                results.append((inst, disasm, canon))
        except Exception:
            continue
    return results


def _base_key_from_parsed_key(parsed_key: str) -> str:
    """从 parsed_key 如 F2FP_R_FI 提取 base 如 F2FP。"""
    m = re.match(r"^([A-Z0-9]+)", parsed_key)
    return m.group(1) if m else parsed_key


def extract_from_html(html_path: str) -> tuple[list[tuple[str, str, str]], str | None]:
    """从 HTML 提取 (inst_hex, expected_distilled, family_label) 列表。

    优先从 data-inst-hex 属性获取 inst。返回 (results, base_key_for_fallback)。
    base_key_for_fallback 用于无 data-inst-hex 时从 pipeline/isa 获取 inst。
    """
    with open(html_path) as f:
        content = f.read()

    # 匹配 data-inst-hex
    inst_pattern = r'data-inst-hex="([0-9a-fA-F]+)"'
    inst_matches = re.findall(inst_pattern, content)

    # 匹配 <p> distilled: ... </p>
    distilled_pattern = r'<p>\s*distilled:\s*([^<]+)</p>'
    distilled_matches = re.findall(distilled_pattern, content)

    # 匹配 key: parsed_key（用于 label 和 fallback）
    key_pattern = r'<p>\s*key:\s*([^<]+)</p>'
    key_matches = re.findall(key_pattern, content)

    # 匹配 Family F1/F2 标题（用于 label）
    family_pattern = r'<h3>Family F(\d+):\s*([^<]*)</h3>'
    family_matches = re.findall(family_pattern, content)

    base_key = _base_key_from_parsed_key(key_matches[0]) if key_matches else None

    results = []
    for i, distilled in enumerate(distilled_matches):
        distilled = distilled.strip()
        inst_hex = inst_matches[i] if i < len(inst_matches) else ""
        if i < len(family_matches):
            fn, tokens = family_matches[i]
            label = f"F{fn}"
        elif i < len(key_matches):
            label = key_matches[i].strip()
        else:
            label = f"entry_{i}"
        results.append((inst_hex, distilled, label))
    return results, base_key


def verify_from_pipeline(key_pattern: str, arch: str = "SM100a", cache_file: str = None) -> list[tuple[str, str, str]]:
    """运行 pipeline 获取 specs，返回 (inst_hex, expected_disasm, canonical_name) 列表。"""
    from nv_isa_solver.disasm_utils import Disassembler
    from nv_isa_solver.instruction_solver import instruction_analysis_pipeline

    if cache_file is None:
        cache_file = os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt")
    if not os.path.exists(cache_file):
        print(f"Cache not found: {cache_file}")
        return []

    d = Disassembler(arch)
    d.load_cache(cache_file)
    d.find_uniques_from_cache()

    # 收集同 parsed_key 的 specs（不同 canonical = 不同 family）
    uniques = d.find_uniques_from_cache()
    by_parsed_key = {}
    for full_key, inst in list(uniques.items()):
        if key_pattern not in full_key:
            continue
        try:
            spec = instruction_analysis_pipeline(inst, d, 100)
            if spec is None:
                continue
            pk = spec.parsed.get_key()
            canon = getattr(spec, "canonical_name", "") or spec.parsed.base_name
            if pk not in by_parsed_key:
                by_parsed_key[pk] = {}
            if canon not in by_parsed_key[pk]:
                by_parsed_key[pk][canon] = spec
        except Exception as e:
            print(f" 跳过 {full_key}: {e}", file=sys.stderr)
            continue

    results = []
    for pk, canon_to_spec in by_parsed_key.items():
        for canon, spec in canon_to_spec.items():
            try:
                inst_hex = spec.ranges.inst.hex()
                disasm = spec.disasm or ""
                results.append((inst_hex, disasm, canon))
            except Exception:
                continue
    return results


def main():
    ap = argparse.ArgumentParser(description="验证 family 编码的 nvdisasm 输出与 distilled 一致")
    ap.add_argument("--isa", help="isa.json 路径")
    ap.add_argument("--html", help="HTML 路径（提取 F1/F2 inst 与 distilled，或覆盖 expected）")
    ap.add_argument("--key", help="parsed_key 或 key 模式，用于过滤（--isa/--pipeline 时）")
    ap.add_argument("--pipeline", action="store_true", help="运行 pipeline 获取 specs（较慢）")
    ap.add_argument("--arch", default="SM100a")
    ap.add_argument("--nvdisasm", default="nvdisasm")
    ap.add_argument("--cache_file", default=None)
    args = ap.parse_args()

    # 收集 (inst_hex, expected_disasm, label)
    items = []

    if args.html and os.path.exists(args.html):
        # 从 HTML 提取 F1/F2 的 inst 十六进制与 distilled
        extracted, base_key = extract_from_html(args.html)
        items = [(inst, distilled, label) for inst, distilled, label in extracted if inst]
        # 若无 data-inst-hex，尝试从 isa 或 pipeline 获取 inst，用 HTML 的 distilled 作为 expected
        if not items and extracted:
            fallback_key = args.key or base_key
            if args.isa and fallback_key:
                isa_items = extract_from_isa(args.isa, fallback_key)
                html_by_dist = {_normalize_asm(d): (d, lbl) for _, d, lbl in extracted}
                for inst_hex, disasm, canon in isa_items:
                    dn = _normalize_asm(disasm)
                    if dn in html_by_dist:
                        distilled, label = html_by_dist[dn]
                        items.append((inst_hex, distilled, label))
            if not items and base_key:
                print(f"从 pipeline 获取 inst（key={base_key}）...")
                pipeline_items = verify_from_pipeline(base_key, args.arch, args.cache_file)
                html_by_dist = {_normalize_asm(d): (d, lbl) for _, d, lbl in extracted}
                for inst_hex, disasm, canon in pipeline_items:
                    dn = _normalize_asm(disasm)
                    if dn in html_by_dist:
                        distilled, label = html_by_dist[dn]
                        items.append((inst_hex, distilled, label))
            if not items:
                print("HTML 中未找到带 data-inst-hex 的条目。")
                print("可选：1) 重新生成 HTML: python -m nv_isa_solver.instruction_solver --arch SM100a --cache_file disasm_cache_sm100a.merged.txt --filter <BASE>")
                print("      2) 使用 --isa isa.json --key <BASE> 从 isa 获取 inst")
                print("      3) 使用 --pipeline --key <BASE> 从 pipeline 获取 inst（较慢）")
                return 1
    elif args.isa and args.key:
        items = extract_from_isa(args.isa, args.key)
        if not items:
            print(f"isa.json 中未找到匹配 {args.key} 的条目")
    elif args.pipeline and args.key:
        print("运行 pipeline 获取 specs（较慢）...")
        items = verify_from_pipeline(args.key, args.arch, args.cache_file)
        if not items:
            print(f"Pipeline 未找到匹配 {args.key} 的 specs")
    else:
        print("请指定 --html，或 --isa 与 --key，或 --pipeline 与 --key")
        return 1

    if not items:
        return 1

    # 若 items 来自 isa/pipeline 且指定了 HTML，用 HTML 的 distilled 覆盖 expected
    html_expected = {}
    if (args.isa or args.pipeline) and args.html and os.path.exists(args.html):
        extracted, _ = extract_from_html(args.html)
        for inst_hex, distilled, label in extracted:
            html_expected[label] = distilled

    ok = 0
    fail = 0
    for inst_hex, expected, label in items:
        actual = run_nvdisasm(inst_hex, args.arch, args.nvdisasm)
        exp = html_expected.get(label, expected) if html_expected else expected
        exp_n = _normalize_asm(exp)
        act_n = _normalize_asm(actual)

        if exp_n == act_n:
            print(f"[OK] {label}")
            print(f"  inst: {inst_hex[:48]}..." if len(inst_hex) > 48 else f"  inst: {inst_hex}")
            ok += 1
        else:
            print(f"[FAIL] {label}")
            print(f"  inst: {inst_hex[:48]}..." if len(inst_hex) > 48 else f"  inst: {inst_hex}")
            print(f"  expected: {exp[:80]}..." if len(exp) > 80 else f"  expected: {exp}")
            print(f"  actual:   {actual[:80]}..." if len(actual) > 80 else f"  actual:   {actual}")
            fail += 1

    print(f"\n结果: {ok} 通过, {fail} 失败")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
