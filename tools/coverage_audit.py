#!/usr/bin/env python3
"""Audit token coverage: cache-observed vs isa/html-visible tokens.

Report is grouped by parsed_key and focuses on modifier-like tokens.
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from html import unescape

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler, FAMILY_KEY_DELIM  # noqa: E402
from nv_isa_solver.instruction_solver import (  # noqa: E402
    is_placeholder_modifier,
    diagnose_missing_tokens_for_key,
    InstructionSpec,
    EncodingRangeType,
    get_bit_range,
    _visible_tokens_from_spec,
)
from nv_isa_solver.parser import InstructionParser  # noqa: E402


WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*")
TAG_RE = re.compile(r"<[^>]+>")
KEY_RE = re.compile(r"<p>\s*key:\s*([^<]+)</p>", flags=re.IGNORECASE)

STOPWORDS = {
    "modi",
    "modifiers",
    "modifier",
    "group",
    "operand",
    "operands",
    "key",
    "distilled",
    "read",
    "write",
    "read_write",
    "invalid",  # handled by placeholder filter anyway
    "smoll",
    "predicate",
    "stall",
    "reuse",
    "yield",
    # operand 类型指示符（parsed_key 中的 R/UR/FI/I 等），非 modifier token
    "fi",
    "fimm",
    "imm",
    "i",
    "r",
    "ur",
}


def extract_parsed_key(spec_key: str):
    if not isinstance(spec_key, str):
        return ""
    parsed = spec_key.split(".", 1)[1] if "." in spec_key else spec_key
    if FAMILY_KEY_DELIM in parsed:
        parsed = parsed.split(FAMILY_KEY_DELIM, 1)[0]
    return parsed.strip()


def extract_opcode_value(spec_key: str):
    if not isinstance(spec_key, str):
        return None
    head = spec_key.split(".", 1)[0].strip() if "." in spec_key else spec_key.strip()
    try:
        return int(head)
    except Exception:
        return None


def extract_family_head(spec_key: str):
    if not isinstance(spec_key, str):
        return ""
    parsed = spec_key.split(".", 1)[1] if "." in spec_key else spec_key
    if FAMILY_KEY_DELIM not in parsed:
        return ""
    return parsed.split(FAMILY_KEY_DELIM, 1)[1].strip()


def mnemonic_head_from_asm_line(asm_line: str):
    if not isinstance(asm_line, str) or not asm_line:
        return ""
    parts = asm_line.strip().split()
    if not parts:
        return ""
    head = parts[0]
    if head.startswith("@") and len(parts) >= 2:
        head = parts[1]
    return head.strip()


def _norm_single_token(token: str):
    if not token or not isinstance(token, str):
        return None
    tok = token.strip().rstrip(".;")
    if not tok:
        return None
    if is_placeholder_modifier(tok):
        return None
    if tok.lower() in STOPWORDS:
        return None
    if re.match(r"^[0-9.-]+$", tok) and re.search(r"[0-9]", tok):
        return None
    return tok


def norm_token_parts(token: str):
    out = []
    if not token or not isinstance(token, str):
        return out
    parts = [p for p in token.strip().rstrip(".;").split(".") if p]
    for part in parts:
        t = _norm_single_token(part)
        if t:
            out.append(t)
    return out


def tokens_from_base_name(base_name: str):
    out = set()
    if not isinstance(base_name, str):
        return out
    parts = [p for p in base_name.split(".") if p]
    for p in parts[1:]:
        for t in norm_token_parts(p):
            out.add(t)
    return out


def parsed_family_signature_from_obj(parsed_obj):
    """从 isa.json 的 parsed 字段提取 family 签名（与 solver 的 parsed 口径一致）。"""
    tokens = set()
    if not isinstance(parsed_obj, dict):
        return tuple()

    base_name = parsed_obj.get("base_name")
    if isinstance(base_name, str):
        parts = [p for p in base_name.split(".") if p]
        for part in parts[1:]:
            for t in norm_token_parts(part):
                tokens.add(t)

    for modifier in parsed_obj.get("modifiers", []) or []:
        for t in norm_token_parts(modifier):
            tokens.add(t)
    return tuple(sorted(tokens))


def parsed_family_signature_from_parsed(parsed):
    """从 parser 结果提取 family 签名（用于 cache 候选过滤）。"""
    tokens = set()
    try:
        base_name = getattr(parsed, "base_name", None)
        if isinstance(base_name, str):
            parts = [p for p in base_name.split(".") if p]
            for part in parts[1:]:
                for t in norm_token_parts(part):
                    tokens.add(t)
    except Exception:
        pass
    try:
        for modifier in getattr(parsed, "modifiers", []) or []:
            for t in norm_token_parts(modifier):
                tokens.add(t)
    except Exception:
        pass
    return tuple(sorted(tokens))


def extract_tokens_from_isa_obj(obj):
    toks = set()
    parsed = obj.get("parsed", {}) if isinstance(obj, dict) else {}

    try:
        spec = InstructionSpec.from_json_obj(obj)
        toks.update(_visible_tokens_from_spec(spec))
    except Exception:
        pass

    for t in tokens_from_base_name(parsed.get("base_name")):
        toks.add(t)

    for m in parsed.get("modifiers", []) or []:
        for t in norm_token_parts(m):
            toks.add(t)

    for m in obj.get("opcode_modis", []) or []:
        for t in norm_token_parts(m):
            toks.add(t)

    for group in obj.get("modifiers", []) or []:
        try:
            for _v, n in group:
                for t in norm_token_parts(n):
                    toks.add(t)
        except Exception:
            continue

    op_mods = obj.get("operand_modifiers", {}) or {}
    if isinstance(op_mods, dict):
        for rows in op_mods.values():
            try:
                for _v, n in rows:
                    for t in norm_token_parts(n):
                        toks.add(t)
            except Exception:
                continue

    ranges = ((obj.get("ranges") or {}).get("ranges")) or []
    for r in ranges:
        if not isinstance(r, dict):
            continue
        if r.get("type") not in ("flag", "operand_flag", "modifier"):
            continue
        for t in norm_token_parts(r.get("name")):
            toks.add(t)
    return toks


def token_in_parsed(parsed, token: str):
    target = token.rstrip(".;")
    if not target:
        return False
    try:
        base_name = getattr(parsed, "base_name", None)
        if isinstance(base_name, str):
            for part in base_name.split(".")[1:]:
                if part == target:
                    return True
    except Exception:
        pass
    try:
        for modifier in getattr(parsed, "modifiers", []) or []:
            if target in norm_token_parts(modifier):
                return True
    except Exception:
        pass
    try:
        for operand in parsed.get_flat_operands():
            for modifier in getattr(operand, "modifiers", []) or []:
                if target in norm_token_parts(modifier):
                    return True
    except Exception:
        pass
    return False


def verify_extra_token_with_bit_evidence(disassembler, parsed_key, token, spec_objs):
    """用 spec 编码位直接构造样本，验证 extra token 是否真实可由位控制出现。"""
    target = token.rstrip(".;")
    if not target:
        return None
    for obj in spec_objs:
        try:
            spec = InstructionSpec.from_json_obj(obj)
        except Exception:
            continue
        try:
            mod_ranges = spec.ranges._find(EncodingRangeType.MODIFIER)
        except Exception:
            mod_ranges = []
        if not mod_ranges or not getattr(spec, "modifiers", None):
            continue
        try:
            base_values = [
                get_bit_range(spec.ranges.inst, rng.start, rng.start + rng.length)
                for rng in mod_ranges
            ]
        except Exception:
            base_values = [0] * len(mod_ranges)
        for group_idx, group in enumerate(spec.modifiers):
            for value, name in group:
                if target not in norm_token_parts(name):
                    continue
                trial_values = list(base_values)
                if group_idx < len(trial_values):
                    trial_values[group_idx] = value
                ops = [0] * spec.ranges.operand_count()
                try:
                    inst = spec.ranges.encode(ops, trial_values)
                except Exception:
                    continue
                asm = disassembler.disassemble(inst)
                lines = [line for line in (asm or "").splitlines() if line.strip()]
                if not lines:
                    continue
                line = lines[-1]
                try:
                    parsed = InstructionParser.parseInstruction(line)
                except Exception:
                    continue
                if parsed.get_key() != parsed_key:
                    continue
                if token_in_parsed(parsed, target):
                    return {
                        "reason": "bit_verified_not_in_cache_scope",
                        "group_index": group_idx,
                        "group_value": value,
                        "asm": line,
                    }
    return None


def extract_html_tokens_by_key(output_dir):
    tokens_by_key = defaultdict(set)
    if not os.path.isdir(output_dir):
        return tokens_by_key

    for name in sorted(os.listdir(output_dir)):
        if not name.endswith(".html") or name == "index.html":
            continue
        path = os.path.join(output_dir, name)
        try:
            text = open(path, "r", encoding="utf-8", errors="ignore").read()
        except Exception:
            continue

        parts = text.split('<div class="instruction-desc">')
        if len(parts) <= 1:
            continue
        for block in parts[1:]:
            km = KEY_RE.search(block)
            if not km:
                continue
            parsed_key = km.group(1).strip()
            plain = unescape(TAG_RE.sub(" ", block))
            for raw in WORD_RE.findall(plain):
                for t in norm_token_parts(raw):
                    tokens_by_key[parsed_key].add(t)
    return tokens_by_key


def _parsed_has_placeholders(parsed, asm_line: str):
    try:
        if isinstance(asm_line, str):
            up = asm_line.upper()
            if "???" in asm_line or "INVALID" in up:
                return True
        for m in getattr(parsed, "modifiers", []) or []:
            if is_placeholder_modifier(m):
                return True
        for op in parsed.get_flat_operands():
            for m in getattr(op, "modifiers", []) or []:
                if is_placeholder_modifier(m):
                    return True
    except Exception:
        return True
    return False


def cache_observed_tokens(
    disassembler,
    parsed_key,
    family_signature=None,
    family_signatures=None,
    family_heads=None,
    opcode_value=None,
    *,
    skip_placeholders=False,
):
    tokens = set()
    meta = {}  # token -> {"count": int, "sources": set, "sample": str}
    total = 0
    ok = 0
    for inst_b, asm_text in disassembler.get_cache_candidates(parsed_key):
        total += 1
        if not asm_text:
            continue
        lines = [l for l in asm_text.splitlines() if l.strip()]
        if not lines:
            continue
        try:
            parsed = InstructionParser.parseInstruction(lines[-1])
        except Exception:
            continue
        if parsed.get_key() != parsed_key:
            continue
        if opcode_value is not None:
            try:
                if get_bit_range(inst_b, 0, 12) != opcode_value:
                    continue
            except Exception:
                continue
        if skip_placeholders and _parsed_has_placeholders(parsed, lines[-1]):
            continue
        parsed_sig = None
        if family_signature is not None or family_signatures:
            parsed_sig = parsed_family_signature_from_parsed(parsed)
        if family_signature is not None:
            if parsed_sig != family_signature:
                continue
        if family_signatures:
            if parsed_sig not in family_signatures:
                continue
        if family_heads:
            head = mnemonic_head_from_asm_line(lines[-1])
            if head not in family_heads:
                continue
        ok += 1

        asm_head = mnemonic_head_from_asm_line(lines[-1])
        if asm_head:
            for part in asm_head.split(".")[1:]:
                for t in norm_token_parts(part):
                    tokens.add(t)
                    e = meta.setdefault(
                        t, {"count": 0, "sources": set(), "sample": lines[-1]}
                    )
                    e["count"] += 1
                    e["sources"].add("asm.family_head")
                    if not e.get("sample"):
                        e["sample"] = lines[-1]

        for t in tokens_from_base_name(getattr(parsed, "base_name", None)):
            tokens.add(t)
            e = meta.setdefault(
                t, {"count": 0, "sources": set(), "sample": lines[-1]}
            )
            e["count"] += 1
            e["sources"].add("parsed.base_name")
            if not e.get("sample"):
                e["sample"] = lines[-1]

        for m in getattr(parsed, "modifiers", []) or []:
            for t in norm_token_parts(m):
                tokens.add(t)
                e = meta.setdefault(
                    t, {"count": 0, "sources": set(), "sample": lines[-1]}
                )
                e["count"] += 1
                e["sources"].add("parsed.modifiers")
                if not e.get("sample"):
                    e["sample"] = lines[-1]

        try:
            for op in parsed.get_flat_operands():
                if isinstance(op, parser.FloatIMMOperand):
                    continue
                for m in getattr(op, "modifiers", []) or []:
                    for t in norm_token_parts(m):
                        if isinstance(op, parser.IntIMMOperand) and t not in {"cNEG", "cABS"}:
                            continue
                        tokens.add(t)
                        e = meta.setdefault(
                            t, {"count": 0, "sources": set(), "sample": lines[-1]}
                        )
                        e["count"] += 1
                        e["sources"].add("operand.modifiers")
                        if not e.get("sample"):
                            e["sample"] = lines[-1]
        except Exception:
            pass
    return tokens, total, ok, meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--arch", default="SM100a")
    ap.add_argument("--cache_file", default="disasm_cache_sm100a.merged.txt")
    ap.add_argument("--isa_json", default="isa.json")
    ap.add_argument("--output_dir", default="output")
    ap.add_argument(
        "--report_md",
        default="docs/COVERAGE_AUDIT_REPORT.md",
        help="Markdown report path (relative to project root).",
    )
    ap.add_argument(
        "--all_cache_keys",
        action="store_true",
        help="Audit all parsed keys from cache (can be very large).",
    )
    ap.add_argument("--top", type=int, default=200, help="Max rows in markdown table.")
    ap.add_argument(
        "--sort-by",
        choices=("missing", "parsed_key"),
        default="missing",
        help="Sort order: missing=worst first, parsed_key=alphabetical.",
    )
    ap.add_argument(
        "--miss-only",
        action="store_true",
        help="Only include keys that have missing tokens.",
    )
    ap.add_argument(
        "--group-by",
        choices=("spec_key", "parsed_key"),
        default="spec_key",
        help="统计粒度：spec_key=按 family/spec；parsed_key=同 key 下所有 family 合并后统计。",
    )
    ap.add_argument(
        "--include_placeholder_observed",
        action="store_true",
        help="观测集合包含带 ???/INVALID 的反汇编样本（默认跳过）。",
    )
    ap.add_argument(
        "--analyze_miss_reasons",
        action="store_true",
        help="对 missing token 做位翻转证据诊断（调用 instruction_solver 诊断逻辑）。",
    )
    ap.add_argument("--reason_max_keys", type=int, default=12)
    ap.add_argument("--reason_max_tokens", type=int, default=8)
    ap.add_argument("--reason_pair_budget", type=int, default=96)
    ap.add_argument("--reason_max_cache_samples", type=int, default=4000)
    args = ap.parse_args()

    isa_path = (
        args.isa_json
        if os.path.isabs(args.isa_json)
        else os.path.join(PROJECT_ROOT, args.isa_json)
    )
    out_dir = (
        args.output_dir
        if os.path.isabs(args.output_dir)
        else os.path.join(PROJECT_ROOT, args.output_dir)
    )
    report_path = (
        args.report_md
        if os.path.isabs(args.report_md)
        else os.path.join(PROJECT_ROOT, args.report_md)
    )

    if not os.path.exists(isa_path):
        print(f"[ERR] isa json not found: {isa_path}")
        return 1

    with open(isa_path, "r", encoding="utf-8") as f:
        isa_data = json.load(f)

    isa_obj_by_key = {}
    isa_entries = []
    for full_key, obj in isa_data.items():
        isa_obj_by_key[full_key] = obj
        parsed_key = extract_parsed_key(full_key)
        toks = extract_tokens_from_isa_obj(obj)
        family_signature = parsed_family_signature_from_obj(
            (obj or {}).get("parsed", {}) if isinstance(obj, dict) else {}
        )
        isa_entries.append(
            {
                "spec_key": full_key,
                "opcode_value": extract_opcode_value(full_key),
                "parsed_key": parsed_key,
                "family_signature": family_signature,
                "family_head": extract_family_head(full_key),
                "visible_tokens": toks,
            }
        )

    dis = Disassembler(args.arch)
    cache_path = (
        args.cache_file
        if os.path.isabs(args.cache_file)
        else os.path.join(PROJECT_ROOT, args.cache_file)
    )
    dis.load_cache(cache_path)
    dis.find_uniques_from_cache()  # build cache_by_key

    html_tokens_by_key = extract_html_tokens_by_key(out_dir)

    rows = []
    skip_placeholders = not bool(args.include_placeholder_observed)
    if args.all_cache_keys:
        for parsed_key in sorted(dis.cache_by_key.keys()):
            observed, cand_total, cand_ok, observed_meta = cache_observed_tokens(
                dis,
                parsed_key,
                family_signature=None,
                skip_placeholders=skip_placeholders,
            )
            combined = set(html_tokens_by_key.get(parsed_key, set()))
            missing = sorted(observed - combined)
            extra = sorted(combined - observed)
            rows.append(
                {
                    "spec_key": parsed_key,
                    "parsed_key": parsed_key,
                    "observed_n": len(observed),
                    "visible_n": len(combined),
                    "visible_tokens": combined,
                    "missing": missing,
                    "extra": extra,
                    "candidates": cand_total,
                    "parsed_ok": cand_ok,
                    "observed_meta": observed_meta,
                }
            )
    else:
        if args.group_by == "parsed_key":
            grouped = defaultdict(
                lambda: {
                    "visible_tokens": set(),
                    "spec_keys": [],
                    "family_signatures": set(),
                    "family_heads": set(),
                }
            )
            for entry in isa_entries:
                pk = entry["parsed_key"]
                grouped[pk]["visible_tokens"].update(entry["visible_tokens"])
                grouped[pk]["spec_keys"].append(entry["spec_key"])
                grouped[pk]["family_signatures"].add(entry["family_signature"])
                if entry.get("family_head"):
                    grouped[pk]["family_heads"].add(entry["family_head"])
            for parsed_key in sorted(grouped.keys()):
                observed, cand_total, cand_ok, observed_meta = cache_observed_tokens(
                    dis,
                    parsed_key,
                    family_signature=None,
                    family_signatures=None,
                    family_heads=grouped[parsed_key]["family_heads"],
                    skip_placeholders=skip_placeholders,
                )
                combined = set(grouped[parsed_key]["visible_tokens"])
                missing = sorted(observed - combined)
                extra = sorted(combined - observed)
                rows.append(
                    {
                        "spec_key": ",".join(sorted(grouped[parsed_key]["spec_keys"])),
                        "parsed_key": parsed_key,
                        "observed_n": len(observed),
                        "visible_n": len(combined),
                        "visible_tokens": combined,
                        "missing": missing,
                        "extra": extra,
                        "candidates": cand_total,
                        "parsed_ok": cand_ok,
                        "observed_meta": observed_meta,
                    }
                )
        else:
            for entry in sorted(
                isa_entries, key=lambda x: (x["parsed_key"], x["spec_key"])
            ):
                parsed_key = entry["parsed_key"]
                family_signature = entry["family_signature"]
                observed, cand_total, cand_ok, observed_meta = cache_observed_tokens(
                    dis,
                    parsed_key,
                    family_signature=family_signature,
                    opcode_value=entry.get("opcode_value"),
                    skip_placeholders=skip_placeholders,
                )
                # spec_key 精确视角：保留 opcode 约束，仅在 family_signature 过严时
                # 回退到同 opcode 的 parsed_key 口径，避免混入别的 spec/opcode。
                #
                # 注意：family_signature 为空元组（无显式 family marker）时，
                # observed 可能合法地为 0（例如该 family 本身不暴露 token）。
                # 这种情况若回退到全 opcode，会把其它 family 的 token 混入，
                # 产生 RELU/F32 之类的假 missing。
                should_fallback = False
                if family_signature is not None and cand_ok == 0:
                    should_fallback = True
                elif family_signature is not None and len(observed) == 0:
                    try:
                        should_fallback = len(tuple(family_signature)) > 0
                    except Exception:
                        should_fallback = bool(family_signature)
                if should_fallback:
                    observed, cand_total, cand_ok, observed_meta = cache_observed_tokens(
                        dis,
                        parsed_key,
                        family_signature=None,
                        opcode_value=entry.get("opcode_value"),
                        skip_placeholders=skip_placeholders,
                    )
                combined = set(entry["visible_tokens"])
                missing = sorted(observed - combined)
                extra = sorted(combined - observed)
                rows.append(
                    {
                        "spec_key": entry["spec_key"],
                        "parsed_key": parsed_key,
                        "observed_n": len(observed),
                        "visible_n": len(combined),
                        "visible_tokens": combined,
                        "missing": missing,
                        "extra": extra,
                        "candidates": cand_total,
                        "parsed_ok": cand_ok,
                        "observed_meta": observed_meta,
                    }
                )

    if args.miss_only:
        rows = [r for r in rows if r["missing"]]

    if args.sort_by == "parsed_key":
        rows.sort(key=lambda r: (r["parsed_key"], r["spec_key"]))
    else:
        rows.sort(
            key=lambda r: (
                len(r["missing"]),
                r["observed_n"] - r["visible_n"],
                r["parsed_key"],
            ),
            reverse=True,
        )

    audited = len(rows)
    keys_with_missing = sum(1 for r in rows if r["missing"])
    keys_with_extra = sum(1 for r in rows if r["extra"])
    miss_reason_by_key = {}
    extra_reason_by_key = {}
    if args.analyze_miss_reasons:
        diagnosed = 0
        seen = set()
        for row in rows:
            if not row.get("missing"):
                continue
            parsed_key = row.get("parsed_key")
            if not parsed_key or parsed_key in seen:
                continue
            seen.add(parsed_key)
            if args.reason_max_keys > 0 and diagnosed >= args.reason_max_keys:
                break
            diag = diagnose_missing_tokens_for_key(
                dis,
                parsed_key,
                row.get("visible_tokens") or set(),
                max_tokens=args.reason_max_tokens,
                pair_budget=args.reason_pair_budget,
                max_cache_samples=args.reason_max_cache_samples,
            )
            miss_reason_by_key[parsed_key] = diag
            diagnosed += 1
    if args.analyze_miss_reasons:
        for row in rows:
            if not row.get("extra"):
                continue
            parsed_key = row.get("parsed_key")
            if not parsed_key:
                continue
            spec_keys = [x for x in (row.get("spec_key") or "").split(",") if x]
            spec_objs = [isa_obj_by_key[k] for k in spec_keys if k in isa_obj_by_key]
            token_reasons = {}
            for token in row.get("extra") or []:
                evidence = verify_extra_token_with_bit_evidence(
                    dis, parsed_key, token, spec_objs
                )
                if evidence:
                    token_reasons[token] = evidence
            if token_reasons:
                extra_reason_by_key[parsed_key] = token_reasons

    os.makedirs(os.path.dirname(report_path), exist_ok=True)
    with open(report_path, "w", encoding="utf-8") as f:
        f.write("# Coverage Audit Report\n\n")
        if args.group_by == "spec_key":
            f.write("cache观测 token 集合 vs isa/html 可见 token 集合（按 spec_key/opcode 精确分组）\n\n")
        else:
            f.write("cache观测 token 集合 vs isa/html 可见 token 集合（按 parsed_key 分组）\n\n")
        f.write(f"- audited_keys: {audited}\n")
        f.write(f"- keys_with_missing: {keys_with_missing}\n")
        f.write(f"- keys_with_extra: {keys_with_extra}\n")
        f.write(
            f"- mode: {'all_cache_keys' if args.all_cache_keys else 'isa_keys_only'}\n"
        )
        f.write(f"- group_by: {args.group_by}\n")
        f.write(f"- include_placeholder_observed: {bool(args.include_placeholder_observed)}\n")
        f.write(f"- sort_by: {args.sort_by}\n")
        f.write(f"- miss_only: {args.miss_only}\n\n")
        if args.analyze_miss_reasons:
            f.write(f"- analyze_miss_reasons: true ({len(miss_reason_by_key)} keys diagnosed)\n")
            f.write(f"- reason_max_tokens: {args.reason_max_tokens}\n")
            f.write(f"- reason_pair_budget: {args.reason_pair_budget}\n\n")
            f.write(f"- reason_max_cache_samples: {args.reason_max_cache_samples}\n\n")

        f.write("## Top Groups\n\n")
        f.write("| spec_key | parsed_key | observed | visible | missing_count | extra_count | cache_candidates |\n")
        f.write("|---|---|---:|---:|---:|---:|---:|\n")
        for r in rows[: args.top]:
            f.write(
                f"| `{r['spec_key']}` | `{r['parsed_key']}` | {r['observed_n']} | {r['visible_n']} | "
                f"{len(r['missing'])} | {len(r['extra'])} | {r['parsed_ok']}/{r['candidates']} |\n"
            )

        f.write("\n## Detailed Missing Tokens\n\n")
        for r in rows:
            if not r["missing"]:
                continue
            f.write(f"### `{r['spec_key']}` (`{r['parsed_key']}`)\n")
            f.write(
                f"- observed={r['observed_n']}, visible={r['visible_n']}, "
                f"cache_parsed_ok={r['parsed_ok']}/{r['candidates']}\n"
            )
            f.write(f"- missing_tokens: `{', '.join(r['missing'])}`\n")
            for tok in r["missing"]:
                info = (r.get("observed_meta") or {}).get(tok) or {}
                src = ",".join(sorted(info.get("sources") or []))
                cnt = info.get("count", 0)
                sample = info.get("sample", "")
                f.write(
                    f"  - `{tok}`: count={cnt}, source={src}, sample=`{sample[:180]}`\n"
                )
            if r["extra"]:
                f.write(f"- extra_tokens: `{', '.join(r['extra'])}`\n")
                extra_reason = extra_reason_by_key.get(r["parsed_key"], {})
                if extra_reason:
                    f.write("- extra_reasons:\n")
                    for tok in r["extra"]:
                        ev = extra_reason.get(tok)
                        if not ev:
                            continue
                        f.write(
                            f"  - `{tok}`: reason={ev.get('reason')}, group={ev.get('group_index')}, "
                            f"value={ev.get('group_value')}, asm=`{(ev.get('asm') or '')[:180]}`\n"
                        )
            diag = miss_reason_by_key.get(r["parsed_key"])
            if diag and diag.get("diagnostics"):
                by_token = {entry.get("token"): entry for entry in diag.get("diagnostics") or []}
                f.write("- miss_reasons:\n")
                for tok in r["missing"]:
                    entry = by_token.get(tok)
                    if not entry:
                        continue
                    reason = entry.get("reason", "unknown")
                    ev = entry.get("evidence") or {}
                    bits = ev.get("single_bits") or []
                    pair = ev.get("coupled_pair")
                    sample = ev.get("raw_asm", "")
                    f.write(
                        f"  - `{tok}`: reason={reason}, single_bits={bits[:4]}, "
                        f"coupled_pair={pair}, sample=`{sample[:180]}`\n"
                    )
            f.write("\n")

    print(f"[OK] Report written: {report_path}")
    print(
        f"[SUMMARY] audited={audited}, missing_keys={keys_with_missing}, extra_keys={keys_with_extra}"
    )
    if rows:
        worst = rows[0]
        print(
            "[TOP] "
            f"{worst['spec_key']} missing={len(worst['missing'])} "
            f"observed={worst['observed_n']} visible={worst['visible_n']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
