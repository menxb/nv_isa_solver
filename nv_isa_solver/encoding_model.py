from __future__ import annotations

import json
import os
import sys
from collections import Counter, defaultdict
from enum import Enum
from itertools import product
from typing import List

from . import table_utils
from .disasm_utils import get_bit_range, set_bit_range
from .modifier_domain import (
    filter_non_placeholder_modifiers,
    is_diagnose_noise_token as _is_diagnose_noise_token_base,
    is_placeholder_modifier,
    split_token_parts as _split_token_parts_base,
)
from .parser import InstructionParser

MODIFIER_CARTESIAN_MAX_ENUM = 32768
MODIFIER_ENUM_MAX = int(os.environ.get("NV_ISA_SOLVER_MAX_MODIFIER_ENUM", "32768"))
OPERAND_MODIFIER_ENUM_MAX = int(
    os.environ.get("NV_ISA_SOLVER_MAX_OPERAND_MODIFIER_ENUM", "32768")
)
CACHE_AUGMENT_MAX_SAMPLES = int(
    os.environ.get("NV_ISA_SOLVER_CACHE_AUGMENT_MAX_SAMPLES", "1024")
)

operand_colors = [
    "#FE8386",
    "#F5B7DC",
    "#BF91F3",
    "#C9F3FF",
    "#FBDA73",
    "#72fc44",
    "#4e56fc",
    "#fc9b14",
    "#fc556e",
    "#256336",
]


def _split_token_parts(token: str):
    return _split_token_parts_base(token, is_placeholder_modifier_fn=is_placeholder_modifier)


def _warn_operand_modifier_enum_cap(
    ranges,
    base_key,
    modifier,
    total_values,
):
    try:
        analysis_key = getattr(ranges, "_analysis_key", None)
    except Exception:
        analysis_key = None
    try:
        inst_hex = getattr(ranges, "inst", b"").hex()
    except Exception:
        inst_hex = ""
    try:
        sys.stderr.write(
            "[nv_isa_solver] capped operand modifier enumeration: "
            f"analysis_key={analysis_key or '<unknown>'} "
            f"base_key={base_key or '<unknown>'} "
            f"operand_index={getattr(modifier, 'operand_index', None)} "
            f"start={getattr(modifier, 'start', None)} "
            f"length={getattr(modifier, 'length', None)} "
            f"values={total_values} "
            f"cap={OPERAND_MODIFIER_ENUM_MAX} "
            f"inst={inst_hex}\n"
        )
        sys.stderr.flush()
    except Exception:
        pass


def _warn_modifier_enum_cap(
    ranges,
    base_key,
    modifier,
    total_values,
):
    try:
        analysis_key = getattr(ranges, "_analysis_key", None)
    except Exception:
        analysis_key = None
    try:
        inst_hex = getattr(ranges, "inst", b"").hex()
    except Exception:
        inst_hex = ""
    try:
        sys.stderr.write(
            "[nv_isa_solver] capped modifier enumeration: "
            f"analysis_key={analysis_key or '<unknown>'} "
            f"base_key={base_key or '<unknown>'} "
            f"start={getattr(modifier, 'start', None)} "
            f"length={getattr(modifier, 'length', None)} "
            f"values={total_values} "
            f"cap={MODIFIER_ENUM_MAX} "
            f"inst={inst_hex}\n"
        )
        sys.stderr.flush()
    except Exception:
        pass


def _is_diagnose_noise_token(token: str):
    return _is_diagnose_noise_token_base(
        token,
        is_placeholder_modifier_fn=is_placeholder_modifier,
    )


class EncodingRangeType(str, Enum):
    CONSTANT = "constant"

    OPERAND = "operand"
    OPERAND_FLAG = "operand_flag"
    OPERAND_MODIFIER = "operand_modifier"

    FLAG = "flag"
    MODIFIER = "modifier"

    PREDICATE = "predicate"

    STALL_CYCLES = "stall"
    YIELD_FLAG = "y"
    READ_BARRIER = "r-bar"
    WRITE_BARRIER = "w-bar"
    BARRIER_MASK = "b-mask"
    REUSE_MASK = "reuse"


class EncodingRange:
    def __init__(
        self,
        type,
        start,
        length,
        operand_index=None,
        name=None,
        constant=None,
        group_id=None,
    ):
        self.type = type
        self.start = start
        self.length = length
        self.operand_index = operand_index
        self.group_id = group_id
        self.name = name
        self.constant = constant

    def to_json_obj(self):
        return self.__dict__

    def to_json(self):
        return json.dumps(self.__dict__)

    @classmethod
    def from_json_obj(cls, obj):
        return cls(**obj)

    def __repr__(self):
        return self.to_json()


class EncodingRanges:
    def __init__(self, ranges, inst):
        self.ranges = ranges
        self.inst = inst
        self._enumerate_modifiers_cache = {}
        self._enumerate_operand_modifiers_cache = {}

    def _range_signature(self):
        return tuple(
            (
                getattr(rng.type, "value", rng.type),
                rng.start,
                rng.length,
                rng.operand_index,
                rng.name,
                rng.constant,
                rng.group_id,
            )
            for rng in self.ranges
        )

    @staticmethod
    def _clone_modifier_rows(rows):
        return [[(val, name) for val, name in (group or [])] for group in (rows or [])]

    @staticmethod
    def _clone_operand_modifier_rows(rows_by_key):
        return {
            key: [(val, name) for val, name in (rows or [])]
            for key, rows in (rows_by_key or {}).items()
        }

    def to_json_obj(self):
        ranges = [rng.to_json_obj() for rng in self.ranges]
        return {"ranges": ranges, "inst": self.inst.hex()}

    @classmethod
    def from_json_obj(cls, obj):
        ranges = [EncodingRange.from_json_obj(r) for r in obj["ranges"]]
        return cls(ranges, bytes.fromhex(obj["inst"]))

    def operand_count(self) -> int:
        result = 0
        for rng in self.ranges:
            if rng.type == EncodingRangeType.OPERAND:
                result = max(result, rng.operand_index + 1)
        return result

    def _find(self, type) -> List[EncodingRange]:
        return list(filter(lambda x: x.type == type, self.ranges))

    def get_flags(self) -> List[str]:
        return [rng.name for rng in self._find(EncodingRangeType.FLAG)]

    def encode(
        self,
        sub_operands,
        modifiers,
        flags=None,
        operand_modifiers=None,
        operand_flags=None,
        predicate=None,
        stall_cycles=None,
        yield_flag=None,
        read_barrier=None,
        write_barrier=None,
        barrier_mask=None,
        reuse_mask=None,
    ) -> bytearray:
        result = bytearray(bytes(self.inst))
        if len(result) < 16:
            result.extend(b"\0" * (16 - len(result)))
        modifier_i = 0

        if flags is not None:
            try:
                flags = set(flags)
            except Exception:
                flags = set()
        if operand_modifiers is None:
            operand_modifiers = {}
        operand_flags_provided = operand_flags is not None
        if operand_flags is None:
            operand_flags = {}

        range_vals = {
            EncodingRangeType.PREDICATE: predicate,
            EncodingRangeType.STALL_CYCLES: stall_cycles,
            EncodingRangeType.YIELD_FLAG: (1 if yield_flag else 0)
            if yield_flag is not None
            else None,
            EncodingRangeType.READ_BARRIER: read_barrier,
            EncodingRangeType.WRITE_BARRIER: write_barrier,
            EncodingRangeType.BARRIER_MASK: barrier_mask,
            EncodingRangeType.REUSE_MASK: reuse_mask,
        }

        for rng in self.ranges:
            value = None
            if rng.type == EncodingRangeType.CONSTANT:
                value = rng.constant
            elif rng.type == EncodingRangeType.OPERAND:
                value = sub_operands[rng.operand_index]
            elif rng.type == EncodingRangeType.MODIFIER:
                if modifier_i < len(modifiers):
                    value = modifiers[modifier_i]
                    modifier_i += 1
            elif rng.type == EncodingRangeType.FLAG:
                if flags is not None:
                    value = 1 if rng.name in flags else 0
            elif rng.type == EncodingRangeType.OPERAND_MODIFIER:
                range_key = (rng.operand_index, rng.start, rng.length)
                if range_key in operand_modifiers:
                    value = operand_modifiers[range_key]
                elif rng.operand_index in operand_modifiers:
                    value = operand_modifiers[rng.operand_index]
            elif rng.type == EncodingRangeType.OPERAND_FLAG and operand_flags_provided:
                allowed = (
                    operand_flags.get(rng.operand_index, set())
                    if isinstance(operand_flags, dict)
                    else set()
                )
                value = 1 if rng.name in allowed else 0
            elif rng.type in range_vals:
                value = range_vals[rng.type]

            if value is None:
                continue
            set_bit_range(result, rng.start, rng.start + rng.length, value)
        return result

    def enumerate_modifiers(self, disassembler, initial_values=None, use_parallel=True):
        cache_key = (
            id(disassembler),
            self.inst,
            self._range_signature(),
            tuple(initial_values) if initial_values is not None else None,
        )
        cached = self._enumerate_modifiers_cache.get(cache_key)
        if cached is not None:
            return self._clone_modifier_rows(cached)

        modifiers = self._find(EncodingRangeType.MODIFIER)
        operand_values = [0] * self.operand_count()
        try:
            for rng in self._find(EncodingRangeType.OPERAND):
                idx = getattr(rng, "operand_index", None)
                if idx is None or idx < 0 or idx >= len(operand_values):
                    continue
                operand_values[idx] = get_bit_range(
                    self.inst, rng.start, rng.start + rng.length
                )
        except Exception:
            pass

        base_line = ""
        base_parse_ok = False
        try:
            base_asm = disassembler.disassemble(self.inst)
            base_lines = [l for l in base_asm.splitlines() if l.strip()]
            base_line = base_lines[-1] if base_lines else base_asm
            base_parsed = InstructionParser.parseInstruction(base_line)
            base_mods = getattr(base_parsed, "modifiers", []) or []
            try:
                base_key = base_parsed.get_key()
            except Exception:
                base_key = None
            base_parse_ok = True
        except Exception:
            base_mods = []
            base_key = None

        if initial_values:
            base_values = list(initial_values)
        else:
            base_values = [
                get_bit_range(self.inst, rng.start, rng.start + rng.length)
                for rng in modifiers
            ]

        use_segment_isolation = len(modifiers) >= 2

        analysis_result = []
        for modi_i, rng in enumerate(modifiers):
            total_values = 2 ** rng.length
            if total_values > MODIFIER_ENUM_MAX:
                _warn_modifier_enum_cap(
                    self,
                    base_key,
                    rng,
                    total_values,
                )
                current = []
                try:
                    base_val = get_bit_range(self.inst, rng.start, rng.start + rng.length)
                except Exception:
                    base_val = 0
                try:
                    cache_mapping = defaultdict(list)
                    if base_key is not None:
                        samples = 0
                        for inst_bytes, asm_text in disassembler.get_cache_candidates(
                            base_key
                        ):
                            samples += 1
                            if samples > CACHE_AUGMENT_MAX_SAMPLES:
                                break
                            try:
                                lines = [
                                    l for l in (asm_text or "").splitlines() if l.strip()
                                ]
                                asm_line = lines[-1] if lines else (asm_text or "")
                                parsed = InstructionParser.parseInstruction(asm_line)
                                if parsed.get_key() != base_key:
                                    continue
                                val = get_bit_range(
                                    inst_bytes,
                                    rng.start,
                                    rng.start + rng.length,
                                )
                                diff = find_modifier_difference(
                                    base_mods, getattr(parsed, "modifiers", []) or []
                                )
                            except Exception:
                                continue
                            cache_mapping[val].append(
                                diff[:-1] if isinstance(diff, str) and diff.endswith(".") else (diff or "")
                            )
                    seen_values = sorted(cache_mapping.keys())
                    if base_val not in seen_values:
                        seen_values = [base_val] + seen_values
                    for val in seen_values:
                        names = [name for name in cache_mapping.get(val, []) if name]
                        chosen = Counter(names).most_common(1)[0][0] if names else ""
                        current.append((val, chosen))
                except Exception:
                    current = [(base_val, "")]
                analysis_result.append(current if current else [(base_val, "")])
                continue
            parsed_per_value = []
            value_inst_bytes = []
            parsed_asm_lines = []
            disasm_indexes = {}
            probe_base = list(base_values)
            base_value = probe_base[modi_i]
            for val in range(total_values):
                vals = list(probe_base)
                vals[modi_i] = val
                try:
                    inst_bytes = self.encode(operand_values, vals)
                except Exception:
                    value_inst_bytes.append(None)
                    continue
                value_inst_bytes.append(inst_bytes)
                if (
                    base_parse_ok
                    and val == base_value
                    and bytes(inst_bytes) == bytes(self.inst)
                ):
                    continue
                disasm_indexes[val] = len(disasm_indexes)

            try:
                insts = [
                    value_inst_bytes[val]
                    for val in range(total_values)
                    if val in disasm_indexes and value_inst_bytes[val] is not None
                ]
                asms = disassembler.disassemble_parallel(
                    insts, force_sequential=not use_parallel
                )
            except Exception:
                asms = []

            ptr = 0
            for idx in range(len(value_inst_bytes)):
                inst_bytes = value_inst_bytes[idx]
                if inst_bytes is None:
                    parsed_per_value.append([])
                    parsed_asm_lines.append("")
                    continue
                if (
                    base_parse_ok
                    and idx == base_value
                    and bytes(inst_bytes) == bytes(self.inst)
                ):
                    parsed_per_value.append(
                        [
                            m
                            for m in (base_mods or [])
                            if not is_placeholder_modifier(m)
                        ]
                    )
                    parsed_asm_lines.append(base_line)
                    continue

                asm = asms[ptr] if ptr < len(asms) else ""
                ptr += 1
                lines = [l for l in (asm or "").splitlines() if l.strip()]
                if not lines:
                    parsed_per_value.append([])
                    parsed_asm_lines.append("")
                    continue
                try:
                    parsed = InstructionParser.parseInstruction(lines[-1])
                    if base_key is not None and parsed.get_key() != base_key:
                        mods = []
                    else:
                        mods = [
                            m
                            for m in (getattr(parsed, "modifiers", []) or [])
                            if not is_placeholder_modifier(m)
                        ]
                    parsed_per_value.append(mods)
                    parsed_asm_lines.append(lines[-1])
                except Exception:
                    parsed_per_value.append([])
                    parsed_asm_lines.append("")

            range_group = []
            for idx, mods in enumerate(parsed_per_value):
                others = set()
                for j, om in enumerate(parsed_per_value):
                    if j == idx:
                        continue
                    others.update(om or [])
                valid_mods = filter_non_placeholder_modifiers(mods)
                unique = [m for m in valid_mods if m not in others]
                chosen = ""
                if len(unique) == 1:
                    chosen = unique[0]
                else:
                    try:
                        base_diff = ""
                        try:
                            line = (
                                parsed_asm_lines[idx]
                                if idx < len(parsed_asm_lines)
                                else ""
                            )
                            if line:
                                parsed = InstructionParser.parseInstruction(line)
                                ref_mods = base_mods
                                if use_segment_isolation and parsed_per_value:
                                    ref_mods = parsed_per_value[0] or []
                                base_diff = find_modifier_difference(
                                    ref_mods, parsed.modifiers
                                )
                        except Exception:
                            base_diff = ""
                        if base_diff:
                            chosen = (
                                base_diff[:-1]
                                if base_diff.endswith(".")
                                else base_diff
                            )
                    except Exception:
                        chosen = ""
                if not chosen and valid_mods and not use_segment_isolation:
                    non_base = [m for m in valid_mods if m not in base_mods]
                    if len(non_base) > 0:
                        chosen = non_base[0]
                    else:
                        chosen = ""

                if chosen:
                    range_group.append((idx, chosen))
                else:
                    range_group.append((idx, ""))
            analysis_result.append(range_group)

        unresolved_positions = [
            (group_idx, val)
            for group_idx, group in enumerate(analysis_result)
            for val, name in (group or [])
            if not (isinstance(name, str) and name.strip())
        ]

        if len(modifiers) >= 2 and unresolved_positions:
            try:
                domains = [range(2 ** rng.length) for rng in modifiers]
                total_combos = 1
                for domain in domains:
                    total_combos *= len(domain)

                if total_combos <= MODIFIER_CARTESIAN_MAX_ENUM:
                    all_combos = list(product(*domains))
                    combo_insts = []
                    for combo in all_combos:
                        try:
                            combo_insts.append(self.encode(operand_values, list(combo)))
                        except Exception:
                            combo_insts.append(None)

                    disasm_inputs = [x for x in combo_insts if x is not None]
                    disasm_outputs = (
                        disassembler.disassemble_parallel(
                            disasm_inputs, force_sequential=not use_parallel
                        )
                        if disasm_inputs
                        else []
                    )
                    disasm_iter = iter(disasm_outputs)

                    combo_mods = []
                    for combo, inst_bytes in zip(all_combos, combo_insts):
                        if inst_bytes is None:
                            continue
                        asm = next(disasm_iter, "")
                        lines = [l for l in (asm or "").splitlines() if l.strip()]
                        if not lines:
                            continue
                        try:
                            parsed = InstructionParser.parseInstruction(lines[-1])
                        except Exception:
                            continue
                        try:
                            if base_key is not None and parsed.get_key() != base_key:
                                continue
                        except Exception:
                            continue
                        mods = [
                            m
                            for m in (getattr(parsed, "modifiers", []) or [])
                            if isinstance(m, str) and not is_placeholder_modifier(m)
                        ]
                        combo_mods.append((combo, mods))

                    inferred = {}
                    for range_idx, rng in enumerate(modifiers):
                        for value in range(2 ** rng.length):
                            support = Counter()
                            other = Counter()
                            support_combo_count = 0
                            for combo, mods in combo_mods:
                                tokens = [
                                    m.rstrip(".")
                                    for m in mods
                                    if isinstance(m, str) and m
                                ]
                                if combo[range_idx] == value:
                                    support_combo_count += 1
                                    for tok in tokens:
                                        support[tok] += 1
                                else:
                                    for tok in tokens:
                                        other[tok] += 1
                            candidates = [
                                tok
                                for tok, cnt in support.items()
                                if (
                                    cnt > 0
                                    and other.get(tok, 0) == 0
                                    and support_combo_count > 0
                                    and cnt == support_combo_count
                                )
                            ]
                            if candidates:
                                max_cnt = max(support[t] for t in candidates)
                                chosen_tokens = sorted(
                                    [t for t in candidates if support[t] == max_cnt]
                                )
                                inferred[(range_idx, value)] = ".".join(chosen_tokens)

                    if inferred:
                        for i, group in enumerate(analysis_result):
                            patched = []
                            for val, name in group:
                                if isinstance(name, str) and name.strip():
                                    patched.append((val, name))
                                    continue
                                inferred_name = inferred.get((i, val), "")
                                patched.append((val, inferred_name))
                            analysis_result[i] = patched
            except Exception:
                pass
        self._enumerate_modifiers_cache[cache_key] = self._clone_modifier_rows(
            analysis_result
        )
        return analysis_result

    def enumerate_operand_modifiers(self, disassembler):
        cache_key = (id(disassembler), self.inst, self._range_signature())
        cached = self._enumerate_operand_modifiers_cache.get(cache_key)
        if cached is not None:
            return self._clone_operand_modifier_rows(cached)

        operand_modifiers = self._find(EncodingRangeType.OPERAND_MODIFIER)
        modifiers = self._find(EncodingRangeType.MODIFIER)
        result = {}
        modi_values = [
            get_bit_range(self.inst, rng.start, rng.start + rng.length)
            for rng in modifiers
        ]
        operand_modifier_base_values = {
            (rng.operand_index, rng.start, rng.length): get_bit_range(
                self.inst, rng.start, rng.start + rng.length
            )
            for rng in operand_modifiers
        }
        operand_values = [0] * self.operand_count()
        try:
            for rng in self._find(EncodingRangeType.OPERAND):
                idx = getattr(rng, "operand_index", None)
                if idx is None or idx < 0 or idx >= len(operand_values):
                    continue
                operand_values[idx] = get_bit_range(
                    self.inst, rng.start, rng.start + rng.length
                )
        except Exception:
            pass

        instruction_flag_tokens = set()
        operand_flag_tokens_by_operand = defaultdict(set)
        try:
            for fr in self._find(EncodingRangeType.FLAG):
                try:
                    if (
                        fr.name
                        and isinstance(fr.name, str)
                        and not is_placeholder_modifier(fr.name)
                    ):
                        instruction_flag_tokens.add(fr.name.rstrip("."))
                except Exception:
                    continue
            for fr in self._find(EncodingRangeType.OPERAND_FLAG):
                try:
                    if (
                        fr.name
                        and isinstance(fr.name, str)
                        and not is_placeholder_modifier(fr.name)
                    ):
                        operand_flag_tokens_by_operand[
                            getattr(fr, "operand_index", None)
                        ].add(fr.name.rstrip("."))
                except Exception:
                    continue
        except Exception:
            instruction_flag_tokens = set()
            operand_flag_tokens_by_operand = defaultdict(set)

        def _strip_flag_tokens(raw: str, strip_tokens) -> str:
            try:
                if not raw or not isinstance(raw, str):
                    return ""
                stripped = raw.rstrip(".")
                parts = [p for p in stripped.split(".") if p]
                parts = [p for p in parts if p not in strip_tokens]
                if not parts:
                    return ""
                return ".".join(parts)
            except Exception:
                return raw

        try:
            base_asm = disassembler.disassemble(self.inst)
            base_lines = [l for l in (base_asm or "").splitlines() if l.strip()]
            base_line = base_lines[-1] if base_lines else (base_asm or "")
            base_key = InstructionParser.parseInstruction(base_line).get_key()
        except Exception:
            base_key = None

        for modifier in operand_modifiers:
            insts = []
            same_operand_ranges = [
                rng
                for rng in operand_modifiers
                if rng.operand_index == modifier.operand_index
            ]
            multi_range_same_operand = len(same_operand_ranges) >= 2
            same_operand_has_flags = bool(
                operand_flag_tokens_by_operand.get(modifier.operand_index, set())
            )
            total_values = 2 ** modifier.length
            if total_values > OPERAND_MODIFIER_ENUM_MAX:
                _warn_operand_modifier_enum_cap(
                    self,
                    base_key,
                    modifier,
                    total_values,
                )
                range_key = (modifier.operand_index, modifier.start, modifier.length)
                current = []
                try:
                    base_val = get_bit_range(
                        self.inst, modifier.start, modifier.start + modifier.length
                    )
                except Exception:
                    base_val = 0
                try:
                    cache_mapping = defaultdict(list)
                    if base_key is not None:
                        samples = 0
                        for inst_bytes, asm_text in disassembler.get_cache_candidates(
                            base_key
                        ):
                            samples += 1
                            if samples > CACHE_AUGMENT_MAX_SAMPLES:
                                break
                            try:
                                lines = [
                                    l for l in (asm_text or "").splitlines() if l.strip()
                                ]
                                asm_line = lines[-1] if lines else (asm_text or "")
                                parsed = InstructionParser.parseInstruction(asm_line)
                                op = parsed.get_flat_operands()[modifier.operand_index]
                            except Exception:
                                continue
                            try:
                                val = get_bit_range(
                                    inst_bytes,
                                    modifier.start,
                                    modifier.start + modifier.length,
                                )
                            except Exception:
                                continue
                            tokens = []
                            try:
                                for raw in (getattr(op, "modifiers", []) or []):
                                    for token in _split_token_parts(raw):
                                        if token.lower() == "reuse":
                                            continue
                                        tokens.append(token)
                            except Exception:
                                tokens = []
                            full = ".".join(
                                [
                                    tok.rstrip(".")
                                    for tok in tokens
                                    if isinstance(tok, str) and tok
                                ]
                            )
                            cache_mapping[val].append(full)
                    seen_values = sorted(cache_mapping.keys())
                    if base_val not in seen_values:
                        seen_values = [base_val] + seen_values
                    for val in seen_values:
                        names = [name for name in cache_mapping.get(val, []) if name]
                        chosen = Counter(names).most_common(1)[0][0] if names else ""
                        current.append((val, chosen))
                except Exception:
                    current = [(base_val, "")]
                if current:
                    result[range_key] = current
                continue
            for modi_i in range(total_values):
                operand_modis = {}
                for rng in operand_modifiers:
                    key = (rng.operand_index, rng.start, rng.length)
                    base_val = operand_modifier_base_values.get(key, 0)
                    operand_modis[key] = base_val
                if multi_range_same_operand:
                    for rng in same_operand_ranges:
                        key = (rng.operand_index, rng.start, rng.length)
                        operand_modis[key] = 0
                operand_modis[
                    (modifier.operand_index, modifier.start, modifier.length)
                ] = modi_i
                insts.append(
                    self.encode(
                        operand_values, modi_values, operand_modifiers=operand_modis
                    )
                )
            disasms = disassembler.disassemble_parallel(insts)

            current = []
            raw_tokens_per_value = []
            for asm in disasms:
                try:
                    parsed = InstructionParser.parseInstruction(asm)
                    flat_ops = parsed.get_flat_operands()
                    if modifier.operand_index >= len(flat_ops):
                        raw_tokens_per_value.append([])
                        continue
                    tokens = []
                    for raw in (
                        getattr(flat_ops[modifier.operand_index], "modifiers", []) or []
                    ):
                        for token in _split_token_parts(raw):
                            if token.lower() == "reuse":
                                continue
                            tokens.append(token)
                    raw_tokens_per_value.append(tokens)
                except Exception:
                    raw_tokens_per_value.append([])

            same_operand_flag_tokens = set(
                operand_flag_tokens_by_operand.get(modifier.operand_index, set())
            )
            common_tokens = None
            for tokens in raw_tokens_per_value:
                token_set = set(tokens or [])
                if common_tokens is None:
                    common_tokens = token_set
                else:
                    common_tokens &= token_set
            common_tokens = common_tokens or set()
            locally_controlled_tokens = set()
            for tokens in raw_tokens_per_value:
                locally_controlled_tokens.update(tokens or [])
            locally_controlled_tokens -= common_tokens
            strip_tokens = (
                set(instruction_flag_tokens) | same_operand_flag_tokens | common_tokens
            ) - locally_controlled_tokens
            parsed_tokens_per_value = [
                [tok for tok in (tokens or []) if tok not in strip_tokens]
                for tokens in raw_tokens_per_value
            ]

            for i, tokens in enumerate(parsed_tokens_per_value):
                others = set()
                for j, other_tokens in enumerate(parsed_tokens_per_value):
                    if j == i:
                        continue
                    others.update(other_tokens or [])
                unique = [tok for tok in (tokens or []) if tok not in others]
                if unique:
                    name = ".".join(unique)
                else:
                    base_tokens = (
                        parsed_tokens_per_value[0]
                        if parsed_tokens_per_value and parsed_tokens_per_value[0]
                        else []
                    )
                    non_base = [tok for tok in (tokens or []) if tok not in base_tokens]
                    name = ".".join(non_base) if non_base else ""
                current.append((i, name))

            try:
                cache_mapping = defaultdict(list)
                if (
                    base_key is not None
                    and not multi_range_same_operand
                    and not same_operand_has_flags
                ):
                    samples = 0
                    for inst_bytes, asm_text in disassembler.get_cache_candidates(
                        base_key
                    ):
                        samples += 1
                        if samples > CACHE_AUGMENT_MAX_SAMPLES:
                            break
                        try:
                            lines = [l for l in (asm_text or "").splitlines() if l.strip()]
                            asm_line = lines[-1] if lines else (asm_text or "")
                            parsed = InstructionParser.parseInstruction(asm_line)
                        except Exception:
                            continue

                        try:
                            val = get_bit_range(
                                inst_bytes,
                                modifier.start,
                                modifier.start + modifier.length,
                            )
                        except Exception:
                            continue

                        try:
                            op = parsed.get_flat_operands()[modifier.operand_index]
                            if getattr(op, "modifiers", None):
                                full = ".".join(
                                    [
                                        m.rstrip(".")
                                        for m in op.modifiers
                                        if isinstance(m, str)
                                        and m
                                        and m.rstrip(".").strip().lower() != "reuse"
                                    ]
                                )
                            else:
                                full = ""
                        except Exception:
                            full = ""

                        if full:
                            cache_mapping[val].append(full)

                for idx, (val, name) in enumerate(current):
                    if val in cache_mapping and cache_mapping[val]:
                        most = Counter(cache_mapping[val]).most_common(1)[0][0]
                        most_clean = _strip_flag_tokens(most, strip_tokens)
                        if (
                            most_clean
                            and not is_placeholder_modifier(most_clean)
                            and (not name or len(most_clean) > len(name))
                        ):
                            current[idx] = (val, most_clean)
            except Exception:
                pass

            try:
                range_key = (modifier.operand_index, modifier.start, modifier.length)
                result[range_key] = current
            except Exception:
                pass

        self._enumerate_operand_modifiers_cache[cache_key] = (
            self._clone_operand_modifier_rows(result)
        )
        return result

    def _compute_unified_modi_numbering(self):
        order = []
        try:
            modifier_ranges = self._find(EncodingRangeType.MODIFIER)
            mod_index_map = {}
            for idx, mr in enumerate(modifier_ranges):
                mod_index_map[(mr.start, mr.length, mr.group_id)] = idx

            modi_id = 1
            operand_modifier_group_ids = {}
            for er in self.ranges:
                if er.type == EncodingRangeType.MODIFIER:
                    gidx = mod_index_map.get((er.start, er.length, er.group_id))
                    order.append(
                        {
                            "modi": modi_id,
                            "kind": "modifier",
                            "group_index": gidx,
                            "operand_index": None,
                            "range": er,
                        }
                    )
                    modi_id += 1
                elif er.type == EncodingRangeType.OPERAND_MODIFIER:
                    operand_group_key = None
                    if (
                        getattr(er, "group_id", None) is not None
                        and getattr(er, "operand_index", None) is not None
                    ):
                        operand_group_key = (
                            "operand_modifier",
                            er.operand_index,
                            er.group_id,
                        )
                    assigned_modi = operand_modifier_group_ids.get(operand_group_key)
                    if assigned_modi is None:
                        assigned_modi = modi_id
                        if operand_group_key is not None:
                            operand_modifier_group_ids[operand_group_key] = assigned_modi
                        modi_id += 1
                    order.append(
                        {
                            "modi": assigned_modi,
                            "kind": "operand_modifier",
                            "group_index": None,
                            "operand_index": er.operand_index,
                            "range": er,
                            "group_key": operand_group_key,
                        }
                    )
        except Exception:
            order = []
        self._unified_modi_order = order
        return order

    def generate_html_table(self) -> str:
        builder = table_utils.TableBuilder()
        builder.tbody_start()

        def seperator():
            builder.tr_start("smoll")
            for i in range(64):
                builder.push(str(i % 8), 1)
            builder.tr_end()

        try:
            order = self._compute_unified_modi_numbering()
            range_to_modi = {id(e["range"]): e["modi"] for e in order}
        except Exception:
            range_to_modi = {}

        seperator()
        current_length = 0
        builder.tr_start()

        def _wrap_row_if_needed():
            nonlocal current_length
            if current_length == 8 * 8:
                builder.tr_end()
                seperator()
                builder.tr_start()
                current_length = 0

        for erange in self.ranges:
            _wrap_row_if_needed()

            bg_color = None
            if erange.operand_index is not None:
                bg_color = operand_colors[erange.operand_index]
            if erange.type in (
                EncodingRangeType.MODIFIER,
                EncodingRangeType.OPERAND_MODIFIER,
            ):
                if getattr(erange, "hide_modi_label", False):
                    text = erange.name
                else:
                    modi_id = range_to_modi.get(id(erange))
                    if modi_id is not None:
                        if getattr(erange, "name", None) == "__OVL__":
                            text = f"modi {modi_id} (ovl)"
                        else:
                            text = f"modi {modi_id}"
                    else:
                        text = erange.name
            else:
                text = erange.name

            vertical = erange.type in (
                EncodingRangeType.FLAG,
                EncodingRangeType.OPERAND_FLAG,
            )
            push_bg = bg_color
            push_vertical = vertical

            if not text:
                if getattr(erange, "hide_modi_label", False):
                    text = ""
                else:
                    text = erange.type

            if (
                isinstance(text, str)
                and "flag" in text.lower()
                and erange.type
                in (EncodingRangeType.FLAG, EncodingRangeType.OPERAND_FLAG)
            ):
                try:
                    bits = []
                    for bit in range(erange.start, erange.start + erange.length):
                        try:
                            byte = self.inst[bit // 8]
                            bval = (byte >> (bit % 8)) & 1
                        except Exception:
                            bval = 0
                        bits.append(str(bval))
                    for c in bits:
                        _wrap_row_if_needed()
                        builder.push(c, 1, bg=push_bg, vertical=False)
                        current_length += 1
                    continue
                except Exception:
                    pass

            if erange.type == EncodingRangeType.CONSTANT:
                bits = bin(erange.constant)[2:].zfill(erange.length)[::-1]
                for c in bits:
                    _wrap_row_if_needed()
                    builder.push(c, 1, bg=push_bg, vertical=push_vertical)
                    current_length += 1
                continue
            elif erange.type == EncodingRangeType.OPERAND:
                text += f" {erange.operand_index}"

            length = erange.length
            while length > 0:
                _wrap_row_if_needed()
                remain = 8 * 8 - current_length
                push_len = min(length, remain)
                builder.push(text, push_len, bg=push_bg, vertical=push_vertical)
                current_length += push_len
                length -= push_len
        builder.tr_end()
        builder.tbody_end()
        builder.end()
        return builder.result


def find_modifier_difference(original: List[str], mutated: List[str]):
    original = Counter(original)
    mutated = Counter(mutated)

    difference = Counter(mutated)
    difference.subtract(original)
    result = ""
    for name, count in difference.items():
        if len(name) == 0 or count <= 0:
            continue
        result += ".".join([name] * count) + "."

    return result


def analyse_modifiers(original: List[str], mutated: List[str]):
    original = Counter(original)
    mutated = Counter(mutated)

    difference = Counter(mutated)
    difference.subtract(original)

    raw_nonzero = [(name, count) for name, count in difference.items() if count != 0]
    if not raw_nonzero:
        return (False, None)

    nonzero = [
        (name, count)
        for name, count in raw_nonzero
        if not (isinstance(name, str) and is_placeholder_modifier(name))
    ]
    if not nonzero:
        return (True, None)

    if len(nonzero) == 1:
        name, count = nonzero[0]
        if abs(count) == 1 and not _is_diagnose_noise_token(name):
            return (True, name)

    return (True, None)


def generate_modifier_table(title: str, modifiers, rng: "EncodingRange", selected_value=None):
    del selected_value

    def _clean_name(name):
        if name and isinstance(name, str):
            normalized = name.rstrip(".").strip()
            if normalized in ("-", ""):
                return None
            if normalized and not is_placeholder_modifier(normalized):
                return normalized
        return None

    if not modifiers:
        return ""

    valid_rows = []
    for value, name in modifiers:
        clean_name = _clean_name(name)
        if clean_name is not None:
            valid_rows.append((value, clean_name))

    if len(valid_rows) == 0:
        return ""

    def _strip_common_tokens_for_instruction_modi(rows):
        if not isinstance(title, str) or not title.startswith("modi "):
            return rows
        if len(rows) <= 1:
            return rows
        token_rows = []
        for _, name in rows:
            token_rows.append([part for part in str(name).split(".") if part])
        if not token_rows or any(len(parts) == 0 for parts in token_rows):
            return rows
        prefix = []
        for parts in zip(*token_rows):
            head = parts[0]
            if any(part != head for part in parts[1:]):
                break
            prefix.append(head)
        if not prefix:
            return rows

        stripped = []
        changed = False
        non_empty = 0
        for (value, _name), parts in zip(rows, token_rows):
            remain = parts[len(prefix):]
            if remain != parts:
                changed = True
            if remain:
                non_empty += 1
            stripped.append((value, ".".join(remain)))
        if (not changed) or non_empty == 0:
            return rows
        return [(value, name) for value, name in stripped if name]

    try:
        valid_rows = _strip_common_tokens_for_instruction_modi(valid_rows)
    except Exception:
        pass

    if len(valid_rows) == 0:
        return ""

    html_result = "<p>" + title
    builder = table_utils.TableBuilder()
    builder.tbody_start()

    if rng is None:
        try:
            max_bits = 1
            for row in valid_rows:
                max_bits = max(max_bits, len(bin(int(row[0]))[2:]))
        except Exception:
            max_bits = 1
    else:
        max_bits = rng.length

    try:
        if max_bits is not None and max_bits > 0:
            capacity = 1 << max_bits
            if len(valid_rows) > capacity:
                seen_codes = set()
                deduped = []
                mask = (1 << max_bits) - 1
                for value, name in valid_rows:
                    try:
                        masked_value = int(value) & mask
                        code = format(masked_value, f"0{max_bits}b")
                    except Exception:
                        code = str(value)
                    if code in seen_codes:
                        continue
                    seen_codes.add(code)
                    deduped.append((value, name))
                valid_rows = deduped
    except Exception:
        pass

    for value, name in valid_rows:
        builder.tr_start()
        try:
            encoded_value = int(value)
            if max_bits > 0:
                mask = (1 << max_bits) - 1
                encoded_value &= mask
            bit_str = bin(encoded_value)[2:].zfill(max_bits)
            builder.push(bit_str, bg=None, vertical=False)
        except Exception:
            builder.push(str(value), bg=None, vertical=False)
        builder.push(str(name), bg=None, vertical=False)
        builder.tr_end()
    builder.tbody_end()
    builder.end()

    html_result += builder.result + "</p>"
    return html_result


__all__ = [
    "EncodingRange",
    "EncodingRanges",
    "EncodingRangeType",
    "analyse_modifiers",
    "find_modifier_difference",
    "generate_modifier_table",
    "operand_colors",
]
