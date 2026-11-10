#!/usr/bin/env python3
"""FSEM-01 COVERAGE-1 referential integrity controls, NOT a semantic proof."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/phase-1/fsem01-coverage1-register.json"
DOC = ROOT / "docs/phase-1/formal-semantics-fsem01-coverage1-v1.md"
GRAMMAR = ROOT / "grammar/phase1-surface.ebnf"

FIELDS = {
    "id", "grammar", "shape", "status", "owner", "positive", "negative",
    "implementation", "rocq", "pr", "gap",
}
STATUSES = {"bounded", "gap", "handoff"}
REQUIRED = {
    "term_param", "statement", "structural_mode", "tuple_type", "tuple_expression",
    "tuple_pattern", "record_pattern", "record_decl", "data_decl", "type_alias_decl",
    "construct_expression", "postfix_expression", "borrow_expression",
    "if_expression", "join_clause", "state_slot", "match_expression",
    "decide_expression", "case_pattern", "loop_expression", "state_binding",
    "continue_expression", "break_expression", "closure_expression",
    "function_decl", "invoke_expression", "fallback", "send_expression",
    "receive_expression", "offer_expression", "architecture_decl",
    "refinement_type", "callable_contract_decl", "program_decl", "component_decl",
}
START = "<!-- COVERAGE-1-REGISTER-START -->\n"
END = "<!-- COVERAGE-1-REGISTER-END -->"


def check(data: dict, grammar: str, doc: str) -> list[str]:
    errors = []
    if data.get("schema") != "fsem01-coverage1-register-v1":
        errors.append("unknown schema")
    if data.get("grammar") != "grammar/phase1-surface.ebnf":
        errors.append("wrong canonical grammar")
    if data.get("reviewed_through_pr") != 1712:
        errors.append("wrong evidence cutoff")
    if not re.fullmatch("[0-9a-f]{40}", data.get("source_main_sha", "")):
        errors.append("unknown reviewed main SHA")
    rows = data.get("rows")
    if not isinstance(rows, list) or len(rows) < 40:
        return errors + ["insufficient or invalid rows"]

    actual = set(re.findall(r"(?m)^([a-z][a-z0-9_]*)\s*=", grammar))
    seen, present = set(), set()
    counts = {"bounded": 0, "gap": 0, "handoff": 0}
    for row in rows:
        if not isinstance(row, dict) or set(row) != FIELDS:
            errors.append("unknown/missing row fields")
            continue
        rid = row["id"]
        if not isinstance(rid, str) or not re.fullmatch(r"[A-Z]+-[0-9]{2}", rid):
            errors.append("invalid ID " + str(rid))
            continue
        if rid in seen:
            errors.append("duplicate ID " + rid)
        seen.add(rid)
        rule = row["grammar"]
        present.add(rule)
        if rule not in actual:
            errors.append(f"{rid}: unknown grammar rule {rule}")
        if row["status"] not in STATUSES:
            errors.append(f"{rid}: false or unknown status")
            continue
        counts[row["status"]] += 1
        if not isinstance(row["gap"], str) or len(row["gap"]) < 32:
            errors.append(f"{rid}: missing precise limitation")
        for field in ("positive", "negative", "implementation", "rocq"):
            path = row[field]
            if path == "-":
                continue
            if (not isinstance(path, str) or path.startswith("/")
                    or ".." in Path(path).parts or "://" in path):
                errors.append(f"{rid}: unsafe {field} path")
                continue
            if not (ROOT / path).is_file():
                errors.append(f"{rid}: nonexistent {field} path {path}")
        if row["status"] == "bounded":
            if row["owner"] != "FSEM-01":
                errors.append(f"{rid}: bounded entry must be owned by FSEM-01")
            if any(row[k] == "-" for k in
                   ("positive", "negative", "implementation", "rocq", "pr")):
                errors.append(f"{rid}: bounded entry lacks source/native/model evidence")
            if not isinstance(row["pr"], str) or not re.fullmatch(r"[0-9]+", row["pr"]):
                errors.append(f"{rid}: malformed merged PR reference")
            elif int(row["pr"]) > 1712:
                errors.append(f"{rid}: future PR falsely marked merged")
        elif row["status"] == "gap":
            if row["owner"] != "FSEM-01" or row["pr"] != "-":
                errors.append(f"{rid}: gap promotes external or unverified claim")
        elif row["status"] == "handoff":
            if row["owner"] not in (
                    "FSEM-02", "FSEM-03", "FSEM-04", "FSEM-05", "FSEM-06"):
                errors.append(f"{rid}: unknown handoff owner")
            if row["pr"] != "-":
                errors.append(f"{rid}: handoff invents local proof")
    missing = REQUIRED - present
    if missing:
        errors.append("unreviewed required grammar rules: " + ", ".join(sorted(missing)))
    if counts["bounded"] < 15 or counts["gap"] < 15 or counts["handoff"] < 5:
        errors.append("missing bounded/gap/handoff coverage strata")
    if doc.count(START) != 1 or doc.count(END) != 1:
        errors.append("missing or duplicated table markers")
    else:
        section = doc.split(START, 1)[1].split(END, 1)[0]
        observed = re.findall(r"(?m)^\| \x60([A-Z]+-[0-9]{2})\x60 \|", section)
        if observed != [r["id"] for r in rows]:
            errors.append("register/table row order drifted")
        for row in rows:
            needle = f"\x60{row['grammar']}\x60 — {row['shape']} | **{row['status']}**"
            if needle not in section:
                errors.append(row["id"] + ": table status/shape drift")
    return errors


class CoverageControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(DATA.read_text())
        cls.grammar = GRAMMAR.read_text()
        cls.doc = DOC.read_text()

    def test_register_and_evidence_paths(self):
        self.assertEqual(check(self.data, self.grammar, self.doc), [])

    def test_unknown_status_fails(self):
        d = copy.deepcopy(self.data)
        d["rows"][0]["status"] = "universally proved"
        self.assertTrue(any("false or unknown status" in e
                            for e in check(d, self.grammar, self.doc)))

    def test_grammar_anchor_fails_closed(self):
        d = copy.deepcopy(self.data)
        d["rows"][0]["grammar"] = "invented_language"
        self.assertTrue(any("unknown grammar" in e
                            for e in check(d, self.grammar, self.doc)))

    def test_bounded_negative_cannot_disappear(self):
        d = copy.deepcopy(self.data)
        d["rows"][0]["negative"] = "-"
        self.assertTrue(any("lacks source/native/model" in e
                            for e in check(d, self.grammar, self.doc)))

    def test_required_grammar_family_cannot_disappear(self):
        d = copy.deepcopy(self.data)
        d["rows"] = [r for r in d["rows"] if r["grammar"] != "fallback"]
        self.assertTrue(any("unreviewed required grammar" in e
                            for e in check(d, self.grammar, self.doc)))

    def test_no_false_handoff(self):
        d = copy.deepcopy(self.data)
        d["rows"][-1]["owner"] = "FSEM-09"
        self.assertTrue(any("unknown handoff owner" in e
                            for e in check(d, self.grammar, self.doc)))

    def test_table_status_drift_fails(self):
        doc = self.doc.replace(
            "\x60term_param\x60 — Function parameter identity and modes | **bounded**",
            "\x60term_param\x60 — Function parameter identity and modes | **complete**",
            1,
        )
        self.assertTrue(any("table status/shape drift" in e
                            for e in check(self.data, self.grammar, doc)))

    def test_missing_evidence_path_fails(self):
        d = copy.deepcopy(self.data)
        d["rows"][0]["implementation"] = "src/NonexistentFSEM01.hs"
        self.assertTrue(any("nonexistent implementation path" in e
                            for e in check(d, self.grammar, self.doc)))


if __name__ == "__main__":
    unittest.main()
