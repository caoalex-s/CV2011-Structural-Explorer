"""Require both smoke-theorem reports under the existing real-field axiom policy.

The allowlist matches scripts/audit_real_axioms.py and the portal pilot audit.
This isolated gate also rejects unknown, repeated or malformed reports.
Run with an axiom log and optional --output receipt; no Lean execution occurs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPECTED_THEOREMS = frozenset({"WasmSmoke.accepts_sound", "WasmSmoke.accepts_complete"})
REPORT = re.compile(
    r"'([A-Za-z0-9_.]+)' "
    r"(does not depend on any axioms|depends on axioms:\s*\[[^\[\]]*\])"
)
WHITESPACE = re.compile(r"\s*")
AXIOM_LIST = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")
AXIOM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")


def complete_reports(log):
    """Read whole reports, permitting Lean's line breaks inside axiom lists.

    Every non-whitespace character must belong to a recognized report. Never
    skip malformed text or join fragments by discarding unrecognized lines.
    """
    position = 0
    while position < len(log):
        position = WHITESPACE.match(log, position).end()
        if position == len(log):
            break
        match = REPORT.match(log, position)
        if match is None or (match.end() < len(log) and not log[match.end()].isspace()):
            raise ValueError("Unrecognized or incomplete axiom report: " + log[position:position + 200])
        yield match.groups()
        position = match.end()


def audit_reports(log):
    """Return theorem-to-axiom lists, or reject any incomplete/unapproved log."""
    reports = {}
    for name, detail in complete_reports(log):
        line = f"'{name}' {detail}"
        if name not in EXPECTED_THEOREMS:
            raise ValueError("Unexpected theorem report: " + name)
        if name in reports:
            raise ValueError("Repeated theorem report: " + name)
        if detail == "does not depend on any axioms":
            axioms = []
        else:
            listed = AXIOM_LIST.fullmatch(detail)
            if listed is None:
                raise ValueError("Malformed axiom list: " + line)
            axioms = [item.strip() for item in listed.group(1).split(",")]
            if not all(AXIOM_NAME.fullmatch(item) for item in axioms):
                raise ValueError("Malformed axiom name: " + line)
            if len(set(axioms)) != len(axioms):
                raise ValueError("Repeated axiom name: " + line)
            forbidden = set(axioms) - ALLOWED_AXIOMS
            if forbidden:
                raise ValueError("Unapproved axioms: " + ", ".join(sorted(forbidden)))
        reports[name] = sorted(axioms)
    missing = EXPECTED_THEOREMS - reports.keys()
    if missing:
        raise ValueError("Missing theorem reports: " + ", ".join(sorted(missing)))
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    log_bytes = arguments.log.read_bytes()
    try:
        reports = audit_reports(log_bytes.decode("utf-8"))
    except ValueError as error:
        raise SystemExit(str(error)) from error
    receipt = {"passed": True, "reports": reports,
               "allowed_axioms": sorted(ALLOWED_AXIOMS),
               "expected_theorems": sorted(EXPECTED_THEOREMS),
               "log_sha256": hashlib.sha256(log_bytes).hexdigest()}
    if arguments.output:
        arguments.output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("Audited exactly both WasmSmoke theorems against the standard axiom allowlist.")


if __name__ == "__main__":
    main()
