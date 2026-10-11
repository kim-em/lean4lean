#!/usr/bin/env python3
"""Audit the dependency closure of the verified theorems, including opaque bodies and types.

The roots are listed below. Every axiom a root reaches must
be listed in scripts/inductive-audit-inventory.json; the strict roots (generator definitions,
foundational lemmas, and the confluence theorem with its coverage lemmas) may use only the
standard axioms. Every `sorry` a root reaches must come from a declaration listed there as an
accepted open proof (`openProofs`). With --require-complete the inventory must also be exact:
every accepted open proof must still be reached by some root, so that closing a proof forces
its removal from the list.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MARKER = "INDUCTIVE_AUDIT "
ROOTS = {
    "Lean4Lean.addDecl.WF",
    "Lean4Lean.addQuot.WF",
    "Lean4Lean.inductiveDeclPreserves",
    "Lean4Lean.VerifyInductive.addInductiveDeclaration.preserves",
    "Lean4Lean.VerifyInductive.Environment.addInductive.inductiveExtensionWF",
    "Lean4Lean.VerifyInductive.Environment.addInductive.primitiveInductiveExtensionWF",
    "Lean4Lean.VerifyInductive.nestedInductivePreserves",
    "Lean4Lean.TypeChecker.whnf.WF",
    "Lean4Lean.TypeChecker.Inner.reduceRecursor.WF",
    "Lean4Lean.VerifyInductive.RecursorConstruction.typeTranslations",
    "Lean4Lean.addDecl.preludeEq_hasCanonicalEq",
    "Lean4Lean.VEnv.NormalEq.parRed",
    "Lean4Lean.VEnv.PrefixUnfold.defeq",
    "Lean4Lean.VEnv.QuotPrefixUnfold.defeq",
    "Lean4Lean.VEnv.QuotRegistered.propInhabitant_app",
    "Lean4Lean.VEnv.IsDefEq.full_church_rosser",
    "Lean4Lean.Replay.replayFresh.WF",
    "Lean4Lean.Replay.replayFresh.WF_target",
    "Lean4Lean.Replay.replayPure.WF_fromImports",
    "Lean4Lean.Replay.Replayed.foldlM",
}
DEFINITION_ROOTS = {
    "Lean4Lean.QuotPrefixUnfolding.propInhabitant",
    "Lean4Lean.QuotPrefixUnfolding.generate",
    "Lean4Lean.VEnv.QuotRegistered",
    "Lean4Lean.VEnv.QuotPrefixUnfold",
    "Lean4Lean.VEnv.DefinitionRegistered",
    "Lean4Lean.VEnv.DefinitionPattern",
    "Lean4Lean.InductiveSignature.RecursorData.compilationEntries",
    "Lean.Level.paramsIn",
    "Lean.Expr.levelParamsIn",
    "Lean4Lean.InductiveSignature.TrRestoredCompilation",
    "Lean4Lean.InductiveSignature.Restoration.expr",
    "Lean4Lean.CompiledInductive",
    "Lean4Lean.InductiveSignature.Instance.equation",
    "Lean4Lean.InductiveSignature.Compiles",
    "Lean4Lean.InductiveSignature.TrRecursorVal",
    "Lean4Lean.InductiveSignature.RecursorData.singletonEquation",
    "Lean4Lean.InductiveSignature.RecursorData.singletonUnfolding",
    "Lean4Lean.VEnv.RecursorRegistered",
    "Lean4Lean.VEnv.RecursorEntry",
    "Lean4Lean.VEnv.recursorRegistry",
    "Lean4Lean.VEnv.definitionRegistry",
    "Lean4Lean.VEnv.ConcretePattern",
    "Lean4Lean.VEnv.GuardedIotaPattern",
    "Lean4Lean.VEnv.PatternReductionTrace",
    "Lean4Lean.VEnv.HeadParallelReduction",
    "Lean4Lean.VEnv.PrefixUnfold",
    "Lean4Lean.VEnv.FullStep",
    "Lean4Lean.VEnv.FullReduction",
    "Lean4Lean.VEnv.FullEquationCoverage",
    "Lean4Lean.VEnv.FullPatCoverage",
    "Lean4Lean.VEnv.HasCanonicalEq",
}
# Foundational lemmas, and the confluence theorem for every well-formed environment with
# canonical `Eq` with its parameters and coverage lemmas.
FOUNDATION_ROOTS = {
    "Lean4Lean.VEnv.IsDefEq.strong",
    "Lean4Lean.VEnv.IsDefEqStrong.subst",
    "Lean4Lean.VEnv.IsDefEq.transport_bvar",
    "Lean4Lean.VEnv.ConstructorCaptureReplay.transport",
    "Lean4Lean.VEnv.HasType.etaOpen_wf",
    "Lean4Lean.VEnv.HasType.etaOpen_defeq",
    "Lean4Lean.VEnv.IsDefEq.etaOpen_wrapLams",
    "Lean4Lean.VEnv.WF.params",
    "Lean4Lean.VEnv.WF.church_rosser",
    "Lean4Lean.VEnv.WF.equationCoverage",
    "Lean4Lean.VEnv.WF.patCoverage",
    "Lean4Lean.VEnv.WF.singletonPatCoverageJ",
    "Lean4Lean.VEnv.WF.patCoverageJ",
}
STRICT_ROOTS = DEFINITION_ROOTS | FOUNDATION_ROOTS
ROOTS |= STRICT_ROOTS
BUILD_TARGETS = [
    "Lean4Lean.Verify.Inductive.Dispatch",
    "Lean4Lean.Verify.Inductive.Nested.Install.Dispatch",
    "Lean4Lean.Verify.Environment",
    "Lean4Lean.Verify.TypeChecker",
    "Lean4Lean.Verify.CanonicalEq",
    "Lean4Lean.Theory.Typing.Confluence.WFParams",
    "Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift",
    "Lean4Lean.Theory.Typing.QuotPropInhabitant",
    "Lean4Lean.Theory.Typing.RecursorRegistryInstallation",
    "Lean4Lean.Theory.Typing.ConstructorCaptureTransport",
    "Lean4Lean.Verify.Replay",
]


def run_audit(path):
    proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                          text=True, capture_output=True)
    if proc.returncode:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise RuntimeError("Lean dependency audit failed")
    reports = [json.loads(line[len(MARKER):]) for line in proc.stdout.splitlines()
               if line.startswith(MARKER)]
    if not reports:
        raise RuntimeError("Lean dependency audit produced no reports")
    return reports


def self_test():
    source = (ROOT / "scripts/InductiveAudit.lean").read_text()
    source = "import Lean\n" + "\n".join(
        line for line in source.splitlines() if not line.startswith("import "))
    source = source.split("\n#inductive_audit ", 1)[0]
    source += """
namespace AuditSelfTest
axiom typeDependency : Prop
axiom assumed : typeDependency
theorem throughType : typeDependency := assumed
opaque hidden : True := by sorry
theorem throughOpaque : True := hidden
theorem clean : True := True.intro
end AuditSelfTest
#inductive_audit AuditSelfTest.throughType
#inductive_audit AuditSelfTest.throughOpaque
#inductive_audit AuditSelfTest.clean
"""
    with tempfile.TemporaryDirectory(prefix="inductive-audit-") as directory:
        path = Path(directory) / "AuditSelfTest.lean"
        path.write_text(source)
        reports = {r["root"]: r for r in run_audit(path)}
    opaque = reports["AuditSelfTest.throughOpaque"]
    assert any(d["name"] == "AuditSelfTest.hidden" and
               d["path"] == ["AuditSelfTest.throughOpaque", "AuditSelfTest.hidden"]
               for d in opaque["sorrySources"]), "missed an opaque sorry body"
    typed = reports["AuditSelfTest.throughType"]
    assert {d["name"] for d in typed["axioms"]} == {
        "AuditSelfTest.typeDependency", "AuditSelfTest.assumed"}, "missed a type dependency"
    clean = reports["AuditSelfTest.clean"]
    assert not clean["axioms"] and not clean["sorrySources"], "false positive on a clean proof"
    print("Audit self-test passed: opaque bodies, types, paths, and clean proofs.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true",
                        help="also reject accepted open proofs that no root reaches any more")
    parser.add_argument("--no-build", action="store_true", help="use already-built dependencies")
    parser.add_argument("--json", type=Path, help="write full dependency paths to this file")
    parser.add_argument("--self-test", action="store_true", help="test the auditor and exit")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.no_build:
        subprocess.run(["lake", "build", *BUILD_TARGETS], cwd=ROOT, check=True)
    reports = run_audit(ROOT / "scripts/InductiveAudit.lean")
    if len(reports) != len(ROOTS) or {r["root"] for r in reports} != ROOTS:
        raise RuntimeError("audit roots changed or a theorem report is missing")
    if args.json:
        args.json.write_text(json.dumps(reports, indent=2) + "\n")
    inventory = json.loads((ROOT / "scripts/inductive-audit-inventory.json").read_text())
    standard = set(inventory["standardAxioms"])
    allowed = standard | set(inventory["implementationAxioms"])
    accepted = set(inventory["openProofs"])
    failed = False
    reached = set()
    for report in reports:
        sorries = {d["name"] for d in report["sorrySources"]}
        reached |= sorries
        axioms = {d["name"] for d in report["axioms"]}
        print(f'{report["root"]}: {len(sorries)} open proofs, {len(axioms - {"sorryAx"})} axioms besides sorryAx')
        permitted = standard if report["root"] in STRICT_ROOTS else allowed
        for dependency in report["axioms"]:
            name = dependency["name"]
            if name != "sorryAx" and name not in permitted:
                failed = True
                print("  UNLISTED AXIOM: " + " -> ".join(dependency["path"]))
        for dependency in report["sorrySources"]:
            if dependency["name"] not in accepted:
                failed = True
                print("  OPEN PROOF NOT ACCEPTED: " + " -> ".join(dependency["path"]))
        if "sorryAx" in axioms and not sorries:
            failed = True
            print("  sorryAx reached without a recorded source")
    if args.require_complete:
        for name in sorted(accepted - reached):
            failed = True
            print("ACCEPTED OPEN PROOF NO LONGER REACHED (remove it from the inventory): " + name)
    if failed:
        print("Inductive dependency audit FAILED.", file=sys.stderr)
        return 1
    if reached:
        print(f"Inventory matches; {len(reached)} accepted open proofs remain: "
              + ", ".join(sorted(reached)))
    else:
        print("No sorry dependencies; all remaining axioms are listed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError, AssertionError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
