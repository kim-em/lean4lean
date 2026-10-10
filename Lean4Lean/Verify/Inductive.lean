import Lean4Lean.Verify.Inductive.Basic
import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Verify.Inductive.Header.Check
import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation
import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Lowering
import Lean4Lean.Verify.Inductive.Primitive.Shape
import Lean4Lean.Verify.Inductive.Primitive.Run
import Lean4Lean.Verify.Inductive.Primitive.Extension
import Lean4Lean.Verify.Inductive.Dispatch

/-!
# Verification of inductive declarations

Collects the verification of the executable inductive checker (`Lean4Lean/Verify/Inductive/`):
headers, constructors, checked formation, recursors and rules, block installation, primitive
families and the dispatch over the executable's branches (section 3 of the design notes). The
nested branch is the hypothesis `VerifyInductive.NestedInductivePreserves` (wave 3). The
interface between the directories and its ownership are described in `Inductive/README.md`;
the open proofs are the "Wave 2 scaffold" section of `STUBS.md`.
-/
