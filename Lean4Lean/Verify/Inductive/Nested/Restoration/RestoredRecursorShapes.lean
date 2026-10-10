import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Environment.Blocks

/-! # The telescopes of the restored recursors

`RecursorShapesAt` of every restored kernel recursor in the recursor stage of a restored block
base, read by `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) for
`RestoredBlock.recShapes`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- **Stub (restB).** The recursor and constructor telescopes of every restored kernel recursor
in the recursor stage of the base (`RecursorShapesAt`, with its rules). The rule-free part is
`RestoredRecursorShape.alignmentCore`; the rule part is the `VConstructorShape` of each rule's
restored constructor (`restoredRuleConstructors`) at the recursor's major inductive. -/
theorem NestedRun.restoredRecursorShapes
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered) :
    ∀ rv ∈ E.restoration.rvals, RecursorShapesAt outEnv.constants C.recursorVEnv rv := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := wf; have := Hsources; have := hC; sorry


end VerifyInductive
end Lean4Lean
