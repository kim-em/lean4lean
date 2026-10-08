import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-! Regression for the metadata-erasure witness from the branch review.
The old constant translation still accepts a corrupted parameter count, but
no choice of signature in the shared compilation/realization result does. -/

namespace Lean4Lean.Tests.RecursorMetadata
open Lean hiding Environment

theorem corrupted_parameter_count_rejected
    (safety : DefinitionSafety) (source target : VEnv)
    (decl : VInductDecl) (block : VInductBlock)
    (rec : RecursorVal) (value : VConstVal)
    (h : TrConstVal safety target (.recInfo rec) value) :
    let corrupted := { rec with numParams := decl.nparams + 1 }
    TrConstVal safety target (.recInfo corrupted) value ∧
      ¬ InductiveSignature.CompilationRealization source decl block target
        [(.recInfo corrupted, value)] := by
  refine ⟨h, ?_⟩
  intro realized
  have hcount := realized.parameterCount (List.mem_singleton_self _)
  change decl.nparams + 1 = decl.nparams at hcount
  omega

end Lean4Lean.Tests.RecursorMetadata
