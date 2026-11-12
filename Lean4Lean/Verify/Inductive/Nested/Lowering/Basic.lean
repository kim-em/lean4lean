import Lean4Lean.Verify.Inductive.Lowering

/-! # The lowering verification

The interface of the lowering run is `NestedLoweringOutput` and its boundary theorem
`loweringRun.WF` (`Verify/Inductive/Lowering.lean`); this directory proves it: the refinement
of `ElimNestedInductive.run` (`NestedLowering`, `LowerNextStep`), the cache
(`NestedAuxMapModels`), the auxiliary family specifications and the restoration inverse
(`ConstructorRestorationInverse.restoredType_eqv_source`), the zero-auxiliary identity
(`types_eq_source_of_aux2nested_size_eq_zero`). The semantic content (the specialization of
the auxiliary families, the typing of the nested occurrences) belongs to the restoration side:
the restoration translates the syntactic cache facts of `NestedLoweringOutput` (`nested_app`,
`aux_cached`) through the validation pass `validateNestedAuxiliaries`
(`Nested/Restoration/Validation/Passes.lean`).

This file collects the consequences of `NestedLoweringOutput` the nested pipeline reads
directly. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {env : Environment} {fuel nparams : Nat} {sourceTypes : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

theorem NestedLoweringOutput.types_ne_nil
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) : res.types ≠ [] := by
  intro hnil
  have hlen := H.types_length
  rw [hnil] at hlen
  exact H.source_nonempty (List.eq_nil_of_length_eq_zero (by simp at hlen; omega))

theorem NestedLoweringOutput.types_size_pos
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) :
    0 < res.types.toArray.size := by
  cases h : res.types with
  | nil => exact (H.types_ne_nil h).elim
  | cons _ _ => simp

end VerifyInductive
end Lean4Lean
