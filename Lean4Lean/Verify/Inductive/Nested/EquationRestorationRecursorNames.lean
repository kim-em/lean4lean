import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedAtomic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Exact ordered change of the recursor-name guard set across nested
restoration.  Each target name is the executable `getD` image of the source
name at the same block position.  Map-domain coverage is retained separately
because it is what rules out a bare rename in ordinary guarded syntax. -/
structure RestoredRecursorNames
    (auxRec : NameMap Name) (sourceRecursors targetRecursors : List Name) :
    Prop where
  aligned : List.Forall₂
    (fun source target => target = auxRec.getD source source)
    sourceRecursors targetRecursors
  keys_covered : NestedRestorationPlan.RecursorKeysCovered
    auxRec sourceRecursors

/-- Every source recursor's executable restored name occurs in the target
guard set. -/
theorem RestoredRecursorNames.getD_mem
    (H : RestoredRecursorNames auxRec sourceRecursors targetRecursors)
    (hsource : source ∈ sourceRecursors) :
    auxRec.getD source source ∈ targetRecursors := by
  rcases Lean4Lean.List.Forall₂.forall_exists_l H.aligned source hsource with
    ⟨target, htarget, heq⟩
  simpa [heq] using htarget

/-- A mapped auxiliary recursor occurs under its exact mapped name in the
target guard set. -/
theorem RestoredRecursorNames.mapped_mem
    (H : RestoredRecursorNames auxRec sourceRecursors targetRecursors)
    (hsource : source ∈ sourceRecursors)
    (hfind : auxRec.find? source = some target) :
    target ∈ targetRecursors := by
  have hmem := H.getD_mem hsource
  have hgetD : auxRec.getD source source = target := by
    change Std.TreeMap.getD
      (show Std.TreeMap Name Name Name.quickCmp from auxRec)
        source source = target
    change (show Std.TreeMap Name Name Name.quickCmp from auxRec)[source]? =
      some target at hfind
    rw [Std.TreeMap.getD_eq_getD_getElem?, hfind]
    rfl
  simpa [hgetD] using hmem

/-- An unmapped primary recursor keeps its name and remains in the target
guard set. -/
theorem RestoredRecursorNames.unmapped_mem
    (H : RestoredRecursorNames auxRec sourceRecursors targetRecursors)
    (hsource : source ∈ sourceRecursors)
    (hfind : auxRec.find? source = none) :
    source ∈ targetRecursors := by
  have hmem := H.getD_mem hsource
  have hgetD : auxRec.getD source source = source := by
    change Std.TreeMap.getD
      (show Std.TreeMap Name Name Name.quickCmp from auxRec)
        source source = source
    change (show Std.TreeMap Name Name Name.quickCmp from auxRec)[source]? =
      none at hfind
    rw [Std.TreeMap.getD_eq_getD_getElem?, hfind]
    rfl
  simpa [hgetD] using hmem

end VerifyInductive
end Lean4Lean
