import Lean4Lean.Verify.Inductive.CompletedRecursorConstruction
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem CompletedRecursorConstruction.sourceFamilyCount
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) : H.recInfos.size = indTypes.size := by
  have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hrecords := H.cardinality.records
  simp only [Array.length_toList] at htypes
  omega

theorem CompletedRecursorConstruction.sourceMinorOffsetBound
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length := by
  have hsourceOwner : owner < indTypes.size := by rw [← H.sourceFamilyCount]; exact howner
  have hsize := (H.origins.minors owner howner).size_eq
  have hcounts := H.minorCounts owner howner
  have hroom := recursorMinorOffset_room indTypes owner hsourceOwner
  have htotal := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core
  simp only [ownedConstructors, List.length_flatMap, List.length_map] at htotal
  rw [List.length_flatMap] at hroom
  omega

end Lean4Lean.VerifyInductive
