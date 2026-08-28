import Lean4Lean.Verify.Inductive.Nested.CanonicalSuffixSemantics

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The canonical semantic domains following the restored motive/minor
prefix of one generated recursor: all owner indices, then the major premise.
Keeping this suffix literal makes the dependent-fold positions independent
of the executable restoration accumulator. -/
def RestoredFamilySemantics.canonicalIndexMajorTargets
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) : List VExpr :=
  S.indexDomainsAfter motiveMinorTargets ++
    [S.majorTypeAfter motiveMinorTargets]

/-- The complete canonical target list for one restored recursor suffix. -/
def RestoredFamilySemantics.canonicalRecursorTargets
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) : List VExpr :=
  motiveMinorTargets ++ S.canonicalIndexMajorTargets motiveMinorTargets

@[simp] theorem RestoredFamilySemantics.canonicalIndexMajorTargets_length
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) :
    (S.canonicalIndexMajorTargets motiveMinorTargets).length =
      numIndices + 1 := by
  simp [RestoredFamilySemantics.canonicalIndexMajorTargets]

@[simp] theorem RestoredFamilySemantics.canonicalRecursorTargets_length
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) :
    (S.canonicalRecursorTargets motiveMinorTargets).length =
      motiveMinorTargets.length + numIndices + 1 := by
  simp [RestoredFamilySemantics.canonicalRecursorTargets]
  omega

/-- Before any motive/minor-prefix slot, the complete canonical list has
exactly the same prefix as the supplied motive/minor target list. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_take_prefix
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) (i : Nat)
    (hi : i <= motiveMinorTargets.length) :
    (S.canonicalRecursorTargets motiveMinorTargets).take i =
      motiveMinorTargets.take i := by
  exact List.take_append_of_le_length hi

/-- Selecting a motive/minor-prefix slot from the complete canonical list is
the same as selecting it from the supplied prefix. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_getElem_prefix
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) (i : Nat)
    (hi : i < motiveMinorTargets.length) :
    let targets := S.canonicalRecursorTargets motiveMinorTargets
    targets[i]? = motiveMinorTargets[i]? := by
  dsimp only
  exact List.getElem?_append_left hi

/-- Recursor cardinalities fix the length of the concrete canonical target
list once the motive/minor prefix and restored owner-index count are known. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_length_of_recInfos
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr)
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat)
    (hprefix : motiveMinorTargets.length =
      (recInfos.map (fun info => info.motive)).size +
        (recInfos.flatMap (fun info => info.minors)).size)
    (hindices : numIndices = recInfos[ownerIdx]!.indices.size) :
    (S.canonicalRecursorTargets motiveMinorTargets).length =
      (recInfos.map (fun info => info.motive)).size +
        (recInfos.flatMap (fun info => info.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1 := by
  rw [S.canonicalRecursorTargets_length, hprefix, hindices]

/-- Before an owner-index slot, the canonical target list contains exactly
the motive/minor prefix and the preceding owner indices. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_take_index
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) (i : Nat) (hi : i < numIndices) :
    (S.canonicalRecursorTargets motiveMinorTargets).take
        (motiveMinorTargets.length + i) =
      motiveMinorTargets ++
        (S.indexDomainsAfter motiveMinorTargets).take i := by
  have hi' : i < (S.indexDomainsAfter motiveMinorTargets).length := by
    simpa using hi
  rw [RestoredFamilySemantics.canonicalRecursorTargets,
    RestoredFamilySemantics.canonicalIndexMajorTargets, List.take_append]
  rw [List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length]
  exact Nat.le_of_lt hi'

/-- Selecting an owner-index slot from the canonical target list returns the
corresponding restored semantic index domain. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_getElem_index
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) (i : Nat) (hi : i < numIndices) :
    let targets := S.canonicalRecursorTargets motiveMinorTargets
    let indices := S.indexDomainsAfter motiveMinorTargets
    targets[motiveMinorTargets.length + i]? = indices[i]? := by
  dsimp only
  have hi' : i < (S.indexDomainsAfter motiveMinorTargets).length := by
    simpa using hi
  rw [RestoredFamilySemantics.canonicalRecursorTargets,
    List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,
    RestoredFamilySemantics.canonicalIndexMajorTargets]
  exact List.getElem?_append_left hi'

/-- Immediately before the major premise, every canonical owner index has
already been appended to the motive/minor prefix. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_take_major
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) :
    (S.canonicalRecursorTargets motiveMinorTargets).take
        (motiveMinorTargets.length + numIndices) =
      motiveMinorTargets ++ S.indexDomainsAfter motiveMinorTargets := by
  have hindices :
      (S.indexDomainsAfter motiveMinorTargets).length = numIndices := by
    simp
  rw [RestoredFamilySemantics.canonicalRecursorTargets,
    RestoredFamilySemantics.canonicalIndexMajorTargets, List.take_append]
  rw [List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length (by omega)]
  rw [List.take_of_length_le (by omega)]

/-- The terminal domain of the canonical target list is precisely the
restored major-premise type. -/
theorem RestoredFamilySemantics.canonicalRecursorTargets_getElem_major
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (motiveMinorTargets : List VExpr) :
    let targets := S.canonicalRecursorTargets motiveMinorTargets
    targets[motiveMinorTargets.length + numIndices]? =
      some (S.majorTypeAfter motiveMinorTargets) := by
  dsimp only
  have hindices :
      (S.indexDomainsAfter motiveMinorTargets).length = numIndices := by
    simp
  rw [RestoredFamilySemantics.canonicalRecursorTargets,
    List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,
    RestoredFamilySemantics.canonicalIndexMajorTargets]
  rw [List.getElem?_append_right]
  · simp [hindices]
  · simpa [hindices]

end VerifyInductive
end Lean4Lean
