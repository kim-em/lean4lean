import Lean4Lean.Verify.Inductive.Recursor.InstanceAlignment
import Lean4Lean.Verify.Inductive.Recursor.RuleCoverage
import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratedShapes

/-! # The model recursors of a recursor installation

The kernel recursors of an installation (`rvals`, read off the generated entries) and the model
recursors (`recs`, PR #43's `VRecursor`) they translate to: the generated recursor constant of
each owner with the kernel's telescope split and K flag, and one `VRecRule` per kernel rule,
firing on its constructor with the declaration's parameter count and reducing to the generated
equation's right-hand side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RecursorInstallation

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

theorem entries_lt (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : owner.val < H.entries.length := by
  rw [H.entries_length_eq]; exact owner.isLt

/-- The kernel recursor installed for an owner. -/
noncomputable def rvalAt (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : RecursorVal :=
  (H.generated.entry owner.val (H.entries_lt owner)).info

/-- The kernel recursors, in family order. -/
noncomputable def rvals (H : RecursorInstallation R outEnv) : List RecursorVal :=
  List.ofFn H.rvalAt

/-- The model rule of a kernel rule firing on the constructor `index`. -/
noncomputable def modelRule (H : RecursorInstallation R outEnv)
    (index : Fin H.generationSignature.constructors.size) (rule : RecursorRule) : VRecRule where
  ctor := rule.ctor
  ctorParams := decl.nparams
  nfields := rule.nfields
  rhs := (H.generationInstance.equation index).rhs

/-- The model recursor of an owner. -/
noncomputable def modelRecursor (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : VRecursor where
  toVConstVal := H.generationInstance.recursor owner
  all := (H.rvalAt owner).all
  numParams := (H.rvalAt owner).numParams
  numMotives := (H.rvalAt owner).numMotives
  numMinors := (H.rvalAt owner).numMinors
  numIndices := (H.rvalAt owner).numIndices
  k := (H.rvalAt owner).k
  rules := List.zipWith H.modelRule (H.generationSignature.ownedConstructors owner)
    (H.rvalAt owner).rules

/-- The model recursors, in family order. -/
noncomputable def recs (H : RecursorInstallation R outEnv) : List VRecursor :=
  List.ofFn H.modelRecursor

@[simp] theorem rvals_length (H : RecursorInstallation R outEnv) :
    H.rvals.length = H.generationSignature.families.size := by simp [rvals]

@[simp] theorem recs_length (H : RecursorInstallation R outEnv) :
    H.recs.length = H.generationSignature.families.size := by simp [recs]

theorem entry_fst (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.entries[owner.val]'(H.entries_lt owner)).1 = .recInfo (H.rvalAt owner) :=
  (H.generated.entry owner.val (H.entries_lt owner)).source_eq

theorem entry_snd (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.entries[owner.val]'(H.entries_lt owner)).2 = H.generationInstance.recursor owner := by
  rw [H.targets owner.val (H.entries_lt owner)]
  unfold RecursorConstruction.recursorTarget
  rw [dif_pos owner.isLt]

theorem entries_fst (H : RecursorInstallation R outEnv) :
    H.entries.map Prod.fst = H.rvals.map .recInfo := by
  apply List.ext_getElem
  · simp [H.entries_length_eq]
  · intro i h₁ h₂
    have hi : i < H.generationSignature.families.size := by simpa using h₂
    simp only [List.getElem_map, rvals, List.getElem_ofFn]
    exact H.entry_fst ⟨i, hi⟩

theorem entries_snd (H : RecursorInstallation R outEnv) :
    H.entries.map Prod.snd = H.recs.map (·.toVConstVal) := by
  apply List.ext_getElem
  · simp [H.entries_length_eq]
  · intro i h₁ h₂
    have hi : i < H.generationSignature.families.size := by simpa using h₂
    simp only [List.getElem_map, recs, List.getElem_ofFn]
    exact H.entry_snd ⟨i, hi⟩

theorem recs_recursors (H : RecursorInstallation R outEnv) :
    H.recs.map (·.toVConstVal) = H.generationInstance.recursors := by
  simp only [recs, InductiveSignature.Instance.recursors, List.map_ofFn, modelRecursor,
    Function.comp_def]
  simp [List.finRange, List.map_ofFn, Function.comp_def]

theorem rvalAt_metadata (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    InductiveSignature.RecursorMetadata H.generationInstance H.outVEnv owner (H.rvalAt owner) := by
  obtain ⟨rec, h1, -, hm⟩ := H.trMetadata owner
  have : rec = H.rvalAt owner := by
    have h := h1.symm.trans (H.entry_fst owner)
    cases h; rfl
  subst this; exact hm

end RecursorInstallation

end VerifyInductive
end Lean4Lean
