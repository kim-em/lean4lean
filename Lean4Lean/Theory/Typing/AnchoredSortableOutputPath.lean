import Lean4Lean.Theory.Typing.AnchoredAtomActionGrades
import Lean4Lean.Theory.Typing.AnchoredApplicationTrace

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive SortableOutputPath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) {r : Nat} (source : Atom r) : {n : Nat} → Atom n → Type where
  | legacy (path : AppOutputPath env U registry Γ source out) : SortableOutputPath env U registry Γ source out
  | refl : SortableOutputPath env U registry Γ source source
  | action (path : SortableOutputPath env U registry Γ source (a : Atom n))
      (change : AtomAction env U registry Γ a b) : SortableOutputPath env U registry Γ source b
  | pad (path : SortableOutputPath env U registry Γ source (a : Atom n)) :
      SortableOutputPath env U registry Γ source (n := n + 1) (.pad a)
  | unpad (path : SortableOutputPath env U registry Γ source (n := n + 1) (.pad (a : Atom n))) :
      SortableOutputPath env U registry Γ source a
  | rowShift (path : SortableOutputPath env U registry Γ source (n := n + 1) (.fn (key : Key n) output)) :
      SortableOutputPath env U registry Γ source (n := n + 2) (.fn key.pad (.pad output))

def SortableOutputPath.height : {n : Nat} → {out : Atom n} →
    SortableOutputPath env U registry Γ (source : Atom r) out → Nat
  | _, _, .refl => r
  | _, _, .legacy path => path.height
  | _, _, .action path _ => path.height
  | n + 1, _, .pad path => max (n + 1) path.height
  | _, _, .unpad path => path.height
  | n + 2, _, .rowShift path => max (n + 2) path.height

theorem SortableOutputPath.bounds (path : SortableOutputPath env U registry Γ (source : Atom r) (out : Atom n)) :
    r ≤ path.height ∧ n ≤ path.height := by
  induction path with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | legacy path => exact path.bounds
  | action path change ih => exact ih
  | pad | rowShift => exact ⟨Nat.le_trans ‹_ ∧ _›.1 (Nat.le_max_right _ _), Nat.le_max_left _ _⟩
  | unpad path ih => exact ⟨ih.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) ih.2⟩

noncomputable def SortableOutputPath.normalize
    (path : SortableOutputPath env U registry Γ (source : Atom r) (out : Atom n))
    (N : Nat) (bound : path.height ≤ N) :
    AtomAction env U registry Γ
      (raiseAtom N (Nat.le_trans path.bounds.1 bound) source)
      (raiseAtom N (Nat.le_trans path.bounds.2 bound) out) := by
  induction path with
  | legacy path => exact .view (path.normalize N bound)
  | refl => exact .view (.refl _)
  | action path change ih => exact .comp (ih bound) (AtomAction.raise (Nat.le_trans path.bounds.2 bound) change)
  | pad path ih =>
    have hp := Nat.le_trans (Nat.le_max_right _ _) bound
    simpa only [raiseAtom_pad] using ih hp
  | unpad path ih => simpa only [raiseAtom_pad] using ih bound
  | @rowShift n key output path ih =>
    have hp := Nat.le_trans (Nat.le_max_right _ _) bound
    have ho : n + 2 ≤ N := Nat.le_trans (Nat.le_max_left _ _) bound
    have shift := AtomView.raise ho (AtomView.commutePadFn (env := env) (U := U)
      (registry := registry) (Γ := Γ) key output)
    rw [raiseAtom_pad] at shift
    exact .comp (ih hp) (.view shift)


end Lean4Lean.AnchoredSource.Adapted
