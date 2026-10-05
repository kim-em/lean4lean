import Lean4Lean.Theory.Typing.AnchoredContextCongruence
import Lean4Lean.Theory.Typing.AnchoredExposureAbsorption

/-! Semantic transport through actual mixed world routes. Only lifted
operands descend; private display components are transported forward. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

namespace MixedInsertion

theorem code (henv : env.Ordered) (path : MixedInsertion env U Γ Δ ρ)
    (related : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ) := by
  induction path generalizing left right profile with
  | proof insertion => exact related.future henv insertion.toFuture
  | context chain => simpa only [lift'_refl, Profile.rename_refl] using chain.code henv related
  | comp _ _ first second =>
    simpa only [lift'_comp, ← Profile.rename_comp] using second (first related)

theorem term (henv : env.Ordered) (path : MixedInsertion env U Γ Δ ρ)
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (support.rename ρ) := by
  induction path generalizing left right type value support with
  | proof insertion => exact related.future henv insertion.toFuture
  | context chain => simpa only [lift'_refl, Profile.rename_refl] using chain.term henv related
  | comp _ _ first second =>
    simpa only [lift'_comp, ← Profile.rename_comp] using second (first related)

theorem admitted (henv : env.Ordered) (path : MixedInsertion env U Γ Δ ρ)
    (related : Admitted env U registry Γ key left right) :
    Admitted env U registry Δ (key.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  induction path generalizing key left right with
  | proof insertion => exact related.future henv insertion.toFuture
  | context chain => simpa only [lift'_refl, Key.rename_refl] using chain.admitted henv related
  | comp _ _ first second =>
    simpa only [lift'_comp, Key.rename_comp] using second (first related)

/-- Only literally lifted operands descend; private display components are
never retracted by this operation. -/
theorem codeBack (henv : env.Ordered) (hscoped : registry.Scoped)
    (path : MixedInsertion env U Γ Δ ρ)
    (related : TypeRelated env U registry Δ
      (left.lift' ρ) (right.lift' ρ) (profile.rename ρ)) :
    TypeRelated env U registry Γ left right profile := by
  induction path generalizing left right profile with
  | proof insertion => exact related.absorb henv hscoped insertion
  | context chain =>
    apply (chain.symm henv).code henv
    simpa only [lift'_refl, Profile.rename_refl] using related
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp, ← Profile.rename_comp] using related

theorem termBack (henv : env.Ordered) (path : MixedInsertion env U Γ Δ ρ)
    (related : Related env U registry Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (value.rename ρ) (support.rename ρ)) :
    Related env U registry Γ left right type value support := by
  induction path generalizing left right type value support with
  | proof insertion => exact related.absorb henv insertion
  | context chain =>
    apply (chain.symm henv).term henv
    simpa only [lift'_refl, Profile.rename_refl] using related
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp, ← Profile.rename_comp] using related

end MixedInsertion

/-- The exact three codomain capabilities stored by a concrete Pi row. -/
def RowCapabilities (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (key : Key n) (leftBody rightBody : VExpr) (result : Profile n) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
    Admitted env U registry Δ (key.rename ρ) x y →
    TypeRelated env U registry Δ ((leftBody.lift' ρ.cons).inst x)
      ((leftBody.lift' ρ.cons).inst y) (result.rename ρ) ∧
    TypeRelated env U registry Δ ((rightBody.lift' ρ.cons).inst x)
      ((rightBody.lift' ρ.cons).inst y) (result.rename ρ) ∧
    TypeRelated env U registry Δ ((leftBody.lift' ρ.cons).inst x)
      ((rightBody.lift' ρ.cons).inst x) (result.rename ρ)

private theorem lift_cons_comp (expression : VExpr) (ρ τ : Lift) :
    (expression.lift' ρ.cons).lift' τ.cons = expression.lift' (ρ.comp τ).cons :=
  (@lift'_comp ρ.cons τ.cons expression).symm

/-- Actual Pi-row transport: future arguments are pulled backwards through
context changes and the resulting lower-rank codes move forwards. -/
theorem MixedInsertion.rowCapabilities
    (henv : env.Ordered) (path : MixedInsertion env U Γ Δ ρ)
    (capability : RowCapabilities env U registry Γ key leftBody rightBody result) :
    RowCapabilities env U registry Δ (key.rename ρ)
      (leftBody.lift' ρ.cons) (rightBody.lift' ρ.cons) (result.rename ρ) := by
  induction path generalizing key leftBody rightBody result with
  | @proof Γ Δ ρ insertion =>
    intro Ω τ future x y admitted
    have admitted' : Admitted env U registry Ω (key.rename (ρ.comp τ)) x y := by
      simpa only [Key.rename_comp] using admitted
    have result := capability Ω (ρ.comp τ) (insertion.toFuture.comp future henv) x y admitted'
    simpa only [lift_cons_comp, ← Profile.rename_comp] using result
  | context chain =>
    simp only [Key.rename_refl, lift'_depth_zero (l := Lift.cons .refl) rfl,
      Profile.rename_refl]
    intro Ω τ future x y admitted
    obtain ⟨oldΩ, oldFuture, changed⟩ := chain.pullFuture henv future
    have oldAdmission := (changed.symm henv).admitted henv admitted
    obtain ⟨first, second, cross⟩ := capability oldΩ τ oldFuture x y oldAdmission
    exact ⟨changed.code henv first, changed.code henv second, changed.code henv cross⟩
  | comp _ _ first second =>
    simpa only [Key.rename_comp, ← Profile.rename_comp, lift_cons_comp] using second (first capability)


/-- Query an original concrete Pi row after an arbitrary mixed display leg. -/
theorem PiWitness.rowBodies_mixed
    (henv : env.Ordered)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows)
    (route : MixedInsertion env U display.context Ω i)
    (member : (key, result) ∈ rows)
    (future : FutureInsertion env U Ω Δ ρ) (x y : VExpr)
    (admitted : Admitted env U registry Δ
      (key.rename (display.map.comp (i.comp ρ))) x y) :
    TypeRelated env U registry Δ ((display.leftBody.lift' (i.comp ρ).cons).inst x)
      ((display.leftBody.lift' (i.comp ρ).cons).inst y)
      (result.rename (display.map.comp (i.comp ρ))) ∧
    TypeRelated env U registry Δ ((display.rightBody.lift' (i.comp ρ).cons).inst x)
      ((display.rightBody.lift' (i.comp ρ).cons).inst y)
      (result.rename (display.map.comp (i.comp ρ))) ∧
    TypeRelated env U registry Δ ((display.leftBody.lift' (i.comp ρ).cons).inst x)
      ((display.rightBody.lift' (i.comp ρ).cons).inst x)
      (result.rename (display.map.comp (i.comp ρ))) := by
  obtain ⟨oldΔ, oldFuture, changed⟩ := route.pullFuture henv future
  have oldAdmission := (changed.symm henv).admitted henv admitted
  obtain ⟨first, second, cross⟩ :=
    display.rowBodies key result member oldΔ (i.comp ρ) oldFuture x y oldAdmission
  exact ⟨changed.code henv first, changed.code henv second, changed.code henv cross⟩

end Lean4Lean.AnchoredSemantics
