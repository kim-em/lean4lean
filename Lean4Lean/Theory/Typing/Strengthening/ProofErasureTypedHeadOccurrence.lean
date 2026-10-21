import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstHeadStep
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Actual typed sources for the first primitive at a computed prefix

Compatible computation of a prefix inherits a typed realization from the
whole spine. The primitive classification therefore need hold only at typed
sources; no claim about arbitrary unrealizable raw prefixes is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

omit [Params] in
private theorem apps_append (f : ProofShape) (args rest : List ProofShape) :
    mkApps f (args ++ rest) = mkApps (mkApps f args) rest := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih _

private theorem typed_mkApps_fn (H : TypedSource Δ (mkApps f args)) : TypedSource Δ f := by
  induction args generalizing f with
  | nil => exact H
  | cons a args ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := ih H
    obtain ⟨f₀, a₀, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact ⟨Γ, f₀, _, hΓ, EΓ, hf, Ef⟩

omit [Params] in
private theorem compute_apps (RF : ScopedCompute Step Δ f g)
    (HA : List.Forall₂ (ScopedCompute Step Δ) args args') :
    ScopedCompute Step Δ (mkApps f args) (mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact RF
  | cons H HA ih => exact ih (.app RF H)

/-- Every computed initial segment of an actually typed raw spine has an
actual typed realization in the same erased context. Source descent is used
only forward at that realized prefix. -/
theorem ProofShape.TypedSource.computed_prefix
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (mkApps f args))
    (HA : List.Forall₂ (ScopedCompute Step Δ) (args.take k) changed) :
    TypedSource Δ (mkApps f changed) := by
  have HP : TypedSource Δ (mkApps f (args.take k)) := by
    apply typed_mkApps_fn (args := args.drop k)
    simpa only [← apps_append, List.take_append_drop] using HT
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HP
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee
    (compute_apps ScopedCompute.refl HA)
  exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, Ee'⟩

/-- A first-head occurrence from a typed constant spine can always carry the
typed-source witness needed to classify its primitive. The original prefix
length and every component path are retained. -/
theorem ProofShape.ScopedHeadOccurrence.with_typed_source
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (mkApps (.const c ls) args))
    (H : ScopedHeadOccurrence Step Δ c ls args) :
    ∃ k changed out, k ≤ args.length ∧
      List.Forall₂ (ScopedCompute Step Δ) (args.take k) changed ∧
      TypedSource Δ (mkApps (.const c ls) changed) ∧
      Step Δ (mkApps (.const c ls) changed) out := by
  obtain ⟨k, changed, out, hk, HA, HP⟩ := H
  exact ⟨k, changed, out, hk, HA, HT.computed_prefix hstep HA, HP⟩

end Lean4Lean.VEnv.Strengthening
