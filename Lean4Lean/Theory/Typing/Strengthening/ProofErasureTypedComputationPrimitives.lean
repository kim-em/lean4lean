import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationProjection

/-! # Primitive equations in typed computation chains

Universe changes and selected closed declarations are available at stage zero.
Projection selection derives its saturation premise from the actual major's
typing, so the ordinary projection rule requires no additional assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every context-independent primitive computation belongs to the full union. -/
theorem primitive_compute_static_structure
    (R : Compute (Primitive D) a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b :=
  R.scoped (fun H => .base ⟨0, .inl (.inl (.inl (.inl H)))⟩)

/-- Equivalent well-formed universes give a generating computation at sorts. -/
theorem TypedComputationEq.sortDF
    (hΓ : OnCtx Γ (env.IsType univs))
    (hu : u.WF univs) (hv : v.WF univs) (H : u ≈ v) :
    TypedComputationEq D Γ (.sort u) (.sort v) (.sort (.succ u)) := by
  refine .step (.sortDF hu hv H) ?_
  simp only [proofErase, if_neg (not_isProof_of_sort hΓ (HasType.sort hu)),
    if_neg (not_isProof_of_sort hΓ (HasType.sort hv))]
  exact .base ⟨0, .inl (.inr (.sort H hv))⟩

/-- Universe conversion at constants retains a primitive step unless both
endpoints erase as proofs, in which case the computation is reflexive. -/
theorem TypedComputationEq.constDF
    (hΓ : OnCtx Γ (env.IsType univs)) (hc : env.constants c = some ci)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = ci.uvars) (HE : List.Forall₂ (· ≈ ·) ls ls') :
    TypedComputationEq D Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  have H := IsDefEq.constDF (Γ := Γ) hc hw hw' hl HE
  refine .step H ?_
  classical
  by_cases hp : IsProof Γ (.const c ls)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ H).1 hp)]
    exact .refl
  have hp' : ¬ IsProof Γ (.const c ls') := fun h => hp ((isProof_congr hΓ H).2 h)
  simp only [proofErase, if_neg hp, if_neg hp']
  exact .base ⟨0, .inl (.inr (.const HE hw'))⟩

/-- A sound selected declaration unfolds at any actual source assignment. -/
theorem TypedComputationEq.delta
    (hs : D.Sound env univs) (hd : D.unfolds c ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.const c ls) T) :
    TypedComputationEq D Γ (.const c ls) rhs T :=
  .step ((hs Γ c ls rhs hd).of_l henv hΓ ht)
    (primitive_compute_static_structure (proofErase_delta hs hd hΓ ht))

/-- The actual projection rule supplies a computation chain. Constructor
saturation follows from projection typing and rigid family identification. -/
theorem TypedComputationEq.projIota
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections s info)
    (ht : env.HasType univs Γ (.proj s i (mkApps (.const info.ctorName ls) args)) T)
    (hg : args[info.nparams + i]? = some field) (hf : env.HasType univs Γ field T) :
    TypedComputationEq D Γ (.proj s i (mkApps (.const info.ctorName ls) args)) field T := by
  obtain ⟨info', _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  obtain rfl := henv.ordered.projections_unique hi hi'
  have hl := (projection_major_family henv hΓ hi (henv.projectionRigid hi) hm.hasType.2).2
  exact .step (.projIota hi ht hg hf)
    (primitive_compute_static_structure (proofErase_projIota hs hi hl hg hΓ ht))

end Lean4Lean.VEnv.Strengthening
