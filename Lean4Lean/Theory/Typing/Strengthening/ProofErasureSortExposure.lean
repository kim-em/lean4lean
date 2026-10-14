import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortRecovery
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary

/-! # Sort recovery as repair of full universe exposure

Confluence already exposes a literal universe on the original syntax. The
missing erased sort-recovery clause is exactly the ability to replace these
full reductions by erased computation, allowing an equivalent output universe.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A typed universe has no full reduction step other than identity. In
particular neither function eta nor structure eta can expand its root. -/
theorem FullStep.sort_fixed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.sort u) T) (H : FullStep Γ (.sort u) out) :
    out = .sort u := by
  generalize E : VExpr.sort u = source at H ht
  cases H with
  | core R =>
    cases R with
    | sort => cases E; rfl
    | extra hp hm =>
      obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
      subst E
      simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at hh
    | _ => cases E
  | delta | quotDelta =>
    exact (VExpr.mkApps_ne_sort (fn := .const _ _) (fun _ h => nomatch h) _ E.symm).elim
  | structEta hi _ _ hs =>
    subst E
    have hu := HasType.sort_inv henv.ordered ht
    have ht₀ : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort hu
    exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      ((ht₀.uniqU henv hΓ hs).typeChain henv hΓ (.sort hu))).elim
  | funEta hs =>
    subst E
    have ht₀ : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
      .sort (HasType.sort_inv henv.ordered ht)
    exact ((ht₀.uniqU henv hΓ hs).sort_forallE_inv henv hΓ).elim
  | app | proj | projIota | lam | forallE => cases E

/-- Every finite full reduction from a typed universe preserves it exactly. -/
theorem FullReduction.sort_fixed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.sort u) T) (H : FullReduction Γ (.sort u) out) :
    out = .sort u := by
  induction H with
  | rfl => rfl
  | tail _ R ih => subst ih; exact R.sort_fixed hΓ ht

namespace Strengthening
/-- Normal comparison with a universe has a universe at the other endpoint.
Proof irrelevance and function eta cannot change this head shape. -/
theorem normal_sort_right (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ e (.sort u)) : ∃ v, e = .sort v := by
  obtain ⟨n, H⟩ := H
  generalize E : VExpr.sort u = right at H
  cases H with
  | refl => cases E; exact ⟨_, rfl⟩
  | sortDF => cases E; exact ⟨_, rfl⟩
  | etaL hs _ | etaBoth _ hs _ =>
    cases E
    have ht₀ : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
      .sort (HasType.sort_inv henv.ordered hs)
    exact ((ht₀.uniqU henv hΓ hs).sort_forallE_inv henv hΓ).elim
  | proofIrrel hP _ hs =>
    cases E
    exact (not_isProof_of_sort hΓ (HasType.sort (HasType.sort_inv henv.ordered hs)) ⟨_, hs, hP⟩).elim
  | _ => cases E

omit [Params] in
/-- Canonical-Eq confluence exposes some literal universe from any expression
convertible to one. This is full reduction, not yet erased computation. -/
theorem defeq_sort_full_exposure {E : VEnv} (hE : E.WF) (heq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (H : E.IsDefEq U Γ e (.sort u) T) :
    ∃ v, @FullReduction (hE.params U) Γ e (.sort v) := by
  letI := hE.params U
  obtain ⟨left, right, hl, hr, hn⟩ := hE.church_rosser heq hΓ H
  obtain rfl := hr.sort_fixed hΓ H.hasType.2
  obtain ⟨v, rfl⟩ := normal_sort_right hΓ hn
  exact ⟨v, hl⟩

/-- Repair only full reductions that expose a universe from a sort-typed source.
Exact intermediate replay and a prescribed output level are unnecessary. This
remains open for the concrete erased computational stages. -/
def ErasedFullSortRepair (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ T u v}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ T (.sort u) →
    @FullReduction (henv.params univs) Γ T (.sort v) →
    ∃ w, ProofShape.Compute Step (proofErase Γ T) (.sort w)

/-- Full exposure repair suffices for the universe exposure interface by the
already-proved original confluence theorem. -/
theorem ErasedFullSortRepair.exposure (heq : env.HasCanonicalEq)
    (H : ErasedFullSortRepair Step) : ErasedSortExposure Step := by
  intro Γ T u v hΓ hT HT
  obtain ⟨w, R⟩ := defeq_sort_full_exposure henv heq hΓ (HT.of_l henv hΓ hT)
  exact H hΓ hT R

/-- Universe exposure already repairs every such full reduction: soundness
supplies the endpoint equality needed by the exposure interface. -/
theorem ErasedSortExposure.full_repair (H : ErasedSortExposure Step) :
    ErasedFullSortRepair Step := by
  intro Γ T u v hΓ hT R
  letI : Params := henv.params univs
  exact H hΓ hT ⟨_, R.defeq hΓ hT⟩

/-- Under canonical Eq the missing sort-recovery clause is precisely repair of
full universe exposure. The equivalence does not assert that this clause alone
suffices for the full proposition front. -/
theorem erasedSortRecovery_iff_fullRepair (heq : env.HasCanonicalEq)
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ)) :
    ErasedSortRecovery Step ↔ ErasedFullSortRepair Step := by
  rw [erasedSortRecovery_iff_exposure hstep hsubst]
  exact ⟨ErasedSortExposure.full_repair, ErasedFullSortRepair.exposure heq⟩

end Strengthening
end Lean4Lean.VEnv
