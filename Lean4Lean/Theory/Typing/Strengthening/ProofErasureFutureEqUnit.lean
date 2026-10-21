import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDeltaBoundary

/-! # Literal unit carriers preserve future Eq guards

The Eq guard can check its last endpoints at the native literal unit carrier.
They need no common comparison, and may be arbitrary raw computed outputs.
Only the repeated anchor retains a reflexive future certificate. Thus the
distinct-variable delta example does not refute Eq guard persistence at the
literal unit carrier; the converted supplied carrier is a separate problem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_eq_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
open private eq_prefix_certified_with_family
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation
variable [Params]

private theorem eq_unit_recovery (heq : env.HasCanonicalEq) (hu : u.WF univs) :
    ScopedTypeRecovery Step Δ (.app (.app (.const ``Eq [u]) (.const family ls)) z)
      (.forallE (.const family ls) (.sort .zero)) := by
  have R0 : ScopedTypeRecovery Step Δ (.const ``Eq [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    rw [← erase_eq_type hu]
    exact .const heq.1 (by simpa using hu) rfl
  have R1 := ScopedTypeRecovery.app (a := ProofShape.const family ls) R0
  have R1 : ScopedTypeRecovery Step Δ (.app (.const ``Eq [u]) (.const family ls))
      (.forallE (.const family ls) (.forallE (.const family ls) (.sort .zero))) := by
    simpa [ProofShape.inst, ProofShape.liftN] using R1
  simpa [ProofShape.inst] using ScopedTypeRecovery.app (a := z) R1

private theorem eq_unit_beta
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (HZ : ∀ {z' w'}, ProofShape.BetaRed z z' → ProofShape.BetaRed w w' →
      JointCompare Step Δ true z' w')
    (RA : ProofShape.BetaRed (eqProofType u (.const family ls) z a) p)
    (RB : ProofShape.BetaRed (eqProofType u (.const family ls) w b) q) :
    JointCompare Step Δ true p q := by
  obtain ⟨left, rfl, HA⟩ := RA.const_spine (args := [.const family ls, z, a])
  obtain ⟨right, rfl, HB⟩ := RB.const_spine (args := [.const family ls, w, b])
  cases HA with | cons RS HA =>
  cases HA with | cons RZ HA =>
  cases HA with | cons _ HA =>
  cases HA
  cases HB with | cons RT HB =>
  cases HB with | cons RW HB =>
  cases HB with | cons _ HB =>
  cases HB
  have hn : NormalSyntax (fun _ _ => False) (.const family ls) := ⟨fun _ H => H, trivial⟩
  cases RS.fixed_of_normal hn
  cases RT.fixed_of_normal hn
  exact .appCarrier (eq_unit_recovery heq hu)
    (.app (.app (.leaf .refl) (.leaf .refl)) (HZ RZ RW))
    (.carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm))

/-- Future Eq comparison at a literal unit carrier allows arbitrary last
endpoints. Only the anchors require a future comparison; no endpoint typing,
recovery, comparison, or computational join is needed for this raw certificate. -/
theorem unit_eq_family_of_anchors
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (HZ : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ z w) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (eqProofType u (.const family ls) z a) (eqProofType u (.const family ls) w b) := by
  refine ⟨fun RA RB => eq_unit_beta heq hu hi hp hx hf HZ.1 RA RB, ?_⟩
  intro Δ' τ p q W RA RB
  simp only [eqProofType, ProofShape.subst] at RA RB
  exact eq_unit_beta heq hu hi hp hx hf (HZ.subst W).1 RA RB

/-- Any typed repeated anchor supplies the literal-unit Eq family certificate
for arbitrary raw final endpoints. This includes distinct variables exposed
by delta computation, even though those variables have no common comparison. -/
theorem proofErase_unit_eq_family
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hz : env.HasType univs Γ z T) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (eqProofType u (.const family ls) (proofErase Γ z) a)
      (eqProofType u (.const family ls) (proofErase Γ z) b) :=
  unit_eq_family_of_anchors heq hu hi hp hx hf
    (proofErase_beta_join_family hΓ hz hz .refl .refl)

/-- Certified computation of an anchor preserves the literal-unit Eq family
guard for arbitrary computed endpoints. Replay supplies a typed new anchor;
the last endpoints themselves need no typing or future common certificate. -/
theorem proofErase_computed_unit_eq_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hu : u.WF univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hz : env.HasType univs Γ z T)
    (RZ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ z) z') :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (eqProofType u (.const family ls) z' a') (eqProofType u (.const family ls) z' b') := by
  obtain ⟨z₀, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓ hz rfl rfl RZ
  rw [← EE]
  exact proofErase_unit_eq_family heq hu hi hp hx hf hΓ HE.hasType.2

/-- Every typed non-proof Eq recursor prefix over a literal registered unit
has a certified singleton step. Its indices may be arbitrary unit terms,
including distinct variables reached by non-beta computation. No previous
guard, index comparison, join, or general guard-transport law is assumed. -/
theorem proofErase_unit_eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w (.const family ls) a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w (.const family ls) a M m b)) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w (.const family ls) a M m b))
      (proofErase Γ (.lam (eqApp w (.const family ls) a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eα : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hα)
  have HC : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.const family ls)) (proofErase Γ a) (proofErase Γ b) := by
    rw [Eα]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  have hab := proofErase_joint_carrier_reflect (erased_beta_stable_joint_descent heq hs) hΓ ha hb HC
  apply eq_prefix_certified_with_family heq hregistry hΓ ht hn hab.toU
  rw [proofErase_eqProofType heq hw hΓ hα ha ha,
    proofErase_eqProofType heq hw hΓ hα ha hb, Eα]
  exact proofErase_unit_eq_family heq hw hi hp hx hf hΓ ha

end Lean4Lean.VEnv.Strengthening
