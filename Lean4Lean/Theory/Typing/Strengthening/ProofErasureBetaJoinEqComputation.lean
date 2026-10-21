import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbeComputation

/-! # Certified Eq computation from beta-joined indices

Literal beta joins supply future-stable certificates for the generated Eq
family, including the fresh proof-major binder. This handles primitive Eq
computation constructively without a global endpoint-beta transport law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature ProofShape
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Beta-joined indices give a future-stable comparison between the reflexive
and requested Eq families, for arbitrary typed carriers and primitive targets. -/
theorem proofErase_beta_join_eq_family
    (heq : env.HasCanonicalEq) (hw : w.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort w))
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (RA : ProofShape.BetaRed (proofErase Γ a) shared)
    (RB : ProofShape.BetaRed (proofErase Γ b) shared) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp w α a a)) (proofErase Γ (eqApp w α a b)) := by
  apply proofErase_beta_join_family hΓ (HasType.eqApp heq hw hα ha ha)
    (HasType.eqApp heq hw hα ha hb)
    (shared := ProofShape.eqProofType w (proofErase Γ α) shared shared)
  · rw [proofErase_eqProofType heq hw hΓ hα ha ha]
    exact .app (.app (.app .refl .refl) RA) RA
  · rw [proofErase_eqProofType heq hw hΓ hα ha hb]
    exact .app (.app (.app .refl .refl) RA) RB

private theorem eq_prefix_certified_with_family
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (hab : env.IsDefEqU univs Γ a b)
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ (eqApp w α a a))
      (proofErase Γ (eqApp w α a b))) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  obtain ⟨hv, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hz := hr.eqRec_source_zero henv heq hn hΓ ⟨_, ht⟩
  have hl := hr.eqRec_large heq hn
  obtain ⟨_, _, _, hrest, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  obtain ⟨i, ho, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hpat := hr.patEquation_of_empty henv hrest hgen
  have hlevels : ∀ l ∈ [v,w], l.WF univs := by simp_all
  have hlen : [v,w].length = data.uvars := by simp [(hr.eqRec_target heq hn).1]
  obtain ⟨S, E, hS, hE, _⟩ := RecursorData.propElim_wf henv hr hl hz hlevels hlen ⟨i, ho⟩
  have hg := eqRec_prefix_generated (U := univs) (α := α) (a := a) (M := M) (m := m) (b := b)
    heq hr hn hz hS hE
  have HC := canonicalEqPrefixProgram_check henv heq hΓ hpat ⟨_, ht⟩ hab
  have hEQ := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hEQ⟩
  have hP := HasType.eqApp heq hw hα ha ha
  have HF := HF.subst (ContextRenaming.of_liftN hΓ hΓE Ctx.LiftN.one).interpretation
  have HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx (eqApp w α a b :: Γ))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α a a).lift)
      (proofErase (eqApp w α a b :: Γ) (eqApp w α a b).lift) := by
    rw [proofErase_liftN hΓ hΓE Ctx.LiftN.one hP,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hEQ]
    simpa only [subst_bvar_liftN] using HF
  have HG := (eqRec_family_guard_iff (Cmp := ErasedFamilyComparison
    (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)))
    (M := M) (m := m) (reconstructed := eqReflApp w α.lift a.lift)
    heq hr hn hz hS hE).2
    HF
  obtain ⟨recType, hrec⟩ := hr.recursorType_exists
  let args := [α,a,M,m,b]
  let program := canonicalEqPrefixProgram v w α a M m b (eqReflApp w α.lift a.lift)
  let C : SingletonPrefixCode := ⟨data, [v,w], args.length, recType,
    program.equation, program.equationBody, S, E⟩
  obtain ⟨_, _, _, _, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  have V : C.Valid := ⟨hn ▸ hregistry.trans hlookup, hr, hl, hz, hlevels, hrec,
    heqn, hbody, hS, hE, args, program, rfl, hg⟩
  have HC : UnfoldingCheck env univs Γ (mkApps (.const data.name [v,w]) args) program := by
    simpa only [hn, args, program, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using HC
  have hnp : ¬ IsProof Γ (mkApps (.const data.name [v,w]) args) := by simpa only [hn, args, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using hnp
  have HE := proofErase_const_spine hΓ HC.source_typed hnp
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const data.name [v,w]) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, HC.source_typed, HE⟩
  change ErasedBetaStableJoint D (proofEraseCtx Γ)
    (proofErase Γ (mkApps (.const ``Eq.rec [v,w]) args)) (proofErase Γ program.rhs)
  rw [← hn, HE, V.output_eq heq hΓ hg HC hnp]
  exact .inr ⟨HT, .intro V (by simp only [List.length_map, C])
    (V.telescope_eq hΓ hg ⟨_, HC.source_typed⟩) ((V.guardWith_iff heq hΓ hg ⟨_, HC.source_typed⟩).2 HG)⟩

/-- The actual generated Eq prefix is a certified primitive whenever its
indices beta-join. The output remains the exact original proof-major lambda;
no finite-stage endpoint-beta closure is assumed. -/
theorem proofErase_beta_join_eq_prefix_certified
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (RA : ProofShape.BetaRed (proofErase Γ a) shared)
    (RB : ProofShape.BetaRed (proofErase Γ b) shared) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  exact eq_prefix_certified_with_family heq hregistry hΓ ht hnp
    (proofErase_beta_join_reflect hΓ ha hb RA RB).toU
    (proofErase_beta_join_eq_family heq hw hΓ hα ha hb RA RB)

private theorem eqTypeProbe_compute_of_prefix
    (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HG : Step (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q))
      (proofErase Γ (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift))) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  have hE := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hL := HasType.lam hE (hS.weak henv)
  have hLq : env.HasType univs Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q)
      (.sort u) := hL.app hq
  have EB : proofErase Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q) =
      .app (proofErase Γ (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift)) .proof := by
    rw [show proofErase Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q) =
        .app _ _ from if_neg (not_isProof_of_sort hΓ hLq),
      proofErase_eq_proof.2 ⟨_, hq, hE⟩]
  have HB := proofErase_beta_forward hΓ hLq
    (VExpr.BetaRed.beta (A := eqApp (.succ .zero) (.sort .zero) P Q) (b := S.lift) (a := q))
  rw [EB, VExpr.inst_lift] at HB
  have hfull := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have EF : proofErase Γ (eqTypeProbe u S P Q q) =
      .app (proofErase Γ (eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q)) .proof := by
    rw [show proofErase Γ (eqTypeProbe u S P Q q) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hfull), proofErase_eq_proof.2 ⟨_, hq, hE⟩]
    rfl
  rw [EF]
  exact ScopedCompute.trans (ScopedCompute.app (.base HG) .refl) (.beta HB)

/-- A type probe with beta-joined proposition indices computes to its exact
minor in the certified relation. The equality proof may be arbitrary. -/
theorem eqTypeProbe_compute_certified_of_beta_join
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (RP : ProofShape.BetaRed (proofErase Γ P) shared)
    (RQ : ProofShape.BetaRed (proofErase Γ Q) shared) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  exact eqTypeProbe_compute_of_prefix heq hΓ hS hP hQ hq
    (proofErase_beta_join_eq_prefix_certified heq hregistry hΓ ht hn RP RQ)

end Lean4Lean.VEnv.Strengthening
