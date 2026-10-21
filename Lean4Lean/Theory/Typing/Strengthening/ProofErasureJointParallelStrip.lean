import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointParallelPrimitive
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBetaStrip
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLambdaJoins

/-! # A parallel beta development across a full joint computation

Primitive residuals retain one parallel beta step. Typed replay handles
sequential computation; context transport handles changing annotations; exact
head-beta exchange handles the application case and duplicated arguments.
Proposition beta stability of the joint union remains an explicit premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv beta_eq beta_not_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private union_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLambdaJoins
variable [Params]

private theorem parallel_app_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) fOut)
    (Pb : BetaPar (proofErase (A :: Γ) b) bBeta) (Px : BetaPar (proofErase Γ x) xBeta)
    (HF : ∃ shared, BetaPar fOut shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (.lam (proofErase Γ A) bBeta) shared)
    (HX : ∃ shared, BetaPar xOut shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) xBeta shared) :
    ∃ shared, BetaPar (.app fOut xOut) shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (bBeta.inst xBeta) shared := by
  obtain ⟨Af, bf, rfl, _, _⟩ := union_lam_inv heq hs hΓ hA hb hn RF
  obtain ⟨fShared, PF, RF⟩ := HF
  cases PF with
  | lam PA PB =>
    obtain ⟨xShared, PX, RX⟩ := HX
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨b₁, Rb, Eb⟩ := proofErase_parallel_beta_replay hΓA hb Pb
    obtain ⟨x₁, Rx, Ex⟩ := proofErase_parallel_beta_replay hΓ hx Px
    have hb₁ := (beta_eq hΓA hb Rb.toCompute.to_beta).hasType.2
    have hx₁ := (beta_eq hΓ hx Rx.toCompute.to_beta).hasType.2
    have hn₁ : ¬ IsProof Γ (.lam A b₁) := beta_not_proof hΓ (HasType.lam hA hb)
      (ComputePar.lam (.refl _) Rb).toCompute.to_beta hn
    obtain ⟨sf, RF⟩ := RF.finite_stage erased_joint_stage_mono
    obtain ⟨sx, RX⟩ := RX.finite_stage erased_joint_stage_mono
    have RF' := RF.mono (erased_joint_stage_mono (Nat.le_max_left sf sx))
    have RX' := RX.mono (erased_joint_stage_mono (Nat.le_max_right sf sx))
    rw [← Eb] at RF'
    rw [← Ex] at RX'
    obtain ⟨later, A', body', _, EF, R, _⟩ :=
      proofErase_joint_beta_exchange_of_prop_beta heq hs hregistry Hbeta
        hΓ hA hb₁ hx₁ hn₁ RF' RX'
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EF
    rw [proofErase_instN hΓA hx₁ Ctx.InstN.zero hb₁, Eb, Ex] at R
    exact ⟨_, .beta PB PX, R.mono (fun H => ⟨later, H⟩)⟩

private theorem compute_parallel_aux
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (R : ScopedCompute (ErasedJointUnion D) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (P : BetaPar source reduced) :
    ∃ shared, BetaPar out shared ∧ ScopedCompute (ErasedJointUnion D) Δ reduced shared := by
  induction R generalizing Γ e T reduced with
  | base H =>
    obtain ⟨shared, PB, H⟩ := proofErase_joint_primitive_parallel_beta_residual
      heq hs hregistry Hbeta hΓ ht (EΓ.symm ▸ Ee.symm ▸ H) (Ee.symm ▸ P)
    exact ⟨shared, PB, .base (EΓ ▸ H)⟩
  | beta R =>
    obtain ⟨shared, PB, RB⟩ := proofErase_parallel_beta_strip hΓ ht (Ee.symm ▸ R) (Ee.symm ▸ P)
    exact ⟨shared, PB, .beta RB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨shared, PB, RS⟩ := ih₁ hΓ ht EΓ Ee P
    obtain ⟨e₁, HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_joint_union_descent heq hs) hΓ ht EΓ Ee R₁
    obtain ⟨target, PT, RT⟩ := ih₂ hΓ HE.hasType.2 EΓ EE PB
    exact ⟨target, PT, RS.trans RT⟩
  | app RF RX ihf ihx =>
    obtain ⟨f, x, rfl, hn, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    cases P with
    | app Pf Px =>
      obtain ⟨fs, PF, RF⟩ := ihf hΓ hf EΓ Ef Pf
      obtain ⟨xs, PX, RX⟩ := ihx hΓ hx EΓ Ex Px
      exact ⟨_, .app PF PX, .app RF RX⟩
    | beta Pb Px =>
      obtain ⟨A, b, rfl, hnf, EA, Eb⟩ := erase_lam_inv Ef
      obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
      obtain ⟨⟨_, hDA⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
      have hxA := hDA.defeq hx
      have HF := ihf hΓ hf EΓ Ef (BetaPar.lam (.refl _) Pb)
      have HX := ihx hΓ hxA EΓ Ex Px
      have RF' := RF
      rw [← EΓ, ← EA, ← Eb] at RF'
      have H := parallel_app_beta heq hs hregistry Hbeta hΓ hA hb hxA hnf RF'
        (Eb.symm ▸ Pb) (Ex.symm ▸ Px)
        (by simpa only [EΓ, EA] using HF) (EΓ.symm ▸ HX)
      simpa only [EΓ] using H
  | proj RM ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    cases P with
    | proj Pm =>
      obtain ⟨shared, PM, RM⟩ := ihm hΓ hm.hasType.2 EΓ Em Pm
      exact ⟨_, .proj PM, .proj RM⟩
  | lam RA RB ihA ihB =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    cases P with
    | lam PA PB =>
      obtain ⟨As, QA, SA⟩ := ihA hΓ hA EΓ EA PA
      obtain ⟨bs, QB, SB⟩ := ihB hΓA hb (by simp only [proofEraseCtx, EΓ, EA]) Eb PB
      obtain ⟨A₁, HA, E₁⟩ := proofErase_parallel_beta_replay hΓ hA (EA.symm ▸ PA)
      obtain ⟨b₁, HB, E₂⟩ := proofErase_parallel_beta_replay hΓA hb (Eb.symm ▸ PB)
      have HT : TypedSource (proofEraseCtx (A :: Γ)) _ :=
        ⟨A :: Γ, b₁, _, hΓA, rfl, (beta_eq hΓA hb HB.toCompute.to_beta).hasType.2, E₂⟩
      have SB' := proofErase_joint_compute_defeqCtx_of_prop_beta heq hs hregistry Hbeta hΓ
        (.succ .zero (beta_eq hΓ hA HA.toCompute.to_beta)) HT
        (by simpa only [proofEraseCtx, EΓ, EA] using SB)
      exact ⟨_, .lam QA QB, .lam SA (by simpa only [proofEraseCtx, EΓ, E₁] using SB')⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    cases P with
    | forallE PA PB =>
      obtain ⟨As, QA, SA⟩ := ihA hΓ hA EΓ EA PA
      obtain ⟨bs, QB, SB⟩ := ihB hΓA hb (by simp only [proofEraseCtx, EΓ, EA]) Eb PB
      obtain ⟨A₁, HA, E₁⟩ := proofErase_parallel_beta_replay hΓ hA (EA.symm ▸ PA)
      obtain ⟨b₁, HB, E₂⟩ := proofErase_parallel_beta_replay hΓA hb (Eb.symm ▸ PB)
      have HT : TypedSource (proofEraseCtx (A :: Γ)) _ :=
        ⟨A :: Γ, b₁, _, hΓA, rfl, (beta_eq hΓA hb HB.toCompute.to_beta).hasType.2, E₂⟩
      have SB' := proofErase_joint_compute_defeqCtx_of_prop_beta heq hs hregistry Hbeta hΓ
        (.succ .zero (beta_eq hΓ hA HA.toCompute.to_beta)) HT
        (by simpa only [proofEraseCtx, EΓ, EA] using SB)
      exact ⟨_, .forallE QA QB, .forallE SA (by simpa only [proofEraseCtx, EΓ, E₁] using SB')⟩

/-- Any full joint computation from a typed source commutes with one parallel
beta development, retaining one parallel beta step on the computed-output
side. The other residual is actual joint computation in the original context.
Proposition beta stability remains unproved and is explicitly assumed. -/
theorem proofErase_joint_parallel_beta_strip
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) reduced shared :=
  compute_parallel_aux heq hs hregistry Hbeta R hΓ ht rfl rfl P

end Lean4Lean.VEnv.Strengthening
