import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBetaStrip
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation

/-! # Parallel residuals in a target relation closed under substitution

A typed primitive square lifts to every compatible source path when target
primitives carry substitution closure. Source and target relations stay
separate, so a residual body is instantiated without any source-stage beta
stability assertion about the target path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv beta_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

omit [Params] in
private theorem lambda_head
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.lam A b) out) : ∃ A' b', out = .lam A' b' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | base H => exact (E ▸ hhead H).elim
  | beta H => cases E; obtain ⟨A', b', HE, _, _⟩ := H.lam_inv; exact ⟨_, _, HE⟩
  | trans _ _ ih₁ ih₂ => obtain ⟨A', b', rfl⟩ := ih₁ E; exact ih₂ rfl
  | lam => cases E; exact ⟨_, _, rfl⟩
  | app | proj | forallE => cases E

private theorem inst_argument
    (hsubst : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextSubstitution Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute Target (proofEraseCtx Γ)
      ((proofErase (A :: Γ) b).inst (proofErase Γ x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming (fun H W => hsubst H W.interpretation)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

private theorem parallel_app_beta
    (hsourceHead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargetHead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextSubstitution Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RF : ScopedCompute Source (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) fOut)
    (Pb : BetaPar (proofErase (A :: Γ) b) bBeta) (Px : BetaPar (proofErase Γ x) xBeta)
    (HF : ∃ shared, BetaPar fOut shared ∧
      ScopedCompute Target (proofEraseCtx Γ) (.lam (proofErase Γ A) bBeta) shared)
    (HX : ∃ shared, BetaPar xOut shared ∧
      ScopedCompute Target (proofEraseCtx Γ) xBeta shared) :
    ∃ shared, BetaPar (.app fOut xOut) shared ∧
      ScopedCompute Target (proofEraseCtx Γ) (bBeta.inst xBeta) shared := by
  obtain ⟨Af, bf, rfl⟩ := lambda_head hsourceHead RF
  obtain ⟨fShared, PF, RF⟩ := HF
  cases PF with
  | @lam _ _ _ bs PA PB =>
    obtain ⟨xShared, PX, RX⟩ := HX
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨b₁, Rb, Eb⟩ := proofErase_parallel_beta_replay hΓA hb Pb
    obtain ⟨x₁, Rx, Ex⟩ := proofErase_parallel_beta_replay hΓ hx Px
    have hb₁ := (beta_eq hΓA hb Rb.toCompute.to_beta).hasType.2
    have hx₁ := (beta_eq hΓ hx Rx.toCompute.to_beta).hasType.2
    obtain ⟨A', b', HE, _, RB⟩ := RF.lam_inv_typed htarget hsubst htargetHead hΓ hA rfl
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj HE
    have RB : ScopedCompute Target (proofEraseCtx (A :: Γ)) bBeta bs := RB
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x₁) (A₀ := A)).substEq hΓA hx₁
    have RI := RB.subst hsubst (ContextSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓA hx₁))
    have RI : ScopedCompute Target (proofEraseCtx Γ) (bBeta.inst xBeta) (bs.inst xBeta) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Ex] using RI
    obtain ⟨b₂, HB, Eb₂⟩ := proofErase_scoped_compute_realize htarget hΓA hb₁ rfl Eb RB
    have RX' := inst_argument hsubst hΓA HB.hasType.2 hx₁ (Ex.symm ▸ RX)
    rw [Eb₂, Ex] at RX'
    exact ⟨_, .beta PB PX, RI.trans RX'⟩

private theorem compute_parallel_aux
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourceHead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargetHead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextSubstitution Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hprimitive : ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ e T → Source (proofEraseCtx Γ) (proofErase Γ e) out →
      BetaPar (proofErase Γ e) reduced →
      ∃ shared, BetaPar out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (R : ScopedCompute Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (P : BetaPar source reduced) :
    ∃ shared, BetaPar out shared ∧ ScopedCompute Target Δ reduced shared := by
  induction R generalizing Γ e T reduced with
  | base H =>
    obtain ⟨shared, PB, H⟩ := hprimitive hΓ ht (EΓ.symm ▸ Ee.symm ▸ H) (Ee.symm ▸ P)
    exact ⟨shared, PB, EΓ ▸ H⟩
  | beta R =>
    obtain ⟨shared, PB, RB⟩ := proofErase_parallel_beta_strip hΓ ht (Ee.symm ▸ R) (Ee.symm ▸ P)
    exact ⟨shared, PB, .beta RB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨shared, PB, RS⟩ := ih₁ hΓ ht EΓ Ee P
    obtain ⟨e₁, HE, EE⟩ := proofErase_scoped_compute_realize
      hsource hΓ ht EΓ Ee R₁
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
      have H := parallel_app_beta hsourceHead htarget htargetHead hsubst hΓ hA hb hxA RF'
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
      have SB₀ : ScopedCompute Target (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b₁) bs := by
        simpa only [proofEraseCtx, EΓ, EA, E₂] using SB
      have SB' := SB₀.defeqCtx hsubst hΓ
        (.succ .zero (beta_eq hΓ hA HA.toCompute.to_beta))
      exact ⟨_, .lam QA QB, .lam SA (by simpa only [proofEraseCtx, EΓ, E₁, E₂] using SB')⟩
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
      have SB₀ : ScopedCompute Target (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b₁) bs := by
        simpa only [proofEraseCtx, EΓ, EA, E₂] using SB
      have SB' := SB₀.defeqCtx hsubst hΓ
        (.succ .zero (beta_eq hΓ hA HA.toCompute.to_beta))
      exact ⟨_, .forallE QA QB, .forallE SA (by simpa only [proofEraseCtx, EΓ, E₁, E₂] using SB')⟩

/-- Typed primitive parallel squares lift to full compatible computation in
an independently sound target relation closed under interpreted substitution.
The target residuals need no beta-stability or confluence hypothesis. -/
theorem proofErase_scoped_parallel_beta_strip_to
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourceHead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargetHead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextSubstitution Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hprimitive : ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ e T → Source (proofEraseCtx Γ) (proofErase Γ e) out →
      BetaPar (proofErase Γ e) reduced →
      ∃ shared, BetaPar out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared :=
  compute_parallel_aux hsource hsourceHead htarget htargetHead hsubst hprimitive
    R hΓ ht rfl rfl P

end Lean4Lean.VEnv.Strengthening
