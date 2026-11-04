import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredGuardTransport

/-! # Recovered singleton guards through common native images

Independent native outputs are aligned by typed core confluence. The carrier
guard follows the resulting forward carrier path. This transports the complete
recovered-family checker without exact native images.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private inferred from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRecoveredTransport
variable [Params] {hq : QuotRegistered env}

/-- Two substituted native outputs meet by forward core computation, and the
full dependent carrier guard moves to that shared result. -/
theorem recovered_node_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images hq Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (RA : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ a) α)
    (RB : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ b) α)
    (HC : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ) α
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (fun _ => Step hq) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  obtain ⟨T, haT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ha RA
  have hbT := hb.defeqU_r henv W.wf (ha.uniqU henv W.wf haT)
  obtain ⟨_, hT⟩ := haT.isType henv W.wf
  have ET' : proofErase Γ₀ (T.subst σ) = α.subst τ := by
    rw [proofErase_subst_with hΓ₀ W hT ES, ET]
  obtain ⟨left, RAL, RαL⟩ := recovery_subst hcon RA hΓ₀ W ES ha rfl rfl HI
  obtain ⟨right, RBR, RαR⟩ := recovery_subst hcon RB hΓ₀ W ES hb rfl rfl HI
  obtain ⟨shared, RL, RR⟩ := confluent hq hcon hΓ₀ (hT.subst henv.orderedStrong W hΓ₀)
    (ET' ▸ RαL) (ET' ▸ RαR)
  have HC' := carrier_subst hcon hΓ₀ W ES HI haT hbT (by simpa only [ET] using HC)
  have HS := computed_carrier_compute_forward hq hcon hΓ₀
    (haT.subst henv.orderedStrong W hΓ₀) (hbT.subst henv.orderedStrong W hΓ₀) HC'
    (ET' ▸ RαL.trans RL)
  rw [← proofErase_subst_with hΓ₀ W ha ES] at RAL
  rw [← proofErase_subst_with hΓ₀ W hb ES] at RBR
  exact .recovered (RAL.convert (RL.scoped (fun H => .base H)))
    (RBR.convert (RR.scoped (fun H => .base H))) HS

/-- The full recovered-family checker substitutes through common native
images, including its recovered nodes and arbitrary computed subcomparisons. -/
theorem recovered_transport
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : CarrierRecoveredCompare (fun _ => Step hq) Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ImageSubstitution hq Δ Δ' τ) :
    CarrierRecoveredCompare (fun _ => Step hq) Δ' mode (sa.subst τ) (sb.subst τ) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  induction H generalizing Γ a b A Δ' τ with
  | base H => exact .base (transport hcon H hΓ ha hb EΓ Ea Eb W)
  | @recovered Δ a₀ α b₀ mode RA RB H =>
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have HH := recovered_node_subst (mode := mode) hcon hΓ₀ WS ES HI ha hb
      (by simpa only [EΓ, Ea] using RA) (by simpa only [EΓ, Eb] using RB)
      (by simpa only [EΓ, Ea, Eb] using H)
    simpa only [proofErase_subst_with hΓ₀ WS ha ES, proofErase_subst_with hΓ₀ WS hb ES,
      EΓ₀, Ea, Eb] using HH
  | app HF HX ihf ihx =>
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := inferred hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | proj HM ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := inferred hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ih hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W)
      (ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' W.cons)
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨v, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := inferred hstep HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, v, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := inferred hstep HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    exact .forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' W.cons)
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .compute (RA.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation) (RB.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm H ih => exact .symm (ih hΓ hb ha EΓ Eb Ea W)


/-- Joined native images discharge both the computed and recovered recursive
guard interfaces, including extension under generated dependent telescopes. -/
theorem recovered_guard_substitution
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    RecoveredGuardSubstitution (fun _ => Step hq) (fun _ => Step hq) (ImageSubstitution hq) := by
  refine ⟨⟨(fun W => W.interpretation), (fun W => W.cons), (fun H => transport hcon H)⟩, ?_⟩
  intro Δ mode sa sb H Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
  exact recovered_transport hcon H hΓ ha hb EΓ Ea Eb W

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
