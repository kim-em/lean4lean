import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelCore

/-! # Exact recovered carriers after universe variation

Two independently varied recoveries need not initially select the same raw type.
Explicit universe conversion aligns one output with the other, preserving the
original recovered-carrier comparison judgment. The target carrier guard follows
from full joint transport, including function and record guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private recovery_context compute_context oracle_cons_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJointVariants
open private native_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecoveryVariants
variable [Params]

private theorem infer_recovered (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierRecoveredCompare Step Δ false sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b) : env.IsDefEq univs Γ a b A := by
  have HH := proofErase_carrier_recovered_compare_descend hstep hΓ hΓ (Ctx.LiftN.zero []) rfl ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Ea, Eb] using H)
  exact (HH.2 rfl hna hnb).of_l henv hΓ ha

/-- Independently simulated native recoveries regain a literal common carrier
by a finite path of explicit universe steps. The existing recovered constructor
is retained, and its full carrier guard is transported to the selected output. -/
theorem proofErase_carrier_aligned_recovered_node_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (RA : ScopedTypeRecovery Step Δ sa α) (RB : ScopedTypeRecovery Step Δ sb α)
    (HC : ComputedJointCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    CarrierRecoveredCompare Step (proofEraseCtx Γ') mode sa sb := by
  have hΓ' := (W.symm henv.ordered).isType
  obtain ⟨A₀, ha₀, EA₀⟩ := native_type hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
  have hb₀ := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha₀)
  obtain ⟨α', RA', VA⟩ := recovery_context hstep hsim RA hΓ ha EΓ Ea W HO
  obtain ⟨β', RB', VB⟩ := recovery_context hstep hsim RB hΓ hb EΓ Eb W HO
  have Ea' := (proofErase_defeqCtx hΓ W ha).symm.trans Ea
  obtain ⟨A', ha', EA'⟩ := native_type hstep hΓ' (ha.defeqDFC henv W)
    (by simpa only [Ea'] using RA')
  obtain ⟨_, hA'⟩ := ha'.isType henv hΓ'
  have EA's := (proofErase_defeqCtx hΓ' (W.symm henv.ordered) hA').symm.trans EA'
  have HAB := ha₀.uniqU henv hΓ (ha'.defeqDFC henv (W.symm henv.ordered))
  have HC' := HC.structural_variant hstep hctx hsim hΓ ha₀ hb₀ EΓ EA₀ Ea Eb W HO HAB
    (by simpa only [EA's] using VA)
  have RL := (proofErase_carrier_aligned_variant_level_compute
    (by simpa only [EA'] using VB.symm.trans VA) hΓ' hA').scoped (Δ := proofEraseCtx Γ') hlevel
  exact .recovered RA' (RB'.convert (by simpa only [EA'] using RL)) (by simpa only [EA's] using HC')

/-- The whole recovered-carrier comparison language transports through equal
actual contexts with structural universe variants. Universe conversion repairs
the exact-common-carrier requirement of recovered nodes. -/
theorem ProofShape.CarrierRecoveredCompare.structural_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    CarrierRecoveredCompare Step (proofEraseCtx Γ') mode sa sb := by
  induction H generalizing Γ Γ' a b A with
  | base H => exact .base (H.structural_variant hstep hctx hsim hΓ ha hb EΓ Ea Eb W HO)
  | recovered RA RB HC =>
    exact proofErase_carrier_aligned_recovered_node_context hstep hctx hsim hlevel RA RB HC
      hΓ ha hb EΓ Ea Eb W HO
  | app HF HX ihf ihx =>
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_recovered hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO) (ihx hΓ hx hy' EΓ Ex Ey W HO)
  | proj HM ihm =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_recovered hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W HO)
  | lam HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply CarrierRecoveredCompare.lam (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := infer_recovered hstep HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := infer_recovered hstep HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    apply CarrierRecoveredCompare.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO))
  | compute Ra Rb HC ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (compute_context hctx hΓ ha W HO EΓ Ea Ra)
      (compute_context hctx hΓ hb W HO EΓ Eb Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W HO)
  | symm HC ih =>
    exact .symm (ih hΓ hb ha EΓ Eb Ea W HO)

/-- The level-extended concrete core discharges every interface needed by
recovered comparison context transport. This is a closed theorem about the
original recovered-carrier judgment, not a replacement comparison language. -/
theorem proofErase_carrier_aligned_level_core_recovered_context
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierRecoveredCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ') mode
      (proofErase Γ' a) (proofErase Γ' b) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := fun _ => ErasedLevelCore D) hstep hΓ hΓ' HO
  have H' := H.structural_context hstep structuralVariantComputeContext_level_core
    (structuralVariantCompute_level_core hs hlevels hcon) (fun H => .base (.inr H)) hΓ ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at H'

end Lean4Lean.VEnv.Strengthening
