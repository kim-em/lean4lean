import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperNativeOrigin

/-! # Original native header histories through function eta

The function under the new eta binder is a lift of the original source. Its
selected native certificate descends, retaining a path from the original
header. Pi readout supplies the codomain path in the original binder context;
backward context transport pulls the eta body's conversion tail into that same
context. The two paths then assemble the complete new native Pi history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params] {D : PureObservation.Definitions}

/-- Every native selection starts at the same raw header. This records directed
ancestry, not exact recovery of an arbitrary assigned type. -/
def NativeHeaderHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (header source : ProofShape) : Prop :=
  ∀ {out}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
    (proofEraseCtx Γ) source out →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) header out

/-- Native function eta preserves the original typed Pi header's complete
history, including changed guard domains, proof-erased arguments, arbitrary
body recovery choices and all conversion tails. No joining hypothesis occurs. -/
theorem NativeHeaderHistory.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : NativeHeaderHistory D Γ (proofErase Γ (.forallE A B)) (proofErase Γ f))
    (RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) target) :
    NativeHeaderHistory D Γ (proofErase Γ (.forallE A B)) target := by
  intro out RN
  cases RE with
  | @intro X Y w RG SD =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) :=
      erased_static_structure_eta_expansion_union_descent heq hs
    obtain ⟨A', B', hf', EA', EB'⟩ := proofErase_scoped_recovered_pi_descend
      hstep hΓ hΓ (Ctx.LiftN.zero []) hf
      (by simpa only [List.length_nil, ProofShape.liftN_zero] using RG)
    simp only [List.length_nil, ProofShape.liftN_zero] at EA' EB'
    obtain ⟨_, hPi'⟩ := hf'.isType henv hΓ
    obtain ⟨⟨_, hA'⟩, _, _⟩ := hPi'.forallE_inv henv
    have hA' : env.HasType univs Γ A' (.sort w) := by
      have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A').liftN 0) w := by
        simpa only [ProofShape.liftN_zero, EA'] using SD
      exact SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hA'
    have hΓ' : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, w, hA'⟩
    have EP : proofErase Γ (.forallE A B) =
        .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))
    have RGpath := H RG
    rw [EP] at RGpath
    obtain ⟨_, _, _, _, _, _, RA, _⟩ :=
      proofErase_static_structure_union_pi_components heq hs hΓ hA hB RGpath
    rw [← EA'] at RA
    obtain ⟨HAA', _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HAA' := HAA'.choose_spec.toU.of_l henv hΓ hA
    obtain ⟨C, RB, RP⟩ := RN.lam_compute
    rw [← EA'] at RB
    obtain ⟨L, M, RF, RC⟩ := RB.app_origin
    obtain ⟨F, hfF, RNF, EF⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
      hΓ hΓ' Ctx.LiftN.one hf (by rfl) RF
    obtain ⟨L₀, M₀, EF₀, EL, EM⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A₀, B₀, rfl, _, EA₀, EB₀⟩ := erase_forallE_inv EF₀
    have RP₀ := H RNF
    rw [EP, EF₀] at RP₀
    obtain ⟨_, _, _, _, _, _, _, RB₀⟩ :=
      proofErase_static_structure_union_pi_components heq hs hΓ hA hB RP₀
    obtain ⟨_, hPi₀⟩ := hfF.isType henv hΓ
    obtain ⟨⟨z, hA₀⟩, q, hB₀⟩ := hPi₀.forallE_inv henv
    have hΓ₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, z, hA₀⟩
    obtain ⟨H₀', _⟩ := (hfF.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A' :: Γ) := .succ .zero H₀'.choose_spec
    have hB₀' := hB₀.defeqDFC henv HC
    have EB₀' := proofErase_defeqCtx hΓ₀ HC hB₀
    have EI : M.inst (etaArgument w) = proofErase (A' :: Γ) B₀ := by
      rw [← EM, ← EB₀, EB₀']
      exact proofErase_eta_inst hΓ hA' hB₀'
    rw [EI] at RC
    have RC' := proofErase_static_structure_union_compute_backward_context
      heq hs hΓ HAA' RA hB₀' RC
    have EBack := proofErase_defeqCtx hΓ' (IsDefEqCtx.succ .zero HAA'.symm) hB₀'
    rw [← EBack, ← EB₀', EB₀] at RC'
    have RH : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) (.forallE X C) := by
      rw [EP]
      exact .forallE (EA' ▸ RA) (RB₀.trans RC')
    exact RH.trans RP

end Lean4Lean.VEnv.Strengthening
