import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaDiamond
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaLambdaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRetainedInstantiation

/-! # Exact native recovery through a beta cut with a native argument

Literal Pi-to-Pi readout preserves the exact selected codomain, even through
nested structure eta. The body therefore recovers that codomain before
substitution. A retained argument needs native recovery only at the lambda's
written domain; proof arguments require none. All final type conversions remain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full structure/function-eta recovery instantiates at a retained native
argument. Finiteness supplies independent body and image stage bounds; proof
arguments impose no native obligation. -/
theorem static_structure_union_recovery_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (hb : env.HasType univs (A :: Γ) b B)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
  classical
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have HI : ∃ k, ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A) := by
    by_cases hp : IsProof Γ x
    · exact ⟨0, fun hn => (hn hp).elim⟩
    · obtain ⟨k, R⟩ := (HR hp).finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
        (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
      exact ⟨k, fun _ => R⟩
  obtain ⟨k, HI⟩ := HI
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have R := StaticStructureEtaNativeSubstitution.recovery heq hs RN hΓA hb rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ W ES
      (NativeImageTransport.Images.inst_retained hΓ hx HI))
  rw [← proofErase_subst_with hΓ W hb ES] at R
  have R' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D (n+k)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using R
  exact R'.mono (fun H => ⟨n+k, H⟩)

/-- Every native type selected for a beta redex survives contraction exactly,
provided its retained argument recovers the lambda's written domain. The
lambda's selected native Pi may have different computed components, and all
post-application type conversions are retained. No confluence is assumed. -/
theorem static_structure_root_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hn : ¬ IsProof Γ (.app (.lam A b) x) := fun H => RN.ne_proof (proofErase_eq_proof.2 H)
  have hnf := not_isProof_fn hΓ (HasType.lam hA hb) hx hn
  rw [show proofErase Γ (.app (.lam A b) x) = .app _ _ from if_neg hn,
    show proofErase Γ (.lam A b) = .lam _ _ from if_neg hnf] at RN
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  obtain ⟨C, RB, RP⟩ := RF.lam_compute
  have RB' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) C := by
    simpa only [proofEraseCtx] using RB
  obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb RB'
  obtain ⟨v, hC⟩ := hbC.isType henv hΓA
  rw [← EC] at RP
  obtain ⟨_, _, _, _, _, _, _, RCbody⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hC RP
  rw [EC] at RCbody
  exact (static_structure_union_recovery_inst heq hs hΓ hx HR hb (RB'.convert RCbody)).convert RC

/-- Beta contraction at a proof argument preserves every selected native type
in the enriched language without any argument-recovery premise. -/
theorem static_structure_proof_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hproof : IsProof Γ x)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out :=
  static_structure_root_beta_native_recovery heq hs hΓ hA hb hx (fun hn => (hn hproof).elim) RN

end Lean4Lean.VEnv.Strengthening
