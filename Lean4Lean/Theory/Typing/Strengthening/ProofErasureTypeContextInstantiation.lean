import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Generic computations inside arbitrary type contexts

The type-instantiation joining obligation can be applied after a generic
variable computes inside a type context. Thus generic native guards can provide
contextual equality without native coverage of the actual substituted value.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A computation of the generic variable can run through every occurrence in
a typed type context before instantiation. TypeInstantiationJoin then joins its
arbitrary typed instance. The actual substituted value has no native premise.
The computed generic image is a raw shape and may contain the generic variable. -/
theorem TypeInstantiationJoin.generic_type_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hC : env.HasType univs (A :: Γ) C (.sort v)) (ha : env.HasType univs Γ a A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (.bvar 0) generic) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst a)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        ((proofErase (A :: Γ) C).inst (generic.inst (proofErase Γ a))) shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  let τ : ProofShape.Subst := fun i => match i with
    | 0 => generic
    | i+1 => .bvar (i+1)
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have ES : ErasedSubstAgreement (A :: Γ) (A :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn, ProofShape.Subst.id]
  have RC := proofErase_compute_subst_images_of_renaming hrename hΓA
    (Ctx.SubstEq.id henv.ordered hΓA) hC ES (τ := τ) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [ProofShape.subst_id] at RC
  obtain ⟨shared, RL, RR⟩ := HJ hΓ hA hC ha RC
  refine ⟨shared, RL, ?_⟩
  have E : ((proofErase (A :: Γ) C).subst τ).inst (proofErase Γ a) =
      (proofErase (A :: Γ) C).inst (generic.inst (proofErase Γ a)) := by
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
    congr 1
    funext i
    cases i <;> rfl
  exact E ▸ RR

/-- The open type-instantiation join suffices for ordinary function eta inside
any typed type context. Eta is performed on a fresh variable whose declaration
supplies its native guard, then the actual function is substituted. No native
certificate at any type is assumed for that function. Proof functions are
handled by erasure, and proposition-valued input domains remain allowed. -/
theorem TypeInstantiationJoin.contextual_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hC : env.HasType univs (.forallE A B :: Γ) C (.sort v)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst f)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst (.lam A (.app f.lift (.bvar 0))))) shared := by
  obtain ⟨w, hT⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, _⟩ := hT.forallE_inv henv
  have hΓT : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, w, hT⟩
  have heta := (IsDefEq.eta hf).hasType.1
  classical
  by_cases hp : IsProof Γ f
  · have hp' := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    have E : proofErase Γ (C.inst f) = proofErase Γ (C.inst (.lam A (.app f.lift (.bvar 0)))) := by
      rw [proofErase_instN hΓT hf Ctx.InstN.zero hC,
        proofErase_instN hΓT heta Ctx.InstN.zero hC,
        proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact ⟨_, .refl, E ▸ ScopedCompute.refl⟩
  have ET : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hT)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.forallE A B :: Γ)) (.bvar 0)
      (.forallE ((proofErase Γ A).liftN 1) ((proofErase (A :: Γ) B).liftN 1 1)) := by
    simpa only [proofEraseCtx, ET, contextOracle, TypeOracle.cons, ProofShape.liftN] using
      (ScopedTypeRecovery.bvar (Step := ErasedStaticStructureEtaExpansionUnion D)
        (Δ := proofEraseCtx (.forallE A B :: Γ)) (i := 0))
  have SD := DomainSort.of_typed hΓT (hA.weakN henv Ctx.LiftN.one)
  rw [proofErase_liftN hΓ hΓT Ctx.LiftN.one hA] at SD
  have RG := ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RN SD))
  obtain ⟨shared, RL, RR⟩ := TypeInstantiationJoin.generic_type_context heq hs HJ hΓ hT hC hf RG
  have EG : (ProofShape.lam ((proofErase Γ A).liftN 1)
      (.app ((ProofShape.bvar 0).liftN 1) (etaArgument u))).inst (proofErase Γ f) =
      proofErase Γ (.lam A (.app f.lift (.bvar 0))) := by
    rw [proofErase_nativeEtaExpansion hΓ hA hf hp]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, etaArgument_subst]
    rfl
  rw [EG, ← proofErase_instN hΓT heta Ctx.InstN.zero hC] at RR
  exact ⟨shared, RL, RR⟩

end Lean4Lean.VEnv.Strengthening
