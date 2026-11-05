import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGenericNestedEta

/-! # Generic computation followed by beta cleanup in a type context

The fork is formed before substitution. Its computed branch may beta-reduce
after the actual value is supplied. Type-only fork joining then compares the
original observation with the cleaned-up observation, without native recovery
of the actual value. The fork-joining premise remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Type-only forks transport a generic computation into an arbitrary typed
type context, allowing an actual beta cleanup after substitution. This is
conditional on fork joining; neither native coverage nor exact substitution of
the primitive computation is assumed for the supplied value. -/
theorem type_forks_generic_context_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ha : env.HasType univs Γ a A)
    (hg : env.HasType univs (A :: Γ) generic A.lift)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (.bvar 0) (proofErase (A :: Γ) generic))
    (HB : VExpr.BetaRed (generic.inst a) b) : TypeContextJoin D Γ A a b := by
  intro C v hC
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  let τ : ProofShape.Subst := fun i => match i with
    | 0 => proofErase (A :: Γ) generic
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
  obtain ⟨ht, RL, RR⟩ := type_instantiation_compute_peak hΓ hA hC ha RC
  have E : ((proofErase (A :: Γ) C).subst τ).inst (proofErase Γ a) =
      (proofErase (A :: Γ) C).inst (proofErase Γ (generic.inst a)) := by
    rw [proofErase_instN hΓA ha Ctx.InstN.zero hg]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
    congr 1
    funext i
    cases i <;> rfl
  have hga : env.HasType univs Γ (generic.inst a) A := by
    simpa only [VExpr.inst_lift] using hg.instN henv.ordered Ctx.InstN.zero ha
  rw [E, ← proofErase_instN hΓA hga Ctx.InstN.zero hC] at RR
  have RB := proofErase_static_structure_compute_inst_argument heq hs hΓA hC hga
    (ScopedCompute.beta (Step := ErasedStaticStructureEtaExpansionUnion D)
      (proofErase_beta_forward hΓ hga HB))
  have hb := (beta_eq hΓ hga HB).hasType.2
  rw [← proofErase_instN hΓA hb Ctx.InstN.zero hC] at RB
  exact HF hΓ ht RL (RR.trans RB)

/-- Function eta below a lambda is observed in every typed type context,
assuming only type-level fork joining. The original body and its abstraction
need no native certificates. Abstracting the body into a generic function
supplies the two native Pi layers used before substitution. This closes this
binder case for eta, not arbitrary lambda-body congruence. -/
theorem type_forks_contextual_eta_under_lambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs (A :: Γ) f (.forallE B C)) :
    TypeContextJoin D Γ (.forallE A (.forallE B C))
      (.lam A f) (.lam A (.lam B (.app f.lift (.bvar 0)))) := by
  intro K z hK
  have hLam := HasType.lam hA hf
  obtain ⟨w, hG⟩ := hLam.isType henv hΓ
  have hΓG : OnCtx (.forallE A (.forallE B C) :: Γ) (env.IsType univs) := ⟨hΓ, w, hG⟩
  have HE := (IsDefEq.lamDF hA (IsDefEq.eta hf)).symm
  classical
  by_cases hp : IsProof Γ (.lam A f)
  · exact TypeContextJoin.of_erasure_eq hΓG hLam HE.hasType.2
      ((proofErase_eq_proof.2 hp).trans (proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)).symm) hK
  have hw : ¬ w ≈ .zero := by
    intro hw
    have hG0 := (IsDefEq.sortDF (hG.sort_r henv hΓ) (by trivial) hw).defeq hG
    exact hp ⟨_, hLam, hG0⟩
  have hn : ¬ IsProof (.forallE A (.forallE B C) :: Γ) (.bvar 0) :=
    fun hp => hw ((isProof_fresh_iff hΓ hG).1 hp)
  have RG := static_structure_generic_nested_eta (D := D) hΓ hG
  rw [show proofErase (.forallE A (.forallE B C) :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at RG
  exact type_forks_generic_context_beta heq hs HF hΓ hG hLam
    (generic_nested_eta_typing hΓ hG) RG (generic_nested_eta_inst_beta A B f) hK

end Lean4Lean.VEnv.Strengthening
