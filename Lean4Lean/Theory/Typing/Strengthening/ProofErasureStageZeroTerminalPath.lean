import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroPiReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalImage

/-! # Typed terminal recovery paths through the expansion base

Every node retains its actual assigned type. This permits Pi readout through
constant expansions when an application consumes a lambda path. The path rank
counts recovery constructors, rather than the size of the computation history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Stage-zero primitives admit ordinary typed substitution without native
image hypotheses. Constant expansion uses typing to retain its non-proof side
condition; the other two primitive classes substitute syntactically. -/
theorem stage_zero_primitive_substitution :
    ErasedPrimitiveSubstitutionTo (ErasedStaticStructureEtaExpansionStage D 0)
      (ErasedStaticStructureEtaExpansionStage D 0) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W ES ht H
  rw [proofErase_subst_with hΓ₀ W ht ES]
  rcases H with (H | H) | H
  · exact .base (.inl (.inl (erased_iota_primitive_subst H)))
  · exact .base (.inl (.inr H.subst))
  · exact .base (.inr (H.subst_typed W.wf ht rfl rfl (ContextSubstitution.of_typed hΓ₀ W ES)))

/-- A recovery path ending in an actual terminal image, with the exact
assigned type retained at every node. Conversion carries both ordinary type
equality and a stage-zero forward computation. This is not universal coverage
of native recovery or of arbitrary substitution images. -/
inductive StageZeroTerminalPath (D : PureObservation.Definitions) :
    List VExpr → VExpr → VExpr → Nat → Prop where
  | terminal : TerminalImage Γ e → env.HasType univs Γ e T → StageZeroTerminalPath D Γ e T 0
  | lam : env.HasType univs Γ A (.sort u) → StageZeroTerminalPath D (A :: Γ) b B n →
      StageZeroTerminalPath D Γ (.lam A b) (.forallE A B) (n + 1)
  | app : StageZeroTerminalPath D Γ f (.forallE A B) n → env.HasType univs Γ a A →
      StageZeroTerminalPath D Γ (.app f a) (B.inst a) (n + 1)
  | convert : StageZeroTerminalPath D Γ e T n → env.IsDefEq univs Γ T U (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ T) (proofErase Γ U) → StageZeroTerminalPath D Γ e U (n + 1)

/-- Each path includes an actual typing at its selected output. -/
theorem StageZeroTerminalPath.hasType (H : StageZeroTerminalPath D Γ e T n) :
    env.HasType univs Γ e T := by
  induction H with
  | terminal _ ht => exact ht
  | lam hA _ ih => exact .lam hA ih
  | app _ ha ih => exact .app ih ha
  | convert _ HE _ ih => exact HE.defeq ih

/-- Ordinary typed substitution preserves the path rank and its exact actual
assigned type, including conversion histories through constant expansions. -/
theorem StageZeroTerminalPath.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StageZeroTerminalPath D Γ e T n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) :
    StageZeroTerminalPath D Γ₀ (e.subst σ) (T.subst σ) n := by
  induction H generalizing Γ₀ σ τ with
  | terminal HT ht => exact .terminal (HT.subst hΓ₀ W) (ht.subst henv.orderedStrong W hΓ₀)
  | lam hA H ih =>
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    exact .lam hA' (ih ⟨hΓ₀, _, hA'⟩ (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA))
  | app H ha ih =>
    simpa only [VExpr.subst, VExpr.subst_inst] using
      StageZeroTerminalPath.app (ih hΓ₀ W ES) (ha.subst henv.orderedStrong W hΓ₀)
  | convert H HE R ih =>
    apply StageZeroTerminalPath.convert (ih hΓ₀ W ES) (HE.subst henv.orderedStrong W hΓ₀)
    have RR := proofErase_scoped_compute_subst_typed
      (erased_static_structure_eta_expansion_stage_descent heq hs 0)
      stage_zero_primitive_substitution hΓ₀ W ES HE.hasType.1 R
    simpa only [proofErase_subst_with hΓ₀ W HE.hasType.2 ES] using RR

/-- A typed terminal path either remains terminal or beta-exposes a lambda
whose body has a strictly smaller path. The exact selected type is reached
from that lambda's written Pi at stage zero. This handles applications by
instantiating a smaller body path and its retained codomain computation. -/
theorem StageZeroTerminalPath.expose
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StageZeroTerminalPath D Γ e T n) (hΓ : OnCtx Γ (env.IsType univs)) :
    TerminalImage Γ e ∨ ∃ A b B m u, m < n ∧ env.HasType univs Γ A (.sort u) ∧
      StageZeroTerminalPath D (A :: Γ) b B m ∧ VExpr.BetaRed e (.lam A b) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ T) := by
  induction n using Nat.strongRecOn generalizing Γ e T with
  | ind n ih =>
    cases H with
    | terminal HT _ => exact .inl HT
    | lam hA HB =>
      apply Or.inr
      refine ⟨_, _, _, _, _, by omega, hA, HB, .refl, ?_⟩
      have hPi := (HasType.lam hA HB.hasType).isType henv hΓ |>.choose_spec
      rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
      exact .refl
    | @convert Γ e T k U u H HE R =>
      rcases ih k (by omega) H hΓ with HT | ⟨A, b, B, m, v, hm, hA, HB, RB, RP⟩
      · exact .inl HT
      · exact .inr ⟨A, b, B, m, v, by omega, hA, HB, RB, RP.trans R⟩
    | @app Γ f C E k a HF ha =>
      rcases ih k (by omega) HF hΓ with HT | ⟨A, b, B, m, u, hm, hA, HB, RF, RP⟩
      · exact (HT.not_function hΓ HF.hasType).elim
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have hF := HF.hasType
      have hEq := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hF
      have hLam := HasType.lam hA HB.hasType
      have hF' := (hEq.toU.of_r henv hΓ hLam).hasType.1
      have haA := argument_at_displayed_domain hΓ hF hF' ha
      obtain ⟨v, hB⟩ := HB.hasType.isType henv hΓA
      obtain ⟨w, hCE⟩ := hF.isType henv hΓ
      rw [show proofErase Γ (.forallE C E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hCE)] at RP
      obtain ⟨_, _, _, _, _, _, _, RBody⟩ := proofErase_stage_zero_pi_components heq hs hΓ hA hB RP
      have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA haA
      have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one a)
          (ProofShape.Subst.one (proofErase Γ a)) := erasedSubstAgreement_one hΓA haA
      have HInst : StageZeroTerminalPath D Γ (b.inst a) (B.inst a) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst heq hs hΓ W ES
      have RInst := proofErase_scoped_compute_subst_typed
        (erased_static_structure_eta_expansion_stage_descent heq hs 0)
        stage_zero_primitive_substitution hΓ W ES hB RBody
      obtain ⟨⟨q, hC⟩, r, hE⟩ := hCE.forallE_inv henv
      have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, q, hC⟩
      have RInst' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
          (proofErase Γ (B.inst a)) (proofErase Γ (E.inst a)) := by
        rw [proofErase_instN hΓC ha Ctx.InstN.zero hE]
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using RInst
      have RB : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have hEq' := RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ (HasType.app hF ha)
      have hBInst : env.HasType univs Γ (B.inst a) (.sort v) := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, VExpr.subst] using hB.subst henv.orderedStrong W hΓ
      have HT := (HInst.hasType.uniqU henv hΓ hEq'.hasType.2).of_l henv hΓ hBInst
      rcases ih (m + 1) (by omega) (HInst.convert HT RInst') hΓ with
        HTerm | ⟨A', b', B', j, v', hj, hA', HB', RF', RP'⟩
      · exact .inl (HTerm.back hΓ hEq')
      · exact .inr ⟨A', b', B', j, v', by omega, hA', HB', RB.trans RF', RP'⟩

/-- A retained function with a typed terminal path computes to a lambda at
its exact selected domain. The terminal branch is excluded by actual function
typing; Pi readout supplies the annotation computation in the other branch. -/
theorem StageZeroTerminalPath.selected_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : StageZeroTerminalPath D Γ f T n) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (ET : proofErase Γ T = .forallE X Y) :
    ∃ body, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam X body) := by
  rcases H.expose heq hs hΓ with HT | ⟨A, b, B, m, u, _, hA, HB, RF, RP⟩
  · exact (HT.not_function hΓ hf).elim
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨v, hB⟩ := HB.hasType.isType henv hΓA
  rw [ET] at RP
  obtain ⟨_, _, _, _, _, _, RA, _⟩ := proofErase_stage_zero_pi_components heq hs hΓ hA hB RP
  have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf RF
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨_, (ScopedCompute.beta RB).trans (.lam RA .refl)⟩

end Lean4Lean.VEnv.Strengthening
