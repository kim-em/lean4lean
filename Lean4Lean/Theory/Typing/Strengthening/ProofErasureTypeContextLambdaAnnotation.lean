import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextJoin

/-! # Changing lambda annotations inside type contexts

A generic eta expansion uses the assigned function domain. Substituting a literal
lambda and contracting beta restores its body at that chosen domain. Type-only
fork joining therefore suffices to change a lambda annotation in an arbitrary
typed type context. No native certificate for the lambda is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- The still-open fork-joining premise restricted to roots that are typed types.
This definition asserts neither confluence nor completeness for ordinary equality.
In particular it does not supply data joins for the bodies of lambdas. -/
def TypeForkJoin (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ T (.sort u) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) left →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) right →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared

/-- A type-valued beta fork is one of the forks requested by TypeForkJoin. -/
theorem TypeForkJoin.instantiation_join (HF : TypeForkJoin D) : TypeInstantiationJoin D :=
  type_instantiation_join_of_type_forks HF

/-- A literal lambda can be observed at the domain of its assigned Pi type,
regardless of its written domain. Its entire body is preserved. Ordinary typing
of the original lambda supplies typing of the reannotated one by eta and beta;
no native evidence, computational domain join or generic-domain typing is needed.
The only open premise is type-only fork joining. -/
theorem TypeForkJoin.contextual_lambda_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam L b) (.forallE A B)) :
    env.HasType univs Γ (.lam A b) (.forallE A B) ∧
      TypeContextJoin D Γ (.forallE A B) (.lam L b) (.lam A b) := by
  have heta := (IsDefEq.eta hf).hasType.1
  have RB : VExpr.BetaRed (.lam A (.app (VExpr.lam L b).lift (.bvar 0))) (.lam A b) := by
    apply VExpr.BetaRed.lam .refl
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
      (VExpr.BetaRed.beta (A := L.lift) (b := b.liftN 1 1) (a := .bvar 0))
  have hg := (beta_eq hΓ heta RB).hasType.2
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, u, hPi⟩
  have Hη : TypeContextJoin D Γ (.forallE A B) (.lam L b)
      (.lam A (.app (VExpr.lam L b).lift (.bvar 0))) :=
    fun hC => TypeInstantiationJoin.contextual_function_eta heq hs HF.instantiation_join hΓ hf hC
  have Hβ : TypeContextJoin D Γ (.forallE A B)
      (.lam A (.app (VExpr.lam L b).lift (.bvar 0))) (.lam A b) :=
    TypeContextJoin.of_compute_join heq hs hΓPi heta hg
    (ScopedCompute.beta (Step := ErasedStaticStructureEtaExpansionUnion D)
      (proofErase_beta_forward hΓ heta RB)) ScopedCompute.refl
  exact ⟨hg, TypeContextJoin.trans HF hΓ heta Hη Hβ⟩

/-- For type-valued endpoints, the identity type context extracts a direct
computational join. This extraction does not apply to arbitrary data endpoints. -/
theorem TypeContextJoin.type_join (H : TypeContextJoin D Γ (.sort u) a b) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ a) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ b) shared := by
  have hC : env.HasType univs (VExpr.sort u :: Γ) (.bvar 0) (.sort u) := .bvar .zero
  simpa only [VExpr.inst, VExpr.instVar_zero] using H hC

/-- Contextual observations of type-valued bodies suffice for contextual
lambda congruence, even when the two lambdas are written with different domains.
Both are assigned the displayed Pi type. Generic eta first aligns their domains,
the identity type context extracts the body's join, and compatible lambda
computation lifts it. Only type-rooted fork joining is assumed. -/
theorem TypeForkJoin.contextual_family_lambdas
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam L b) (.forallE A (.sort v)))
    (hg : env.HasType univs Γ (.lam M c) (.forallE A (.sort v)))
    (HB : TypeContextJoin D (A :: Γ) (.sort v) b c) :
    TypeContextJoin D Γ (.forallE A (.sort v)) (.lam L b) (.lam M c) := by
  obtain ⟨hfA, Hf⟩ := HF.contextual_lambda_annotation heq hs hΓ hf
  obtain ⟨hgA, Hg⟩ := HF.contextual_lambda_annotation heq hs hΓ hg
  obtain ⟨shared, Rb, Rc⟩ := TypeContextJoin.type_join HB
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  have hΓPi : OnCtx (.forallE A (.sort v) :: Γ) (env.IsType univs) := ⟨hΓ, u, hPi⟩
  have Ef : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hfA)
  have Eg : proofErase Γ (.lam A c) = .lam (proofErase Γ A) (proofErase (A :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hgA)
  have Rf : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (.lam (proofErase Γ A) shared) := by
    rw [Ef]
    exact .lam .refl (by simpa only [proofEraseCtx] using Rb)
  have Rg : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A c)) (.lam (proofErase Γ A) shared) := by
    rw [Eg]
    exact .lam .refl (by simpa only [proofEraseCtx] using Rc)
  have Hfg : TypeContextJoin D Γ (.forallE A (.sort v)) (.lam A b) (.lam A c) :=
    TypeContextJoin.of_compute_join heq hs hΓPi hfA hgA Rf Rg
  intro C w hC
  exact TypeContextJoin.trans HF hΓ hfA Hf
    (TypeContextJoin.trans HF hΓ hgA Hfg (TypeContextJoin.symm Hg)) hC

end Lean4Lean.VEnv.Strengthening
