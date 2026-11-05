import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerEtaAnnotation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta

/-! # Repairing supplied function eta through the caller

The caller's declared function domain can absorb an eta wrapper with a different
annotation. This gives an actual common reduct without joining the annotations
or recovering the supplied function. Both retained and erased proof inputs are
handled. The argument's outer function type must be retained by the caller.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {x L : ProofShape}

/-- Expand a function argument through its caller, including functions whose
own argument is erased as a proof. The supplied function has no native premise. -/
theorem static_structure_caller_argument_eta_with_proofs
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x)
      (.app f (.lam A (.app (x.liftN 1) (etaArgument v)))) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.lam (.forallE A B) (.app (f.liftN 1) (.bvar 0))) := by
    simpa only [etaArgument, if_neg hu] using
      (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RN SQ)))
  have RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (.forallE A B :: Δ) (.bvar 0) (.forallE (A.liftN 1) (B.liftN 1 1)) := .bvar
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (.forallE A B :: Δ)
      (.bvar 0) (.lam (A.liftN 1) (.app (.bvar 1) (etaArgument v))) := by
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte] using
      (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RX SA)))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RE)) .refl).trans
  have R := ProofShape.BetaRed.beta (A := .forallE A B)
    (b := .app (f.liftN 1) (.lam (A.liftN 1) (.app (.bvar 1) (etaArgument v)))) (a := x)
  apply ScopedCompute.beta
  unfold etaArgument at R ⊢
  by_cases hv : v ≈ .zero <;> simpa only [hv, ↓reduceIte, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.lift,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using R

omit [Params] in
/-- Once the caller supplies the outer eta frame, beta removes an inner eta
frame with any annotation. Both frames use the same proof-erasure mode. -/
theorem caller_eta_absorb_beta (A L x : ProofShape) (v : VLevel) :
    ProofShape.BetaRed (.lam A (.app ((ProofShape.lam L (.app (x.liftN 1) (etaArgument v))).liftN 1) (etaArgument v)))
      (.lam A (.app (x.liftN 1) (etaArgument v))) := by
  apply ProofShape.BetaRed.lam .refl
  change ProofShape.BetaRed (.app (.lam (L.liftN 1) ((ProofShape.app (x.liftN 1) (etaArgument v)).liftN 1 1)) _) _
  have R := ProofShape.BetaRed.beta (A := L.liftN 1)
    (b := (ProofShape.app (x.liftN 1) (etaArgument v)).liftN 1 1) (a := etaArgument v)
  have E : ((ProofShape.app (x.liftN 1) (etaArgument v)).liftN 1 1).inst (etaArgument v) =
      .app (x.liftN 1) (etaArgument v) := by
    unfold etaArgument
    split <;> simp [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.liftN, ProofShape.Subst.one, ProofShape.Subst.cons, liftVar]
    all_goals rw [← ProofShape.liftN_comm x 1 1 0 0 (Nat.zero_le _),
      ProofShape.lift_subst_cons, ProofShape.subst_id]
  rw [E] at R
  exact R

/-- An arbitrary eta annotation on a supplied function is absorbed by the
caller's selected annotation. No path between the two annotations is needed. -/
theorem static_structure_caller_absorbs_argument_eta
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.app f (.lam L (.app (x.liftN 1) (etaArgument v))))
      (.app f (.lam A (.app (x.liftN 1) (etaArgument v)))) :=
  (static_structure_caller_argument_eta_with_proofs RN SQ hu SA).trans
    (.beta (.app .refl (caller_eta_absorb_beta A L x v)))

/-- The call before and after eta expansion of an arbitrary supplied function
has an explicit common reduct. The repair uses the caller's type, not native
coverage of the argument or computational joining of the two domains. -/
theorem static_structure_caller_argument_eta_join
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (.app f (.lam L (.app (x.liftN 1) (etaArgument v)))) shared :=
  ⟨_, static_structure_caller_argument_eta_with_proofs RN SQ hu SA,
    static_structure_caller_absorbs_argument_eta RN SQ hu SA⟩

/-- The caller can replace a literal lambda's annotation while retaining its
entire erased body. Ordinary body typing handles the erased-proof input case;
there is no native certificate or domain-joining premise for that lambda. -/
theorem static_structure_caller_reannotates_lambda
    (hΓ : OnCtx Γ (env.IsType univs))
    (hL : env.HasType univs Γ L₀ (.sort v)) (hb : env.HasType univs (L₀ :: Γ) b T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort (proofEraseCtx Γ) (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: proofEraseCtx Γ) (A.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f (.lam (proofErase Γ L₀) (proofErase (L₀ :: Γ) b)))
      (.app f (.lam A (proofErase (L₀ :: Γ) b))) :=
  (static_structure_caller_argument_eta_with_proofs RN SQ hu SA).trans
    (.beta (.app .refl (proofErase_eta_lambda_beta hΓ hL hb A)))

/-- The generic-function eta/beta peak in a caller has a common reduct even
when the generic function's declared domain differs from the caller's selected
domain. All four paths are explicit. The supplied argument is arbitrary, the
two domains need no computational join, and either proof-erasure mode is allowed.
This solves this eta peak, not arbitrary computations under the generic binder. -/
theorem static_structure_caller_generic_eta_beta_peak
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v)
    (SL : DomainSort (.forallE L M :: Δ) (L.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (.app (.lam (.forallE L M) (.app (f.liftN 1) (.bvar 0))) x) (.app f x) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (.app (.lam (.forallE L M) (.app (f.liftN 1) (.bvar 0))) x)
        (.app f (.lam L (.app (x.liftN 1) (etaArgument v)))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x)
        (.app f (.lam A (.app (x.liftN 1) (etaArgument v)))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (.app f (.lam L (.app (x.liftN 1) (etaArgument v))))
        (.app f (.lam A (.app (x.liftN 1) (etaArgument v)))) := by
  have RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (.forallE L M :: Δ) (.bvar 0) (.forallE (L.liftN 1) (M.liftN 1 1)) := .bvar
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (.forallE L M :: Δ)
      (.bvar 0) (.lam (L.liftN 1) (.app (.bvar 1) (etaArgument v))) := by
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte] using
      (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RG SL)))
  refine ⟨?_, ?_, static_structure_caller_argument_eta_with_proofs RN SQ hu SA,
    static_structure_caller_absorbs_argument_eta RN SQ hu SA⟩
  · have R := ProofShape.BetaRed.beta (A := .forallE L M)
      (b := .app (f.liftN 1) (.bvar 0)) (a := x)
    exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using R)
  · apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RE)) .refl).trans
    apply ScopedCompute.beta
    have R := ProofShape.BetaRed.beta (A := .forallE L M)
      (b := .app (f.liftN 1) (.lam (L.liftN 1) (.app (.bvar 1) (etaArgument v)))) (a := x)
    unfold etaArgument at R ⊢
    by_cases hv : v ≈ .zero <;> simpa only [hv, ↓reduceIte, ProofShape.inst_eq_subst,
      ProofShape.Subst.liftN, ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons,
      ProofShape.Subst.lift, ProofShape.lift_subst_cons, ProofShape.subst_id] using R

/-- If the supplied lambda is already written at the caller's selected
domain, the branch eta-expanded at any other domain returns to the original
call. Its arbitrary typed body is restored exactly, in either proof mode. -/
theorem static_structure_caller_eta_lambda_return
    (hΓ : OnCtx Γ (env.IsType univs))
    (hL : env.HasType univs Γ L₀ (.sort v)) (hb : env.HasType univs (L₀ :: Γ) b T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (.forallE (.forallE (proofErase Γ L₀) B) C))
    (SQ : DomainSort (proofEraseCtx Γ) (.forallE (proofErase Γ L₀) B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE (proofErase Γ L₀) B :: proofEraseCtx Γ)
      ((proofErase Γ L₀).liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f (.lam A (.app
        ((ProofShape.lam (proofErase Γ L₀) (proofErase (L₀ :: Γ) b)).liftN 1) (etaArgument v))))
      (.app f (.lam (proofErase Γ L₀) (proofErase (L₀ :: Γ) b))) :=
  (static_structure_caller_absorbs_argument_eta RN SQ hu SA).trans
    (.beta (.app .refl (proofErase_eta_lambda_beta hΓ hL hb (proofErase Γ L₀))))

end Lean4Lean.VEnv.Strengthening
