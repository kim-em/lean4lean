import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDisplayedLambdaCoverage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureInhabitedRecoveryFront

/-! # The recovery requirement behind displayed-domain applications

Any recovered type of the displayed lambda suffices to recover a Pi at its
original domain. Thus only absence of all recovery can prevent this particular
embedding into the old application rule. Supplying recovery uniformly is not
a small missing lemma: even constant predicates over the fixed function type
Prop -> Prop test recovery of every inhabited proposition, and hence the front.
This does not make recovery necessary for comparison; beta may compare the
applications without recovering their function.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Any selected recovery of the lambda, not a prescribed Pi output, suffices
for the old application rule. Inverting recovery retains a body certificate,
which reconstructs a Pi with the original displayed domain. -/
theorem DisplayedLambdaApplication.joint_of_recovery
    (H : DisplayedLambdaApplication Step Δ (.app (.lam A body) x) (.app g y))
    (HR : ScopedTypeRecovery Step Δ (.lam A body) out) :
    JointCompare Step Δ mode (.app (.lam A body) x) (.app g y) := by
  obtain ⟨B, RB⟩ := HR.lam_body_inv
  exact H.joint (.lam RB)

/-- A constant proposition-valued lambda has some recovered type exactly when
its original proposition body does. The dummy domain is arbitrary and needs
no inhabitant or recovery. The forward implication retains the lower recovery
certificate through typed binder removal, not inverse typing weakening. -/
theorem proofErase_joint_constant_lambda_recovery_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    (∃ out, ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A P.lift)) out) ↔
    ∃ out, ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ P) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hf : env.HasType univs Γ (.lam A P.lift) (.forallE A (.sort .zero)) :=
    .lam hA (hP.weak henv)
  have Ef : proofErase Γ (.lam A P.lift) =
      .lam (proofErase Γ A) ((proofErase Γ P).liftN 1) := by
    rw [show proofErase Γ (.lam A P.lift) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf),
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hP]
  rw [Ef]
  constructor
  · rintro ⟨out, R⟩
    obtain ⟨B, RB⟩ := R.lam_body_inv
    obtain ⟨T, _, RT, _⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_joint_union_certificate_descent heq hs)
      hΓ hΓA Ctx.LiftN.one hP rfl RB
    exact ⟨_, RT⟩
  · rintro ⟨out, R⟩
    have RB := (proofErase_joint_union_recovery_lift_iff heq hs
      hΓ hΓA Ctx.LiftN.one hP).2 R
    exact ⟨_, .lam RB⟩

/-- The recovery test above is not a comparison-coverage obstruction:
applications of two constant lambdas returning the same raw body already
compare by beta at every stage, with arbitrary arguments and annotations.
No recovery of the body or carrier relation between the arguments is needed. -/
theorem constant_lambda_applications_compare (P A B x y : ProofShape) :
    JointCompare Step Δ mode (.app (.lam A (P.liftN 1)) x)
      (.app (.lam B (P.liftN 1)) y) := by
  have HX : ScopedCompute Step Δ (.app (.lam A (P.liftN 1)) x) P := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (ScopedCompute.beta (Step := Step) (Δ := Δ)
        (ProofShape.BetaRed.beta (A := A) (b := P.liftN 1) (a := x)))
  have HY : ScopedCompute Step Δ (.app (.lam B (P.liftN 1)) y) P := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (ScopedCompute.beta (Step := Step) (Δ := Δ)
        (ProofShape.BetaRed.beta (A := B) (b := P.liftN 1) (a := y)))
  exact .compute HX HY (.leaf .refl)

/-- Missing recovery coverage only for constant predicates over one fixed,
closed function domain, Prop -> Prop, returning inhabited propositions.
No output type is prescribed. This property is not proved; the theorems below
show why supplying it as a routine reconstruction lemma would hide the front. -/
def ConstantStructuralPredicateRecovery
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P p}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ p P →
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.lam (.forallE (.sort .zero) (.sort .zero)) P.lift)) out

/-- Even recovery restricted to constant predicates at this one structural
domain yields recovery of every inhabited proposition in the old joint union.
The supplied proof restricts the coverage premise; it is not used as a filler. -/
theorem ConstantStructuralPredicateRecovery.inhabited
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ConstantStructuralPredicateRecovery (ErasedJointUnion D)) :
    InhabitedPropositionRecovery (ErasedJointUnion D) := by
  intro Γ P p hΓ hP hp
  have hA : env.HasType univs Γ (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (.sort (by trivial)) (.sort (by trivial))
  exact (proofErase_joint_constant_lambda_recovery_iff heq hs hΓ hA hP).1 (H hΓ hP hp)

/-- The restricted constant-predicate coverage premise already suffices for
the original proposition front. This is a barrier to treating recovery as
automatic, not a proof of the premise or of a strictly smaller obligation. -/
theorem ConstantStructuralPredicateRecovery.joint_union_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : ConstantStructuralPredicateRecovery (ErasedJointUnion D)) : PropositionFront :=
  InhabitedPropositionRecovery.joint_union_propositionFront heq hs hregistry hEq hRec
    (ConstantStructuralPredicateRecovery.inhabited heq hs H)

end Lean4Lean.VEnv.Strengthening
