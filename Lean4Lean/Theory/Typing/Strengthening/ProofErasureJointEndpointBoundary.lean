import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreCastBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeInhabitants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypeExposure

/-! # Same-core joint checking is not stable under endpoint beta

The full joint checker still reads the annotations of diagonal loops. A single
right-endpoint beta step can expose a canonical-Eq cast hidden by common lambda
checking. The repaired ordinary core cannot remove that cast. The actual
recursive extension used here separately satisfies the proposition front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_diagonal from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
variable [Params]

/-- Candidate right-endpoint beta closure for common joint checking. This
same-relation law is refuted below even for the repaired ordinary core; no
claim is made against closure allowing a larger singleton stage. -/
def JointCommonBetaStability (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ a b T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ a T → env.HasType univs Γ b T →
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) →
    ProofShape.BetaRed (proofErase Γ b) out →
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) out

/-- Even right-endpoint beta closure must recover every conversion out of a
recursive Pi domain. The input compares a loop with a mixed-annotation loop;
its functions are identical, and common lambda checking relates its arguments. -/
theorem JointCommonBetaStability.recursive_type_coverage
    (Hbeta : JointCommonBetaStability Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ D) (proofErase Γ D') := by
  have hD := Hrec.hasType.1
  have hD' := HD.hasType.2
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  have hb' : env.HasType univs (D' :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx := Hrec.symm.defeq Hdiag.hasType.1
  have hy := Hrec.symm.defeq Hdiag.hasType.2
  have EX := erase_diagonal hΓ hD hb
  have EY := erase_diagonal hΓ hD' hb'
  have HX : JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (RecursiveDomain.diagonal D))
      (proofErase Γ (RecursiveDomain.diagonal D')) := by
    rw [EX, EY]
    exact .lamCommon (.leaf .refl)
  have hl := HasType.app Hdiag.hasType.1 hx
  have hr := HasType.app Hdiag.hasType.1 hy
  have EL : proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)) =
      .app (ProofShape.diagonal (proofErase Γ D)) (ProofShape.diagonal (proofErase Γ D)) := by
    rw [show proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hl), EX]
  have ER : proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D')) =
      .app (ProofShape.diagonal (proofErase Γ D)) (ProofShape.diagonal (proofErase Γ D')) := by
    rw [show proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D')) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hr), EX, EY]
  have Hinput : JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)))
      (proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D'))) := by
    rw [EL, ER]
    rw [EX, EY] at HX
    exact .app (.leaf .refl) HX
  have RB : ProofShape.BetaRed
      (proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D')))
      (ProofShape.selfLoop (proofErase Γ D')) := by
    rw [ER]
    have R := ProofShape.BetaRed.beta (A := proofErase Γ D)
      (b := ProofShape.app (.bvar 0) (.bvar 0))
      (a := ProofShape.diagonal (proofErase Γ D'))
    simpa [ProofShape.diagonal, ProofShape.selfLoop, ProofShape.inst,
      ProofShape.liftN_zero] using R
  have Hout := Hbeta hΓ hl hr Hinput RB
  change JointCompare Step (proofEraseCtx Γ) true
    (proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)))
    (ProofShape.selfLoop (proofErase Γ D')) at Hout
  rw [EL] at Hout
  exact JointCompare.selfLoop_annotations hhead Hout


omit [Params] in
/-- A recursive Pi and a free reflexive equality proof refute single-endpoint
beta closure for full joint checking over the quotient-repaired ordinary core.
This is a certificate obstruction, not a failure of declarative strengthening. -/
theorem JointCommonBetaStability.not_beta_of_recursive_pi {env : VEnv}
    (henv : env.WF) (U : Nat) (hquot : QuotRegistered env) :
    letI := henv.params U
    ∀ {Γ A B u v i}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ¬ JointCommonBetaStability (fun _ => ErasedQuotCore.Step hquot) := by
  letI := henv.params U
  intro Γ A B u v i heq hu hΓ hX hq Hrec Hbeta
  have hs := ErasedQuotCore.sound hquot
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedQuotCore.Step hquot) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  have hhead : ∀ {Δ : List ProofShape} {a b},
      (fun _ => ErasedQuotCore.Step hquot) Δ a b → PrimitiveHead a :=
    fun H => erased_iota_primitive_head H
  have HD := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  have HC := Hbeta.recursive_type_coverage @hhead hΓ Hrec HD.symm
  have HC' := proofErase_joint_types_inferred hstep hΓ Hrec.hasType.1 HD.hasType.1 HC
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ Hrec.hasType.1)
  rw [EP] at HC'
  obtain ⟨A', B', R⟩ := JointCompare.forallE_exposure @hhead HC'
  exact ErasedQuotCore.cast_no_pi henv U hquot heq hu hΓ hX hq Hrec.hasType.1 R

omit [Params] in
/-- The installed recursive family supplies the recursive Pi obstruction to
endpoint beta closure, retaining every repaired ordinary-core equation. -/
theorem JointCommonBetaStability.not_beta_recursive {env : VEnv} (henv : env.WF) (U : Nat) (hquot : QuotRegistered env) (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq U Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    letI := henv.params U
    ¬ JointCommonBetaStability (fun _ => ErasedQuotCore.Step hquot) := by
  letI := henv.params U
  have Hrec := RecursiveDomain.domain_recursive hδ
  let D := RecursiveDomain.domainL c
  let P := VExpr.forallE D (.sort .zero)
  have HP : env.IsDefEq U RecursiveDomain.loopCtx P (.forallE P (.sort .zero))
      (.sort (.succ .zero)) := by
    have H := IsDefEq.forallEDF Hrec (HasType.sort (env := env) (l := .zero) (by trivial))
    exact IsDefEq.defeqDF (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self) H
  let u : VLevel := .succ (.succ .zero)
  let X : VExpr := .sort (.succ .zero)
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX {Γ} : env.HasType U Γ X (.sort u) := .sort (by trivial)
  have hQ : env.HasType U RecursiveDomain.loopCtx Q (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort hu) hX hX
  have hbase : OnCtx RecursiveDomain.loopCtx (env.IsType U) :=
    ⟨trivial, _, RecursiveDomain.argType_typed env U []⟩
  have hΓ : OnCtx (Q :: RecursiveDomain.loopCtx) (env.IsType U) := ⟨hbase, _, hQ⟩
  have hq : env.HasType U (Q :: RecursiveDomain.loopCtx) (.bvar 0) Q := by
    have H : env.HasType U (Q :: RecursiveDomain.loopCtx) (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, VExpr.liftN] using H
  have HP' : env.IsDefEq U (Q :: RecursiveDomain.loopCtx)
      (.forallE D.lift (.sort .zero))
      (.forallE (.forallE D.lift (.sort .zero)) (.sort .zero)) X := by
    exact HP.weakN henv Ctx.LiftN.one
  exact not_beta_of_recursive_pi henv U hquot heq hu hΓ hX hq HP'


omit [Params] in
/-- A well-formed extension preserving canonical Eq and quotient registration
has the proposition front but fails common joint endpoint beta closure for its
repaired ordinary core. Hence this closure law is stronger than necessary in
this environment and its failure is not a strengthening counterexample. -/
theorem JointCommonBetaStability.canonical_core_beta_failure
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hquot : QuotRegistered base)
    (hfresh : base.constants c = none) :
    let henv' := RecursiveDomain.extended_wf hbase hfresh
    let hquot' := hquot.mono (RecursiveDomain.extended_le hfresh)
    letI := henv'.params 0
    (RecursiveDomain.extended base c).HasCanonicalEq ∧ PropositionFront ∧
      ¬ JointCommonBetaStability (fun _ => ErasedQuotCore.Step hquot') := by
  letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
  have heq' := RecursiveDomain.extended_canonicalEq heq hfresh
  refine ⟨heq', canonical_recursiveDomain_front hbase heq hfresh, ?_⟩
  apply not_beta_recursive (RecursiveDomain.extended_wf hbase hfresh) 0
    (hquot.mono (RecursiveDomain.extended_le hfresh)) heq' (c := c)
  exact fun Γ => RecursiveDomain.equation 0 Γ

/-- The precise cast hidden by the beta obstruction computes away at repaired
joint stage one. This verifies that the obstruction needs additional singleton
computation, without asserting general endpoint closure at that stage. -/
theorem ErasedQuotCore.reflexive_cast_joint_stage_one
    (hquot : QuotRegistered env) (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (he : env.HasType univs Γ e X) :
    ScopedCompute (ErasedJointStage (definitions hquot) 1) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u X X q e)) (proofErase Γ e) := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq he
  have R : ScopedCompute (ErasedScopedPrefixStage (definitions hquot) 1) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u X X q e)) (proofErase Γ e) :=
    proofErase_scoped_prefix_full_forward heq (sound hquot) hΓ HC.hasType.1 .refl
  exact R.mono (fun H => erased_recursive_singleton_into_joint 1
    (erased_application_into_recursive_singleton 1
      (erased_structure_into_application 1 (erased_scoped_prefix_into_structure 1 H))))

/-- At repaired joint stage one, comparison of the two beta-result loops is
restored by computing their cast annotations. No normalization of either loop
is used, and no arbitrary endpoint-transport law is assumed. -/
theorem ErasedQuotCore.cast_loop_joint_stage_one
    (hquot : QuotRegistered env) (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (he : env.HasType univs Γ e X) :
    JointCompare (ErasedJointStage (definitions hquot) 1) (proofEraseCtx Γ) true
      (ProofShape.selfLoop (proofErase Γ e))
      (ProofShape.selfLoop (proofErase Γ (typeCast u X X q e))) := by
  have R := reflexive_cast_joint_stage_one hquot heq hu hΓ hX hq he
  exact .compute .refl (.app (.lam R .refl) (.lam R .refl)) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
