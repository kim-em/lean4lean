import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEndpointBoundary

/-! # A boundary for transporting recovery through compared contexts

Replacing exact output preservation by comparison with the old selected output
still asks too much of the repaired ordinary core. The obstruction already
uses a fresh non-proof variable and explicitly compared binder annotations.
This does not refute transport that only reconstructs the recovery and guard
needed by an application, or transport allowing later singleton stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
open private erase_diagonal from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
variable [Params]

/-- Candidate compared-context transport restricted to the fresh non-proof
variable. The binder annotations already have inferred joint comparison and
the same actual sort. The newly selected output need only compare in common
mode with the old output. This same-core law is refuted below. -/
def JointVariableRecoveryContextComparison
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ A B u out}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ A (.sort u) → env.HasType univs Γ B (.sort u) →
    JointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ B) →
    ¬ IsProof (A :: Γ) (.bvar 0) →
    ScopedTypeRecovery Step (proofEraseCtx (A :: Γ)) (.bvar 0) out →
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx (B :: Γ)) (.bvar 0) out' ∧
      JointCompare Step (proofEraseCtx (B :: Γ)) true out out'

private theorem pi_domains
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false (.forallE A B) (.forallE C D)) :
    JointCompare Step Δ true A C := by
  obtain ⟨C', D', R, HD⟩ := H.forallE_domain_exposure hhead
  obtain ⟨C'', D'', HE, RC⟩ := R.forallE_domain_inv hhead
  cases HE
  exact .compute .refl RC HD

private theorem erase_pi_prop (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    proofErase Γ (.forallE A (.sort .zero)) = .forallE (proofErase Γ A) (.sort .zero) := by
  have hPi := HasType.forallE hA (HasType.sort (l := .zero) (by trivial))
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  rw [show proofErase Γ (.forallE A (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)]
  rw [show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]

private theorem compute_above
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hctx : JointVariableRecoveryContextComparison Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort u))
    (H : JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) out) :
    JointCompare Step (proofEraseCtx (.forallE a (.sort .zero) :: Γ)) true
      ((proofErase Γ a).liftN 1) (out.liftN 1) := by
  let A := VExpr.forallE b (.sort .zero)
  let B := VExpr.forallE a (.sort .zero)
  have hA : env.HasType univs Γ A (.sort (.imax u (.succ .zero))) :=
    .forallE hb (.sort (by trivial))
  have hB : env.HasType univs Γ B (.sort (.imax u (.succ .zero))) :=
    .forallE ha (.sort (by trivial))
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have EA := erase_pi_prop hΓ hb
  have EB := erase_pi_prop hΓ ha
  have HC : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ B) := by
    rw [EA, EB]
    exact .forallE (.symm (proofErase_joint_types_inferred hstep hΓ ha hb H)) (.leaf .refl)
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hn := not_isProof_function_to_sort hΓA hv
  have RP : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (.forallE out (.sort .zero)) := by
    rw [EA]; exact .forallE R .refl
  have RL := RP.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at RL
  have HR : ScopedTypeRecovery Step (proofEraseCtx (A :: Γ)) (.bvar 0)
      ((ProofShape.forallE out (.sort .zero)).liftN 1) :=
    ScopedTypeRecovery.convert .bvar RL
  obtain ⟨out', RR, HH⟩ := Hctx hΓ hA hB HC hn HR
  have HT : JointCompare Step (proofEraseCtx (B :: Γ)) true
      ((ProofShape.forallE out (.sort .zero)).liftN 1) ((proofErase Γ B).liftN 1) :=
    .compute .refl RR.bvar_compute HH
  obtain ⟨b', Hb, Eb⟩ := proofErase_scoped_compute_realize hstep hΓ hb rfl rfl R
  have hb' := Hb.hasType.2
  have hP : env.HasType univs Γ (.forallE b' (.sort .zero))
      (.sort (.imax u (.succ .zero))) := .forallE hb' (.sort (by trivial))
  have EP := erase_pi_prop hΓ hb'
  rw [← Eb, ← EP] at HT
  rw [← proofErase_liftN hΓ hΓB Ctx.LiftN.one hP,
    ← proofErase_liftN hΓ hΓB Ctx.LiftN.one hB] at HT
  have HI := proofErase_joint_types_inferred hstep hΓB (hP.weak henv) (hB.weak henv) HT
  rw [proofErase_liftN hΓ hΓB Ctx.LiftN.one hP,
    proofErase_liftN hΓ hΓB Ctx.LiftN.one hB, EP, EB, Eb] at HI
  exact .symm (pi_domains hhead HI)

private theorem beta_above
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hctx : JointVariableRecoveryContextComparison Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort u))
    (H : JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b))
    (R : BetaRed (proofErase Γ b) out) :
    JointCompare Step (proofEraseCtx (.forallE a (.sort .zero) :: Γ)) true
      ((proofErase Γ a).liftN 1) (out.liftN 1) :=
  compute_above hstep hhead hrename Hctx hΓ ha hb H (.beta R)

private theorem recursive_coverage_above
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hctx : JointVariableRecoveryContextComparison Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    ∃ C, env.IsType univs Γ C ∧
      JointCompare Step (proofEraseCtx (C :: Γ)) true
        ((proofErase Γ D).liftN 1) ((proofErase Γ D').liftN 1) := by
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
  have Hout := beta_above hstep hhead hrename Hctx hΓ hl hr Hinput RB
  simp only [RecursiveDomain.diagonal] at EL
  rw [EL] at Hout
  have Hread := JointCompare.selfLoop_annotations hhead
    (A := (proofErase Γ D).liftN 1) (B := (proofErase Γ D').liftN 1) (by
      simpa [ProofShape.selfLoop, ProofShape.diagonal, ProofShape.liftN, liftVar] using Hout)
  exact ⟨.forallE (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)) (.sort .zero),
    ⟨_, HasType.forallE hl (HasType.sort (by trivial))⟩, Hread⟩

omit [Params] in
/-- Even allowing a new recovered output compared with the old one fails for
the repaired ordinary core in the presence of a recursive Pi and a free
reflexive equality major. The binder change itself has a joint certificate. -/
theorem JointVariableRecoveryContextComparison.not_of_recursive_pi {env : VEnv}
    (henv : env.WF) (U : Nat) (hquot : QuotRegistered env) :
    letI := henv.params U
    ∀ {Γ A B u v i}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ¬ JointVariableRecoveryContextComparison (fun _ => ErasedQuotCore.Step hquot) := by
  letI := henv.params U
  intro Γ A B u v i heq hu hΓ hX hq Hrec Hctx
  have hs := ErasedQuotCore.sound hquot
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedQuotCore.Step hquot) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  have hhead : ∀ {Δ : List ProofShape} {a b},
      (fun _ => ErasedQuotCore.Step hquot) Δ a b → PrimitiveHead a :=
    fun H => erased_iota_primitive_head H
  have HD := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  obtain ⟨C, hC, HC⟩ := recursive_coverage_above hstep @hhead
    (fun H _ => erased_iota_primitive_subst H) Hctx hΓ Hrec HD.symm
  have hΓC : OnCtx (C :: Γ) (env.IsType U) := ⟨hΓ, hC⟩
  have HP := Hrec.hasType.1
  have HQ := HD.hasType.1
  have HT : JointCompare (fun _ => ErasedQuotCore.Step hquot) (proofEraseCtx (C :: Γ)) true
      (proofErase (C :: Γ) ((VExpr.forallE A B).lift))
      (proofErase (C :: Γ) ((typeCast u (.sort v) (.sort v) (.bvar i) (.forallE A B)).lift)) := by
    rw [proofErase_liftN hΓ hΓC Ctx.LiftN.one HP,
      proofErase_liftN hΓ hΓC Ctx.LiftN.one HQ]
    exact HC
  have HI := proofErase_joint_types_inferred hstep hΓC (HP.weak henv) (HQ.weak henv) HT
  rw [proofErase_liftN hΓ hΓC Ctx.LiftN.one HP,
    proofErase_liftN hΓ hΓC Ctx.LiftN.one HQ] at HI
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ HP)
  rw [EP] at HI
  obtain ⟨A', B', R⟩ := JointCompare.forallE_exposure @hhead HI
  have RR := (forget_scope R).subst (fun H => erased_iota_primitive_subst H)
    (σ := ProofShape.Subst.one .proof)
  have RS : ScopedCompute (fun _ => ErasedQuotCore.Step hquot) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar i) (.forallE A B)))
      (.forallE (A'.subst (ProofShape.Subst.one .proof))
        (B'.subst (ProofShape.Subst.one .proof).lift)) := by
    simpa only [ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
      ProofShape.subst] using RR.scoped (fun H => .base H)
  exact ErasedQuotCore.cast_no_pi henv U hquot heq hu hΓ hX hq HP RS

omit [Params] in
/-- The installed recursive family supplies the obstruction to compared-output
recovery transport, retaining every repaired ordinary-core equation. -/
theorem JointVariableRecoveryContextComparison.not_recursive {env : VEnv} (henv : env.WF) (U : Nat) (hquot : QuotRegistered env) (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq U Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    letI := henv.params U
    ¬ JointVariableRecoveryContextComparison (fun _ => ErasedQuotCore.Step hquot) := by
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
  exact not_of_recursive_pi henv U hquot heq hu hΓ hX hq HP'


omit [Params] in
/-- A well-formed extension preserving canonical Eq and quotient registration
has the proposition front but fails compared-output variable recovery transport
for its repaired ordinary core. Thus this transport invariant is stronger than
necessary here, and its failure is not a strengthening counterexample. -/
theorem JointVariableRecoveryContextComparison.canonical_core_failure
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hquot : QuotRegistered base)
    (hfresh : base.constants c = none) :
    let henv' := RecursiveDomain.extended_wf hbase hfresh
    let hquot' := hquot.mono (RecursiveDomain.extended_le hfresh)
    letI := henv'.params 0
    (RecursiveDomain.extended base c).HasCanonicalEq ∧ PropositionFront ∧
      ¬ JointVariableRecoveryContextComparison (fun _ => ErasedQuotCore.Step hquot') := by
  letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
  have heq' := RecursiveDomain.extended_canonicalEq heq hfresh
  refine ⟨heq', canonical_recursiveDomain_front hbase heq hfresh, ?_⟩
  apply not_recursive (RecursiveDomain.extended_wf hbase hfresh) 0
    (hquot.mono (RecursiveDomain.extended_le hfresh)) heq' (c := c)
  exact fun Γ => RecursiveDomain.equation 0 Γ


end Lean4Lean.VEnv.Strengthening
