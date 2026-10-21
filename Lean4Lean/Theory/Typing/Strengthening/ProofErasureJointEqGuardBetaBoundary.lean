import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointProofInstantiation
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqFamilyGuard

/-! # The canonical Eq family guard already contains proposition beta stability

The fresh proof-major binder does not make the beta stability question smaller.
Encoding a supplied comparison gives the input family guard. Its semantic
equality also supplies an inhabitant of the reduced proof-major type, allowing
proof substitution after guard transport. The literal-sort decoder then reads
out the desired proposition comparison in the original context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Missing beta stability for the literal family comparison of the canonical
Eq prefix, specialized to carrier Prop and reduction of its requested index.
The context changes with the requested equality, exactly as in
`eqRec_family_guard_iff`. No arbitrary carrier or general singleton is involved. -/
def JointEqPropFamilyBetaStability
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P Q Q'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    VExpr.BetaRed Q Q' →
    JointCompare Step (proofEraseCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)) true
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P P).lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P Q).lift) →
    JointCompare Step (proofEraseCtx (eqApp (.succ .zero) (.sort .zero) P Q' :: Γ)) true
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q' :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P P).lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q' :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P Q').lift)

/-- Even the Prop-carrier instance of actual Eq family-guard beta transport
implies the entire proposition beta-stability law. The fresh proof major is
removed by an explicitly constructed equality proof, never by strengthening. -/
theorem JointEqPropFamilyBetaStability.prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (HG : JointEqPropFamilyBetaStability (ErasedJointUnion D)) :
    JointPropBetaStability (ErasedJointUnion D) := by
  intro Γ P Q out hΓ hP hQ HC R
  obtain ⟨Q', RQ, EQ⟩ := proofErase_beta_replay hΓ hQ R
  have HQQ := beta_eq hΓ hQ RQ
  have hQ' := HQQ.hasType.2
  have hEP := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hP
  have hEQ := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hEQ' := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ'
  have hΓQ : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, hEQ⟩
  have H0 := proofErase_joint_carrier_propositions (mode := true) heq
    (show (VLevel.succ .zero).WF univs by trivial) hΓ (HasType.sort (by trivial))
    hP hP hQ (JointCheck.carrierChecked HC)
  have HL := H0.rename (erased_joint_union_rename heq hs)
    (ContextRenaming.of_liftN hΓ hΓQ Ctx.LiftN.one)
  have Hguard : JointCompare (ErasedJointUnion D) (proofEraseCtx
      (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)) true
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P P).lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P Q).lift) := by
    rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hEP,
      proofErase_liftN hΓ hΓQ Ctx.LiftN.one hEQ]
    simpa only [subst_bvar_liftN, JointCheckKind.subst] using HL
  have Hnew := HG hΓ hP hQ RQ Hguard
  have HPQ := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs)
    hΓ hP hQ (JointCheck.carrierChecked HC)
  have HPQ' := HPQ.trans HQQ
  have hp : env.HasType univs Γ (eqReflApp (.succ .zero) (.sort .zero) P)
      (eqApp (.succ .zero) (.sort .zero) P Q') :=
    (IsDefEq.eqApp_r heq (by trivial) (HasType.sort (by trivial)) hP HPQ').defeq
      (HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hP)
  obtain ⟨stage, Hstage⟩ := Hnew.finite_stage erased_joint_stage_mono
  have Hbelow := proofErase_joint_compare_inst_proofs heq hs hΓ hEQ' hp hp
    (hEP.weakN henv.ordered Ctx.LiftN.one) (hEQ'.weakN henv.ordered Ctx.LiftN.one) Hstage
  simp only [VExpr.inst_lift] at Hbelow
  rw [← EQ]
  apply proofErase_joint_eq_sort_decode heq (by trivial)
    (erased_joint_union_descent heq hs) erased_joint_union_head ?_ hΓ hP hP hP hQ'
    (Hbelow.mono (fun H => ⟨stage, H⟩))
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (heq.rigid henv) hD H (constHead_mkApps _ _)

/-- Proposition beta stability transports the canonical Prop-carrier family
comparison, including the converted proof-major context. -/
theorem JointPropBetaStability.eq_prop_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HB : JointPropBetaStability (ErasedJointUnion D)) :
    JointEqPropFamilyBetaStability (ErasedJointUnion D) := by
  intro Γ P Q Q' hΓ hP hQ RQ HC
  have HQQ := beta_eq hΓ hQ RQ
  have hQ' := HQQ.hasType.2
  have hEP := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hP
  have hEQ := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hEQ' := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ'
  have hΓQ : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, hEQ⟩
  have hEPw := hEP.weakN henv.ordered (Ctx.LiftN.one (A := eqApp (.succ .zero) (.sort .zero) P Q))
  have hEQw := hEQ.weakN henv.ordered (Ctx.LiftN.one (A := eqApp (.succ .zero) (.sort .zero) P Q))
  have hEQ'w := hEQ'.weakN henv.ordered (Ctx.LiftN.one (A := eqApp (.succ .zero) (.sort .zero) P Q))
  have RE : VExpr.BetaRed (eqApp (.succ .zero) (.sort .zero) P Q)
      (eqApp (.succ .zero) (.sort .zero) P Q') := .app .refl RQ
  have Rlift : ProofShape.BetaRed
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P Q).lift)
      (proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
        (eqApp (.succ .zero) (.sort .zero) P Q').lift) := by
    rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hEQ,
      proofErase_liftN hΓ hΓQ Ctx.LiftN.one hEQ']
    exact (proofErase_beta_forward hΓ hEQ RE).liftN
  have HR := HB hΓQ hEPw hEQw HC Rlift
  have W : IsDefEqCtx env univs Γ
      (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
      (eqApp (.succ .zero) (.sort .zero) P Q' :: Γ) :=
    .succ .zero (IsDefEq.eqApp_r heq (by trivial) (HasType.sort (by trivial)) hP HQQ)
  have HT := HB.defeqCtx heq hs hΓ W hEPw hEQ'w HR
  rw [proofErase_defeqCtx hΓQ W hEPw, proofErase_defeqCtx hΓQ W hEQ'w] at HT
  exact HT

/-- Restricting the full-union stability task to the actual Eq family guard
at carrier Prop is equivalent to general proposition beta stability. Inertness
of Eq is explicit; sound definitions alone do not imply that syntactic fact. -/
theorem joint_eq_prop_family_beta_stability_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) :
    JointEqPropFamilyBetaStability (ErasedJointUnion D) ↔
      JointPropBetaStability (ErasedJointUnion D) :=
  ⟨fun H => H.prop_beta heq hs hD, fun H => H.eq_prop_family heq hs⟩

end Lean4Lean.VEnv.Strengthening
