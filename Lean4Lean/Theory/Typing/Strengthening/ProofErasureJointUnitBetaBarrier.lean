import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNeutralCarrierReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary

/-! # Proposition beta transport already carries the front obligation

In the presence of a closed positive empty structure, even stage-zero
proposition beta transport implies PropositionFront. Carrier conversion moves
the structure's two-variable guard to a type-valued Eq probe. Distinct bare
variables force actual carrier exposure, whose first-head primitive reads out
the original proposition equality below every inserted binder.

This is a conditional implication, not a refutation of beta transport and not
a claim that canonical Eq alone guarantees a positive empty structure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

private theorem carrier_exposure_ne_eqRec (heq : env.HasCanonicalEq)
    (H : CarrierExposure B) : B.constHead ≠ some ``Eq.rec := by
  cases H with
  | function => simp [ProofShape.constHead]
  | record hi _ _ =>
    rw [constHead_mkApps]
    intro E
    have Ec := Option.some.inj E
    have hr := henv.projectionRigid hi
    rw [Ec] at hr
    obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
    exact hr.pats _ _ hp rfl

/-- With distinct unit variables above an inserted context block, proposition
beta transport descends arbitrary proposition conversion below that block.
The initial unit guard uses no primitive steps, at any chosen finite stage. -/
theorem JointPropBetaTransport.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN n) (Q.liftN n)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have ES : proofErase Γ' (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ' hSw)
  have Ei : proofErase Γ' (.bvar i) = .bvar i :=
    if_neg (not_proof_at_positive_type hΓ' hSw hiT)
  have Ej : proofErase Γ' (.bvar j) = .bvar j :=
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)
  have HX : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (.const family ls)) (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j)) := by
    rw [ES]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  have HG := Hbeta.carrier_conversion_stage heq hs hΓ' HE.symm hiT hjT HX
  rw [Ei, Ej] at HG
  rcases HG.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact (hne (HC.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Even proposition beta transport from one finite stage (in particular
stage zero) implies PropositionFront when a closed positive empty structure
is present. This does not establish strictness or an unconditional converse. -/
theorem JointPropBetaTransport.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family ls
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hSA : env.HasType univs (A :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hSA⟩
  have hΓSS : OnCtx (S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓS, _, hSA.weak henv⟩
  have W3 : Ctx.LiftN 3 0 Γ (S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
  have hP3 : env.HasType univs (S :: S :: A :: Γ) (P.liftN 3) (.sort .zero) := hP.weakN henv W3
  have hQ3 : env.HasType univs (S :: S :: A :: Γ) (Q.liftN 3) (.sort .zero) := hQ.weakN henv W3
  let E := eqApp (.succ .zero) (.sort .zero) (P.liftN 3) (Q.liftN 3)
  have hE : env.HasType univs (S :: S :: A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP3 hQ3
  have hΓE : OnCtx (E :: S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓSS, _, hE⟩
  have W4 : Ctx.LiftN 4 0 Γ (E :: S :: S :: A :: Γ) := W3.cons0
  have hq : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    have h := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using h
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    have H := HT.weakN henv WX
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using H⟩
  exact Hbeta.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

end Lean4Lean.VEnv.Strengthening
