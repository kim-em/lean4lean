import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNeutralCarrierReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangePaths
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathProbeBoundary

/-! # The unit-probe coverage obligation for mixed type paths

Transport along mixed paths is proved. Covering even the unit-valued Eq probe
would already imply PropositionFront when a closed positive unit is present.
This is a conditional sufficiency boundary, not a proof of path coverage or a
strictly smaller irreducible obligation.
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

/-- A mixed path from a unit to the lifted Eq probe descends the original
proposition equality. Distinct unit variables force actual target-carrier
exposure; the first changed head reads the lower proposition endpoints. -/
theorem TypeChangePath.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (L : TypeChangeLaws (ErasedBetaStableJoint D) Rel)
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
    (Hpath : TypeChangePath Rel Γ' (.succ u) (.const family ls)
      (eqTypeProbe (.succ u) (.const family ls) (P.liftN n) (Q.liftN n) q)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have ES : proofErase Γ' (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ' hSw)
  have Ei : proofErase Γ' (.bvar i) = .bvar i :=
    if_neg (not_proof_at_positive_type hΓ' hSw hiT)
  have Ej : proofErase Γ' (.bvar j) = .bvar j :=
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)
  have HX : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
      (proofErase Γ' (.const family ls)) (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j)) := by
    rw [ES]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  have HG : JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe (.succ u) (.const family ls) (P.liftN n) (Q.liftN n) q))
      (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j)) :=
    (Hpath.carrier heq hs L hΓ' hiT hjT HX).mono (fun H => erased_beta_stable_joint_into_union H)
  rw [Ei, Ej] at HG
  rcases HG.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact (hne (HC.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Mixed-path coverage restricted to the positive unit-valued Eq probe.
The only supplied equality is its proposition-index equality in the current
context. This property is an explicit unproved coverage requirement. -/
def UnitProbePathCoverage (Rel : Nat → ProofShape → ProofShape → Prop)
    (family : Name) (ls : List VLevel) (u : VLevel) : Prop :=
  ∀ {Γ P Q q}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.const family ls) (.sort (.succ u)) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q) →
    env.IsDefEqU univs Γ P Q →
    TypeChangePath Rel Γ (.succ u) (.const family ls)
      (eqTypeProbe (.succ u) (.const family ls) P Q q)

/-- Covering just these unit-valued probes with mixed type paths implies the
full proposition front, given a closed positive unit and the local transport
laws. Strictness and an unconditional converse are not established. -/
theorem UnitProbePathCoverage.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (L : TypeChangeLaws (ErasedBetaStableJoint D) Rel)
    (Hcover : UnitProbePathCoverage Rel family ls u)
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
  have Hpath := Hcover hΓE (hS.weak0 henv.ordered) (hP.weakN henv W4) (hQ.weakN henv W4) hq HPQ4
  exact TypeChangePath.unit_probe_descend heq hs hregistry hEq hRec L hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) Hpath

/-- The current Pi/Box/beta paths fail even this restricted coverage condition,
for any closed positive constant type other than Eq.rec. The test uses a
reflexive, closed proposition index, so it does not assume an unsolved front. -/
theorem UnitProbePathCoverage.not_box
    (heq : env.HasCanonicalEq)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u)))
    (hne : family ≠ ``Eq.rec) :
    ¬ UnitProbePathCoverage (BoxTypeChange boxFamily) family ls u := by
  intro Hcover
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType univs [] P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hProp : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq := HasType.eqReflApp heq (by trivial) hProp hP
  exact no_box_path_to_const_probe heq (by trivial) hS hne hP hP hq
    (Hcover (by trivial) hS hP hP hq ⟨_, hP⟩)

end Lean4Lean.VEnv.Strengthening
