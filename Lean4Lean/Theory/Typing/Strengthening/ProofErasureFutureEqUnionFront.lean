import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureComputeFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointVariableEqDecode

/-! # Full-union forward transport of diagonal Eq guards contains the front

Native probe-typed variable anchors allow full-union decoding. Thus weakening
the target from certified comparison to union comparison does not escape the
conditional proposition-front barrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
open private constant_motive_lift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params]

/-- Missing forward transport of a diagonal future Eq family guard to a
base comparison in the full union. Sources need no primitives and endpoint
paths are certified. This law is unproved; the conditional implication below
rules out treating it as an automatic repair or a demonstrated smaller front. -/
def TypedFutureEqFamilyUnionForwardCompute (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ α a b a' b' u}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ α (.sort u) →
    env.HasType univs Γ a α → env.HasType univs Γ b α →
    env.HasType univs Γ a' α → env.HasType univs Γ b' α →
    BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α a a)) (proofErase Γ (eqApp u α a b)) →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ a') →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) (proofErase Γ b') →
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (eqApp u α a' a')) (proofErase Γ (eqApp u α a' b'))

/-- Forward computation of only the indices of a diagonal Eq family guard
descends a hidden proposition equation. Both target indices are explicitly
typed at the unchanged supplied carrier. The source certificate is available
with no primitive computations, and the paths just unfold a unit identity. -/
theorem TypedFutureEqFamilyUnionForwardCompute.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqFamilyUnionForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family []))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family [])) (hne : i ≠ j)
    (HRi : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') (.bvar i)
      (proofErase Γ' (eqTypeProbe (.succ u) (.const family []) (P.liftN n) (Q.liftN n) q)))
    (HPQ : env.IsDefEqU univs Γ' (P.liftN n) (Q.liftN n)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have hα := HE.hasType.1
  have hiα := HE.symm.defeq hiT
  have hjα := HE.symm.defeq hjT
  have Ei : proofErase Γ' (.bvar i) = .bvar i :=
    if_neg (not_proof_at_positive_type hΓ' hSw hiT)
  have Ej : proofErase Γ' (.bvar j) = .bvar j :=
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)
  obtain ⟨a, b, ha, hb, HC, RA, RB, _, _⟩ :=
    unit_constant_future_compute_failure hi hp hx hf hc hd hS hΓ' hiT hjT hne
  have HF := proofErase_stable_eq_family heq (hα.sort_r henv hΓ') hΓ' hα
    (HE.symm.defeq ha) (HE.symm.defeq hb) HC
  rw [← Ei] at RA
  rw [← Ej] at RB
  have Hout := Hcompute hΓ' hα (HE.symm.defeq ha) (HE.symm.defeq hb) hiα hjα HF RA RB
  have Hleft := HasType.eqApp heq (hα.sort_r henv hΓ') hα hiα hiα
  have Hright := HasType.eqApp heq (hα.sort_r henv hΓ') hα hiα hjα
  have HCout := proofErase_joint_types_inferred (erased_joint_union_descent heq hs)
    hΓ' Hleft Hright Hout
  have Eleft := proofErase_eqProofType heq (hα.sort_r henv hΓ') hΓ' hα hiα hiα
  have Eright := proofErase_eqProofType heq (hα.sort_r henv hΓ') hΓ' hα hiα hjα
  rw [Ei] at Eleft Eright
  rw [Eleft, Eright] at HCout
  have HG := HCout.union_eq_carrier_decode_variables heq hs hEq
    ⟨Γ', _, _, hΓ', rfl, Hleft, Eleft⟩ ⟨Γ', _, _, hΓ', rfl, Hright, Eright⟩
    HRi HRi .refl .refl
  rw [Ej] at HG
  rcases JointCarrierGuard.checked_or_exposed HG with Hcmp | ⟨B, R, HB, _⟩
  · exact (hne (Hcmp.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W (hS.weak0 henv.ordered) hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Even diagonal Eq-family forward transport to base full-union checking
implies PropositionFront under a closed positive unit and its identity
unfolding. The fresh variable anchor is declared at the Eq probe itself, so
its native recovery remains available throughout decoding. -/
theorem TypedFutureEqFamilyUnionForwardCompute.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqFamilyUnionForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family []
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  let E := eqApp (.succ .zero) (.sort .zero) P.lift Q.lift
  have hE : env.HasType univs (A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) (hP.weak henv) (hQ.weak henv)
  have hΓE : OnCtx (E :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hE⟩
  have W2 : Ctx.LiftN 2 0 Γ (E :: A :: Γ) := Ctx.LiftN.one.cons0
  have hq2 : env.HasType univs (E :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 2) (Q.liftN 2)) := by
    have H := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using H
  let K := eqTypeProbe (.succ u) S (P.liftN 2) (Q.liftN 2) (.bvar 0)
  have hK : env.HasType univs (E :: A :: Γ) K (.sort (.succ u)) :=
    eqTypeProbe_typed heq hΓE (hS.weak0 henv.ordered) (hP.weakN henv W2) (hQ.weakN henv W2) hq2
  have hΓK : OnCtx (K :: E :: A :: Γ) (env.IsType univs) := ⟨hΓE, _, hK⟩
  have hΓKK : OnCtx (K.lift :: K :: E :: A :: Γ) (env.IsType univs) :=
    ⟨hΓK, _, hK.weak henv⟩
  have W4 : Ctx.LiftN 4 0 Γ (K.lift :: K :: E :: A :: Γ) := W2.cons0.cons0
  have WX : Ctx.LiftN 2 0 (E :: A :: Γ) (K.lift :: K :: E :: A :: Γ) := Ctx.LiftN.one.cons0
  have hq4 : env.HasType univs (K.lift :: K :: E :: A :: Γ) (.bvar 2)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    simpa [eqApp, VExpr.liftN, VExpr.liftN_liftN, liftVar] using hq2.weakN henv WX
  have EK : K.liftN 2 = eqTypeProbe (.succ u) S (P.liftN 4) (Q.liftN 4) (.bvar 2) := by
    simp only [K, S, eqTypeProbe, eqRecApp, VExpr.liftN, constant_motive_lift,
      VExpr.liftN_liftN, liftVar]
    rfl
  have HPQ4 : env.IsDefEqU univs (K.lift :: K :: E :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WA : Ctx.LiftN 3 0 (A :: Γ) (K.lift :: K :: E :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using HT.weakN henv WA⟩
  have HE := eqTypeProbe_defeq heq hΓKK (hS.weak0 henv.ordered)
    (hP.weakN henv W4) (hQ.weakN henv W4) hq4 HPQ4
  have hiK : env.HasType univs (K.lift :: K :: E :: A :: Γ) (.bvar 0) (K.liftN 2) := by
    simpa only [VExpr.lift, VExpr.liftN_liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := K.lift) (Γ := K :: E :: A :: Γ)))
  have hjK : env.HasType univs (K.lift :: K :: E :: A :: Γ) (.bvar 1) (K.liftN 2) := by
    simpa only [VExpr.lift, VExpr.liftN_liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.succ (A := K.lift) (Lookup.zero (ty := K) (Γ := E :: A :: Γ))))
  rw [EK] at hiK hjK
  have HRi : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (K.lift :: K :: E :: A :: Γ))
      (.bvar 0) (proofErase (K.lift :: K :: E :: A :: Γ) (K.liftN 2)) := by
    have HR := ScopedTypeRecovery.bvar (Step := ErasedJointUnion D)
      (Δ := proofEraseCtx (K.lift :: K :: E :: A :: Γ)) (i := 0)
    have ER := proofErase_liftN hΓK hΓKK Ctx.LiftN.one (hK.weak henv)
    change ScopedTypeRecovery (ErasedJointUnion D) _ _
      ((proofErase (K :: E :: A :: Γ) K.lift).liftN 1) at HR
    rw [← ER] at HR
    simpa only [VExpr.lift, VExpr.liftN_liftN] using HR
  rw [EK] at HRi
  exact Hcompute.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hc hd hS
    hΓ hΓKK W4 hP hQ hq4 (HE.defeq hiK) (HE.defeq hjK) (by decide) HRi HPQ4

/-- Missing full-union forward transport restricted further to canonical Eq
families over literal Prop. All four indices are propositions at the same
literal sort. The theorem below shows that nested Eq propositions still
encode arbitrary supplied carriers; no strictness claim is made for this law. -/
def TypedFutureEqPropFamilyUnionForwardCompute (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ P Q P' Q'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ P' (.sort .zero) → env.HasType univs Γ Q' (.sort .zero) →
    BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P P))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q)) →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P') →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ Q) (proofErase Γ Q') →
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P' P'))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P' Q'))

/-- Restricting the outer Eq carrier to literal Prop still yields full-union
forward transport at every actual supplied carrier. Nesting Eq propositions
encodes the arbitrary carrier; literal-sort decoding removes the outer layer. -/
theorem TypedFutureEqPropFamilyUnionForwardCompute.eq_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (Hcompute : TypedFutureEqPropFamilyUnionForwardCompute D) :
    TypedFutureEqFamilyUnionForwardCompute D := by
  intro Γ α a b a' b' u hΓ hα ha hb ha' hb' HF RA RB
  have hu := hα.sort_r henv hΓ
  have hP := HasType.eqApp heq hu hα ha ha
  have hQ := HasType.eqApp heq hu hα ha hb
  have hP' := HasType.eqApp heq hu hα ha' ha'
  have hQ' := HasType.eqApp heq hu hα ha' hb'
  have HG := proofErase_stable_eq_family heq (by trivial) hΓ (HasType.sort (by trivial)) hP hQ HF
  have RP : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α a a)) (proofErase Γ (eqApp u α a' a')) := by
    rw [proofErase_eqProofType heq hu hΓ hα ha ha,
      proofErase_eqProofType heq hu hΓ hα ha' ha']
    exact .app (.app (.app .refl .refl) RA) RA
  have RQ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α a b)) (proofErase Γ (eqApp u α a' b')) := by
    rw [proofErase_eqProofType heq hu hΓ hα ha hb,
      proofErase_eqProofType heq hu hΓ hα ha' hb']
    exact .app (.app (.app .refl .refl) RA) RB
  have HO := Hcompute hΓ hP hQ hP' hQ' HG RP RQ
  apply proofErase_joint_eq_sort_decode heq (by trivial)
    (erased_joint_union_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    hΓ hP' hP' hP' hQ' HO

/-- Forward guard transport just for diagonal Eq over literal Prop to a
base full-union comparison already implies PropositionFront under the
closed-unit identity assumptions. No arbitrary-carrier output is needed. -/
theorem TypedFutureEqPropFamilyUnionForwardCompute.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqPropFamilyUnionForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    PropositionFront :=
  TypedFutureEqFamilyUnionForwardCompute.propositionFront_of_closed_unit
    heq hs hregistry hEq hRec (Hcompute.eq_family heq hs hEq) hi hp hx hf hc hd hS

end Lean4Lean.VEnv.Strengthening
