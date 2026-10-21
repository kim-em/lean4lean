import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureComputeFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCarrierDecode

/-! # Certified forward computation of diagonal Eq family guards

Restricting the guard to canonical Eq does not eliminate freely converted
supplied carriers. A declared unit identity hides distinct unit variables in
the source future certificate. A certified target comparison must expose an
Eq probe used as their supplied carrier, which descends its proposition indices.
The target here is certified checking, not arbitrary full-union checking.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- Missing forward-computation law restricted to the diagonal Eq family
guard at one unchanged actual supplied carrier. The source certificate uses
no primitives; only a base certified comparison is requested at the outputs.
This law is not established or claimed smaller than PropositionFront. It is
stronger than asking for a target guard in the unrestricted joint union. -/
def TypedFutureEqFamilyForwardCompute (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ α a b a' b' u}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ α (.sort u) →
    env.HasType univs Γ a α → env.HasType univs Γ b α →
    env.HasType univs Γ a' α → env.HasType univs Γ b' α →
    BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α a a)) (proofErase Γ (eqApp u α a b)) →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ a') →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) (proofErase Γ b') →
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (eqApp u α a' a')) (proofErase Γ (eqApp u α a' b'))

/-- Forward computation of only the indices of a diagonal Eq family guard
descends a hidden proposition equation. Both target indices are explicitly
typed at the unchanged supplied carrier. The source certificate is available
with no primitive computations, and the paths just unfold a unit identity. -/
theorem TypedFutureEqFamilyForwardCompute.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqFamilyForwardCompute D)
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
  have HG := (proofErase_certified_carrier_propositions_iff heq hs hEq
    (hα.sort_r henv hΓ') hΓ' hα hiα hiα hjα).1 Hout
  have HG := HG.mono (fun H => erased_beta_stable_joint_into_union H)
  rw [Ei, Ej] at HG
  rcases JointCarrierGuard.checked_or_exposed HG with Hcmp | ⟨B, R, HB, _⟩
  · exact (hne (Hcmp.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W (hS.weak0 henv.ordered) hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Even source-False diagonal Eq family transport to base certified checking
implies PropositionFront, given a closed positive unit and its declared
identity unfolding. This is a conditional strength result. It neither proves
transport nor settles transport to the weaker full-union target relation. -/
theorem TypedFutureEqFamilyForwardCompute.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqFamilyForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family []
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
  exact Hcompute.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hc hd hS
    hΓ hΓE W4 hP hQ hq hiT hjT (by decide) HPQ4

/-- Missing certified forward transport restricted further to canonical Eq
families over literal Prop. All four indices are propositions at the same
literal sort. The theorem below shows that nested Eq propositions still
encode arbitrary supplied carriers; no strictness claim is made for this law. -/
def TypedFutureEqPropFamilyForwardCompute (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ P Q P' Q'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ P' (.sort .zero) → env.HasType univs Γ Q' (.sort .zero) →
    BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P P))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q)) →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P') →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ Q) (proofErase Γ Q') →
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P' P'))
      (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P' Q'))

/-- Restricting the outer Eq carrier to literal Prop still yields certified
forward transport at every actual supplied carrier. Nesting Eq propositions
encodes the arbitrary carrier; literal-sort decoding removes the outer layer. -/
theorem TypedFutureEqPropFamilyForwardCompute.eq_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (Hcompute : TypedFutureEqPropFamilyForwardCompute D) :
    TypedFutureEqFamilyForwardCompute D := by
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
    (erased_beta_stable_joint_descent heq hs) erased_beta_stable_joint_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq
      (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _))
    hΓ hP' hP' hP' hQ' HO

/-- Certified forward guard transport just for diagonal Eq over literal Prop
already implies PropositionFront under the closed-unit identity assumptions.
This says nothing stronger about the unresolved full-union target version. -/
theorem TypedFutureEqPropFamilyForwardCompute.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureEqPropFamilyForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    PropositionFront :=
  TypedFutureEqFamilyForwardCompute.propositionFront_of_closed_unit
    heq hs hregistry hEq hRec (Hcompute.eq_family heq hs hEq) hi hp hx hf hc hd hS

end Lean4Lean.VEnv.Strengthening
