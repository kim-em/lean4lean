import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyCompositionBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront

/-! # Future carrier composition still contains the proposition front

Retaining carriers repairs the literal-unit counterexample. However, even
composition of certificates retaining arbitrary future substitutions and beta
paths implies PropositionFront, conditional on a closed positive unit. The
Eq probe hides that unit behind arbitrary proposition conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private unit_constructor_bridge
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypedCompositionBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- Missing composition law for future carrier certificates with an actual
commonly typed intermediate. Only a base target guard is requested. This is
not established, even from source False into the full joint union, and is not
claimed to be strictly smaller than PropositionFront. -/
def TypedFutureCarrierComposition
    (Source Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ a m b A}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a A → env.HasType univs Γ m A → env.HasType univs Γ b A →
    BetaStableCarrier Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ m) →
    BetaStableCarrier Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ m) (proofErase Γ b) →
    JointCarrierGuard Target (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)

/-- Composing two future carrier certificates through the actual unit
constructor descends proposition equality. Both inputs retain all future
carrier/endpoint beta paths and interpreted substitutions, at any source
relation. The output asks only for a base guard in the full union. -/
theorem TypedFutureCarrierComposition.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcomp : TypedFutureCarrierComposition Source (ErasedJointUnion D))
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
  have Ei : proofErase Γ' (.bvar i) = .bvar i :=
    if_neg (not_proof_at_positive_type hΓ' hSw hiT)
  have Ej : proofErase Γ' (.bvar j) = .bvar j :=
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)
  obtain ⟨hm, Em, _⟩ := unit_constructor_bridge (Step := Source) hΓ' hi hp hx hf hSw hiT
  have HL : BetaStableCarrier Source (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe (.succ u) (.const family ls) (P.liftN n) (Q.liftN n) q))
      (proofErase Γ' (.bvar i)) (proofErase Γ' (.const info.ctorName ls)) := by
    rw [Em]
    exact (unit_constructor_family hi hp hx hf).joint_symm.carrier
  have HR : BetaStableCarrier Source (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe (.succ u) (.const family ls) (P.liftN n) (Q.liftN n) q))
      (proofErase Γ' (.const info.ctorName ls)) (proofErase Γ' (.bvar j)) := by
    rw [Em]
    exact (unit_constructor_family hi hp hx hf).carrier
  have HG := Hcomp hΓ' (HE.symm.defeq hiT) (HE.symm.defeq hm) (HE.symm.defeq hjT) HL HR
  rw [Ei, Ej] at HG
  rcases HG.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact (hne (HC.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Typed composition of future carrier certificates already implies the
full proposition front in the presence of a closed positive empty structure.
This conditional sufficiency result does not prove composition, strictness,
or an unconditional converse. -/
theorem TypedFutureCarrierComposition.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcomp : TypedFutureCarrierComposition Source (ErasedJointUnion D))
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
  exact Hcomp.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4


/-- Even with every future certificate, source computations need not bound
those needed by the composite. With a closed positive unit, composition from
any source relation (including False) into stage zero is false. The probe
indices are reflexive, so this failure uses no unresolved proposition front. -/
theorem TypedFutureCarrierComposition.not_zero_of_closed_unit
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ¬ TypedFutureCarrierComposition Source (ErasedJointStage D 0) := by
  intro Hcomp
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hiT : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hjT : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  let P := eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
  have hP : env.HasType univs Γ P (.sort .zero) := HasType.eqApp heq (by trivial)
    (HasType.sort (by trivial)) (HasType.sort (by trivial)) (HasType.sort (by trivial))
  have hq := HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hP
  have HE := eqTypeProbe_defeq heq hΓ hSΓ hP hP hq ⟨_, hP⟩
  obtain ⟨hm, Em, _⟩ := unit_constructor_bridge (Step := Source) hΓ hi hp hx hf hSΓ hiT
  have HL : BetaStableCarrier Source (proofEraseCtx Γ) (proofErase Γ
      (eqTypeProbe (.succ u) S P P (eqReflApp (.succ .zero) (.sort .zero) P)))
      (proofErase Γ (.bvar 0)) (proofErase Γ (.const info.ctorName ls)) := by
    rw [Em]
    exact (unit_constructor_family hi hp hx hf).joint_symm.carrier
  have HR : BetaStableCarrier Source (proofEraseCtx Γ) (proofErase Γ
      (eqTypeProbe (.succ u) S P P (eqReflApp (.succ .zero) (.sort .zero) P)))
      (proofErase Γ (.const info.ctorName ls)) (proofErase Γ (.bvar 1)) := by
    rw [Em]
    exact (unit_constructor_family hi hp hx hf).carrier
  have HG := Hcomp hΓ (HE.symm.defeq hiT) (HE.symm.defeq hm) (HE.symm.defeq hjT) HL HR
  rw [show proofErase Γ (.bvar 0) = .bvar 0 from
    if_neg (not_proof_at_positive_type hΓ hSΓ hiT),
    show proofErase Γ (.bvar 1) = .bvar 1 from
    if_neg (not_proof_at_positive_type hΓ hSΓ hjT)] at HG
  exact eqTypeProbe_zero_no_distinct_guard heq hregistry hRec hΓ hSΓ hP hP hq (by decide) HG

end Lean4Lean.VEnv.Strengthening
