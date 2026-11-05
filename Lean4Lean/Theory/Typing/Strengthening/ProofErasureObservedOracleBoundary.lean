import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedRecordOracle

/-! # Why forward annotation provenance does not cover arbitrary conversion

A beta redex binding a proof can be an ordinary typed predecessor of a family
annotation. The current positive-control observer cannot observe that redex,
because every observed lambda domain has positive universe. This refutes
backward closure of this observer, not the desired native join or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType}
variable {uc ctor family : Name}

/-- No positive control type can be equal to an actual proposition. This uses
ordinary sort uniqueness only, without any native or operational hypothesis. -/
theorem no_proposition_control_equality (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    ¬ TypeEquality (proofEraseCtx Γ) (proofErase Γ P) domain := by
  intro H
  have HP := H.actual hΓ rfl hP rfl
  have E := (HP.hasType.1.uniqU henv hΓ hP).sort_inv henv hΓ
  exact domain.level_ne_zero [] (congrFun E [])

/-- A proof-domain redex cannot carry the operational record-family demand
in this observer, even when its entire body and argument are well typed. -/
theorem no_proof_domain_record_observation (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    ¬ Obs unit record parameter uc ctor family (proofEraseCtx Γ) S
      (.app (.lam (proofErase Γ P) b) a) (.type .record) := by
  intro H
  cases H with
  | app _ HF _ =>
    cases HF with
    | lam _ HE _ _ _ => exact no_proposition_control_equality hΓ hP HE

/-- The proof-domain constant beta wrapper is an actual typed type, and its
erasure contracts to the original annotation. Nevertheless the wrapper has no
record-family observation in the current grammar. -/
theorem proof_domain_beta_predecessor_boundary
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hz : env.HasType univs Γ z P) (hA : env.HasType univs Γ A (.sort u)) :
    env.IsDefEq univs Γ (.app (.lam P A.lift) z) A (.sort u) ∧
      BetaRed (proofErase Γ (.app (.lam P A.lift) z)) (proofErase Γ A) ∧
      ¬ Obs unit record parameter uc ctor family (proofEraseCtx Γ) S
        (proofErase Γ (.app (.lam P A.lift) z)) (.type .record) := by
  have HE : env.IsDefEq univs Γ (.app (.lam P A.lift) z) A (.sort u) := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (hA.weak henv) hz
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have hAP : env.HasType univs (P :: Γ) A.lift (.sort u) := hA.weak henv
  have hLam := HasType.lam hP hAP
  have EE : proofErase Γ (.app (.lam P A.lift) z) =
      .app (.lam (proofErase Γ P) ((proofErase Γ A).liftN 1)) .proof := by
    rw [show proofErase Γ (.app (.lam P A.lift) z) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.1),
      show proofErase Γ (.lam P A.lift) = .lam _ _ from
        if_neg (not_isProof_function_to_sort hΓ hLam),
      proofErase_liftN hΓ hΓP Ctx.LiftN.one hA,
      proofErase_eq_proof.2 (show IsProof Γ z from ⟨P, hz, hP⟩)]
  refine ⟨HE, ?_, ?_⟩
  · rw [EE]
    simpa only [ProofShape.inst_eq_subst, Subst.liftN, Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (BetaRed.beta (A := proofErase Γ P) (b := (proofErase Γ A).liftN 1) (a := .proof))
  · rw [EE]
    exact no_proof_domain_record_observation hΓ hP

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- A concrete family seed has an ordinarily equal, beta-contracting typed
predecessor that is not a seed. Thus replacing directed provenance by ordinary
equality cannot establish seed coverage, even for this registered family. -/
theorem family_seed_not_backward_closed
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hz : env.HasType univs Γ z P) (hp : env.HasType univs Γ p (Q.control U).expr) :
    ∃ A, env.IsDefEq univs Γ A (.app (.const t []) p) (.sort (.succ .zero)) ∧
      BetaRed (proofErase Γ A) (proofErase Γ (.app (.const t []) p)) ∧
      AnnotationSeed U RT (Q.control U) uc c t (proofEraseCtx Γ)
        (proofErase Γ (.app (.const t []) p)) .record ∧
      ¬ AnnotationSeed U RT (Q.control U) uc c t (proofEraseCtx Γ) (proofErase Γ A) .record := by
  obtain ⟨HE, HB, HN⟩ := proof_domain_beta_predecessor_boundary
    (unit := U) (record := RT) (parameter := Q.control U) (uc := uc) (ctor := c) (family := t)
    (S := fun _ _ => False) hΓ hP hz ((hF.weak0 henv.ordered).app hp)
  exact ⟨_, HE, HB, family_annotation_seed hi hS Q hTag hF hΓ hp, fun H => HN H.2⟩

/-- The seed-coverage obstruction needs no assumed proposition inhabitant:
the closed identity proof of `(forall X : Prop, X) -> (forall X : Prop, X)`
supplies one in every well-formed context. Thus ordinary equality to this very
family cannot be sufficient for the present annotation-seed grammar. -/
theorem family_seed_not_conversion_complete
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (Q.control U).expr) :
    ∃ A, env.IsDefEq univs Γ A (.app (.const t []) p) (.sort (.succ .zero)) ∧
      BetaRed (proofErase Γ A) (proofErase Γ (.app (.const t []) p)) ∧
      ¬ AnnotationSeed U RT (Q.control U) uc c t (proofEraseCtx Γ) (proofErase Γ A) .record := by
  let F : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hFalse : env.HasType univs Γ F (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_zero).defeq
      (HasType.forallE (HasType.sort (l := .zero) (by trivial)) (HasType.bvar .zero))
  have hP : env.HasType univs Γ (.forallE F F.lift) (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE hFalse (hFalse.weak henv))
  have hz : env.HasType univs Γ (.lam F (.bvar 0)) (.forallE F F.lift) :=
    HasType.lam hFalse (.bvar .zero)
  obtain ⟨A, HE, HB, _, HN⟩ := family_seed_not_backward_closed hi hS Q hTag hF hΓ hP hz hp
  exact ⟨A, HE, HB, HN⟩

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
