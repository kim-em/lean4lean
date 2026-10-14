import Lean4Lean.Theory.Typing.Strengthening.TypeHeadComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaCore

/-! # Cast-head recovery over a preceding computational stage

Payload computations may use any base with checked ordinary descent. The added
cast-head rules need only sort-source descent, and are used to recover types.
A separate eta step consumes that recovery without treating the cast rules as
arbitrary term computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- Extend type computation with outer casts whose payload exposes a Pi or
saturated family using the preceding ordinary computation. -/
inductive TypeHeadExtension (C : List VExpr → VExpr → VExpr → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | base : C Γ e out → TypeHeadExtension C Γ e out
  | castPi : C Γ x (.forallE A B) →
      TypeHeadExtension C Γ (typeCast u X Y p x) (.forallE A B)
  | castFamily : env.projections s info → args.length = info.nparams + info.nindices →
      C Γ x (mkApps (.const s ls) args) →
      TypeHeadExtension C Γ (typeCast u X Y p x) (mkApps (.const s ls) args)
  | trans : TypeHeadExtension C Γ a b → TypeHeadExtension C Γ b c →
      TypeHeadExtension C Γ a c

/-- Source sort typing justifies both added cast rules after lowering the
payload path. No lower computation certificate for that path is required. -/
theorem TypeHeadExtension.typeDescent (heq : env.HasCanonicalEq) (hc : ComputeDescent C) :
    TypeComputeDescent (TypeHeadExtension C) := by
  intro ρ Γ Γ' e target v R W hΓ hΓ' ht
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing ρ Γ e v with
  | base R =>
    rw [← hsrc] at R
    exact hc R W hΓ hΓ' ht
  | castPi R =>
    obtain ⟨X, Y, p, x, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_typeCast hsrc
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    obtain ⟨out, ho, H⟩ := hc R W hΓ hΓ' hx
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE ho.symm
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := HasType.forallE_inv henv.ordered H.hasType.2
    have hxt := IsType.defeqU_l henv hΓ ⟨_, H.symm⟩ ⟨_, HasType.forallE hA hB⟩
    exact ⟨_, rfl, (cast_type_eq henv heq hΓ ht hxt).trans_l henv hΓ H⟩
  | castFamily hi ha R =>
    obtain ⟨X, Y, p, x, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_typeCast hsrc
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    obtain ⟨out, ho, H⟩ := hc R W hΓ hΓ' hx
    obtain ⟨args, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine ho.symm
    have hf := StructureReplay.family_isType_of_arity henv hΓ hi ⟨_, H.hasType.2⟩
      (by simpa using ha)
    have hxt := IsType.defeqU_l henv hΓ ⟨_, H.symm⟩ hf
    exact ⟨_, by simp only [lift'_mkApps, lift'],
      (cast_type_eq henv heq hΓ ht hxt).trans_l henv hΓ H⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨mid, hm, H1⟩ := ih1 W hΓ hΓ' ht hsrc
    obtain ⟨out, ho, H2⟩ := ih2 W hΓ hΓ' H1.hasType.2 hm.symm
    exact ⟨out, ho, H1.trans H2⟩

/-- Weakening depends only on the preceding stage's weakening. -/
theorem TypeHeadExtension.weakening (hw : ComputeWeakening C) :
    ComputeWeakening (TypeHeadExtension C) := by
  intro n k Γ Γ' e out W R
  induction R with
  | base R => exact .base (hw W R)
  | castPi R =>
    simpa only [← lift'_consN_skipN, typeCast_lift', lift', Lift.consN] using
      TypeHeadExtension.castPi (hw W R)
  | castFamily hi ha R =>
    have R' := hw W R
    simp only [liftN_mkApps, liftN] at R'
    simpa only [← lift'_consN_skipN, typeCast_lift', lift'_mkApps, lift'] using
      TypeHeadExtension.castFamily hi (by simpa using ha) R'
  | trans _ _ ih1 ih2 => exact (ih1 W).trans (ih2 W)

/-- Enlarging the payload computation preserves all type-head certificates. -/
theorem TypeHeadExtension.mono (hC : ∀ {Γ a b}, C Γ a b → C' Γ a b)
    (R : TypeHeadExtension C Γ e out) : TypeHeadExtension C' Γ e out := by
  induction R with
  | base R => exact .base (hC R)
  | castPi R => exact .castPi (hC R)
  | castFamily hi ha R => exact .castFamily hi ha (hC R)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The extended inferred types may guard arbitrary common-type endpoints. -/
theorem TypeHeadExtension.comparisonDescent (heq : env.HasCanonicalEq) (hc : ComputeDescent C) :
    EndpointDescent (RecoveredComparisonWith (TypeHeadExtension C) true) := by
  intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
  obtain ⟨_, hα⟩ := ha.isType henv hΓ
  exact H.descend_of_types (typeDescent heq hc) W hΓ hΓ' ha hb ⟨_, hα⟩

/-- An ordinary term step whose eta annotations are reconstructed using a
possibly different, type-restricted computational base. -/
inductive TypedEtaStep (TC : List VExpr → VExpr → VExpr → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | eta : TypeRecoveryWith TC Γ e (.forallE A B) →
      TypedEtaStep TC Γ e (.lam A (.app e.lift (.bvar 0)))

/-- Only type descent is needed to validate the new eta step at arbitrary
source types. Its annotation is reconstructed below from source typing. -/
theorem TypedEtaStep.computeDescent (hc : TypeComputeDescent TC) :
    ComputeDescent (TypedEtaStep TC) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  generalize hsrc : e.lift' ρ = source at R
  cases R with
  | eta R =>
    rw [← hsrc] at R
    obtain ⟨ty, hty, hf⟩ := R.descend_of_types hc W hΓ hΓ' ⟨_, ht⟩
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hty.symm
    refine ⟨.lam A (.app e.lift (.bvar 0)), ?_, ?_⟩
    · simp only [lift', lift_lift'_cons, Lift.liftVar, hsrc]
    · exact IsDefEq.trans_l henv hΓ ht (IsDefEq.eta hf).symm

/-- Type certificates and their eta expansion weaken together. -/
theorem TypedEtaStep.weakening (hw : ComputeWeakening TC) :
    ComputeWeakening (TypedEtaStep TC) := by
  intro n k Γ Γ' e out W R
  cases R with
  | eta R =>
    simpa only [liftN, liftVar, Nat.zero_lt_succ, if_true, ← lift_liftN'] using
      TypedEtaStep.eta (R.weakN hw W)

/-- Enlarging only the annotation computation enlarges the eta step. -/
theorem TypedEtaStep.mono (hC : ∀ {Γ a b}, TC Γ a b → TC' Γ a b)
    (R : TypedEtaStep TC Γ e out) : TypedEtaStep TC' Γ e out := by
  cases R with
  | eta R => exact .eta (R.mono hC)

end Lean4Lean.VEnv.Strengthening
