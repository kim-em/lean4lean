import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadTyping
import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaEnvironment

/-! # Recursive environment tests for declaration head exposure

The admitted equation D := D → (Prop → Prop) gives a genuine delta-only head
exposure unavailable to the beta-only model, in a canonical-Eq extension. A mixed
eta/beta/delta trace also checks exposure across an unscoped intermediate annotation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Developments GuardedEta

/-- The recursive declaration is recognized by the actual-environment model. -/
theorem guarded_definition (henv : (extended base c).WF) (U : Nat) :
    (Definitions.ofEnv (extended base c) U henv).unfolds c [] (domainValue c) := by
  refine ⟨(declaration c).toDefEq, [], .inl rfl, by simp, rfl, ?_, ?_⟩ <;>
    simp [VDefVal.toDefEq, declaration, domainValue, domain, resultType, prop,
      instL, VLevel.params, VLevel.inst]

/-- The extension exposes a recursive Pi head that beta alone cannot expose. -/
theorem guarded_delta_exposure (henv : (extended base c).WF) (U : Nat) :
    Compute (Definitions.ofEnv (extended base c) U henv) (domain c) (domainValue c) ∧
      ¬ ∃ A B, BetaRed (domain c) (.forallE A B) := by
  refine ⟨.delta (guarded_definition henv U), ?_⟩
  rintro ⟨A, B, R⟩
  have he := beta_eq_of_not_hasBeta R (by simp [domain, HasBeta])
  cases he

/-- Head exposure and typed reconstruction are available in an actual
canonical-Eq extension, even though the constant has no beta Pi reduct. -/
theorem canonical_recursive_head (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) (U : Nat) :
    ∃ henv : (extended base c).WF, (extended base c).HasCanonicalEq ∧
      Compute (Definitions.ofEnv (extended base c) U henv) (domain c) (domainValue c) ∧
      (¬ ∃ A B, BetaRed (domain c) (.forallE A B)) ∧
      ∀ Γ f, OnCtx Γ ((extended base c).IsType U) →
        HasType (extended base c) U Γ f (domain c) →
        ∃ A B, HasType (extended base c) U Γ f (.forallE A B) := by
  let henv := extended_wf hbase hfresh
  obtain ⟨R, hn⟩ := guarded_delta_exposure henv U
  refine ⟨henv, extended_canonicalEq heq hfresh, R, hn, ?_⟩
  intro Γ f hΓ hf
  have RE : ComputeEta (Definitions.ofEnv (extended base c) U henv)
      ((domain c).lift' Lift.refl.skip) (domainValue c) := .compute R
  obtain ⟨A, B, ht, _⟩ := RE.function_type_below henv (Definitions.ofEnv_sound henv) hΓ hf
  exact ⟨A, B, ht⟩

/-- A well-scoped source whose beta result is the recursive type constant. -/
def aliasSource (c : Name) : VExpr := .app (.lam (.sort (.succ .zero)) (domain c)) prop

/-- An eta expansion of the source's function, with an arbitrary annotation. -/
def aliasIntermediate (c : Name) (A : VExpr) : VExpr :=
  .app (.lam A (.app (VExpr.lam (.sort (.succ .zero)) (domain c)).lift (.bvar 0))) prop

/-- Eta and two beta contractions may precede the decisive recursive unfolding.
This trace is syntactic: its arbitrary eta annotation need not be well typed. -/
theorem alias_trace (hd : D.unfolds c [] (domainValue c)) :
    ComputeEta D (aliasSource c) (aliasIntermediate c A) ∧
      ComputeEta D (aliasIntermediate c A) (domainValue c) := by
  refine ⟨.app .eta (.compute .refl), .compute ?_⟩
  have first : Compute D (aliasIntermediate c A) (aliasSource c) := by
    simpa only [aliasIntermediate, aliasSource, inst, inst_lift, instVar_zero] using
      (Compute.beta (D := D) (A := A)
        (b := .app (VExpr.lam (.sort (.succ .zero)) (domain c)).lift (.bvar 0)) (a := prop))
  have second : Compute D (aliasSource c) (domain c) := by
    simpa only [aliasSource, domain, inst] using
      (Compute.beta (D := D) (A := .sort (.succ .zero)) (b := domain c) (a := prop))
  exact first.trans (second.trans (.delta hd))

/-- A captured eta annotation can occur in a beta/delta head trace above a lift;
the recovered computational head still lies below that lift. -/
theorem captured_alias_exposure (hd : D.unfolds c [] (domainValue c)) :
    ¬ (aliasIntermediate c (.bvar 0)).Skips 1 0 ∧
      ∃ A B, Compute D (aliasSource c) (.forallE A B) := by
  refine ⟨by simp [aliasIntermediate, skips_iff, Skips'], ?_⟩
  have trace := (alias_trace (A := .bvar 0) hd).1.trans (alias_trace (A := .bvar 0) hd).2
  have R : ComputeEta D ((aliasSource c).lift' Lift.refl.skip) (domainValue c) := by
    simpa [aliasSource, domain, prop, VExpr.lift', Lift.liftVar] using trace
  exact R.pi_exposure_below

end Lean4Lean.VEnv.Strengthening.PureObservation
