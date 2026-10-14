import Lean4Lean.Theory.Typing.Strengthening.CastFamilyExposure
import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparisonCore
import Lean4Lean.Theory.Typing.Strengthening.GuardedKComputation

/-! # Type computation with outer cast head recovery

The added rules replay at sort-typed sources. They do not assert arbitrary-term
cast erasure. TypeRecoveryWith only computes inferred types, so its type-only
descent interface admits these rules directly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)

/-- Binder insertion reflects all providers of a type cast, without requiring
the cast's endpoint expressions to match each other. -/
theorem lift'_eq_typeCast (h : e.lift' ρ = typeCast u X Y p x) :
    ∃ X₀ Y₀ p₀ x₀, e = typeCast u X₀ Y₀ p₀ x₀ ∧
      X = X₀.lift' ρ ∧ Y = Y₀.lift' ρ ∧ p = p₀.lift' ρ ∧ x = x₀.lift' ρ := by
  have he := congrArg (fun e => e.subst ρ.inv) h
  simp only [subst_lift', lift_l_inv, subst_id, typeCast_subst] at he
  refine ⟨_, _, _, _, he, ?_⟩
  have hh := h.symm.trans (congrArg (fun e => e.lift' ρ) he)
  rw [typeCast_lift'] at hh
  simp only [typeCast, eqRecApp, VExpr.app.injEq] at hh
  exact ⟨hh.1.1.1.1.2, hh.1.2, hh.2, hh.1.1.2⟩

variable [Params] {D : Definitions}

/-- Root type computation: ordinary cast computation, Pi/family exposure
through an outer cast, and composition. Endpoint equality is not a rule premise. -/
inductive TypeHeadCompute (D : Definitions) : VExpr → VExpr → Prop where
  | base : CastCompute D e out → TypeHeadCompute D e out
  | castPi : CastCompute D x (.forallE A B) →
      TypeHeadCompute D (typeCast u X Y p x) (.forallE A B)
  | castFamily : env.projections s info → args.length = info.nparams + info.nindices →
      CastCompute D x (mkApps (.const s ls) args) →
      TypeHeadCompute D (typeCast u X Y p x) (mkApps (.const s ls) args)
  | trans : TypeHeadCompute D a b → TypeHeadCompute D b c → TypeHeadCompute D a c

/-- Raw substitution preserves head certificates and family saturation. -/
theorem TypeHeadCompute.subst (R : TypeHeadCompute D e out) :
    TypeHeadCompute D (e.subst σ) (out.subst σ) := by
  induction R with
  | base R => exact .base R.subst
  | castPi R => simpa only [typeCast_subst, VExpr.subst] using TypeHeadCompute.castPi R.subst
  | castFamily hi ha R =>
    have R' := R.subst (σ := σ)
    simp only [subst_mkApps, VExpr.subst] at R'
    simpa only [typeCast_subst, subst_mkApps, VExpr.subst] using
      TypeHeadCompute.castFamily hi (by simpa using ha) R'
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Binder renaming is a special case of raw substitution. -/
theorem TypeHeadCompute.lift (R : TypeHeadCompute D e out) :
    TypeHeadCompute D (e.lift' ρ) (out.lift' ρ) := by
  simpa only [← lift_as_subst] using R.subst (σ := Subst.lift_r .id ρ)

/-- The same concrete type computations may be used beneath added binders. -/
theorem TypeHeadCompute.weakening : ComputeWeakening (fun _ => TypeHeadCompute D) := by
  intro n k Γ Γ' e out _ R
  simpa only [lift'_consN_skipN] using R.lift (ρ := .consN (.skipN .refl n) k)

/-- A payload computation to a type licenses the outer cast computation when
the source cast itself has sort type. -/
theorem cast_compute_type_eq (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.HasType univs Γ (typeCast u X Y p x) (.sort v))
    (R : CastCompute D x out) (hout : env.IsType univs Γ out) :
    env.IsDefEq univs Γ (typeCast u X Y p x) out (.sort v) := by
  obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, hc⟩
  have H := R.simAt heq hs hΓ X hx
  have hxt := IsType.defeqU_l henv hΓ ⟨_, H.symm⟩ hout
  exact (cast_type_eq henv heq hΓ hc hxt).trans_l henv hΓ H

/-- Every type-head computation replays at the source sort. There is no claim
of SimAt for arbitrary source types. -/
theorem TypeHeadCompute.replay (R : TypeHeadCompute D e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v)) :
    env.IsDefEq univs Γ e out (.sort v) := by
  induction R with
  | base R => exact R.simAt heq hs hΓ _ ht
  | castPi R =>
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    have H := R.simAt heq hs hΓ _ hx
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := HasType.forallE_inv henv.ordered H.hasType.2
    exact cast_compute_type_eq heq hs hΓ ht R ⟨_, .forallE hA hB⟩
  | castFamily hi ha R =>
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    have H := R.simAt heq hs hΓ _ hx
    exact cast_compute_type_eq heq hs hΓ ht R
      (StructureReplay.family_isType_of_arity henv hΓ hi ⟨_, H.hasType.2⟩ ha)
  | trans _ _ ih1 ih2 =>
    have H := ih1 ht
    exact H.trans_l henv hΓ (ih2 H.hasType.2)

/-- The new rules reflect scope exactly: payload computation reflects scope,
and a cast source exposes the same lower payload by syntactic inversion. -/
theorem TypeHeadCompute.lift_inv (R : TypeHeadCompute D (e.lift' ρ) target) :
    ∃ out, TypeHeadCompute D e out ∧ target = out.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | base R =>
    rw [← hsrc] at R
    obtain ⟨out, R, he⟩ := R.lift_inv
    exact ⟨out, .base R, he⟩
  | castPi R =>
    obtain ⟨X, Y, p, x, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_typeCast hsrc
    obtain ⟨out, R₀, he⟩ := CastCompute.lift_inv R
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE he.symm
    exact ⟨_, .castPi R₀, rfl⟩
  | castFamily hi ha R =>
    obtain ⟨X, Y, p, x, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_typeCast hsrc
    obtain ⟨out, R₀, he⟩ := CastCompute.lift_inv R
    obtain ⟨args, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine he.symm
    exact ⟨_, .castFamily hi (by simpa using ha) R₀, by simp only [lift'_mkApps, lift']⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨mid, R1, he1⟩ := ih1 hsrc
    obtain ⟨out, R2, he2⟩ := ih2 he1.symm
    exact ⟨out, R1.trans R2, he2⟩

/-- The concrete type-only descent interface needed for recovery. -/
theorem TypeHeadCompute.typeDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    TypeComputeDescent (fun _ => TypeHeadCompute D) := by
  intro ρ Γ Γ' e target u R _ hΓ _ ht
  obtain ⟨out, R₀, he⟩ := R.lift_inv
  exact ⟨out, he, R₀.replay heq hs hΓ ht⟩

/-- Recovery with the cast-head rules supplies valid endpoint comparisons for
K guards. The endpoints themselves may have any common lower type. -/
theorem TypeHeadCompute.comparisonDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    EndpointDescent (RecoveredComparisonWith (fun _ => TypeHeadCompute D) true) := by
  intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
  obtain ⟨_, hα⟩ := ha.isType henv hΓ
  exact H.descend_of_types (typeDescent heq hs) W hΓ hΓ' ha hb ⟨_, hα⟩

/-- Compatible K computation guarded by these recovered comparisons has full
arbitrary-source descent, although its recovery base uses only type replay. -/
theorem TypeHeadCompute.guardedDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ComputeDescent (GuardedKCompute D
      (RecoveredComparisonWith (fun _ => TypeHeadCompute D) true)) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  obtain ⟨out, he, H⟩ := R.descend heq hs (comparisonDescent heq hs) W hΓ hΓ'
  exact ⟨out, he, H T ht⟩

end Lean4Lean.VEnv.Strengthening
