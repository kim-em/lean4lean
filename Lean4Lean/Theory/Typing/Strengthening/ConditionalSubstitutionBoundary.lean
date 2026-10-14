import Lean4Lean.Theory.Typing.Strengthening.HeterogeneousSubstitutionEquality

/-! # Common-type entry agreement is insufficient for suspended substitution

Two source occurrences share a hidden type variable. Its two ambient realizations
may disagree. Every substitution entry then agrees conditionally at a common
type, while the complete beta redexes have lambda arguments, a common result type,
and distinct results.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- A tempting weakening of the entry invariant: entries need agree only when
separately supplied typings have convertible types. The example below refutes
using this premise in even common-mode suspended comparison descent. -/
def CommonEntryRel (Γ : List VExpr) (σ τ : Subst) : Prop :=
  ∀ i A B, (Γ ⊢ σ i : A) → (Γ ⊢ τ i : B) → (Γ ⊢ A ≡ B) → Γ ⊢ σ i ≡ τ i

namespace ConditionalBoundary

def prop : VExpr := .sort .zero
def outputType : VExpr := .sort (.succ .zero)
def funProp : VExpr := .forallE prop prop
def proposition : VExpr := .forallE prop (.bvar 0)
def identity : VExpr := .lam prop (.bvar 0)
def higherProp : VExpr := .forallE funProp prop
def higherFn : VExpr := .lam funProp proposition
def leftFn : VExpr := .lam funProp prop
def rightFn : VExpr := .lam higherProp funProp
def template : VExpr := .app (.bvar 1) (.bvar 0)
def sourceCtx : List VExpr := [.bvar 1, .forallE (.bvar 0) outputType, outputType]
def scopeLift : Lift := .cons (.cons (.skip .refl))
def belowSubst (x f : VExpr) : Subst := (Subst.id.cons f).cons x
def ambientSubst (T x f : VExpr) : Subst := ((Subst.id.cons T).cons f).cons x

def σ₁ : Subst := belowSubst identity leftFn
def σ₂ : Subst := belowSubst higherFn rightFn

private theorem prop_typed : Γ ⊢ prop : outputType := .sort (by trivial)
private theorem funProp_typed : Γ ⊢ funProp : outputType := by
  have h := HasType.forallE (prop_typed (Γ := Γ)) (prop_typed (Γ := prop :: Γ))
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (by trivial)
    (by trivial) VLevel.imax_self).defeq h
private theorem proposition_typed : Γ ⊢ proposition : prop := by
  have h := HasType.forallE (prop_typed (Γ := Γ)) (HasType.bvar (.zero) : prop :: Γ ⊢ .bvar 0 : prop)
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (by trivial)
    (by trivial) VLevel.imax_zero).defeq h
private theorem identity_typed : Γ ⊢ identity : funProp :=
  .lam prop_typed (.bvar .zero)
private theorem higherProp_typed : Γ ⊢ higherProp : outputType := by
  have h := HasType.forallE (funProp_typed (Γ := Γ)) (prop_typed (Γ := funProp :: Γ))
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (by trivial)
    (by trivial) VLevel.imax_self).defeq h
private theorem higherFn_typed : Γ ⊢ higherFn : higherProp :=
  .lam funProp_typed proposition_typed
private theorem leftFn_typed : Γ ⊢ leftFn : .forallE funProp outputType :=
  .lam funProp_typed prop_typed
private theorem rightFn_typed : Γ ⊢ rightFn : .forallE higherProp outputType :=
  .lam higherProp_typed funProp_typed

private theorem domains_ne (hΓ : OnCtx Γ (env.IsType univs)) : ¬ (Γ ⊢ prop ≡ funProp) :=
  IsDefEqU.sort_forallE_inv henv hΓ

private theorem argumentTypes_ne (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ (Γ ⊢ funProp ≡ higherProp) := by
  intro H
  obtain ⟨⟨_, hD⟩, _⟩ := H.forallE_inv henv hΓ
  exact domains_ne hΓ ⟨_, hD⟩

private theorem sourceFnType : [outputType] ⊢ .forallE (.bvar 0) outputType :
    .sort (.imax (.succ .zero) (.succ (.succ .zero))) :=
  .forallE (.bvar .zero) (.sort (by trivial))
private theorem sourceArgType : [.forallE (.bvar 0) outputType, outputType] ⊢ .bvar 1 : outputType :=
  .bvar (.succ .zero)

/-- The hidden source type is instantiated in the ambient target, while the
raw template contains only the function and its argument. -/
theorem square (hT : [] ⊢ T : outputType) (hx : [] ⊢ x : T)
    (hf : [] ⊢ f : .forallE T outputType) :
    SubstLiftSquare [] [] sourceCtx scopeLift .refl (belowSubst x f) (ambientSubst T x f) where
  context := .refl
  typed := by
    have h₀ := Ctx.SubstEq.id henv.ordered (show OnCtx ([] : List VExpr) (env.IsType univs) from trivial)
    have h₁ : Ctx.SubstEq env univs [] (Subst.id.cons T) (Subst.id.cons T) [outputType] :=
      .cons h₀ (HasType.sort (l := .succ .zero) (by trivial)) hT
    have h₂ : Ctx.SubstEq env univs [] ((Subst.id.cons T).cons f) ((Subst.id.cons T).cons f)
        [.forallE (.bvar 0) outputType, outputType] := .cons h₁ sourceFnType hf
    exact Ctx.SubstEq.cons h₂ sourceArgType hx
  commute := by
    intro i
    cases i with
    | zero => simp [ambientSubst, belowSubst, scopeLift, Subst.cons]
    | succ i =>
      cases i with
      | zero => simp [ambientSubst, belowSubst, scopeLift, Subst.cons]
      | succ i => simp [ambientSubst, belowSubst, scopeLift, Subst.cons]

private theorem source_typed : sourceCtx ⊢ template.lift' scopeLift : outputType := by
  have hf : sourceCtx ⊢ .bvar 1 : .forallE (.bvar 2) outputType := .bvar (.succ .zero)
  have hx : sourceCtx ⊢ .bvar 0 : .bvar 2 := .bvar .zero
  exact HasType.app hf hx

/-- The source comparison is reflexive, in common-type mode. -/
theorem source_comparison : BiNormal true 0 sourceCtx (template.lift' scopeLift) (template.lift' scopeLift) :=
  .refl source_typed

/-- The lower entries have conditional common-type agreement. At each of the
two used indices, type uniqueness makes that condition impossible. -/
theorem entries_common : CommonEntryRel [] σ₁ σ₂ := by
  intro i A B ha hb hAB
  have hΓ : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  cases i with
  | zero =>
    have h := (identity_typed.uniqU henv hΓ ha).trans henv hΓ
      (hAB.trans henv hΓ (hb.uniqU henv hΓ higherFn_typed))
    exact (argumentTypes_ne hΓ h).elim
  | succ i =>
    cases i with
    | zero =>
      have h := (leftFn_typed.uniqU henv hΓ ha).trans henv hΓ
        (hAB.trans henv hΓ (hb.uniqU henv hΓ rightFn_typed))
      obtain ⟨⟨_, hD⟩, _⟩ := h.forallE_inv henv hΓ
      exact (argumentTypes_ne hΓ ⟨_, hD⟩).elim
    | succ i => exact ⟨_, ha⟩

private theorem left_typed : [] ⊢ template.subst σ₁ : outputType :=
  HasType.app leftFn_typed identity_typed
private theorem right_typed : [] ⊢ template.subst σ₂ : outputType :=
  HasType.app rightFn_typed higherFn_typed

/-- Despite a common result type, the instantiated applications are not equal:
they beta-reduce to Prop and Prop → Prop, respectively. -/
theorem instances_ne : ¬ ([] ⊢ template.subst σ₁ ≡ template.subst σ₂) := by
  intro H
  have hΓ : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  have rl : BetaRed (template.subst σ₁) prop := .beta
  have rr : BetaRed (template.subst σ₂) funProp := .beta
  have el := rl.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ left_typed
  have er := rr.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ right_typed
  exact domains_ne hΓ ((show [] ⊢ _ ≡ _ from ⟨_, el.symm⟩).trans henv hΓ
    (H.trans henv hΓ ⟨_, er⟩))

/-- A counterexample to common-entry suspended descent in every Params
environment, hence also with canonical Eq. It refutes this weaker substitution
invariant, not strengthening: the two ambient substitutions realize different
hidden source types. -/
theorem common_entry_descent_failure :
    SubstLiftSquare [] [] sourceCtx scopeLift .refl σ₁ (ambientSubst funProp identity leftFn) ∧
    SubstLiftSquare [] [] sourceCtx scopeLift .refl σ₂ (ambientSubst higherProp higherFn rightFn) ∧
    CommonEntryRel [] σ₁ σ₂ ∧
    ([] ⊢ template.subst σ₁ : outputType) ∧ ([] ⊢ template.subst σ₂ : outputType) ∧
    BiNormal true 0 sourceCtx (template.lift' scopeLift) (template.lift' scopeLift) ∧
    ¬ ([] ⊢ template.subst σ₁ ≡ template.subst σ₂) :=
  ⟨square funProp_typed identity_typed leftFn_typed,
    square higherProp_typed higherFn_typed rightFn_typed,
    entries_common, left_typed, right_typed, source_comparison, instances_ne⟩

end ConditionalBoundary
end Lean4Lean.VEnv.Strengthening
