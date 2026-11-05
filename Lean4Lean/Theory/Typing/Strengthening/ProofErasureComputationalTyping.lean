import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationPiInjectivity
import Lean4Lean.Theory.Typing.Strong

/-! # Application typing with computational conversions

As in the existing joinable-typing construction, variables, constants and applications
retain their structural typings, while other syntax retains ordinary typing.
Every assignment conversion is now an actual typed computation chain. Strong
ordinary derivations can produce these certificates together with term chains,
subject to the remaining pattern coverage obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- A typed computation chain between types at some common universe. -/
def TypedComputationTypeEq (D : PureObservation.Definitions) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∃ u, TypedComputationEq D Γ A B (.sort u)

/-- Computational type equality retains its ordinary equality. -/
theorem TypedComputationTypeEq.defeq (H : TypedComputationTypeEq D Γ A B) :
    env.IsDefEqU univs Γ A B := by
  obtain ⟨u, H⟩ := H
  exact ⟨.sort u, H.defeq⟩

/-- A well-formed type has a reflexive computational comparison. -/
theorem TypedComputationTypeEq.refl (H : env.IsType univs Γ A) : TypedComputationTypeEq D Γ A A := by
  obtain ⟨u, H⟩ := H
  exact ⟨u, .refl H⟩

/-- The type of an actual term supplies a reflexive comparison. -/
theorem TypedComputationTypeEq.of_typing (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.HasType univs Γ e A) : TypedComputationTypeEq D Γ A A :=
  .refl (H.isType henv hΓ)

/-- Computational type equality is symmetric. -/
theorem TypedComputationTypeEq.symm (H : TypedComputationTypeEq D Γ A B) :
    TypedComputationTypeEq D Γ B A := by
  obtain ⟨u, H⟩ := H
  exact ⟨u, H.symm⟩

/-- The actual middle assignment aligns the universes of two type chains. -/
theorem TypedComputationTypeEq.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationTypeEq D Γ A B) (H' : TypedComputationTypeEq D Γ B C) :
    TypedComputationTypeEq D Γ A C := by
  obtain ⟨u, H⟩ := H
  obtain ⟨_, H'⟩ := H'
  exact ⟨u, H.trans (H'.at_source_type hΓ H.defeq.hasType.2)⟩

/-- Computational Pi injectivity supplies both component comparisons under
the left binder. Type-fork joining remains an explicit premise. -/
theorem TypedComputationTypeEq.forallE_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationTypeEq D Γ (.forallE A B) (.forallE A' B')) :
    TypedComputationTypeEq D Γ A A' ∧ TypedComputationTypeEq D (A :: Γ) B B' := by
  obtain ⟨_, H⟩ := H
  exact H.forallE_inv heq hs HF hΓ

/-- Computational type equality survives an arbitrary typed argument. -/
theorem TypedComputationTypeEq.inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.IsType univs Γ A)
    (hx : env.HasType univs Γ x A) (H : TypedComputationTypeEq D (A :: Γ) B C) :
    TypedComputationTypeEq D Γ (B.inst x) (C.inst x) := by
  obtain ⟨u, hA⟩ := hA
  obtain ⟨v, H⟩ := H
  exact ⟨v, H.inst heq hs hΓ hA hx⟩

/-- Structural variable/constant/application typing with computational assignment
conversions. Ordinary typing of other syntax alone does not license a conversion
of a variable, constant or application. This is not claimed complete unconditionally. -/
inductive HasTypeC (D : PureObservation.Definitions) : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → HasTypeC D Γ (.bvar i) A
  | const : env.constants c = some ci → env.HasType univs Γ (.const c ls) (ci.type.instL ls) →
      HasTypeC D Γ (.const c ls) (ci.type.instL ls)
  | app : HasTypeC D Γ f (.forallE A B) → HasTypeC D Γ a A →
      env.HasType univs Γ (.app f a) (B.inst a) → HasTypeC D Γ (.app f a) (B.inst a)
  | other : (∀ f a, e ≠ .app f a) → (∀ c ls, e ≠ .const c ls) → (∀ i, e ≠ .bvar i) →
      env.HasType univs Γ e A → HasTypeC D Γ e A
  | convert : TypedComputationTypeEq D Γ A B → HasTypeC D Γ e A →
      env.HasType univs Γ e B → HasTypeC D Γ e B

/-- Every computational typing certificate retains ordinary typing. -/
theorem HasTypeC.hasType : HasTypeC D Γ e A → env.HasType univs Γ e A
  | .bvar h => .bvar h
  | .const _ H | .app _ _ H | .other _ _ _ H | .convert _ _ H => H

/-- Application inversion retains the computational result-type conversion. -/
theorem HasTypeC.app_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeC D Γ (.app f a) T) :
    ∃ A B, HasTypeC D Γ f (.forallE A B) ∧ HasTypeC D Γ a A ∧
      TypedComputationTypeEq D Γ (B.inst a) T := by
  generalize he : VExpr.app f a = e at H
  induction H with
  | bvar | const => cases he
  | app hf ha h => cases he; exact ⟨_, _, hf, ha, .of_typing hΓ h⟩
  | other hne => exact (hne _ _ he.symm).elim
  | convert hAB _ _ ih =>
    obtain ⟨A, B, hf, ha, hj⟩ := ih hΓ he
    exact ⟨A, B, hf, ha, hj.trans hΓ hAB⟩

/-- Constant inversion retains a chain from its literal declared type. -/
theorem HasTypeC.const_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeC D Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ TypedComputationTypeEq D Γ (ci.type.instL ls) T := by
  generalize he : VExpr.const c ls = e at H
  induction H with
  | const hc h => cases he; exact ⟨_, hc, .of_typing hΓ h⟩
  | bvar | app => cases he
  | other _ hne => exact (hne _ _ he.symm).elim
  | convert hAB _ _ ih =>
    obtain ⟨ci, hc, hj⟩ := ih hΓ he
    exact ⟨ci, hc, hj.trans hΓ hAB⟩

/-- Variable inversion retains its exact context lookup and every later
computational conversion. Ordinary typing alone does not provide this chain. -/
theorem HasTypeC.bvar_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeC D Γ (.bvar i) T) :
    ∃ A, Lookup Γ i A ∧ TypedComputationTypeEq D Γ A T := by
  generalize he : VExpr.bvar i = e at H
  induction H with
  | bvar h => cases he; exact ⟨_, h, .of_typing hΓ (.bvar h)⟩
  | const | app => cases he
  | other _ _ hne => exact (hne _ he.symm).elim
  | convert hAB _ _ ih =>
    obtain ⟨A, hA, hj⟩ := ih hΓ he
    exact ⟨A, hA, hj.trans hΓ hAB⟩

/-- Two computational typings of the same variable give a type chain from
literal lookup uniqueness. No type-fork joining premise is needed. -/
theorem HasTypeC.bvar_uniq (hΓ : OnCtx Γ (env.IsType univs))
    (H : HasTypeC D Γ (.bvar i) A) (H' : HasTypeC D Γ (.bvar i) B) :
    TypedComputationTypeEq D Γ A B := by
  obtain ⟨X, hX, HX⟩ := H.bvar_inv hΓ
  obtain ⟨Y, hY, HY⟩ := H'.bvar_inv hΓ
  cases hX.uniq hY
  exact HX.symm.trans hΓ HY

end Lean4Lean.VEnv.Strengthening
