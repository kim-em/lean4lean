import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSequentialInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-! # A boundary for uniform type abstraction

Sequential specialization needs a typed certificate in the abstract context.
Replacing an arbitrary concrete function domain by a type variable cannot
supply that premise while retaining the body: even ordinary application loses
its typing and its native Pi readout. This refutes this proposed abstraction
step, not strengthening or the conditional sequential transport theorems.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeAbstractionBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The concrete domain is `Type → Type`, with no environment declarations. -/
def concreteDomain : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))

/-- An abstract type and a value of that type. -/
def abstractContext : List VExpr := [.bvar 0, .sort (.succ (.succ .zero))]

/-- The body applies the value to `Prop`. -/
def applicationBody : VExpr := .app (.bvar 0) (.sort .zero)

/-- The concrete domain inhabits the same universe as the abstract type. -/
theorem concreteDomain_typed : env.HasType univs [] concreteDomain
    (.sort (.succ (.succ .zero))) := by
  exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
    (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))

/-- The abstract context is well formed; the obstruction is its missing type
structure rather than a malformed context. -/
theorem abstractContext_wf : OnCtx abstractContext (env.IsType univs) :=
  ⟨⟨trivial, _, HasType.sort (by trivial)⟩, _, HasType.bvar .zero⟩

/-- At the original function type the unchanged application body is typed. -/
theorem concrete_body_typed : env.HasType univs [concreteDomain] applicationBody
    (.sort (.succ .zero)) := by
  have hf : env.HasType univs [concreteDomain] (.bvar 0) concreteDomain := .bvar .zero
  exact HasType.app hf (HasType.sort (l := .zero) (by trivial))

private def separatingSubst : VExpr.Subst
  | 0 => .sort .zero
  | _ + 1 => .sort (.succ .zero)

private theorem separatingSubst_typed :
    Ctx.SubstEq env univs [] separatingSubst separatingSubst abstractContext := by
  apply substEq_of_lookup abstractContext_wf
  intro i A hl
  cases hl with
  | zero => exact HasType.sort (by trivial)
  | succ hl =>
    cases hl with
    | zero => exact HasType.sort (by trivial)
    | succ hl => cases hl

/-- The unchanged body has no type in the abstract context. Substituting
`Type` for the type variable and `Prop` for its value would otherwise type a
sort as a function, contradicting already proved head separation. -/
theorem abstract_body_untypable : ¬ env.HasType univs abstractContext applicationBody T := by
  intro H
  have HS := H.subst henv.orderedStrong separatingSubst_typed (show OnCtx [] (env.IsType univs) from trivial)
  change env.HasType univs [] (.app (.sort .zero) (.sort .zero)) (T.subst separatingSubst) at HS
  have hnil : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  obtain ⟨A, B, hf, _⟩ := HS.app_inv henv hnil
  have hsort : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  exact (hsort.uniqU henv hnil hf).sort_forallE_inv henv hnil

/-- Native readout of the abstract value cannot expose a function type, even
when every primitive of the chosen stage is available. -/
theorem abstract_value_no_pi
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) :
    ¬ ScopedTypeRecovery Step [.bvar 0, .sort (.succ (.succ .zero))]
      (.bvar 0) (.forallE A B) := by
  intro H
  have R : ScopedCompute Step [.bvar 0, .sort (.succ (.succ .zero))]
      (.bvar 1) (.forallE A B) := H.bvar_compute
  cases R.bvar_fixed hhead

/-- The concrete application's function does have exact native Pi recovery. -/
theorem concrete_value_pi : ScopedTypeRecovery Step
    [.forallE (.sort (.succ .zero)) (.sort (.succ .zero))]
    (.bvar 0) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := .bvar

/-- A typed, reflexively checked body in the concrete context cannot be lifted
unchanged to an abstract type context. Thus forward sequential specialization
cannot by itself establish universal typed abstraction. -/
theorem typed_abstraction_failure :
    OnCtx [concreteDomain] (env.IsType univs) ∧
    OnCtx abstractContext (env.IsType univs) ∧
    env.HasType univs [concreteDomain] applicationBody (.sort (.succ .zero)) ∧
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx [concreteDomain]) true
      (proofErase [concreteDomain] applicationBody) (proofErase [concreteDomain] applicationBody) ∧
    ¬ ∃ T, env.HasType univs abstractContext applicationBody T := by
  exact ⟨⟨trivial, _, concreteDomain_typed⟩, abstractContext_wf,
    concrete_body_typed, .leaf .refl, fun ⟨_, H⟩ => abstract_body_untypable H⟩

end Lean4Lean.VEnv.Strengthening.TypeAbstractionBoundary
