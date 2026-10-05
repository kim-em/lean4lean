import Lean4Lean.Theory.Typing.NativeCaptureAbstraction

/-! A plan is fixed by its declared context and its literal ordered field
roles. This identifies independently constructed semantic and machine plans;
it does not infer a plan from coincident capture expressions. -/
namespace Lean4Lean.VEnv.CapturePlan
open VExpr

/-- Declaration order; `none` allocates a proof and `some i` copies index i. -/
def roles : CapturePlan declared → List (Option Nat)
  | .nil => []
  | .index previous position => previous.roles ++ [some position]
  | .proof previous => previous.roles ++ [none]

@[simp] theorem roles_length (plan : CapturePlan declared) : plan.roles.length = declared.length := by
  induction plan with
  | nil => rfl
  | index _ _ ih | proof _ ih => simp [roles, ih]

/-- The context fixes every binder domain, so only field roles remain. -/
theorem eq_of_roles {first second : CapturePlan declared} (same : first.roles = second.roles) :
    first = second := by
  induction first with
  | nil => cases second; rfl
  | index previous position ih =>
    cases second with
    | index other otherPosition =>
      have h := congrArg List.reverse same
      simp only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq, Option.some.injEq] at h
      have hp := ih (List.reverse_inj.mp h.2)
      cases hp
      cases h.1
      rfl
    | proof other =>
      have h := congrArg List.reverse same
      simp only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq, reduceCtorEq, false_and] at h
  | proof previous ih =>
    cases second with
    | index other otherPosition =>
      have h := congrArg List.reverse same
      simp only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq, reduceCtorEq, false_and] at h
    | proof other =>
      have h := congrArg List.reverse same
      simp only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq, true_and] at h
      exact congrArg CapturePlan.proof (ih (List.reverse_inj.mp h))

end Lean4Lean.VEnv.CapturePlan
