import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
open private typeSubset from Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationReplay

theorem RichAppOrigin.reindex_children_bound
    {A B : VExpr} {u v : VLevel}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (sourceOrdered : sourceEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (initial rightCaptured : List Closure)
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (function : EndpointState rightEnv U rightSource rightFn (.forallE A B))
    (argument : EndpointState rightEnv U rightSource rightArg A)
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U) :
    let sourceCaptured := origin.location.dependencyEnvironment sourceOrdered initial
    let parentCost := (Closure.close (root.dependencyOrigin sourceOrdered) initial).cost +
      (Closure.close ((EndpointState.app hu hv domain codomain function argument result).dependencyOrigin rightOrdered)
        rightCaptured).cost
    ((Closure.close (origin.functionNode.dependencyOrigin sourceOrdered) sourceCaptured).cost +
      (Closure.close (function.dependencyOrigin rightOrdered) rightCaptured).cost < parentCost) ∧
    ((Closure.close (origin.argumentNode.dependencyOrigin sourceOrdered) sourceCaptured).cost +
      (Closure.close (argument.dependencyOrigin rightOrdered) rightCaptured).cost < parentCost) := by
  have sourceFunction := (Located.appFunction origin.location).dependency_cost_le sourceOrdered initial
  have sourceArgument := (Located.appArgument origin.location).dependency_cost_le sourceOrdered initial
  have reserve := application_cost_le_captured (domain.dependencyOrigin rightOrdered)
    (codomain.dependencyOrigin rightOrdered) (function.dependencyOrigin rightOrdered)
    (argument.dependencyOrigin rightOrdered) (result.dependencyOrigin rightOrdered) rightCaptured
  have rightFunction : (Closure.close (function.dependencyOrigin rightOrdered) rightCaptured).cost <
      (Closure.close (applicationOrigin (domain.dependencyOrigin rightOrdered)
        (codomain.dependencyOrigin rightOrdered) (function.dependencyOrigin rightOrdered)
        (argument.dependencyOrigin rightOrdered) (result.dependencyOrigin rightOrdered)) rightCaptured).cost :=
    binder_other_cost (by simp) rightCaptured
  have rightArgument : (Closure.close (argument.dependencyOrigin rightOrdered) rightCaptured).cost <
      (Closure.close (applicationOrigin (domain.dependencyOrigin rightOrdered)
        (codomain.dependencyOrigin rightOrdered) (function.dependencyOrigin rightOrdered)
        (argument.dependencyOrigin rightOrdered) (result.dependencyOrigin rightOrdered)) rightCaptured).cost :=
    binder_other_cost (by simp) rightCaptured
  exact ⟨Nat.add_lt_add_of_le_of_lt sourceFunction (Nat.lt_of_lt_of_le rightFunction reserve),
    Nat.add_lt_add_of_le_of_lt sourceArgument (Nat.lt_of_lt_of_le rightArgument reserve)⟩

/-- A bounded expression-reindex step invokes the induction hypothesis only
for the actual child queries retained by each finite seed. -/
theorem RichApplicationSeeds.reindexStep
    {A B : VExpr} {u v : VLevel}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {function : EndpointState rightEnv U rightSource rightFn (.forallE A B)}
    {argument : EndpointState rightEnv U rightSource rightArg A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceOrdered : sourceEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (initial rightCaptured : List Closure)
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms)
    (resources : footprint.Available sourceAvailable)
    (closed : rightAvailable.AtomClosed)
    (sorted : (Profile.mk atoms).HasType (.sort relevant))
    (argumentEq : a.subst σ = rightArg.subst τ)
    (functionReplay : ∀ origin : RichAppOrigin root env registry target source locals σ f a,
      richSchedule .expressionReindex
        ((Closure.close (origin.functionNode.dependencyOrigin sourceOrdered)
          (origin.location.dependencyEnvironment sourceOrdered initial)).cost +
         (Closure.close (function.dependencyOrigin rightOrdered) rightCaptured).cost) <
      richSchedule .expressionReindex
        ((Closure.close (root.dependencyOrigin sourceOrdered) initial).cost +
         (Closure.close ((EndpointState.app hu hv domain codomain function argument result).dependencyOrigin rightOrdered)
           rightCaptured).cost) →
      origin.functionFootprint.Available sourceAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target function rightLocals τ
        rightAvailable (Profile.fn origin.key origin.output)))
    (argumentReplay : ∀ origin : RichAppOrigin root env registry target source locals σ f a,
      richSchedule .expressionReindex
        ((Closure.close (origin.argumentNode.dependencyOrigin sourceOrdered)
          (origin.location.dependencyEnvironment sourceOrdered initial)).cost +
         (Closure.close (argument.dependencyOrigin rightOrdered) rightCaptured).cost) <
      richSchedule .expressionReindex
        ((Closure.close (root.dependencyOrigin sourceOrdered) initial).cost +
         (Closure.close ((EndpointState.app hu hv domain codomain function argument result).dependencyOrigin rightOrdered)
           rightCaptured).cost) →
      origin.argumentFootprint.Available sourceAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target argument rightLocals τ
        rightAvailable origin.rawInput)) :
    ∃ required, Nonempty (RichCert rightEnv env U registry target
      (.app hu hv domain codomain function argument result) rightLocals τ relevant
      (.mk atoms) required) ∧ required.Available rightAvailable := by
  have collect : Nonempty (RichApplicationReplies function argument rightLocals τ rightAvailable seeds) := by
    induction seeds with
    | nil => exact ⟨.nil⟩
    | cons origin path included rest ih =>
      have bounds := origin.reindex_children_bound sourceOrdered rightOrdered initial rightCaptured
        domain codomain function argument result hu hv
      have supplied := origin.originalResources included resources
      obtain ⟨fn⟩ := functionReplay origin (richSchedule_strict bounds.1 _ _) supplied.1
      obtain ⟨arg⟩ := argumentReplay origin (richSchedule_strict bounds.2 _ _) supplied.2
      obtain ⟨tail⟩ := ih (typeSubset (fun _ h => List.mem_cons_of_mem _ h) sorted)
      exact ⟨.cons fn arg tail⟩
  obtain ⟨replies⟩ := collect
  exact replies.reindex henv hscoped formed closed sorted domain codomain result hu hv argumentEq

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
