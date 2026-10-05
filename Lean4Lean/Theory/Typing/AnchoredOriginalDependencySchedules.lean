import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyHeaderCapture

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

theorem Derivation.beta_dependency_comparison_schedule
    (formed : env.Ordered)
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (body : Derivation env U (A :: source) e e B)
    (argument : Derivation env U source a a A)
    (result : Derivation env U source (B.inst a) (B.inst a) (.sort v))
    (instantiated : Derivation env U source (e.inst a) (e.inst a) (B.inst a))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close (instantiated.dependencyOrigin formed) captured).cost +
        (Closure.close (body.dependencyOrigin formed)
          (.bundle (.close (argument.dependencyOrigin formed) captured) (.close (domain.dependencyOrigin formed) captured) :: captured)).cost) <
      schedule .fundamental
        ((Closure.close ((Derivation.beta domainWF bodyWF domain codomain body argument result
          instantiated).dependencyOrigin formed) captured).cost) := by
  rw [dependencyOrigin.eq_def formed (Derivation.beta domainWF bodyWF domain codomain body argument result instantiated)]
  dsimp only
  exact schedule_strict (Nat.lt_trans
    (typed_beta_comparison (domain.dependencyOrigin formed) (body.dependencyOrigin formed) (argument.dependencyOrigin formed) (instantiated.dependencyOrigin formed)
      [.binder (domain.dependencyOrigin formed) [(codomain.dependencyOrigin formed)] [], (result.dependencyOrigin formed)] captured)
    (original_child_same_environment (Origin.rule_child (by simp)) captured)) _ _

/-- Both eta endpoints fit below the original eta rule, with the left
endpoint ledger reserving the actual domain type closures under its binders. -/
theorem Derivation.eta_dependency_endpoint_schedule
    (formed : env.Ordered)
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (liftedCodomain : Derivation env U (A.lift :: A :: source)
      (B.liftN 1 1) (B.liftN 1 1) (.sort v))
    (term : Derivation env U source e e (.forallE A B))
    (liftedTerm : Derivation env U (A :: source) e.lift e.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation env U (A :: source) A.lift A.lift (.sort u))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close (term.dependencyOrigin formed) captured).cost +
        (Closure.close (dependencyEtaLeftOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (liftedCodomain.dependencyOrigin formed)
          (liftedTerm.dependencyOrigin formed) (liftedDomain.dependencyOrigin formed)) captured).cost) <
      schedule .fundamental
        ((Closure.close ((Derivation.eta domainWF bodyWF domain codomain liftedCodomain
          term liftedTerm liftedDomain).dependencyOrigin formed) captured).cost) := by
  rw [dependencyOrigin.eq_def formed (Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain)]
  dsimp only
  exact schedule_strict (original_two_children (term.dependencyOrigin formed)
    (dependencyEtaLeftOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (liftedCodomain.dependencyOrigin formed)
      (liftedTerm.dependencyOrigin formed) (liftedDomain.dependencyOrigin formed)) [] captured) _ _

/-- The two ORIGINAL premises at a transitivity midpoint fit below that
original transitivity node. Endpoint reindexing still needs its own proof. -/
theorem Derivation.trans_dependency_comparison_schedule
    (formed : env.Ordered)
    (first : Derivation env U source left middle type)
    (second : Derivation env U source middle right type)
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close (first.dependencyOrigin formed) captured).cost + (Closure.close (second.dependencyOrigin formed) captured).cost) <
      schedule .fundamental ((Closure.close ((Derivation.trans first second).dependencyOrigin formed) captured).cost) := by
  rw [dependencyOrigin.eq_def formed (Derivation.trans first second)]
  dsimp only
  exact schedule_strict (original_two_children (first.dependencyOrigin formed) (second.dependencyOrigin formed) [] captured) _ _


theorem EndpointState.application_dependency_comparison_schedule
    (formed : env.Ordered) (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : EndpointState env U source A (.sort u))
    (codomain : EndpointState env U (A :: source) B (.sort v))
    (function : EndpointState env U source f (.forallE A B))
    (argument : EndpointState env U source a A)
    (result : EndpointState env U source (B.inst a) (.sort v)) (captured : List Closure) :
    schedule .coherence
      ((Closure.close (result.dependencyOrigin formed) captured).cost +
       (Closure.close (codomain.dependencyOrigin formed)
        (.bundle (.close (argument.dependencyOrigin formed) captured)
          (.close (domain.dependencyOrigin formed) captured) :: captured)).cost) <
    schedule .fundamental
      (Closure.close ((EndpointState.app domainWF bodyWF domain codomain function argument result).dependencyOrigin formed) captured).cost :=
  schedule_strict (capturedApplication_comparison _ _ _ _ _ _) _ _

theorem Derivation.application_dependency_comparison_schedule
    (formed : env.Ordered) (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (function : Derivation env U source f f' (.forallE A B))
    (argument : Derivation env U source a a' A)
    (result : Derivation env U source (B.inst a) (B.inst a') (.sort v))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close (result.dependencyOrigin formed) captured).cost +
       (Closure.close (codomain.dependencyOrigin formed)
        (.bundle (.close (argument.dependencyOrigin formed) captured)
          (.close (domain.dependencyOrigin formed) captured) :: captured)).cost) <
    schedule .fundamental
      (Closure.close ((Derivation.appDF domainWF bodyWF domain codomain function argument result).dependencyOrigin formed) captured).cost := by
  rw [dependencyOrigin.eq_def formed (Derivation.appDF domainWF bodyWF domain codomain function argument result)]
  dsimp only
  exact schedule_strict (Nat.lt_trans
    (capturedApplication_comparison (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed)
      (function.dependencyOrigin formed) (argument.dependencyOrigin formed) (result.dependencyOrigin formed) captured)
    (original_child_same_environment (Origin.rule_child (by simp)) captured)) _ _

theorem Derivation.beta_dependency_codomain_schedule
    (formed : env.Ordered) (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (body : Derivation env U (A :: source) e e B)
    (argument : Derivation env U source a a A)
    (result : Derivation env U source (B.inst a) (B.inst a) (.sort v))
    (instantiated : Derivation env U source (e.inst a) (e.inst a) (B.inst a))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close (result.dependencyOrigin formed) captured).cost +
       (Closure.close (codomain.dependencyOrigin formed)
        (.bundle (.close (argument.dependencyOrigin formed) captured)
          (.close (domain.dependencyOrigin formed) captured) :: captured)).cost) <
    schedule .fundamental
      (Closure.close ((Derivation.beta domainWF bodyWF domain codomain body argument result instantiated).dependencyOrigin formed) captured).cost := by
  rw [dependencyOrigin.eq_def formed (Derivation.beta domainWF bodyWF domain codomain body argument result instantiated)]
  dsimp only
  exact schedule_strict (Nat.lt_trans
    (capturedApplication_comparison (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed)
      (lambdaOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed) (body.dependencyOrigin formed))
      (argument.dependencyOrigin formed) (result.dependencyOrigin formed) captured)
    (original_child_same_environment (Origin.rule_child (by simp [dependencyBetaLeftOrigin])) captured)) _ _

theorem ContextDerivation.Location.dependency_captured_member (formed : env.Ordered)
    {context : ContextDerivation env U source}
    {tail : ContextDerivation env U tailSource}
    {domain : EndpointRef env U tailSource A (.sort level)}
    (location : Location context tail domain) :
    Closure.close (domain.dependencyOrigin formed) (tail.dependencyClosures formed) ∈
      context.dependencyClosures formed := by
  induction location with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem ContextDerivation.Location.dependency_lookup_schedule (formed : env.Ordered)
    {context : ContextDerivation env U source}
    {tail : ContextDerivation env U tailSource}
    {domain : EndpointRef env U tailSource A (.sort level)}
    (location : Location context tail domain)
    (lookupNode : EndpointState env U source (.bvar index) assigned) :
    schedule .fundamental
      (Closure.close (domain.dependencyOrigin formed) (tail.dependencyClosures formed)).cost <
    schedule .fundamental
      (Closure.close (lookupNode.dependencyOrigin formed) (context.dependencyClosures formed)).cost :=
  schedule_strict (variable_lookup _ (location.dependency_captured_member formed)) _ _

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
