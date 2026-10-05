import Lean4Lean.Theory.Typing.Strong

/-! Arithmetic schedule for ORIGINAL derivation closures. These are Type
witnesses, not a function eliminating IsDefEqStrong (which lives in Prop).
Connecting them to every Strong constructor and the actual coherence call
graph is a separate obligation. In particular this schedule does not license
generic beta evaluation of an application through a substituted function. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

/-- Ordinary nodes reserve the sum of their original children. Literal beta
also reserves the body/argument product needed by environment extension. -/
inductive Origin where
  | rule (children : List Origin)
  | binder (domain : Origin) (bodies otherChildren : List Origin)
  | beta (body argument instantiated : Origin) (otherChildren : List Origin)
  | typedBeta (domain body argument instantiated : Origin) (otherChildren : List Origin)
  | eta (term liftedTerm : Origin) (otherChildren : List Origin)

def Origin.weight : Origin → Nat
  | .rule children => 1 + (children.map Origin.weight).sum
  | .binder domain bodies children =>
    2 + domain.weight + (bodies.map Origin.weight).sum * (1 + domain.weight) +
      (children.map Origin.weight).sum
  | .beta body argument instantiated children =>
    3 + instantiated.weight + body.weight * (1 + argument.weight) +
      2 * (children.map Origin.weight).sum
  | .typedBeta domain body argument instantiated children =>
    4 + instantiated.weight + domain.weight +
      body.weight * (1 + argument.weight + domain.weight) +
      2 * (children.map Origin.weight).sum
  | .eta term liftedTerm children =>
    4 + term.weight + liftedTerm.weight + 3 * (children.map Origin.weight).sum

theorem Origin.weight_pos (origin : Origin) : 0 < origin.weight := by
  cases origin <;> simp only [weight] <;> omega

private theorem sum_member_le {values : List Nat} (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.sum_cons]; omega
    · have := ih member
      simp only [List.sum_cons]; omega

theorem Origin.rule_child (member : child ∈ children) : child.weight < (Origin.rule children).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  simp only [weight]
  omega

theorem Origin.binder_domain (domain : Origin) (bodies children : List Origin) :
    domain.weight < (Origin.binder domain bodies children).weight := by
  simp only [weight]
  omega

theorem Origin.binder_body (member : body ∈ bodies) :
    body.weight < (Origin.binder domain bodies children).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  have reserve : (bodies.map Origin.weight).sum ≤
      (bodies.map Origin.weight).sum * (1 + domain.weight) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (bodies.map Origin.weight).sum
      (show 1 ≤ 1 + domain.weight by omega)
  simp only [weight]
  omega

theorem Origin.binder_other (member : child ∈ children) :
    child.weight < (Origin.binder domain bodies children).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  simp only [weight]
  omega

theorem Origin.beta_body (body argument instantiated : Origin) (children : List Origin) :
    body.weight < (Origin.beta body argument instantiated children).weight := by
  have bound : body.weight ≤ body.weight * (1 + argument.weight) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left body.weight
      (show 1 ≤ 1 + argument.weight by omega)
  simp only [weight]
  omega

theorem Origin.beta_argument (body argument instantiated : Origin) (children : List Origin) :
    argument.weight < (Origin.beta body argument instantiated children).weight := by
  have bound : 1 + argument.weight ≤ body.weight * (1 + argument.weight) := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (1 + argument.weight) body.weight_pos
  simp only [weight]
  omega

theorem Origin.beta_instantiated (body argument instantiated : Origin) (children : List Origin) :
    instantiated.weight < (Origin.beta body argument instantiated children).weight := by
  simp only [weight]
  omega

theorem Origin.beta_other_child (member : child ∈ children) :
    child.weight < (Origin.beta body argument instantiated children).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  simp only [weight]
  omega

/-- Environments store original argument closures, including their captured
environments. Taking their maximum avoids charging shared captures twice. -/
inductive Closure where
  | close (origin : Origin) (environment : List Closure)
  /-- A captured value retains its original source-type formation too.
  This is environment bookkeeping, not a synthesized original derivation. -/
  | bundle (term sourceType : Closure)

mutual
  def Closure.cost : Closure → Nat
    | .close origin environment => origin.weight * (1 + environmentCost environment)
    | .bundle term sourceType => term.cost + sourceType.cost
  def environmentCost : List Closure → Nat
    | [] => 0
    | head :: tail => max head.cost (environmentCost tail)
end

theorem Closure.cost_pos (closure : Closure) : 0 < closure.cost := by
  cases closure with
  | close origin environment =>
    exact Nat.mul_pos origin.weight_pos (by omega)
  | bundle term sourceType =>
    exact Nat.lt_of_lt_of_le term.cost_pos (Nat.le_add_right _ _)
termination_by sizeOf closure

theorem environment_entry (member : closure ∈ environment) :
    closure.cost ≤ environmentCost environment := by
  induction environment with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Lookup can jump to a much larger ORIGINAL proof: its complete captured
closure cost was already bounded by the caller's environment maximum. -/
theorem variable_lookup (origin : Origin) (member : argument ∈ environment) :
    argument.cost < (Closure.close origin environment).cost := by
  have included := environment_entry member
  have positive := origin.weight_pos
  have base : 1 + environmentCost environment ≤
      origin.weight * (1 + environmentCost environment) := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (1 + environmentCost environment) positive
  change argument.cost < origin.weight * (1 + environmentCost environment)
  omega

theorem original_child_same_environment
    (smaller : child.weight < parent.weight) (environment : List Closure) :
    (Closure.close child environment).cost < (Closure.close parent environment).cost :=
  Nat.mul_lt_mul_of_pos_right smaller (by omega)

/-- A transitivity midpoint comparison reserves the sum of the two original
premise closures, not merely their maximum. -/
theorem original_two_children (left right : Origin) (others : List Origin)
    (environment : List Closure) :
    (Closure.close left environment).cost + (Closure.close right environment).cost <
      (Closure.close (.rule (left :: right :: others)) environment).cost := by
  have smaller : left.weight + right.weight < (Origin.rule (left :: right :: others)).weight := by
    simp only [Origin.weight, List.map_cons, List.sum_cons]
    omega
  simpa only [Closure.cost, Nat.add_mul] using
    Nat.mul_lt_mul_of_pos_right smaller (show 0 < 1 + environmentCost environment by omega)

private theorem extended_environment_bound (argument : Origin) (environment : List Closure) :
    1 + environmentCost (.close argument environment :: environment) ≤
      (1 + argument.weight) * (1 + environmentCost environment) := by
  have positive := argument.weight_pos
  have base : 1 + environmentCost environment ≤
      argument.weight * (1 + environmentCost environment) := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (1 + environmentCost environment) positive
  have maximum : environmentCost environment ≤
      argument.weight * (1 + environmentCost environment) := by omega
  simp only [environmentCost, Closure.cost, Nat.max_eq_left maximum,
    Nat.add_mul, Nat.one_mul]
  omega

/-- Neutral binder lookup still needs the ORIGINAL source-domain formation.
All under-binder children are covered by the parent's product reserve. -/
theorem binder_body_cost (member : body ∈ bodies) (environment : List Closure) :
    (Closure.close body (.close domain environment :: environment)).cost <
      (Closure.close (.binder domain bodies children) environment).cost := by
  have ext := extended_environment_bound domain environment
  have bodyBound := Nat.mul_le_mul_left body.weight ext
  have included := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  have reserve := Nat.mul_le_mul_right (1 + domain.weight) included
  have smaller : body.weight * (1 + domain.weight) <
      (Origin.binder domain bodies children).weight := by
    simp only [Origin.weight]
    omega
  have strict := Nat.mul_lt_mul_of_pos_right smaller
    (show 0 < 1 + environmentCost environment by omega)
  rw [← Nat.mul_assoc] at bodyBound
  exact Nat.lt_of_le_of_lt bodyBound strict

theorem binder_domain_cost (domain : Origin) (bodies children : List Origin)
    (environment : List Closure) :
    (Closure.close domain environment).cost <
      (Closure.close (.binder domain bodies children) environment).cost :=
  original_child_same_environment (Origin.binder_domain domain bodies children) environment

theorem binder_other_cost (member : child ∈ children) (environment : List Closure) :
    (Closure.close child environment).cost <
      (Closure.close (.binder domain bodies children) environment).cost :=
  original_child_same_environment (Origin.binder_other member) environment

private theorem typed_extended_environment_bound (domain argument : Origin)
    (environment : List Closure) :
    1 + environmentCost
      (.bundle (.close argument environment) (.close domain environment) :: environment) ≤
      (1 + argument.weight + domain.weight) * (1 + environmentCost environment) := by
  have positive : 1 ≤ argument.weight + domain.weight := by have := argument.weight_pos; omega
  have base : 1 + environmentCost environment ≤
      argument.weight * (1 + environmentCost environment) +
        domain.weight * (1 + environmentCost environment) := by
    simpa only [Nat.one_mul, Nat.add_mul] using
      Nat.mul_le_mul_right (1 + environmentCost environment) positive
  have maximum : environmentCost environment ≤
      argument.weight * (1 + environmentCost environment) +
        domain.weight * (1 + environmentCost environment) := by omega
  simp only [environmentCost, Closure.cost, Nat.max_eq_left maximum,
    Nat.add_mul, Nat.one_mul]
  omega

/-- Actual beta capture retains both original argument and source-domain
closures. This is the typed replacement for beta_comparison's term-only
environment model. -/
theorem typed_beta_comparison (domain body argument instantiated : Origin)
    (children : List Origin) (environment : List Closure) :
    (Closure.close instantiated environment).cost +
      (Closure.close body
        (.bundle (.close argument environment) (.close domain environment) :: environment)).cost <
      (Closure.close (.typedBeta domain body argument instantiated children) environment).cost := by
  have bodyBound := Nat.mul_le_mul_left body.weight
    (typed_extended_environment_bound domain argument environment)
  have reserve : instantiated.weight + body.weight * (1 + argument.weight + domain.weight) <
      (Origin.typedBeta domain body argument instantiated children).weight := by
    simp only [Origin.weight]
    omega
  have strict := Nat.mul_lt_mul_of_pos_right reserve
    (show 0 < 1 + environmentCost environment by omega)
  rw [Nat.add_mul] at strict
  rw [← Nat.mul_assoc] at bodyBound
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left bodyBound _) strict

theorem bundle_source_type_bound
    (member : Closure.bundle term sourceType ∈ environment) :
    sourceType.cost ≤ environmentCost environment :=
  Nat.le_trans (Nat.le_add_left _ _) (environment_entry member)

/-- Reindexing compares the occurrence's ORIGINAL type formation with the
ambient entry's ORIGINAL source type. The latter can be larger as a proof;
its complete closure is already charged to the environment maximum. -/
theorem lookup_type_reindex (occurrenceDomain : Origin) (sourceType : Closure)
    (environment : List Closure) (bounded : sourceType.cost ≤ environmentCost environment) :
    (Closure.close occurrenceDomain environment).cost + sourceType.cost <
      (Closure.close (.rule [occurrenceDomain]) environment).cost := by
  simp only [Closure.cost, Origin.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_mul, Nat.one_mul]
  omega

/-- The exact beta comparison uses BOTH the original instantiated child
and the original body under its original argument closure. No instantiated
body derivation is constructed or assigned a fictitious smaller size. -/
theorem beta_comparison
    (body argument instantiated : Origin) (otherChildren : List Origin)
    (environment : List Closure) :
    (Closure.close instantiated environment).cost +
      (Closure.close body (.close argument environment :: environment)).cost <
    (Closure.close (.beta body argument instantiated otherChildren) environment).cost := by
  have ext := extended_environment_bound argument environment
  have bodyBound := Nat.mul_le_mul_left body.weight ext
  have parentReserve : instantiated.weight + body.weight * (1 + argument.weight) <
      (Origin.beta body argument instantiated otherChildren).weight := by
    simp only [Origin.weight]
    omega
  have strict := Nat.mul_lt_mul_of_pos_right parentReserve
    (show 0 < 1 + environmentCost environment by omega)
  change instantiated.weight * (1 + environmentCost environment) +
    body.weight * (1 + environmentCost (.close argument environment :: environment)) < _
  rw [Nat.add_mul] at strict
  rw [← Nat.mul_assoc] at bodyBound
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left bodyBound _) strict

/-- A single natural schedule includes the phase tie-break: coherence may
invoke fundamental interpretation at equal closure cost. All cross-phase
calls in the other direction must strictly decrease the main cost. -/
inductive Phase where
  | fundamental
  | coherence

def Phase.code : Phase → Nat
  | .fundamental => 0
  | .coherence => 1

def schedule (phase : Phase) (cost : Nat) : Nat := 2 * cost + phase.code

theorem schedule_strict (smaller : newCost < oldCost) (newPhase oldPhase : Phase) :
    schedule newPhase newCost < schedule oldPhase oldCost := by
  cases newPhase <;> cases oldPhase <;> simp only [schedule, Phase.code] <;> omega

theorem coherence_to_fundamental (cost : Nat) :
    schedule .fundamental cost < schedule .coherence cost := by
  simp [schedule, Phase.code]

theorem variable_comparison (origin : Origin) (member : argument ∈ environment)
    (other : Closure) :
    schedule .coherence (argument.cost + other.cost) <
      schedule .coherence ((Closure.close origin environment).cost + other.cost) :=
  schedule_strict (Nat.add_lt_add_right (variable_lookup origin member) _) _ _

theorem beta_schedule
    (body argument instantiated : Origin) (otherChildren : List Origin)
    (environment : List Closure) :
    schedule .coherence
      ((Closure.close instantiated environment).cost +
        (Closure.close body (.close argument environment :: environment)).cost) <
    schedule .fundamental
      ((Closure.close (.beta body argument instantiated otherChildren) environment).cost) :=
  schedule_strict (beta_comparison body argument instantiated otherChildren environment) _ _

/-- Only the finite structural nodes introduced by ORIGINAL endpoint rules.
An application node is inspected; it is not evaluated through its function. -/
inductive EndpointNode where
  | app
  | lam
  | bvar

/-- Original formation premises are charged separately from syntax children.
For example an app may call its original domain/codomain/instantiated-domain
children even though its expression has only a function and an argument. -/
inductive EndpointView where
  | original (origin : Origin)
  | node (kind : EndpointNode) (children : List EndpointView) (premises : List Origin)

def EndpointView.weight : EndpointView → Nat
  | .original origin => origin.weight
  | .node _ children premises =>
    1 + (children.map EndpointView.weight).sum + (premises.map Origin.weight).sum

theorem EndpointView.weight_pos (view : EndpointView) : 0 < view.weight := by
  cases view with
  | original origin => simpa only [weight] using origin.weight_pos
  | node => simp only [weight]; omega

theorem EndpointView.child_weight (member : child ∈ children) :
    child.weight < (EndpointView.node kind children premises).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := EndpointView.weight) member)
  simp only [weight]
  omega

theorem EndpointView.premise_weight (member : origin ∈ premises) :
    origin.weight < (EndpointView.node kind children premises).weight := by
  have bound := sum_member_le (List.mem_map_of_mem (f := Origin.weight) member)
  simp only [weight]
  omega

/-- Every metadata entry remains an ORIGINAL proof with its own context.
Duplicating the finite ledger is only an upper bound: no premise is converted
to a different context or obtained by synthetically instantiating a proof. -/
def betaLeftView (body argument : Origin) (premises : List Origin) : EndpointView :=
  .node .app [.node .lam [.original body] premises, .original argument] premises

def etaLeftView (liftedTerm : Origin) (premises : List Origin) : EndpointView :=
  .node .lam [.node .app [.original liftedTerm, .node .bvar [] premises] premises] premises

/-- The beta reserve covers both original endpoint views, as well as the
separate instantiated/body-closure comparison proved above. -/
theorem beta_endpoint_weights (body argument instantiated : Origin) (premises : List Origin) :
    (betaLeftView body argument premises).weight + instantiated.weight <
      (Origin.beta body argument instantiated premises).weight := by
  have product : argument.weight ≤ body.weight * argument.weight := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right argument.weight body.weight_pos
  simp only [betaLeftView, EndpointView.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Origin.weight, Nat.mul_add, Nat.mul_one]
  omega

/-- Original eta has three structural nodes: lambda, application, and the
bound variable. Its original lifted term and formation children are retained. -/
theorem eta_endpoint_weights (term liftedTerm : Origin) (premises : List Origin) :
    (etaLeftView liftedTerm premises).weight + term.weight <
      (Origin.eta term liftedTerm premises).weight := by
  simp only [etaLeftView, EndpointView.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Origin.weight]
  omega

/-- Binder inspection only lifts the ambient substitution and introduces a
neutral source slot; the captured ORIGINAL argument forest stays unchanged.
Actual argument substitution is the distinct beta_comparison transition. -/
def EndpointView.cost (view : EndpointView) (environment : List Closure) : Nat :=
  view.weight * (1 + environmentCost environment)

/-- A freshly bound source variable is a neutral slot, not a captured
argument derivation. This models only the environment-cost effect of lifting. -/
def neutralEnvironmentCost : List (Option Closure) → Nat
  | [] => 0
  | none :: tail => neutralEnvironmentCost tail
  | some head :: tail => max head.cost (neutralEnvironmentCost tail)

theorem neutral_lift_cost (environment : List Closure) :
    neutralEnvironmentCost (none :: environment.map some) = environmentCost environment := by
  change neutralEnvironmentCost (environment.map some) = _
  induction environment with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, neutralEnvironmentCost, environmentCost, ih]

theorem endpoint_child_cost (member : child ∈ children) (environment : List Closure) :
    child.cost environment < (EndpointView.node kind children premises).cost environment :=
  Nat.mul_lt_mul_of_pos_right (EndpointView.child_weight member) (by omega)

theorem endpoint_premise_cost (member : origin ∈ premises) (environment : List Closure) :
    (Closure.close origin environment).cost <
      (EndpointView.node kind children premises).cost environment :=
  Nat.mul_lt_mul_of_pos_right (EndpointView.premise_weight member) (by omega)

/-- Coherence between two eta-left views can descend into their synthesized
bodies without charging the unchanged eta origins again. -/
theorem endpoint_comparison_children
    (leftMember : left ∈ leftChildren) (rightMember : right ∈ rightChildren)
    (leftEnvironment rightEnvironment : List Closure) :
    schedule .coherence (left.cost leftEnvironment + right.cost rightEnvironment) <
      schedule .coherence
        ((EndpointView.node leftKind leftChildren leftPremises).cost leftEnvironment +
          (EndpointView.node rightKind rightChildren rightPremises).cost rightEnvironment) :=
  schedule_strict (Nat.add_lt_add
    (endpoint_child_cost leftMember leftEnvironment)
    (endpoint_child_cost rightMember rightEnvironment)) _ _

theorem beta_endpoint_schedule (body argument instantiated : Origin) (premises : List Origin)
    (environment : List Closure) :
    schedule .coherence ((betaLeftView body argument premises).cost environment +
      (Closure.close instantiated environment).cost) <
      schedule .fundamental ((Closure.close (.beta body argument instantiated premises) environment).cost) := by
  apply schedule_strict
  simpa only [EndpointView.cost, Closure.cost, Nat.add_mul] using
    Nat.mul_lt_mul_of_pos_right (beta_endpoint_weights body argument instantiated premises)
      (show 0 < 1 + environmentCost environment by omega)

theorem eta_endpoint_schedule (term liftedTerm : Origin) (premises : List Origin)
    (environment : List Closure) :
    schedule .coherence ((etaLeftView liftedTerm premises).cost environment +
      (Closure.close term environment).cost) <
      schedule .fundamental ((Closure.close (.eta term liftedTerm premises) environment).cost) := by
  apply schedule_strict
  simpa only [EndpointView.cost, Closure.cost, Nat.add_mul] using
    Nat.mul_lt_mul_of_pos_right (eta_endpoint_weights term liftedTerm premises)
      (show 0 < 1 + environmentCost environment by omega)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
