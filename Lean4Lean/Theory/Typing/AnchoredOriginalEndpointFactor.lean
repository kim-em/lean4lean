import Lean4Lean.Theory.Typing.AnchoredOriginalTypeFormation

/-! Actual original endpoint paths for inverse substitution. Exposure follows
the computed original reference, and conversion descent retains a separate
path step. A whole-expression cut can therefore keep its assigned type before
any conversion is peeled. Binder descent captures the actual domain ledger.
No path contains a caller-supplied numerical origin or semantic producer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

inductive Located (root : EndpointRef env U source expression type) :
    {context : List VExpr} → {selectedExpression selectedType : VExpr} →
      EndpointState env U context selectedExpression selectedType → Type where
  | here : Located root (.ref root)
  | expose (parent : Located root (.ref reference)) : Located root reference.expose
  | convertTerm (parent : Located root (.convert plan term)) : Located root term
  /-- A finite formation view assembled only from the application's retained
  original domain and codomain children. No derivation is reified. -/
  | appPiFormation (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root (.pi hu hv domain codomain)
  | appDomain (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root domain
  | appCodomain (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root codomain
  | appResult (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root result
  | appFunction (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root function
  | appArgument (parent : Located root (.app hu hv domain codomain function argument result)) :
      Located root argument
  | lamDomain (parent : Located root (.lam hu hv domain codomain body)) : Located root domain
  | lamCodomain (parent : Located root (.lam hu hv domain codomain body)) : Located root codomain
  | lamBody (parent : Located root (.lam hu hv domain codomain body)) : Located root body
  | piDomain (parent : Located root (.pi hu hv domain body)) : Located root domain
  | piBody (parent : Located root (.pi hu hv domain body)) : Located root body
  | projField (parent : Located root (.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed relevance)) : Located root field
  | projMajor (parent : Located root (.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed relevance)) : Located root (.ref (.right major))
  | assignedFormation (parent : Located root node) : Located root node.typeFormation.node

def Located.environment (location : Located root selected) (initial : List Closure) : List Closure :=
  match location with
  | .here => initial
  | .expose parent | .convertTerm parent | .appFunction parent | .appArgument parent |
      .appDomain parent | .appResult parent | .appPiFormation parent |
      .lamDomain parent | .piDomain parent | .projField parent | .projMajor parent | .assignedFormation parent => parent.environment initial
  | .lamBody (domain := domain) parent | .lamCodomain (domain := domain) parent |
      .appCodomain (domain := domain) parent | .piBody (domain := domain) parent =>
      .close domain.origin (parent.environment initial) :: parent.environment initial

private def stateExpression (_ : EndpointState env U context expression type) : VExpr := expression

def Located.binderPrefix (location : Located root selected) : List VExpr :=
  match location with
  | .here => []
  | .expose parent | .convertTerm parent | .appFunction parent | .appArgument parent |
      .appDomain parent | .appResult parent | .appPiFormation parent |
      .lamDomain parent | .piDomain parent | .projField parent | .projMajor parent | .assignedFormation parent => parent.binderPrefix
  | .lamBody (domain := domain) parent | .lamCodomain (domain := domain) parent |
      .appCodomain (domain := domain) parent | .piBody (domain := domain) parent =>
      stateExpression domain :: parent.binderPrefix

theorem Located.binderPrefix_cast (equal : selected = selected') (location : Located root selected) :
    (equal ▸ location : Located root selected').binderPrefix = location.binderPrefix := by
  cases equal
  rfl

theorem Located.environment_cast (equal : selected = selected')
    (location : Located root selected) (initial : List Closure) :
    (equal ▸ location : Located root selected').environment initial =
      location.environment initial := by
  cases equal
  rfl

theorem Located.context_eq
    {root : EndpointRef env U source expression type}
    {selected : EndpointState env U context selectedExpression selectedType}
    (location : Located root selected) : context = location.binderPrefix ++ source := by
  induction location with
  | here => rfl
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih | appDomain parent ih | appResult parent ih | appPiFormation parent ih | lamDomain parent ih | piDomain parent ih | projField parent ih | projMajor parent ih | assignedFormation parent ih => exact ih
  | lamBody parent ih | lamCodomain parent ih | appCodomain parent ih | piBody parent ih =>
    simpa only [binderPrefix, stateExpression, List.cons_append] using congrArg (List.cons _) ih

/-- The combined formation view is strictly cheaper than its actual parent,
even before the stronger captured-application reserve is installed. -/
theorem EndpointState.appPiFormation_cost_lt
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState env U source A (.sort u))
    (body : EndpointState env U (A :: source) B (.sort v))
    (function : EndpointState env U source f (.forallE A B))
    (argument : EndpointState env U source a A)
    (result : EndpointState env U source (B.inst a) (.sort v))
    (captured : List Closure) :
    (Closure.close (EndpointState.pi hu hv domain body).origin captured).cost <
      (Closure.close (EndpointState.app hu hv domain body function argument result).origin captured).cost := by
  have positive := function.origin.weight_pos
  have weight : (EndpointState.pi hu hv domain body).origin.weight <
      (EndpointState.app hu hv domain body function argument result).origin.weight := by
    simp only [EndpointState.origin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  exact Nat.mul_lt_mul_of_pos_right weight (by omega)

theorem Located.cost_le (location : Located root selected) (initial : List Closure) :
    (Closure.close selected.origin (location.environment initial)).cost ≤
      (Closure.close root.origin initial).cost := by
  induction location with
  | here => exact Nat.le_refl _
  | expose parent ih =>
    exact Nat.le_trans
      (Nat.mul_le_mul_right (1 + environmentCost (parent.environment initial))
        (EndpointRef.expose_weight_le _)) ih
  | appPiFormation parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (EndpointState.appPiFormation_cost_lt _ _ _ _ _ _ _
      (parent.environment initial))) ih
  | assignedFormation parent ih =>
    exact Nat.le_trans (EndpointState.typeFormation_cost_le _ _) ih
  | convertTerm parent ih | projField parent ih | projMajor parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (original_child_same_environment
      (Origin.rule_child (by simp [EndpointState.origin, EndpointRef.origin])) (parent.environment initial))) ih
  | appFunction parent ih | appArgument parent ih | appResult parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_other_cost (by simp) (parent.environment initial))) ih
  | lamDomain parent ih | appDomain parent ih | piDomain parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_domain_cost _ _ _ (parent.environment initial))) ih
  | lamBody parent ih | lamCodomain parent ih | appCodomain parent ih | piBody parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_body_cost (by simp) (parent.environment initial))) ih

def Head : EndpointState env U context expression type → Prop
  | .ref reference => reference.Primitive
  | .convert .. => False
  | _ => True

/-- A structural head may have a different assigned type after conversion
descent; its source expression and binder prefix remain exactly unchanged. -/
structure HeadView
    {startNode : EndpointState env U context expression type} (start : Located root startNode) where
  type : VExpr
  node : EndpointState env U context expression type
  location : Located root node
  head : Head node
  prefix_eq : location.binderPrefix = start.binderPrefix
  cost_le : ∀ initial,
    (Closure.close node.origin (location.environment initial)).cost ≤
      (Closure.close startNode.origin (start.environment initial)).cost

private theorem head_exists (budget : Nat) :
    ∀ {context expression type} (node : EndpointState env U context expression type),
      node.origin.weight ≤ budget → ∀ (location : Located root node), Nonempty (HeadView location) := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    intro context expression type node bounded location
    cases node with
    | ref reference =>
      have exposed := reference.expose_exposed
      have smaller := reference.expose_weight_le
      let path := Located.expose location
      have exposeCost (initial : List Closure) :
          (Closure.close reference.expose.origin (path.environment initial)).cost ≤
            (Closure.close reference.origin (location.environment initial)).cost :=
        Nat.mul_le_mul_right (1 + environmentCost (location.environment initial)) smaller
      cases eq : reference.expose with
      | convert plan term =>
        have strict : term.origin.weight < budget := by
          have h := Origin.rule_child (child := term.origin)
            (children := [term.origin, plan.origin]) (by simp)
          simp only [eq, EndpointState.origin] at smaller
          exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h smaller) bounded
        obtain ⟨head⟩ := ih term.origin.weight strict term (Nat.le_refl _)
          (.convertTerm (eq ▸ path))
        have prefixEq : (eq ▸ path : Located root (.convert plan term)).convertTerm.binderPrefix =
            location.binderPrefix := by
          simpa only [Located.binderPrefix, path] using Located.binderPrefix_cast eq path
        refine ⟨{ head with prefix_eq := head.prefix_eq.trans prefixEq, cost_le := ?_ }⟩
        intro initial
        have parentCost := Nat.le_of_lt (original_child_same_environment
          (Origin.rule_child (child := term.origin)
            (children := [term.origin, plan.origin]) (by simp))
          ((eq ▸ path : Located root (.convert plan term)).environment initial))
        have originalCost := exposeCost initial
        have envEq := Located.environment_cast eq path initial
        rw [congrArg EndpointState.origin eq] at originalCost
        exact Nat.le_trans (head.cost_le initial) (Nat.le_trans parentCost (by
          simpa only [envEq, EndpointState.origin] using originalCost))
      | ref primitive =>
        exact ⟨⟨_, reference.expose, path,
          by simpa only [eq, Head, EndpointState.Exposed] using exposed, rfl, exposeCost⟩⟩
      | _ =>
        exact ⟨⟨_, reference.expose, path, by simp only [eq, Head], rfl, exposeCost⟩⟩
    | convert plan term =>
      have strict : term.origin.weight < budget :=
        Nat.lt_of_lt_of_le (Origin.rule_child (by simp)) bounded
      obtain ⟨head⟩ := ih term.origin.weight strict term (Nat.le_refl _) (.convertTerm location)
      refine ⟨{ head with prefix_eq := head.prefix_eq, cost_le := ?_ }⟩
      intro initial
      exact Nat.le_trans (head.cost_le initial) (Nat.le_of_lt
        (original_child_same_environment (Origin.rule_child (by simp))
          (location.environment initial)))
    | _ => exact ⟨⟨_, _, location, trivial, rfl, fun _ => Nat.le_refl _⟩⟩

/-- Only reference exposure and conversion peeling recurse here. Exposing a
reference is followed immediately by either a head or a strictly cheaper
conversion term, so the original weight suffices for termination. -/
noncomputable def headView (location : Located root node) : HeadView location :=
  Classical.choice (head_exists node.origin.weight node (Nat.le_refl _) location)

structure AppView
    {node : EndpointState env U context (.app f a) type} (start : Located root node) where
  domainExpression : VExpr
  codomainExpression : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainWF : domainLevel.WF U
  bodyWF : bodyLevel.WF U
  domain : EndpointState env U context domainExpression (.sort domainLevel)
  codomain : EndpointState env U (domainExpression :: context) codomainExpression (.sort bodyLevel)
  function : EndpointState env U context f (.forallE domainExpression codomainExpression)
  argument : EndpointState env U context a domainExpression
  result : EndpointState env U context (codomainExpression.inst a) (.sort bodyLevel)
  location : Located root (.app domainWF bodyWF domain codomain function argument result)
  prefix_eq : location.binderPrefix = start.binderPrefix
  cost_le : ∀ initial,
    (Closure.close (EndpointState.origin (.app domainWF bodyWF domain codomain function argument result)) (location.environment initial)).cost ≤
      (Closure.close node.origin (start.environment initial)).cost

noncomputable def appView
    {node : EndpointState env U context (.app f a) type} (location : Located root node) :
    AppView location := by
  obtain ⟨type, head, path, normal, prefixEq, cost⟩ := headView location
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | app hu hv domain codomain function argument result =>
    exact ⟨_, _, _, _, hu, hv, domain, codomain, function, argument, result, path, prefixEq, cost⟩

/-- The selected result formation and argument together are strictly below
the actual starting endpoint. This reserve is retained through all original
reference exposure and conversion descent. -/
theorem AppView.result_argument_cost_lt
    {node : EndpointState env U context (.app f a) type} {start : Located root node}
    (view : AppView start) (initial : List Closure) :
    (Closure.close view.result.origin (view.location.environment initial)).cost +
      (Closure.close view.argument.origin (view.location.environment initial)).cost <
      (Closure.close node.origin (start.environment initial)).cost := by
  have weight : view.result.origin.weight + view.argument.origin.weight <
      (EndpointState.app view.domainWF view.bodyWF view.domain view.codomain
        view.function view.argument view.result).origin.weight := by
    simp only [EndpointState.origin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  have strict := Nat.mul_lt_mul_of_pos_right weight
    (show 0 < 1 + environmentCost (view.location.environment initial) by omega)
  apply Nat.lt_of_lt_of_le _ (view.cost_le initial)
  simpa only [Closure.cost, Nat.add_mul] using strict

structure LamView
    {node : EndpointState env U context (.lam A expression) type} (start : Located root node) where
  bodyType : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainWF : domainLevel.WF U
  bodyWF : bodyLevel.WF U
  domain : EndpointState env U context A (.sort domainLevel)
  codomain : EndpointState env U (A :: context) bodyType (.sort bodyLevel)
  body : EndpointState env U (A :: context) expression bodyType
  location : Located root (.lam domainWF bodyWF domain codomain body)
  prefix_eq : location.binderPrefix = start.binderPrefix
  cost_le : ∀ initial,
    (Closure.close (EndpointState.origin (.lam domainWF bodyWF domain codomain body)) (location.environment initial)).cost ≤
      (Closure.close node.origin (start.environment initial)).cost

noncomputable def lamView
    {node : EndpointState env U context (.lam A expression) type} (location : Located root node) :
    LamView location := by
  obtain ⟨type, head, path, normal, prefixEq, cost⟩ := headView location
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | lam hu hv domain codomain body => exact ⟨_, _, _, hu, hv, domain, codomain, body, path, prefixEq, cost⟩

structure PiView
    {node : EndpointState env U context (.forallE A B) type} (start : Located root node) where
  domainLevel : VLevel
  bodyLevel : VLevel
  domainWF : domainLevel.WF U
  bodyWF : bodyLevel.WF U
  domain : EndpointState env U context A (.sort domainLevel)
  body : EndpointState env U (A :: context) B (.sort bodyLevel)
  location : Located root (.pi domainWF bodyWF domain body)
  prefix_eq : location.binderPrefix = start.binderPrefix
  cost_le : ∀ initial,
    (Closure.close (EndpointState.origin (.pi domainWF bodyWF domain body)) (location.environment initial)).cost ≤
      (Closure.close node.origin (start.environment initial)).cost

noncomputable def piView
    {node : EndpointState env U context (.forallE A B) type} (location : Located root node) :
    PiView location := by
  obtain ⟨type, head, path, normal, prefixEq, cost⟩ := headView location
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | pi hu hv domain body => exact ⟨_, _, hu, hv, domain, body, path, prefixEq, cost⟩

/-- A cut keeps the unpeeled endpoint's assigned type. Its absolute source
depth is tied to the actual binder path, independently of footprint peeling. -/
structure CutOriginAt (root : EndpointRef env U source expression type)
    (boundary : List VExpr) (argument : VExpr) (baseDepth : Nat := 0) where
  context : List VExpr
  expression : VExpr
  type : VExpr
  view : EndpointState env U context expression type
  location : Located root view
  depth : Nat
  expression_eq : expression = argument.lift' (.skipN .refl depth)
  innerPrefix : List VExpr
  prefix_eq : location.binderPrefix = innerPrefix ++ boundary
  depth_eq : depth = baseDepth + innerPrefix.length

/-- The root boundary is the original API's special case. -/
abbrev CutOrigin (root : EndpointRef env U source expression type)
    (argument : VExpr) (baseDepth : Nat := 0) := CutOriginAt root [] argument baseDepth

theorem CutOriginAt.context_eq
    {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument baseDepth) :
    cut.context = cut.innerPrefix ++ (boundary ++ source) := by
  rw [cut.location.context_eq, cut.prefix_eq, List.append_assoc]

theorem CutOriginAt.sound {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument baseDepth) :
    env.IsDefEqStrong U cut.context cut.expression cut.expression cut.type := cut.view.sound

theorem CutOriginAt.cost_le (cut : CutOriginAt root boundary argument baseDepth)
    (initial : List Closure) :
    (Closure.close cut.view.origin (cut.location.environment initial)).cost ≤
      (Closure.close root.origin initial).cost := cut.location.cost_le initial

def wholeCut (root : EndpointRef env U source argument type) : CutOrigin root argument where
  context := source
  expression := argument
  type := type
  view := .ref root
  location := .here
  depth := 0
  expression_eq := by simp
  innerPrefix := []
  prefix_eq := rfl
  depth_eq := rfl

theorem CutOrigin.sound {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOrigin root argument baseDepth) :
    env.IsDefEqStrong U cut.context cut.expression cut.expression cut.type := cut.view.sound

theorem CutOrigin.cost_le (cut : CutOrigin root argument baseDepth) (initial : List Closure) :
    (Closure.close cut.view.origin (cut.location.environment initial)).cost ≤
      (Closure.close root.origin initial).cost := cut.location.cost_le initial

/-- The actual original application pays for the full located result-type
cut and its ORIGINAL argument premise together, including captured binder
formations. No fabricated endpoint proof or caller-supplied weight occurs. -/
theorem app_cut_schedule
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation env U source A A (.sort u))
    (codomain : Derivation env U (A :: source) B B (.sort v))
    (function : Derivation env U source f f' (.forallE A B))
    (argument : Derivation env U source a a' A)
    (result : Derivation env U source (B.inst a) (B.inst a') (.sort v))
    (cut : CutOrigin (.left result) a) (initial : List Closure) :
    schedule .coherence
      ((Closure.close cut.view.origin (cut.location.environment initial)).cost +
        (Closure.close argument.origin initial).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.appDF hu hv domain codomain function argument result).origin
          initial).cost) := by
  apply schedule_strict
  have cutBound := cut.cost_le initial
  have weightBound : result.origin.weight + argument.origin.weight <
      (Derivation.appDF hu hv domain codomain function argument result).origin.weight := by
    simp only [Derivation.origin, applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  have strict : (Closure.close result.origin initial).cost +
      (Closure.close argument.origin initial).cost <
      (Closure.close (Derivation.appDF hu hv domain codomain function argument result).origin initial).cost := by
    simpa only [Closure.cost, Nat.add_mul] using
      Nat.mul_lt_mul_of_pos_right weightBound (show 0 < 1 + environmentCost initial by omega)
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right cutBound _) strict

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
