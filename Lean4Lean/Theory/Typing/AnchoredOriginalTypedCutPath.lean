import Lean4Lean.Theory.Typing.AnchoredOriginalCutFrames

/-! Focused typed-query paths construct the occurrence frame from actual
binder syntax. A terminal projection query may be nonempty. This is an
isolated path producer, not an extension of the legacy Obs grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Each binder edge retains precisely the finite certificate, guard and
resource pack present in the query. No occurrence frame is supplied. -/
inductive TypedCutPath
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {startNode : EndpointState sourceEnv U startSource startExpression startType}
    (start : Located root startNode) (baseLocals : List Nat) (baseRealization : Subst) :
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → Located root node →
    List Nat → Subst → Nat → Footprint → Footprint → Type where
  | here : TypedCutPath env registry target start baseLocals baseRealization
      start baseLocals baseRealization 0 footprint footprint
  | lamBody
      {source : List VExpr} {A B expression : VExpr} {u v : VLevel}
      {hu : u.WF U} {hv : v.WF U}
      {domain : EndpointState sourceEnv U source A (.sort u)}
      {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {body : EndpointState sourceEnv U (A :: source) expression B}
      {location : Located root (.lam hu hv
        domain codomain body)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before (domainFootprint ++ outside))
      {n : Nat} {support packed : Profile n} {key : Key n}
      (domainCode : CodeCert env U registry target locals σ A support domainFootprint)
      (guard : LambdaGuard env U registry target σ A (key : Key n) support)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.lamBody location)
        (Locals.push locals) (σ.cons key.anchor) (depth + 1) before bodyFootprint
  | piBody
      {source : List VExpr} {A B : VExpr} {u v : VLevel}
      {hu : u.WF U} {hv : v.WF U}
      {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {location : Located root (.pi hu hv
        domain body)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before (domainFootprint ++ outside))
      {n : Nat} {support packed : Profile n} {key : Key n}
      (domainCode : CodeCert env U registry target locals σ A support domainFootprint)
      (guard : LambdaGuard env U registry target σ A (key : Key n) support)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.piBody location)
        (Locals.push locals) (σ.cons key.anchor) (depth + 1) before bodyFootprint
  | appFunction
      {location : Located root (.app hu hv domain codomain function argument result)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before (functionFootprint ++ argumentFootprint)) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.appFunction location) locals σ depth before functionFootprint
  | appArgument
      {location : Located root (.app hu hv domain codomain function argument result)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before (functionFootprint ++ argumentFootprint)) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.appArgument location) locals σ depth before argumentFootprint
  | expose
      {location : Located root (.ref reference)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before after) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.expose location) locals σ depth before after
  | convertTerm
      {location : Located root (.convert plan term)}
      (previous : TypedCutPath env registry target start baseLocals baseRealization
        location locals σ depth before after) :
      TypedCutPath env registry target start baseLocals baseRealization
        (Located.convertTerm location) locals σ depth before after

/-- Source realization suffixes are computed by the syntax of the path. -/
theorem TypedCutPath.realizationTail
    (path : TypedCutPath env registry target start baseLocals baseRealization
      location locals σ depth before after) :
    Subst.lift_l (.skipN .refl depth) σ = baseRealization := by
  induction path with
  | here => rfl
  | lamBody previous domain guard pack covered ih | piBody previous domain guard pack covered ih =>
    funext index
    have old := congrFun ih index
    simpa [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using old
  | expose previous ih | convertTerm previous ih | appFunction previous ih | appArgument previous ih => exact ih

theorem TypedCutPath.depth_eq
    (path : TypedCutPath env registry target start baseLocals baseRealization
      location locals σ depth before after) :
    location.binderPrefix.length = depth + start.binderPrefix.length := by
  induction path with
  | here => simp
  | lamBody previous domain guard pack covered ih | piBody previous domain guard pack covered ih =>
    change _ + 1 = _
    omega
  | expose previous ih | convertTerm previous ih | appFunction previous ih | appArgument previous ih => exact ih

/-- The complete occurrence frame and resource ledger are constructed from
one caller frame. Binder formation annotations are the actual Located refs. -/
theorem TypedCutPath.frames
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {startNode : EndpointState sourceEnv U startSource startExpression startType}
    {start : Located root startNode}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    (path : TypedCutPath env registry target start baseLocals baseRealization
      location locals σ depth before after)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (frame : OriginalQueryFrame env registry target (start.contextDerivation initial)
      baseLocals baseRealization available)
    (closed : available.AtomClosed) (resources : before.Available available) :
    ∃ finalAvailable,
      Nonempty (OriginalQueryFrame env registry target (location.contextDerivation initial)
        locals σ finalAvailable) ∧ finalAvailable.AtomClosed ∧
      after.Available finalAvailable ∧
      (∀ index, finalAvailable (index + depth) = available index) := by
  induction path with
  | here => exact ⟨available, ⟨frame⟩, closed, resources, fun _ => rfl⟩
  | lamBody previous domain guard pack covered ih =>
    obtain ⟨middle, ⟨middleFrame⟩, middleClosed, middleResources, tail⟩ := ih resources
    exact ⟨_, ⟨lambdaBodyFrame _ initial middleFrame henv below domain
      (fun i need member => middleResources i need (List.mem_append_left _ member)) guard pack covered⟩,
      Valuation.push_atomized_closed middleClosed _,
      pack.available_atomized_localNeeds
        (fun i need member => middleResources i need (List.mem_append_right _ member)),
      fun index => by simpa [Valuation.push, Nat.add_assoc] using tail index⟩
  | piBody previous domain guard pack covered ih =>
    obtain ⟨middle, ⟨middleFrame⟩, middleClosed, middleResources, tail⟩ := ih resources
    exact ⟨_, ⟨piBodyFrame _ initial middleFrame henv below domain
      (fun i need member => middleResources i need (List.mem_append_left _ member)) guard pack covered⟩,
      Valuation.push_atomized_closed middleClosed _,
      pack.available_atomized_localNeeds
        (fun i need member => middleResources i need (List.mem_append_right _ member)),
      fun index => by simpa [Valuation.push, Nat.add_assoc] using tail index⟩
  | appFunction previous ih =>
    obtain ⟨middle, fitted, middleClosed, middleResources, tail⟩ := ih resources
    exact ⟨middle, fitted, middleClosed,
      (fun i need member => middleResources i need (List.mem_append_left _ member)), tail⟩
  | appArgument previous ih =>
    obtain ⟨middle, fitted, middleClosed, middleResources, tail⟩ := ih resources
    exact ⟨middle, fitted, middleClosed,
      (fun i need member => middleResources i need (List.mem_append_right _ member)), tail⟩
  | expose previous ih | convertTerm previous ih => exact ih resources

/-- The retained origin is computed from the path, including its actual
absolute location and exact binder depth. -/
def TypedCutPath.cutOrigin
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    (path : TypedCutPath env registry target (Located.here (root := root)) baseLocals baseRealization
      location locals σ depth before after)
    (equal : expression = argument.lift' (.skipN .refl depth)) : CutOrigin root argument 0 where
  context := source
  expression := expression
  type := assigned
  view := node
  location := location
  depth := depth
  expression_eq := equal
  innerPrefix := location.binderPrefix
  prefix_eq := by simp
  depth_eq := by simpa only [Located.binderPrefix, List.length_nil, Nat.add_zero, Nat.zero_add]
    using path.depth_eq.symm

/-- A genuinely typed whole-projection query is reindexed after all its
occurrence frames have been computed by binder descent. The caller supplies
one original source frame, reused unchanged for the original argument.
The result preserves the full demand, including nonempty field packets. -/
theorem TypedCutPath.reindexProjection
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    (path : TypedCutPath env registry target (Located.here (root := root)) baseLocals baseRealization
      location locals σ depth before after)
    (equal : expression = (VExpr.proj name index major).lift' (.skipN .refl depth))
    (query : ProjectionObs env registry target (node.cast equal rfl) locals σ demand after)
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U rootSource (.proj name index major) argumentType)
    (provenance : EndpointProvenance initial argument)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (frame : OriginalQueryFrame env registry target initial baseLocals baseRealization available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (resources : before.Available available)
    (comparison : DisplayCoherence env U registry
      ((path.cutOrigin equal).sourceDisplay initial)
      ((path.cutOrigin equal).argumentDisplay initial argument provenance)) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target argument
      baseLocals baseRealization demand nextFootprint) ∧ nextFootprint.Available available := by
  obtain ⟨fullAvailable, ⟨occurrence⟩, fullClosed, fullResources, tail⟩ :=
    path.frames initial henv below frame closed resources
  exact ProjectionObs.reindexAt (origin := path.cutOrigin equal) query initial initial argument provenance occurrence frame
    path.realizationTail tail fullClosed formed fullResources comparison

/-- Typed path descent does not enlarge the original closure budget. -/
theorem TypedCutPath.cut_cost_le
    {argument : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    (path : TypedCutPath env registry target (Located.here (root := root)) baseLocals baseRealization
      location locals σ depth before after)
    (equal : expression = argument.lift' (.skipN .refl depth))
    (initial : ContextDerivation sourceEnv U rootSource) :
    ((path.cutOrigin equal).sourceDisplay initial).cost ≤
      (Closure.close root.origin initial.closures).cost := by
  rw [CutOriginAt.sourceDisplay_cost]
  exact location.cost_le initial.closures

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
