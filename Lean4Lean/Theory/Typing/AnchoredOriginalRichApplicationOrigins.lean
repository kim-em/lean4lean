import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplication
import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin

/-! Application requests recovered from the actual rich query, including
all code/action wrappers. Physical application leaves retain their original
function and argument queries. Charged code leaves retain their exact recipe
and caller occurrence instead of inventing physical application children.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

structure RichAppOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  A : VExpr
  B : VExpr
  u : VLevel
  v : VLevel
  hu : u.WF U
  hv : v.WF U
  domain : EndpointState sourceEnv U source A (.sort u)
  codomain : EndpointState sourceEnv U (A :: source) B (.sort v)
  functionNode : EndpointState sourceEnv U source f (.forallE A B)
  argumentNode : EndpointState sourceEnv U source a A
  result : EndpointState sourceEnv U source (B.inst a) (.sort v)
  location : Located root (.app hu hv domain codomain functionNode argumentNode result)
  rank : Nat
  key : Key rank
  output : Atom rank
  functionFootprint : Footprint
  argumentFootprint : Footprint
  function : RichObs sourceEnv env U registry target functionNode locals σ
    (Profile.fn key output) functionFootprint
  rawInput : Profile rank
  argument : RichObs sourceEnv env U registry target argumentNode locals σ rawInput argumentFootprint
  arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input
  admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)

noncomputable def RichAppOrigin.ofSortable
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (location : Located root node)
    (origin : SortableAppOrigin env U registry target locals σ f a) :
    RichAppOrigin root env registry target source locals σ f a :=
  let view := appView location
  ⟨view.domainExpression, view.codomainExpression, view.domainLevel, view.bodyLevel,
    view.domainWF, view.bodyWF, view.domain, view.codomain, view.function, view.argument,
    view.result, view.location, origin.rank, origin.key, origin.output,
    origin.functionFootprint, origin.argumentFootprint, .legacy origin.function,
    origin.rawInput, .legacy origin.argument, origin.arguments, origin.admitted⟩

/-- A charged application code request keeps the actual caller occurrence and
its exact finite recipe. Its function and argument need not be physical query
children of that caller: the canonical root remains inside the recipe. -/
structure RichChargedAppOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.app f a) assigned
  location : Located root node
  relevant : Bool
  rank : Nat
  output : Atom rank
  footprint : Footprint
  recipe : RichCodeRecipe env U registry target source locals σ (.app f a)
    relevant (.singleton output) footprint

/-- Source dispatch distinguishes physical application queries from charged
code. Both retain the finite output path subsequently applied by wrappers. -/
inductive RichApplicationOrigin
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  | original (origin : RichAppOrigin root env registry target source locals σ f a)
  | charged (origin : RichChargedAppOrigin root env registry target source locals σ f a)

namespace RichApplicationOrigin

def rank (origin : RichApplicationOrigin root env registry target source locals σ f a) : Nat :=
  match origin with
  | .original source => source.rank
  | .charged source => source.rank

def output (origin : RichApplicationOrigin root env registry target source locals σ f a) : Atom origin.rank :=
  match origin with
  | .original source => source.output
  | .charged source => source.output

def footprint (origin : RichApplicationOrigin root env registry target source locals σ f a) : Footprint :=
  match origin with
  | .original source => source.functionFootprint ++ source.argumentFootprint
  | .charged source => source.footprint

end RichApplicationOrigin

private theorem richCodeOrigin
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint)
    (member : b ∈ q.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, ⟨path⟩, included⟩ := origins a ha
  exact ⟨origin, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included⟩

mutual
theorem RichObs.applicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .legacy source, location =>
    obtain ⟨origin, path, included⟩ := source.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortable location origin), path, included⟩
  | _, _, _, _, _, .code source, location => exact source.applicationOrigin location member
  | _, _, _, _, .app hu hv domain codomain function arg result,
      .app _ _ fn argument arguments admitted, location =>
    cases List.mem_singleton.mp member
    exact ⟨.original ⟨_, _, _, _, hu, hv, _, _, _, _, _, location, _, _, _, _, _, fn, _,
      argument, arguments, admitted⟩, ⟨.refl⟩, fun _ h => h⟩
  | _, _, _, _, _, .route path source, location => exact source.applicationOrigin (path.locate location) member
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin location h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin location h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin location ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, _, _, .unpad source, location =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, _, _, .view source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included⟩
  | _, _, _, _, _, .select source selected, location =>
    cases List.mem_singleton.mp member
    exact source.applicationOrigin location selected
  | _, _, _, _, _, .action source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin location (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path change⟩, included⟩
termination_by sizeOf query

theorem RichCert.applicationOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    (query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .legacy source, location =>
    obtain ⟨origin, path, included⟩ := source.applicationOrigin member
    exact ⟨.original (RichAppOrigin.ofSortable location origin), path, included⟩
  | _, _, _, _, node, .recipe code, location =>
    exact ⟨.charged ⟨_, node, location, _, _, atom, _, .action (.select member) code⟩,
      ⟨.refl⟩, fun _ h => h⟩
  | _, _, _, _, _, .observe source _, location => exact source.applicationOrigin location member
  | _, _, _, _, _, .route path source, location => exact source.applicationOrigin (path.locate location) member
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included⟩ := left.applicationOrigin location h
      exact ⟨origin, path, fun _ h => List.mem_append_left _ (included h)⟩
    · obtain ⟨origin, path, included⟩ := right.applicationOrigin location h
      exact ⟨origin, path, fun _ h => List.mem_append_right _ (included h)⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included⟩ := source.applicationOrigin location ha
    exact ⟨origin, ⟨.pad path⟩, included⟩
  | _, _, _, _, _, .down source, location =>
    exact richCodeOrigin .down source.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, .map view source, location =>
    exact richCodeOrigin (.map view) source.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, .support action source, location =>
    exact richCodeOrigin (.support action) source.formed (fun _ h => source.applicationOrigin location h) member
  | _, _, _, _, _, .select source selected, location =>
    exact richCodeOrigin (.select selected) source.formed (fun _ h => source.applicationOrigin location h) member
termination_by sizeOf query
end

/-- Physical application requests use genuine original function/argument
children strictly below the root. Charged code is handled by its separate
canonical recipe, not this physical-child schedule. -/
theorem RichAppOrigin.child_schedules
    (origin : RichAppOrigin root env registry target source locals σ f a) (initial : List Closure) :
    schedule .fundamental
      (Closure.close origin.functionNode.origin (origin.location.environment initial)).cost <
      schedule .fundamental (Closure.close root.origin initial).cost ∧
    schedule .fundamental
      (Closure.close origin.argumentNode.origin (origin.location.environment initial)).cost <
      schedule .fundamental (Closure.close root.origin initial).cost := by
  constructor <;> apply schedule_strict
  · exact Nat.lt_of_lt_of_le (binder_other_cost (by simp) (origin.location.environment initial))
      (origin.location.cost_le initial)
  · exact Nat.lt_of_lt_of_le (binder_other_cost (by simp) (origin.location.environment initial))
      (origin.location.cost_le initial)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
