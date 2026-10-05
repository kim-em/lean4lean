import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication

/-! Whole application children recovered at one actual original head. Reference
exposure and source conversion routes are deterministic; wrapper traversal does
not require retyping an argument at a merely equal raw domain. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def PrefixRoute.append
    (first : PrefixRoute env U source expression start middle)
    (second : PrefixRoute env U source expression middle last) :
    PrefixRoute env U source expression start last :=
  match first with
  | .done _ => second
  | .expose reference rest => .expose reference (rest.append second)
  | .convert plan term rest => .convert plan term (rest.append second)

def EndpointState.Structural : EndpointState env U source expression assigned → Prop
  | .ref _ | .convert .. => False
  | _ => True

/-- Structural heads reached through original reference/conversion routes
are unique, including their actual typing children. -/
theorem PrefixRoute.structural_unique
    {start : EndpointState env U source expression assigned}
    {last : EndpointState env U source expression natural}
    (first : PrefixRoute env U source expression start last)
    (head : EndpointState.Structural last)
    {other : EndpointState env U source expression otherType}
    (second : PrefixRoute env U source expression start other)
    (otherHead : EndpointState.Structural other) : natural = otherType ∧ HEq last other := by
  induction first generalizing otherType with
  | done node =>
    cases second with
    | done => exact ⟨rfl, HEq.rfl⟩
    | expose => cases head
    | convert => cases head
  | expose reference rest ih =>
    cases second with
    | done => cases otherHead
    | expose _ other => exact ih head other otherHead
  | convert plan term rest ih =>
    cases second with
    | done => cases otherHead
    | convert _ _ other => exact ih head other otherHead

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def RichAppOrigin.node
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a) :
    EndpointState sourceEnv U source (.app f a) (origin.B.inst a) :=
  EndpointState.app origin.hu origin.hv origin.domain origin.codomain
    origin.functionNode origin.argumentNode origin.result

def RichAppOrigin.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (start : EndpointState sourceEnv U source (.app f a) assigned) : Prop :=
  Nonempty (PrefixRoute sourceEnv U source (.app f a) start origin.node)

noncomputable def RichAppOrigin.ofSortablePrefix
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node}
    (packet : ApplicationPrefix start)
    (origin : SortableAppOrigin env U registry target locals σ f a) :
    RichAppOrigin root env registry target source locals σ f a :=
  let view := packet.view
  ⟨view.domainExpression, view.codomainExpression, view.domainLevel, view.bodyLevel,
    view.domainWF, view.bodyWF, view.domain, view.codomain, view.function, view.argument,
    view.result, view.location, origin.rank, origin.key, origin.output,
    origin.functionFootprint, origin.argumentFootprint, .legacy origin.function,
    origin.rawInput, .legacy origin.argument, origin.arguments, origin.admitted⟩

def RichApplicationOrigin.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichApplicationOrigin root env registry target source locals σ f a)
    (start : EndpointState sourceEnv U source (.app f a) assigned) : Prop :=
  match origin with
  | .original physical => physical.RootedAt start
  | .charged packet => Nonempty (PrefixRoute sourceEnv U source (.app f a) start packet.node)

theorem RichApplicationOrigin.RootedAt.prepend
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RichApplicationOrigin root env registry target source locals σ f a}
    {start : EndpointState sourceEnv U source (.app f a) assigned}
    {middle : EndpointState sourceEnv U source (.app f a) otherAssigned}
    (rooted : origin.RootedAt middle)
    (path : PrefixRoute sourceEnv U source (.app f a) start middle) : origin.RootedAt start := by
  cases origin with
  | original physical => obtain ⟨rest⟩ := rooted; exact ⟨path.append rest⟩
  | charged charged => obtain ⟨rest⟩ := rooted; exact ⟨path.append rest⟩

private theorem rootedCodeOrigin
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output a) ∧
      List.Subset origin.footprint footprint ∧ origin.RootedAt node)
    (member : b ∈ q.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output b) ∧
      List.Subset origin.footprint footprint ∧ origin.RootedAt node := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨origin, ⟨path⟩, included, route⟩ := origins a ha
  exact ⟨origin, ⟨.code path leaf (formed.singleton_of_mem ha)⟩, included, route⟩

mutual
theorem RichObs.applicationOriginRooted
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧ origin.RootedAt node := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .legacy source, location =>
    obtain ⟨origin, path, included⟩ := source.applicationOrigin member
    let packet := applicationPrefix location
    exact ⟨.original (RichAppOrigin.ofSortablePrefix packet origin), path, included, ⟨packet.route⟩⟩
  | _, _, _, _, _, .code source, location => exact source.applicationOriginRooted location member
  | _, _, _, _, .app hu hv domain codomain function arg result,
      .app _ _ fn argument arguments admitted, location =>
    cases List.mem_singleton.mp member
    exact ⟨.original ⟨_, _, _, _, hu, hv, _, _, _, _, _, location, _, _, _, _, _, fn, _,
      argument, arguments, admitted⟩, ⟨.refl⟩, (fun _ h => h), ⟨.done _⟩⟩
  | _, _, _, _, _, .route path source, location =>
    obtain ⟨origin, action, included, rooted⟩ := source.applicationOriginRooted (path.locate location) member
    exact ⟨origin, action, included, rooted.prepend path⟩
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, route⟩ := left.applicationOriginRooted location h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), route⟩
    · obtain ⟨origin, path, included, route⟩ := right.applicationOriginRooted location h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), route⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, route⟩ := source.applicationOriginRooted location ha
    exact ⟨origin, ⟨.pad path⟩, included, route⟩
  | _, _, _, _, _, .unpad source, location =>
    obtain ⟨origin, ⟨path⟩, included, route⟩ := source.applicationOriginRooted location (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, route⟩
  | _, _, _, _, _, .view source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, route⟩ := source.applicationOriginRooted location (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included, route⟩
  | _, _, _, _, _, .select source selected, location =>
    cases List.mem_singleton.mp member
    exact source.applicationOriginRooted location selected
  | _, _, _, _, _, .action source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, route⟩ := source.applicationOriginRooted location (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path change⟩, included, route⟩
termination_by sizeOf query

theorem RichCert.applicationOriginRooted
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    (query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) :
    ∃ origin : RichApplicationOrigin root env registry target source locals σ f arg,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset origin.footprint footprint ∧ origin.RootedAt node := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .legacy source, location =>
    obtain ⟨origin, path, included⟩ := source.applicationOrigin member
    let packet := applicationPrefix location
    exact ⟨.original (RichAppOrigin.ofSortablePrefix packet origin), path, included, ⟨packet.route⟩⟩
  | _, _, _, _, node, .recipe code, location =>
    exact ⟨.charged ⟨_, node, location, _, _, atom, _, .action (.select member) code⟩,
      ⟨.refl⟩, (fun _ h => h), ⟨.done _⟩⟩
  | _, _, _, _, _, .observe source _, location => exact source.applicationOriginRooted location member
  | _, _, _, _, _, .route path source, location =>
    obtain ⟨origin, action, included, rooted⟩ := source.applicationOriginRooted (path.locate location) member
    exact ⟨origin, action, included, rooted.prepend path⟩
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, route⟩ := left.applicationOriginRooted location h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), route⟩
    · obtain ⟨origin, path, included, route⟩ := right.applicationOriginRooted location h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), route⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, route⟩ := source.applicationOriginRooted location ha
    exact ⟨origin, ⟨.pad path⟩, included, route⟩
  | _, _, _, _, _, .down source, location =>
    exact rootedCodeOrigin .down source.formed (fun _ h => source.applicationOriginRooted location h) member
  | _, _, _, _, _, .map view source, location =>
    exact rootedCodeOrigin (.map view) source.formed (fun _ h => source.applicationOriginRooted location h) member
  | _, _, _, _, _, .support action source, location =>
    exact rootedCodeOrigin (.support action) source.formed (fun _ h => source.applicationOriginRooted location h) member
  | _, _, _, _, _, .select source selected, location =>
    exact rootedCodeOrigin (.select selected) source.formed (fun _ h => source.applicationOriginRooted location h) member
termination_by sizeOf query
end

/-- Both child queries live at the computed application's actual children.
The equality comes from finite route determinism, not raw type uniqueness. -/
theorem RichAppOrigin.childrenAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (rooted : origin.RootedAt node)
    (packet : ApplicationPrefix start) :
    Nonempty (RichObs sourceEnv env U registry target packet.view.function locals σ
      (Profile.fn origin.key origin.output) origin.functionFootprint) ∧
    Nonempty (RichObs sourceEnv env U registry target packet.view.argument locals σ
      origin.rawInput origin.argumentFootprint) := by
  obtain ⟨route⟩ := rooted
  have equal := route.structural_unique (by trivial) packet.route (by trivial)
  cases origin with
  | mk A B u v hu hv domain codomain functionNode argumentNode result location rank key output
      functionFootprint argumentFootprint function rawInput argument arguments admitted =>
    cases packet with
    | mk view packetRoute locationEq =>
      cases view with
      | mk A' B' u' v' hu' hv' domain' codomain' function' argument' result' location' prefixEq cost =>
        simp only [RichAppOrigin.node] at equal
        obtain ⟨_, _, _, domainEq, _, bodyEq, _, _, _, _, _, functionEq, argumentEq, _⟩ :=
          EndpointState.app.hinj rfl rfl rfl rfl equal.1 equal.2
        cases domainEq
        cases bodyEq
        have functionEq := eq_of_heq functionEq
        have argumentEq := eq_of_heq argumentEq
        cases functionEq
        cases argumentEq
        exact ⟨⟨function⟩, ⟨argument⟩⟩

def RichApplicationSeeds.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms)
    (node : EndpointState sourceEnv U source (.app f a) assigned) : Prop :=
  match seeds with
  | .nil => True
  | .cons origin _ _ rest => origin.RootedAt node ∧ rest.RootedAt node

/-- Mixed finite dispatch keeps charged requests alongside physical children.
Only physical leaves contribute function/argument requests; charged leaves
remain explicit for canonical interpretation at their retained caller node. -/
inductive RichApplicationDispatch
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr)
    (originalFootprint : Footprint) : List (Atom n) → Type where
  | nil : RichApplicationDispatch root env registry target source locals σ f a originalFootprint []
  | cons (origin : RichApplicationOrigin root env registry target source locals σ f a)
      (path : GeneralOutputPath env U registry target origin.output atom)
      (included : List.Subset origin.footprint originalFootprint)
      (rest : RichApplicationDispatch root env registry target source locals σ f a originalFootprint atoms) :
      RichApplicationDispatch root env registry target source locals σ f a originalFootprint (atom :: atoms)

def RichApplicationDispatch.RootedAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (seeds : RichApplicationDispatch root env registry target source locals σ f a footprint atoms)
    (node : EndpointState sourceEnv U source (.app f a) assigned) : Prop :=
  match seeds with
  | .nil => True
  | .cons origin _ _ rest => origin.RootedAt node ∧ rest.RootedAt node

theorem RichCert.applicationSeedsRooted
    {profile : Profile n}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (location : Located root node) :
    ∃ seeds : RichApplicationDispatch root env registry target source locals σ f a footprint profile.atoms,
      seeds.RootedAt node := by
  have each := fun atom member => query.applicationOriginRooted location (atom := atom) member
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, ∃ origin : RichApplicationOrigin root env registry target source locals σ f a,
        Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
        List.Subset origin.footprint footprint ∧
          origin.RootedAt node) →
      ∃ seeds : RichApplicationDispatch root env registry target source locals σ f a footprint atoms,
        seeds.RootedAt node from collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => exact fun _ => ⟨.nil, trivial⟩
  | cons atom atoms ih =>
    intro each
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := each atom (by simp)
    obtain ⟨rest, rootedRest⟩ := ih (fun a h => each a (by simp [h]))
    exact ⟨.cons origin path included rest, rooted, rootedRest⟩

/-- All finite requests for one canonical original child. Source footprints
stay subordinate to the incoming query throughout the collection. -/
inductive RichSourceQueries
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (originalFootprint : Footprint) : List Need → Type where
  | nil : RichSourceQueries sourceEnv env U registry target node locals σ originalFootprint []
  | cons (need : Need)
      (query : RichObs sourceEnv env U registry target node locals σ need.profile footprint)
      (included : List.Subset footprint originalFootprint)
      (rest : RichSourceQueries sourceEnv env U registry target node locals σ originalFootprint needs) :
      RichSourceQueries sourceEnv env U registry target node locals σ originalFootprint (need :: needs)

def RichApplicationSeeds.functionNeeds
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms) : List Need :=
  match seeds with
  | .nil => []
  | .cons origin _ _ rest => origin.functionNeed :: rest.functionNeeds

def RichApplicationSeeds.argumentNeeds
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms) : List Need :=
  match seeds with
  | .nil => []
  | .cons origin _ _ rest => origin.argumentNeed :: rest.argumentNeeds

/-- Route uniqueness constructs both whole original child query lists, so
neither source declared-domain typing nor a child reindex callback is needed. -/
theorem RichApplicationSeeds.childQueries
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node}
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms)
    (rooted : seeds.RootedAt node) (packet : ApplicationPrefix start) :
    Nonempty (RichSourceQueries sourceEnv env U registry target packet.view.function locals σ footprint
      seeds.functionNeeds) ∧
    Nonempty (RichSourceQueries sourceEnv env U registry target packet.view.argument locals σ footprint
      seeds.argumentNeeds) := by
  induction seeds with
  | nil => exact ⟨⟨.nil⟩, ⟨.nil⟩⟩
  | cons origin path included rest ih =>
    obtain ⟨⟨function⟩, ⟨argument⟩⟩ := origin.childrenAt rooted.1 packet
    obtain ⟨⟨functions⟩, ⟨arguments⟩⟩ := ih rooted.2
    exact ⟨⟨.cons origin.functionNeed function
      (fun _ h => included (List.mem_append_left _ h)) functions⟩,
      ⟨.cons origin.argumentNeed argument
        (fun _ h => included (List.mem_append_right _ h)) arguments⟩⟩

def RichApplicationDispatch.functionNeeds
    (seeds : RichApplicationDispatch root env registry target source locals σ f a footprint atoms) : List Need :=
  match seeds with
  | .nil => []
  | .cons (.original origin) _ _ rest => origin.functionNeed :: rest.functionNeeds
  | .cons (.charged _) _ _ rest => rest.functionNeeds

def RichApplicationDispatch.argumentNeeds
    (seeds : RichApplicationDispatch root env registry target source locals σ f a footprint atoms) : List Need :=
  match seeds with
  | .nil => []
  | .cons (.original origin) _ _ rest => origin.argumentNeed :: rest.argumentNeeds
  | .cons (.charged _) _ _ rest => rest.argumentNeeds

theorem RichApplicationDispatch.childQueries
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node}
    (seeds : RichApplicationDispatch root env registry target source locals σ f a footprint atoms)
    (rooted : seeds.RootedAt node) (packet : ApplicationPrefix start) :
    Nonempty (RichSourceQueries sourceEnv env U registry target packet.view.function locals σ footprint
      seeds.functionNeeds) ∧
    Nonempty (RichSourceQueries sourceEnv env U registry target packet.view.argument locals σ footprint
      seeds.argumentNeeds) := by
  induction seeds with
  | nil => exact ⟨⟨.nil⟩, ⟨.nil⟩⟩
  | cons origin path included rest ih =>
    obtain ⟨⟨functions⟩, ⟨arguments⟩⟩ := ih rooted.2
    cases origin with
    | original physical =>
      obtain ⟨⟨function⟩, ⟨argument⟩⟩ := physical.childrenAt rooted.1 packet
      exact ⟨⟨.cons physical.functionNeed function
        (fun _ h => included (List.mem_append_left _ h)) functions⟩,
        ⟨.cons physical.argumentNeed argument
          (fun _ h => included (List.mem_append_right _ h)) arguments⟩⟩
    | charged charged => exact ⟨⟨functions⟩, ⟨arguments⟩⟩

def RichSourceQueries.rank (queries : RichSourceQueries sourceEnv env U registry target node locals σ footprint needs) : Nat :=
  match queries with
  | .nil => 0
  | .cons need _ _ rest => max need.rank rest.rank

theorem RichSourceQueries.bounded
    (queries : RichSourceQueries sourceEnv env U registry target node locals σ footprint needs) :
    ∀ need ∈ needs, need.rank ≤ queries.rank := by
  induction queries with
  | nil => intro _ member; cases member
  | cons need query included rest ih =>
    intro selected member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih _ member) (Nat.le_max_right _ _)

/-- The actual combined source observer is constructed by finite unions at
one computed grade. It retains every whole projected/native child query. -/
theorem RichSourceQueries.collectAt
    (queries : RichSourceQueries sourceEnv env U registry target node locals σ footprint needs)
    (N : Nat) (bounded : ∀ need ∈ needs, need.rank ≤ N)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (RichObs sourceEnv env U registry target node locals σ
      (.mk (needs.flatMap (fun need => (need.atGrade N).atoms))) required) ∧
      required.Available available := by
  induction queries with
  | nil => exact ⟨[], ⟨.legacy (.legacy .empty)⟩, by intro _ _ member; cases member⟩
  | cons need query included rest ih =>
    have firstBound := bounded need List.mem_cons_self
    obtain ⟨remaining, ⟨restQuery⟩, restAvailable⟩ := ih
      (fun next member => bounded next (List.mem_cons_of_mem _ member))
    have first := query.raise firstBound
    rw [← show need.atGrade N = raiseProfile N firstBound need.profile from dif_pos firstBound] at first
    refine ⟨_, ⟨.union first restQuery⟩, ?_⟩
    intro index selected member
    exact (List.mem_append.mp member).elim
      (fun h => resources index selected (included h)) (restAvailable index selected)

structure RichCollectedQuery
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) (needs : List Need) where
  rank : Nat
  input : Profile rank
  footprint : Footprint
  query : RichObs sourceEnv env U registry target node locals σ input footprint
  resources : footprint.Available available
  bounded : ∀ need ∈ needs, need.rank ≤ rank
  covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade rank).atoms, atom ∈ input.atoms

theorem RichSourceQueries.collect
    (queries : RichSourceQueries sourceEnv env U registry target node locals σ footprint needs)
    (resources : footprint.Available available) :
    Nonempty (RichCollectedQuery sourceEnv env U registry target node locals σ available needs) := by
  obtain ⟨required, ⟨query⟩, supplied⟩ := queries.collectAt queries.rank queries.bounded resources
  exact ⟨⟨queries.rank, .mk (needs.flatMap (fun need => (need.atGrade queries.rank).atoms)), required,
    query, supplied, queries.bounded,
    fun need member atom present => List.mem_flatMap.mpr ⟨need, member, present⟩⟩⟩

/-- An application certificate produces exact mixed dispatch and collected
physical child observations. Charged requests remain in the returned dispatch
and are not represented by the two physical child observations. -/
theorem RichCert.applicationInputs
    {profile : Profile n}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    {start : Located root node} (packet : ApplicationPrefix start)
    (resources : footprint.Available available) :
    ∃ seeds : RichApplicationDispatch root env registry target source locals σ f a footprint profile.atoms,
      seeds.RootedAt node ∧
      Nonempty (RichCollectedQuery sourceEnv env U registry target packet.view.function locals σ available seeds.functionNeeds) ∧
      Nonempty (RichCollectedQuery sourceEnv env U registry target packet.view.argument locals σ available seeds.argumentNeeds) := by
  obtain ⟨seeds, rooted⟩ := query.applicationSeedsRooted start
  obtain ⟨⟨functions⟩, ⟨arguments⟩⟩ := seeds.childQueries rooted packet
  exact ⟨seeds, rooted, functions.collect resources, arguments.collect resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
