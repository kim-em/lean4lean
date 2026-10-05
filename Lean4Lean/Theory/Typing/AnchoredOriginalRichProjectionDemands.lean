import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionOrigins

/-! Demand discovery from an ACTUAL returned projected type certificate.
Every request retains its original major observer, field code and prefix
route. This produces source queries, not just target need profiles. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

structure RichProjectionDemand
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (locals : List Nat) (σ : Subst) (available : Valuation) (atom : Atom n) where
  origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value
  path : GeneralOutputPath env U registry target origin.atom atom
  route : PrefixRoute sourceEnv U source (.proj name index value) node (projectionNatural origin.head)
  majorResources : origin.majorFootprint.Available available
  fieldResources : origin.fieldFootprint.Available available

inductive RichProjectionDemands
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (locals : List Nat) (σ : Subst) (available : Valuation) : List (Atom n) → Type where
  | nil : RichProjectionDemands (node := node) (env := env) (registry := registry) (target := target) locals σ available []
  | cons (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom)
      (tail : RichProjectionDemands (node := node) (env := env) (registry := registry)
        (target := target) locals σ available rest) :
      RichProjectionDemands (node := node) (env := env) (registry := registry)
        (target := target) locals σ available (atom :: rest)

/-- Arbitrary wrappers and actions are handled by the original projection
origin theorem. The resulting source major queries inherit actual available
resources from the returned owner certificate. -/
theorem RichCert.projectionDemands
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (RichProjectionDemands (node := node) (env := env) (registry := registry)
      (target := target) locals σ available profile.atoms) := by
  have extract : ∀ atom ∈ profile.atoms,
      Nonempty (RichProjectionDemand (node := node) (env := env) (registry := registry)
        (target := target) locals σ available atom) := by
    intro atom member
    obtain ⟨origin, ⟨path⟩, included, ⟨route⟩⟩ := certificate.projectionOrigin member
    exact ⟨{
      origin := origin
      path := path
      route := route
      majorResources := fun i need hm => resources i need (included (List.mem_append_left _ hm))
      fieldResources := fun i need hm => resources i need (included (List.mem_append_right _ hm)) }⟩
  generalize equation : profile.atoms = atoms at extract ⊢
  clear equation certificate resources
  induction atoms with
  | nil => exact ⟨.nil⟩
  | cons atom rest ih =>
    obtain ⟨head⟩ := extract atom (List.mem_cons_self)
    obtain ⟨tail⟩ := ih (fun a ha => extract a (List.mem_cons_of_mem _ ha))
    exact ⟨.cons head tail⟩

/-- An extracted demand is an actual original child occurrence in the same
source frame. In particular this applies at `location.assignedFormation`
after owner F, even beneath fresh source binders. -/
noncomputable def RichProjectionDemand.majorOccurrence
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom) :
    RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight := by
  let natural := occurrence.route demand.route
  let child : OriginalRichOccurrenceFrame (.projMajor (demand.route.locate location))
      initialContext env registry target locals σ τ available ordered initialEnvironment :=
    ⟨natural.frame, natural.substitutions, natural.environment_le⟩
  exact .ofQuery child closed demand.origin.majorQuery demand.majorResources true
    ((sourceTail.route demand.route).at rfl)

noncomputable def RichProjectionDemand.fieldOccurrence
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom) :
    RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight := by
  let natural := occurrence.route demand.route
  let child : OriginalRichOccurrenceFrame (.projField (demand.route.locate location))
      initialContext env registry target locals σ τ available ordered initialEnvironment :=
    ⟨natural.frame, natural.substitutions, natural.environment_le⟩
  exact .ofQuery child closed (.code demand.origin.fieldCode) demand.fieldResources true
    ((sourceTail.route demand.route).at rfl)

noncomputable def RichProjectionDemand.priorPending
    {field : EndpointRef sourceEnv U rootSource fieldExpression fieldType}
    {major : EndpointRef sourceEnv U rootSource majorExpression majorType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located field node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : value = rawCapture.lift' (.skipN .refl location.binderPrefix.length)) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable initialEnvironment rawCapture
      (rawCapture.subst rootLeft) (rawCapture.subst rootRight) := by
  apply (demand.majorOccurrence occurrence sourceTail closed).pendingField domain
    headerLocals declaredLeft headerAvailable
  simpa only [majorOccurrence, RichQueryOccurrence.ofQuery, Located.binderPrefix,
    demand.route.locate_binderPrefix] using expressionEq

noncomputable def RichProjectionDemands.requests
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (demands : RichProjectionDemands (node := node) (env := env) (registry := registry)
      (target := target) locals σ available (atoms : List (Atom n))) :
    List (Σ atom : Atom n, RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom) :=
  match demands with
  | .nil => []
  | .cons demand rest => ⟨_, demand⟩ :: rest.requests

theorem RichProjectionDemands.requests_atoms
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (demands : RichProjectionDemands (node := node) (env := env) (registry := registry)
      (target := target) locals σ available (atoms : List (Atom n))) :
    demands.requests.map Sigma.fst = atoms := by
  induction demands with
  | nil => rfl
  | cons demand rest ih => simp only [requests, List.map_cons, ih]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
