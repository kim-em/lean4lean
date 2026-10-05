import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandData
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableReplay

/-! A general variable result retains a finite dependency program. Separate
available needs are never replaced by an unavailable union need, and padding
may raise the output grade above every resource leaf. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private traceRename from Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

structure WorldVariableDependency (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (available : Valuation) (index : Nat) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  footprint : Footprint
  trace : SortableVariableTrace env U registry target index raw footprint
  resources : footprint.Available available
  adapter : GeneralNormalProfileAdapter env U registry target raw (raiseProfile rank bound requested)

noncomputable def WorldVariableDependency.ofDependency
    (dependency : RecipeVariableDependency env U registry target available index requested) :
    WorldVariableDependency env U registry target available index requested := by
  classical
  let footprint := Classical.choose dependency
  let trace := Classical.choice (Classical.choose_spec dependency).1
  exact { rank := _, bound := Nat.le_refl _, raw := requested, footprint := footprint
          trace := trace, resources := (Classical.choose_spec dependency).2
          adapter := by rw [raiseProfile_self]; exact .refl _ }

noncomputable def WorldVariableDependency.ofDemand
    (demand : WorldVariableDemand env U registry target available index requested) :
    WorldVariableDependency env U registry target available index requested where
  rank := demand.rank
  bound := demand.bound
  raw := demand.raw
  footprint := [(index, Need.mk demand.rank demand.raw)]
  trace := .legacy (.leaf demand.raw)
  resources := by intro i need member; cases List.mem_singleton.mp member; exact demand.member
  adapter := demand.adapter

noncomputable def WorldVariableDependency.availableMono
    (dependency : WorldVariableDependency env U registry target available index requested)
    (included : ∀ i need, need ∈ available i → need ∈ next i) :
    WorldVariableDependency env U registry target next index requested :=
  { dependency with resources := fun i need member => included i need (dependency.resources i need member) }

noncomputable def WorldVariableDependency.push
    (dependency : WorldVariableDependency env U registry target available index requested)
    (needs : List Need) :
    WorldVariableDependency env U registry target (available.push needs) (index + 1) requested where
  rank := dependency.rank
  bound := dependency.bound
  raw := dependency.raw
  footprint := dependency.footprint.map (fun entry => (entry.1 + 1, entry.2))
  trace := Classical.choice (traceRename dependency.trace Nat.succ)
  resources := by
    intro i need member
    obtain ⟨⟨oldIndex, oldNeed⟩, oldMember, equal⟩ := List.mem_map.mp member
    cases equal
    exact dependency.resources oldIndex oldNeed oldMember
  adapter := dependency.adapter

structure WorldVariableDependencyReply
    {strata : EquationStratification env} (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (commonLeft commonRight : Subst)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length)) (index : Nat) (requested : Profile n) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available
  generation : WorldGenerated strata P base caps commonLeft commonRight graph realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  hereditary : generation.Hereditary frontier
  capacity : ∀ ordered : sourceEnv.Ordered,
    environmentCost (realization.frame.dependencyEnvironment ordered) ≤ environmentCost environment
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds baseline.worlds
  dependency : WorldVariableDependency env U registry target available index requested

noncomputable def WorldVariableDemandReply.toDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDemandReply P base caps graph commonLeft commonRight controls baseline frontier index requested) :
    WorldVariableDependencyReply P base caps graph commonLeft commonRight controls baseline frontier index requested := {
  locals := answer.locals, available := answer.available, realization := answer.realization
  generation := answer.generation, replayable := answer.replayable, controlled := answer.controlled
  compatible := answer.compatible, hereditary := answer.hereditary, capacity := answer.capacity
  covered := answer.covered, dependency := .ofDemand answer.demand }

private noncomputable def variableLeaves
    (locals : List Nat) (σ : Subst) (index N : Nat) (footprint : Footprint)
    (indices : ∀ i need, (i, need) ∈ footprint → i = index)
    (bounded : ∀ i need, (i, need) ∈ footprint → need.rank ≤ N) :
    Obs env U registry target locals σ (.bvar index) (footprint.atGrade N) footprint := by
  match footprint with
  | [] => exact .empty
  | (i, need) :: rest =>
    have same := indices i need List.mem_cons_self
    subst i
    have bound := bounded index need List.mem_cons_self
    let head := (Obs.var (env := env) (U := U) (registry := registry) (target := target) locals σ index need.profile).raise bound
    let tail := variableLeaves (env := env) (U := U) (registry := registry) (target := target) locals σ index N rest
      (fun i need member => indices i need (List.mem_cons_of_mem _ member))
      (fun i need member => bounded i need (List.mem_cons_of_mem _ member))
    simpa only [Footprint.atGrade, List.flatMap_cons, Need.atGrade, dif_pos bound, Profile.union, Profile.atoms, Profile.mk, List.singleton_append] using
      Obs.union head tail

private theorem footprintLive_atGrade
    (live : Footprint.Live env U registry target footprint) (N : Nat) :
    Profile.Live env U registry target (footprint.atGrade N) := by
  induction footprint with
  | nil => exact fun _ member => by cases member
  | cons entry rest ih =>
    change Profile.Live env U registry target ((entry.2.atGrade N).union (Footprint.atGrade N rest))
    apply Profile.Live.union_iff.mpr
    refine ⟨?_, ih (fun i need member => live i need (List.mem_cons_of_mem _ member))⟩
    unfold Need.atGrade
    split
    · exact (raiseProfile_live_iff _ _).mpr (live entry.1 entry.2 List.mem_cons_self)
    · exact fun _ member => by cases member

noncomputable def WorldVariableDependency.atNode
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (dependency : WorldVariableDependency env U registry target available index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned) :
    RichGradedResult sourceEnv env U registry target node locals σ available requested := by
  have indexBound : index < source.length :=
    node.sound.defeq.closedN ordered (CtxWF.closed ordered context.forget.defeq)
  obtain ⟨lookupType, lookup⟩ := Lookup.ofLt indexBound
  have leaves : Footprint.Live env U registry target dependency.footprint := by
    intro i need member
    have same := dependency.trace.indices member
    subst i
    obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed (dependency.resources index need member) lookup
    exact entry.related.live henv hscoped formed
  refine {
    rank := dependency.trace.height
    bound := Nat.le_trans dependency.bound dependency.trace.output_bound
    raw := dependency.footprint.atGrade dependency.trace.height
    footprint := dependency.footprint
    observation := .legacy (.legacy (variableLeaves locals σ index dependency.trace.height dependency.footprint
      (fun i need member => dependency.trace.indices member)
      (fun i need member => dependency.trace.leaf_bound member)))
    resources := dependency.resources
    adapter := ?_
    live := footprintLive_atGrade leaves _ }
  exact (dependency.trace.normalize henv hscoped formed _ (Nat.le_refl _)).comp (by
    simpa only [raiseProfile_trans] using GeneralNormalProfileAdapter.raise henv hscoped formed
      dependency.trace.output_bound dependency.adapter)

noncomputable abbrev WorldVariableDependencyReply.ofDemand := @WorldVariableDemandReply.toDependency

noncomputable def WorldVariableDependency.atNode_controlled
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (dependency : WorldVariableDependency env U registry target available index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned) :
    ControlledStoredQuery controls frontier
      (.observation (dependency.atNode henv hscoped formed ordered frame node).observation) := by
  let query := variableLeaves (env := env) (U := U) (registry := registry) (target := target)
    locals σ index dependency.trace.height dependency.footprint
    (fun i need member => dependency.trace.indices member)
    (fun i need member => dependency.trace.leaf_bound member)
  let result := neutralObsProvenance (strata := strata) query
  let annotation := Classical.choose result
  have worlds := (Classical.choose_spec result).1
  have depth := (Classical.choose_spec result).2
  refine { annotation := .legacy _ (.legacy _ annotation), within := ?_, sponsored := ?_ }
  · intro control active
    simpa only [WorldVariableDependency.atNode, StoredOriginalQuery.headDepth, RichObs.headDepth,
      SortableObs.headDepth] using (show query.headDepth _ ≤ controls.fuel control from by
        rw [depth]; exact Nat.zero_le _)
  · change Sponsored frontier annotation.worlds
    rw [worlds]
    intro child member
    cases member

noncomputable def WorldVariableDependencyReply.atNode
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDependencyReply P base caps graph commonLeft commonRight controls baseline frontier index requested)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node) :
    let display : OriginalNestedDisplay U common (raw index) (assigned.subst raw) :=
      ⟨sourceEnv, source, .bvar index, assigned, context, node, provenance, raw, graph, rfl, rfl⟩
    AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested (environmentCost environment) := {
  answer := {
    reply := {
      locals := answer.locals
      available := answer.available
      realization := answer.realization
      generated := answer.generation.erase.capped.generated
      query := answer.dependency.atNode henv hscoped formed controls.ordered answer.realization.frame node
      closed := answer.hereditary.tablesClosed.closed }
    capped := answer.generation.erase.capped }
  bounded := answer.capacity
  generation := answer.generation.erase.ambientGenerated }

noncomputable def WorldVariableDependencyReply.atNode_data
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDependencyReply P base caps graph commonLeft commonRight controls baseline frontier index requested)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node) :
    WorldGeneratedQueryReplyData (P := P) controls baseline frontier
      (answer.atNode henv hscoped formed node provenance) where
  generation := answer.generation
  replayable := answer.replayable
  controlled := answer.controlled
  compatible := answer.compatible
  query := answer.dependency.atNode_controlled controls frontier henv hscoped formed
    controls.ordered answer.realization.frame node
  covered := answer.covered
  hereditary := answer.hereditary

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
