import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTableClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection

/-! Actual generated source captures are expanded through their retained
queries before a common-variable demand is used. The output footprint obeys
common caps; it does not claim membership in a destination resource table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private traceRename from Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

variable {Fits Next : Nat → Need → Prop}

noncomputable def VariableDependencyProgram.leaf
    (fits : Fits index need) :
    VariableDependencyProgram env U registry target Fits index need.profile where
  rank := need.rank
  bound := Nat.le_refl _
  raw := need.profile
  footprint := [(index, need)]
  trace := .legacy (.leaf need.profile)
  resources := by intro i wanted member; cases List.mem_singleton.mp member; exact fits
  adapter := by rw [raiseProfile_self]; exact .refl _

noncomputable def VariableDependencyProgram.adaptRequest
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (program : VariableDependencyProgram env U registry target Fits index (rawInput : Profile k))
    (queryBound : n ≤ k)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n))) :
    VariableDependencyProgram env U registry target Fits index input :=
  VariableDependencyProgram.lowerRequested queryBound (program.map henv hscoped formed adapter)

noncomputable def VariableDependencyProgram.localDemand
    (program : VariableDependencyProgram env U registry target Fits index (input : Profile n))
    (need : Need) (bound : need.rank ≤ n)
    (included : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    VariableDependencyProgram env U registry target Fits index need.profile := {
  rank := program.rank, bound := Nat.le_trans bound program.bound
  raw := program.raw, footprint := program.footprint, trace := program.trace, resources := program.resources
  adapter := by
    have select : GeneralNormalProfileAdapter env U registry target
        (raiseProfile program.rank program.bound input)
        (raiseProfile program.rank program.bound (need.atGrade n)) := GeneralProfileAdapter.select (by
      intro atom member
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨old, raiseProfile_subset program.bound included old present, rfl⟩)
    simpa only [Need.atGrade, dif_pos bound, raiseProfile_trans] using program.adapter.comp select }

noncomputable def VariableDependencyProgram.renameIndex
    (program : VariableDependencyProgram env U registry target Fits index requested)
    (rename : Nat → Nat)
    (admitted : ∀ i need, (i, need) ∈ program.footprint → Fits i need → Next (rename i) need) :
    VariableDependencyProgram env U registry target Next (rename index) requested where
  rank := program.rank
  bound := program.bound
  raw := program.raw
  footprint := program.footprint.map (fun entry => (rename entry.1, entry.2))
  trace := Classical.choice (traceRename program.trace rename)
  resources := by
    intro i need member
    obtain ⟨⟨oldIndex, oldNeed⟩, oldMember, equal⟩ := List.mem_map.mp member
    cases equal
    exact admitted oldIndex oldNeed oldMember (program.resources oldIndex oldNeed oldMember)
  adapter := program.adapter

private theorem subst_variable_source {expression : VExpr} {raw : Subst} {index : Nat} (same : expression.subst raw = .bvar index) :
    ∃ sourceIndex, expression = .bvar sourceIndex ∧ raw sourceIndex = .bvar index := by
  cases expression <;> simp only [VExpr.subst] at same <;> try contradiction
  case bvar sourceIndex => exact ⟨sourceIndex, rfl, same⟩

private theorem lift_variable_source {expression : VExpr} {rho : Lift} {index : Nat} (same : expression.lift' rho = .bvar index) :
    ∃ sourceIndex, expression = .bvar sourceIndex ∧ rho.liftVar sourceIndex = index := by
  cases expression <;> simp only [VExpr.lift'] at same <;> try contradiction
  case bvar sourceIndex => exact ⟨sourceIndex, rfl, VExpr.bvar.inj same⟩

private theorem query_common_program
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {node : EndpointState sourceEnv U source expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available)
    (same : expression.subst raw = .bvar index)
    (supplied : ∀ i need, need ∈ available i → raw i = .bvar index →
      Nonempty (VariableDependencyProgram env U registry target Fits index need.profile)) :
    Nonempty (VariableDependencyProgram env U registry target Fits index profile) := by
  obtain ⟨sourceIndex, expressionEq, rawEq⟩ := subst_variable_source same
  cases expressionEq
  obtain ⟨used, ⟨trace⟩, present⟩ := query.variableDependency closed resources
  exact ⟨SortableVariableTrace.replayPrograms henv hscoped formed trace (fun i need member =>
    Classical.choice (supplied i need (present i need member) (by rw [trace.indices member]; exact rawEq)))⟩

/-- Every source leaf is expanded using a structural child of the actual
positive generation. A grouped leaf selects its real retained owner query;
no bank, semantic answer, or common-table membership is assumed. -/
theorem WorldGenerated.commonVariableNeed
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    generated.TablesClosed → ∀ (sourceIndex index : Nat) (need : Need),
    need ∈ available sourceIndex → raw sourceIndex = .bvar index →
    Nonempty (VariableDependencyProgram env U registry target caps index need.profile) := by
  induction generated with
  | identity =>
    intro closed sourceIndex index need member same
    have equal : sourceIndex = index := VExpr.bvar.inj same
    subst index
    exact ⟨.leaf member⟩
  | empty => intro _ _ _ _ member; cases member
  | merge first second leftIH rightIH =>
    intro closed sourceIndex index need member same
    rcases List.mem_append.mp member with member | member
    · exact leftIH closed.1 sourceIndex index need member same
    · exact rightIH closed.2 sourceIndex index need member same
  | weaken generated insertion leftTail rightTail capsTail ih =>
    intro closed sourceIndex index need member same
    obtain ⟨oldIndex, rawEq, indexEq⟩ := lift_variable_source same
    obtain ⟨program⟩ := ih closed sourceIndex oldIndex need member rawEq
    cases indexEq
    refine ⟨program.renameIndex _ (fun i need _ fits => ?_)⟩
    have equal := congrFun capsTail i
    change _ = _ at equal
    rw [equal]
    exact fits
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    intro closed sourceIndex index need member same
    cases sourceIndex with
    | zero =>
      have equal : 0 = index := VExpr.bvar.inj same
      subst index
      exact ⟨.leaf ⟨bounded need member, covered need member⟩⟩
    | succ sourceIndex =>
      simp only [Subst.lift, lift_eq_lift'] at same
      obtain ⟨oldIndex, rawEq, indexEq⟩ := lift_variable_source same
      obtain ⟨program⟩ := ih closed.1 sourceIndex oldIndex need member rawEq
      simp only [Lift.liftVar] at indexEq
      cases indexEq
      exact ⟨program.renameIndex Nat.succ (fun _ _ _ fits => fits)⟩
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    intro closed sourceIndex index need member same
    cases sourceIndex with
    | zero =>
      obtain ⟨program⟩ := query_common_program henv hscoped formed query (WorldGenerated.TablesClosed.closed (generated := generated) closed.1) queryAvailable same
        (fun i need member same => ih closed.1 i index need member same)
      exact ⟨(program.adaptRequest henv hscoped formed queryBound queryAdapter).localDemand need
        (bounded need member) (covered need member)⟩
    | succ sourceIndex => exact ih closed.1 sourceIndex index need member same
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    intro closed sourceIndex index need member same
    cases sourceIndex with
    | succ sourceIndex => exact tailIH closed.1 sourceIndex index need member same
    | zero =>
      obtain ⟨entry, entryMember, needed⟩ := List.mem_flatMap.mp member
      let scope := scopes entry entryMember
      have captured := displayed.trans same
      have exposed : entry.owner.expression.subst scope.raw = .bvar (index + entry.depth) := by
        have original := (entry.scopeDisplay scope).expression_eq.symm
        change entry.owner.expression.subst scope.raw = _ at original
        rw [captured] at original
        simpa only [VExpr.lift', Lift.liftVar_skipN, Lift.liftVar] using original
      obtain ⟨program⟩ := query_common_program henv hscoped formed entry.query
        (WorldGenerated.TablesClosed.closed (closed.2.2.2.2 entry entryMember)) entry.queryAvailable exposed
        (fun i need member same => ownerIH entry entryMember (closed.2.2.2.2 entry entryMember)
          i (index + entry.depth) need member same)
      let lowered := program.renameIndex (Next := fun i need => scope.caps ((Lift.skipN .refl entry.depth).liftVar i) need)
        (fun i => i - entry.depth) (fun i need member fits => by
        have equal := program.trace.indices member
        subst i
        simpa only [Nat.add_sub_cancel, Lift.liftVar_skipN, Lift.liftVar] using fits)
      let pulled := scope.capsTail ▸ lowered
      have bound := (captureNeeds_covered entry.input need needed).1
      have covered := (captureNeeds_covered entry.input need needed).2
      simpa only [Nat.add_sub_cancel] using Nonempty.intro
        ((pulled.adaptRequest henv hscoped formed entry.queryBound entry.queryAdapter).localDemand need bound covered)

/-- The actual incoming query and its original source frame compute finite
common-variable requests. Captured source needs are expanded, not relabeled. -/
theorem WorldGenerated.commonVariableQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : generated.TablesClosed)
    {node : EndpointState sourceEnv U source expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (resources : footprint.Available available) (same : expression.subst raw = .bvar index) :
    Nonempty (VariableDependencyProgram env U registry target caps index profile) :=
  query_common_program henv hscoped formed query closed.closed resources same
    (fun i need member same => generated.commonVariableNeed henv hscoped formed closed i index need member same)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
