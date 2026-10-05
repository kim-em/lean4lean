import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanFront
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationStep
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterFamilyOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPairedFrame
import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization

/-! Consume a native family plan at its own original header. The paired
header frame and every source argument query are built from the stored
binder guard and actual application admission. No unrelated normalized
header, declared-domain transfer, or completed family answer is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- One actual original source argument, not a newly typed replacement. -/
structure RichFamilyArgumentQuery
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (profile : Profile n) where
  assigned : VExpr
  node : EndpointState sourceEnv U source expression assigned
  location : Located root node
  query : RichGradedResult sourceEnv env U registry target node locals σ available profile

/-- Every slot retains one actual source endpoint even when its current
finite need list is empty. All later local-demand queries use that same node. -/
structure RichFamilyArgumentSlot
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (needs : List Need) where
  rank : Nat
  input : Profile rank
  argument : RichFamilyArgumentQuery root env registry target source locals σ available expression input
  bounded : ∀ need ∈ needs, need.rank ≤ rank
  covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade rank).atoms, atom ∈ input.atoms

inductive RichFamilyArgumentSpine
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) :
    List VExpr → Valuation → Type where
  | nil : RichFamilyArgumentSpine root env registry target source locals σ available [] (fun _ => [])
  | push (tail : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior)
      (slot : RichFamilyArgumentSlot root env registry target source locals σ available expression needs) :
      RichFamilyArgumentSpine root env registry target source locals σ available
        (arguments ++ [expression]) (Valuation.push needs prior)

/-- A property of actual source observers. It may retain proof-bearing
annotations; adapters and declared header semantics are not part of it. -/
abbrev RichFamilyQueryPredicate
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target source : List VExpr) (locals : List Nat) (σ : Subst) :=
  ∀ {expression assigned : VExpr} {node : EndpointState sourceEnv U source expression assigned}
    {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint → Prop

/-- Every stored slot carries the property of its SAME graded observer. -/
def RichFamilyArgumentSpine.Queries
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior) : Prop := by
  cases spine with
  | nil => exact True
  | push tail slot => exact tail.Queries property ∧ property slot.argument.query.observation

private theorem RichFamilyArgumentSpine.queriesTrue
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior) :
    spine.Queries (fun _ => True) := by
  induction spine with
  | nil => trivial
  | push tail slot ih => exact ⟨ih, trivial⟩

/-- Position selection retains the same owner for all requested atoms. -/
theorem RichFamilyArgumentSpine.lookup
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior)
    (index : Nat) (bound : index < arguments.length) :
    Nonempty (RichFamilyArgumentSlot root env registry target source locals σ available
      (arguments[arguments.length-1-index]'(by omega)) (prior index)) := by
  induction spine generalizing index with
  | nil => cases bound
  | @push arguments prior expression needs tail slot ih =>
    cases index with
    | zero =>
      simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel, Nat.sub_zero,
        List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, Valuation.push] using
        (show Nonempty _ from ⟨slot⟩)
    | succ index =>
      have small : index < arguments.length := by simp only [List.length_append, List.length_singleton] at bound; omega
      obtain ⟨selected⟩ := ih index small
      have position : (arguments ++ [expression]).length - 1 - (index + 1) =
          arguments.length - 1 - index := by simp only [List.length_append, List.length_singleton]; omega
      simpa only [position, List.getElem_append_left (by omega : arguments.length - 1 - index < arguments.length),
        Valuation.push] using (show Nonempty _ from ⟨selected⟩)

noncomputable def RichFamilyArgumentSlot.forNeed
    (slot : RichFamilyArgumentSlot root env registry target source locals σ available expression needs)
    (need : Need) (member : need ∈ needs) :
    RichFamilyArgumentQuery root env registry target source locals σ available expression need.profile :=
  { slot.argument with query := slot.argument.query.localDemand need (slot.bounded need member) (slot.covered need member) }

/-- The complete retained declaration seed is an index of the consumption.
The residual context, realization and rich frame are actual constructed
objects. Finite source requests retain their own original locations. -/
structure RichFamilyPlanConsumption
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType)
    (arguments : List VExpr) (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  anchors : List VExpr
  length : anchors.length = arguments.length
  headerSource : List VExpr
  context : ContextDerivation headerEnv U headerSource
  sourceEq : headerSource = (signature.domains.take arguments.length).reverse
  realization : Subst
  actual : Subst
  actualEq : ∀ i (bound : i < arguments.length), actual i = (arguments[arguments.length-1-i]' (by omega)).subst σ
  output : Atom rank
  footprint : Footprint
  plan : RichFamilyPlan env U registry target header name levels signature context realization anchors
    (.singleton output) footprint
  adapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom rank bound requested)
  valuation : Valuation
  closed : valuation.AtomClosed
  raw : Ctx.SubstEq env U target realization actual headerSource
  frame : HeaderBinderFrame header root root env registry target context (List.range anchors.length)
    realization actual valuation
  resources : footprint.Available valuation
  observed : RichFamilyArgumentSpine root env registry target source locals σ available arguments valuation

private theorem raiseAtom_twice {n k N : Nat} (hn : n ≤ k) (hk : k ≤ N) (a : Atom n) :
    raiseAtom N hk (raiseAtom k hn a) = raiseAtom N (Nat.le_trans hn hk) a := by
  have h := raiseProfile_trans hn hk (.singleton a)
  rw [raiseProfile_singleton, raiseProfile_singleton, raiseProfile_singleton] at h
  exact List.singleton_inj.mp (congrArg Profile.atoms h)

noncomputable def RichFamilyPlanConsumption.raiseTo
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available name levels signature arguments requested)
    (N : Nat) (bound : result.rank ≤ N) :
    RichFamilyPlanConsumption root header env registry target locals σ available name levels signature arguments requested := by
  refine { result with
    rank := N
    bound := Nat.le_trans result.bound bound
    output := raiseAtom N bound result.output
    plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
    adapter := ?_ }
  simpa only [raiseAtom_twice] using result.adapter.raise henv hscoped formed bound

/-- The actual `.family` leaf initializes the unchanged retained header. -/
noncomputable def RichFamilyPlanConsumption.bare
    (plan : RichFamilyPlan env U registry target header name levels signature .nil seed [] (.singleton atom) []) :
    RichFamilyPlanConsumption root header env registry target locals σ available name levels signature [] atom where
  rank := _
  bound := Nat.le_refl _
  anchors := []
  length := rfl
  headerSource := []
  context := .nil
  sourceEq := rfl
  realization := seed
  actual := .id
  actualEq := by intro i bound; cases bound
  output := atom
  footprint := []
  plan := plan
  adapter := by rw [raiseAtom_self]; exact .refl _
  valuation := fun _ => []
  closed := fun _ _ member => nomatch member
  raw := .nil
  frame := .captured .nil
  resources := fun _ _ member => nomatch member
  observed := .nil

/-- Consume an actual application. The declaration-domain certificate is
already a child of the retained plan; its guard and the incoming admission
construct the paired binder frame without an F/C/R supplier. -/
theorem RichFamilyPlanConsumption.appPreserving
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {key : Key n} {output : Atom n}
    (result : RichFamilyPlanConsumption root header env registry target locals σ available name levels signature arguments
      (n := n+1) (.fn key output))
    {argument : EndpointState sourceEnv U source a A}
    (location : Located root argument)
    (observation : RichObs sourceEnv env U registry target argument locals σ (input : Profile n) argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : GeneralNormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    {property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ}
    (raises : ∀ {expression assigned : VExpr} {node : EndpointState sourceEnv U source expression assigned}
      {n N : Nat} {profile : Profile n} {footprint : Footprint}
      (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
      (bound : n ≤ N), property query → property (query.raise bound))
    (priorQueries : result.observed.Queries property) (argumentQuery : property observation) :
    ∃ next : RichFamilyPlanConsumption root header env registry target locals σ available name levels signature
      (arguments ++ [a]) output, next.observed.Queries property := by
  rcases result with ⟨rank, bound, anchors, length, headerSource, context, sourceEq,
    realization, actual, actualEq, atom, footprint, plan, adapter, valuation, closed, raw, frame,
    planResources, observed⟩
  cases rank with
  | zero => omega
  | succ rank =>
    have hn : n ≤ rank := Nat.le_of_succ_le_succ bound
    obtain ⟨front⟩ := plan.front henv hscoped formed atom rfl
    cases front with
    | terminal saturated shape relevant captures terminalBound frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toGeneralAdapter henv hscoped formed
      exact (GeneralNormalAtomAdapter.family_not_fn terminalBound (frontAdapter.toGeneral.comp (adapter.comp expose))).elim
    | @binder r domainFoot bodyFoot outside requested domain level oldKey oldOutput support packed
        origin original domainLocation lineage domainCode guard body pack covered frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toGeneralAdapter henv hscoped formed
      have normalized := frontAdapter.toGeneral.comp (adapter.comp expose)
      obtain ⟨actualKey, actualOutput, equal, ⟨keys⟩, ⟨outputs⟩⟩ := normalized.fn_inv
      obtain ⟨rfl, rfl⟩ := AtomData.fn.inj equal
      have incoming := AdapterNormal.normalizeAdmission henv hscoped formed (Admitted.raise henv hn admitted)
      have seed := AdapterNormal.normalizeAdmission henv hscoped formed guard.anchor
      have pulled := unnormalize_admission henv hscoped formed (keys.pull henv hscoped formed seed incoming)
      have highInputs : GeneralNormalProfileAdapter env U registry target (raiseProfile rank hn input) oldKey.input :=
        (GeneralNormalProfileAdapter.raise henv hscoped formed hn inputs).comp keys.arguments
      let argumentResult : RichFamilyArgumentQuery root env registry target source locals σ available a oldKey.input := {
        assigned := A, node := argument, location := location
        query := {
          rank := rank, bound := Nat.le_refl _, raw := raiseProfile rank hn input,
          footprint := argumentFootprint, observation := observation.raise hn,
          adapter := by simpa only [raiseProfile_self] using highInputs,
          resources := resources, live := (raiseProfile_live_iff hn input).mpr live } }
      have domainResources : domainFoot.Available valuation :=
        fun i need member => planResources i need (List.mem_append_left _ member)
      have outsideResources : outside.Available valuation :=
        fun i need member => planResources i need (List.mem_append_right _ member)
      obtain ⟨rawArgument, _, oldSupport, _, _, _, anchorPair, _⟩ := pulled
      have semanticArgument := Related.convert henv guard.inputTyped guard.domains anchorPair
      let needs := bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons
      have bounded : ∀ need ∈ needs, need.rank ≤ rank :=
        fun need member => (pack.atomized_localNeeds need member).1
      have coveredNeeds : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade rank).atoms, atom ∈ oldKey.input.atoms :=
        fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
      have childRaw : Ctx.SubstEq env U target (realization.cons oldKey.anchor)
          (actual.cons (a.subst σ)) (domain :: headerSource) :=
        .cons raw (original.sound.defeq.mono headerBelow) (guard.path.cast rawArgument)
      let childFrame := HeaderBinderFrame.bind frame original domainLocation lineage domainCode domainResources
        guard.inputTyped semanticArgument needs bounded coveredNeeds
      refine ⟨{
        rank := rank, bound := hn, anchors := anchors ++ [oldKey.anchor],
        length := by simp only [List.length_append, List.length_singleton, length]
        headerSource := domain :: headerSource, context := .cons context original,
        sourceEq := ?_
        realization := realization.cons oldKey.anchor,
        actual := actual.cons (a.subst σ), actualEq := ?_
        output := oldOutput, footprint := bodyFoot, plan := body, adapter := outputs,
        valuation := valuation.push needs,
        closed := Valuation.push_atomized_closed closed _, raw := childRaw,
        frame := by simpa only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push] using childFrame,
        resources := pack.available_atomized_localNeeds outsideResources,
        observed := .push observed ⟨rank, oldKey.input, argumentResult, bounded, coveredNeeds⟩ }, ?_⟩
      · simpa only [List.length_append, List.length_singleton, ← length,
          signature.prefixContext_cons origin, sourceEq]
      · intro i hi
        cases i with
        | zero => simp only [Subst.cons, List.length_append, List.length_singleton, Nat.add_sub_cancel,
            Nat.sub_zero, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
        | succ i =>
          have small : i < arguments.length := by simp only [List.length_append, List.length_singleton] at hi; omega
          rw [show (actual.cons (a.subst σ)) (i+1) = actual i from rfl, actualEq i small]
          have position : (arguments ++ [a]).length - 1 - (i+1) = arguments.length - 1 - i := by
            simp only [List.length_append, List.length_singleton]; omega
          simp only [position, List.getElem_append_left (by omega : arguments.length - 1 - i < arguments.length)]

      · exact ⟨priorQueries, raises observation hn argumentQuery⟩

/-- Compatibility wrapper for consumption without an additional observer property. -/
theorem RichFamilyPlanConsumption.app
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {key : Key n} {output : Atom n}
    (result : RichFamilyPlanConsumption root header env registry target locals σ available name levels signature arguments
      (n := n+1) (.fn key output))
    {argument : EndpointState sourceEnv U source a A}
    (location : Located root argument)
    (observation : RichObs sourceEnv env U registry target argument locals σ (input : Profile n) argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : GeneralNormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Nonempty (RichFamilyPlanConsumption root header env registry target locals σ available name levels signature
      (arguments ++ [a]) output) := by
  obtain ⟨next, _⟩ := result.appPreserving henv hscoped headerBelow formed location observation
    resources live inputs admitted (property := fun _ => True)
    (fun _ _ _ => trivial) result.observed.queriesTrue trivial
  exact ⟨next⟩

/-- Replay a terminal's finite variable program on the SAME source argument.
The returned observation keeps the actual argument footprint; declaration
variable queries contribute an adapter, not a foreign query owner. -/
noncomputable def RichFamilyArgumentSlot.replayVariable
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {input : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (slot : RichFamilyArgumentSlot root env registry target source locals σ available expression needs)
    (value : Obs env U registry target captureLocals seed (.bvar index) (rawInput : Profile n) footprint)
    (adapter : NormalProfileAdapter env U registry target rawInput input)
    (resources : ∀ i need, (i, need) ∈ footprint → need ∈ needs) :
    RichFamilyArgumentQuery root env registry target source locals σ available expression input := by
  let trace : SortableVariableTrace env U registry target index rawInput footprint := .legacy value.variableTrace
  let N := max slot.argument.query.rank trace.height
  have ha : slot.argument.query.rank ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  have hs : slot.rank ≤ N := Nat.le_trans slot.argument.query.bound ha
  have hn : n ≤ N := Nat.le_trans trace.output_bound ht
  have leafBound : ∀ i need, (i, need) ∈ footprint → need.rank ≤ slot.rank :=
    fun i need member => slot.bounded need (resources i need member)
  have covered : List.Subset (footprint.atGrade slot.rank).atoms slot.input.atoms := by
    intro atom member
    obtain ⟨⟨i, need⟩, present, belongs⟩ := List.mem_flatMap.mp member
    exact slot.covered need (resources i need present) atom belongs
  have selected : GeneralNormalProfileAdapter env U registry target
      (raiseProfile N hs slot.input) (footprint.atGrade N) := by
    rw [Footprint.atGrade_raise hs leafBound]
    apply GeneralProfileAdapter.select
    intro atom member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨a, raiseProfile_subset hs covered a ha, rfl⟩
  let raised := RichGradedResult.raiseTo henv hscoped formed slot.argument.query N ha
  refine { slot.argument with query := {
    rank := N, bound := hn, raw := raised.raw, footprint := raised.footprint,
    observation := raised.observation,
    adapter := raised.adapter.comp (selected.comp ((trace.normalize henv hscoped formed N ht).comp
      ((adapter.raise henv hscoped formed hn).toGeneral))),
    resources := raised.resources, live := raised.live } }

/-- A family atom cannot be produced from a still-unconsumed binder. -/
theorem RichFamilyPlanConsumption.saturated
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available name levels signature arguments
      (n := n+1) (.family demand)) :
    arguments.length = signature.domains.length := by
  rcases result with ⟨rank, bound, anchors, length, headerSource, context, sourceEq,
    realization, actual, actualEq, atom, footprint, plan, adapter, valuation, closed, raw, frame,
    planResources, observed⟩
  obtain ⟨front⟩ := plan.front henv hscoped formed atom rfl
  cases front with
  | terminal saturated => exact length.symm.trans saturated
  | binder _ _ _ _ _ _ _ _ _ frontAdapter =>
    exact (GeneralNormalAtomAdapter.fn_not_family bound (frontAdapter.toGeneral.comp adapter)).elim

/-- A terminal capture retains the original frozen request, the actual
source argument query, and the raw path from its frozen anchor. -/
structure RichFamilySourceCapture
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) (expression : VExpr) (request : DataRequest (Profile n)) where
  index : Nat
  expressionEq : expression = .bvar index
  bound : index < arguments.length
  argument : RichFamilyArgumentQuery root env registry target source locals σ available
    (arguments[arguments.length-1-index]'(by omega)) request.input
  anchor : env.IsDefEq U target request.anchor
    ((arguments[arguments.length-1-index]'(by omega)).subst σ) request.domain

/-- Recover terminal source queries from the finite actual argument spine.
No source F, header normalization, or completed family relation is assumed. -/
theorem FamilyCaptures.richSourceCaptures
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (captures : FamilyCaptures env U registry target headerSource captureLocals seed expressions requests footprint)
    (raw : Ctx.SubstEq env U target seed actual headerSource)
    (sourceLength : headerSource.length = arguments.length)
    (actualEq : ∀ i (bound : i < arguments.length), actual i =
      (arguments[arguments.length-1-i]'(by omega)).subst σ)
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior)
    (resources : footprint.Available prior) :
    List.Forall₂ (fun expression request => Nonempty
      (RichFamilySourceCapture root env registry target locals σ available arguments expression request))
      expressions requests := by
  match captures with
  | .nil => exact .nil
  | .cons (index := index) lookup value adapter alignment anchor tail =>
    have bound : index < arguments.length := by simpa only [sourceLength] using lookup.lt
    obtain ⟨slot⟩ := spine.lookup index bound
    let query := slot.replayVariable henv hscoped formed value adapter (by
      intro i need member
      have same : i = index := value.variableTrace.indices member
      subst i
      exact resources index need (List.mem_append_left _ member))
    refine .cons ⟨⟨index, rfl, bound, query, ?_⟩⟩ (FamilyCaptures.richSourceCaptures henv hscoped formed tail raw sourceLength actualEq spine (by
      intro i need member; exact resources i need (List.mem_append_right _ member)))
    have pair := alignment.path.symm.cast (raw.lookup lookup)
    exact anchor.1.trans (by simpa only [actualEq index bound] using pair)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

/-- The terminal packet keeps the full retained seed descriptor and the
finite generalized adapter. It does not falsely identify descriptors after
code actions. Every source query is at an actual original argument node. -/
structure RichFamilyConsumedCaptures
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (consumed : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments requested) where
  rank : Nat
  level : VLevel
  relevant : Bool
  resultSort : signature.result = .sort level
  relevance : Relevant level relevant
  requests : List (DataRequest (Profile rank))
  bound : rank+1 ≤ consumed.rank
  adapter : GeneralNormalAtomAdapter env U registry target
    (raiseAtom consumed.rank bound (.family ⟨name, levels, relevant, requests⟩))
    (raiseAtom consumed.rank consumed.bound requested)
  footprint : Footprint
  captures : FamilyCaptures env U registry target consumed.headerSource
    (List.range consumed.anchors.length) consumed.realization
    (constantCaptureVariables consumed.anchors.length) requests footprint
  resources : footprint.Available consumed.valuation
  sources : List.Forall₂ (fun expression request => Nonempty
    (RichFamilySourceCapture root env registry target locals σ available arguments expression request))
    (constantCaptureVariables consumed.anchors.length) requests

/-- Saturated consumption exposes actual frozen captures and computes their
caller observations from the same retained argument spine. -/
theorem RichFamilyPlanConsumption.sourceCaptures
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments requested)
    (full : arguments.length = signature.domains.length) :
    Nonempty (RichFamilyConsumedCaptures result) := by
  rcases result with ⟨rank, bound, anchors, length, headerSource, context, sourceEq,
    realization, actual, actualEq, atom, footprint, plan, adapter, valuation, closed, raw, frame,
    planResources, observed⟩
  obtain ⟨front⟩ := plan.front henv hscoped formed atom rfl
  cases front with
  | terminal saturated shape relevant captures terminalBound frontAdapter =>
    have sourceLength : headerSource.length = arguments.length := by
      rw [sourceEq, full, List.take_length, List.length_reverse]
    have sources := FamilyCaptures.richSourceCaptures henv hscoped formed captures raw
      sourceLength actualEq observed planResources
    exact ⟨{
      rank := _, level := _, relevant := _, resultSort := shape, relevance := relevant,
      requests := _, bound := terminalBound, adapter := frontAdapter.toGeneral.comp adapter,
      footprint := _, captures := captures, resources := planResources, sources := sources }⟩
  | binder origin =>
    have small := (List.getElem?_eq_some_iff.mp origin).1
    have equal := length.trans full
    omega

/-- The requested family atom itself establishes saturation. -/
theorem RichFamilyPlanConsumption.familySourceCaptures
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n+1) (.family demand)) :
    Nonempty (RichFamilyConsumedCaptures result) :=
  result.sourceCaptures henv hscoped formed (result.saturated henv hscoped formed)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
