import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionGradedRecipe
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionEmptyField
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceStep

/-! A constructor's finite field requests can mix observed and empty inputs.
Empty inputs retain their exact anchors, supports and original projection
origins. A meaningful field supplies the record witness; finite assembly
preserves the original ordering, including repeated requests. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure EmptyFieldRecipe (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (σ : Subst) (major type : VExpr)
    (name : Name) (index : Nat) (request : DataRequest (Profile n)) where
  info : VProjectionInfo
  origin : RankedData.ProjectionOrigin env U target info name index
    (major.subst σ) (type.subst σ) request.domain
  bounded : index < info.numFields
  seed : RankedData.RequestAdmission env U (relations env U registry n) target request
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  empty : request.input = .empty

/-- Raw substitution transports an empty field without asking the original
major theorem for a nonexistent value atom. Its frozen domain is unchanged. -/
theorem EmptyFieldRecipe.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {σ τ : Subst}
    {left right type : VExpr} {request : DataRequest (Profile n)}
    (query : EmptyFieldRecipe env U registry target σ left type name index request)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    Nonempty (EmptyFieldRecipe env U registry target τ right type name index request) := by
  have raw := (original.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
  have seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj name index (left.subst σ)) (.proj name index (left.subst σ)) := query.seed
  have admission := RankedData.RequestAdmission.emptyFieldPair query.origin raw seed query.empty
  obtain ⟨anchor, pair, typed, supportFormed, code, first, last⟩ := admission
  obtain ⟨level, formation⟩ := (original.forget.defeq.mono below).isType henv substitutions.wf
  have typeEq := formation.substDF henv substitutions.wf formed substitutions
  refine ⟨{
    info := query.info
    origin := (query.origin.replaceMajor raw).convertAssignedType (.single typeEq)
    bounded := query.bounded
    empty := query.empty
    seed := ⟨anchor.trans pair, pair.hasType.2, typed, supportFormed, code, ?_, ?_⟩ }⟩
  · rw [query.empty]
    cases n <;> intro atom member <;> cases member
  · rw [query.empty]
    cases n <;> intro atom member <;> cases member

/-- The empty branch is built from the retained projection rule, not an
assumed field packet. Only the final declaration-domain alignment is added. -/
theorem EmptyFieldRecipe.ofOriginalProjection
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major assigned type : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    {info : VProjectionInfo} {request : DataRequest (Profile n)}
    (head : ProjectionHead node) (common : EndpointRef sourceEnv U source major type)
    (registered : sourceEnv.projections name info) (bound : index < info.numFields)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (frame : OriginalQueryFrame env registry target initial locals σ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (comparison : DisplayCoherence env U registry
      (originalDisplay initial common) (originalDisplay initial (.right head.major)))
    (alignment : DomainChain env U registry target request.input (assigned.subst σ) request.domain)
    (seed : RankedData.RequestAdmission env U (relations env U registry n) target request
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (empty : request.input = .empty) :
    Nonempty (EmptyFieldRecipe env U registry target σ major type name index request) := by
  obtain ⟨origin⟩ := head.originAt common henv below initial frame closed formed comparison
  have sameInfo := henv.projections_unique (below.projections registered)
    (below.projections head.registered)
  exact ⟨⟨head.info, { origin with fieldPath := origin.fieldPath.trans alignment.path },
    sameInfo ▸ bound, seed, empty⟩⟩

inductive MixedRecordQuery (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (major type : VExpr) (name : Name) :
    List (Nat × DataRequest (Profile n)) → Footprint → Type where
  | nil : MixedRecordQuery env U registry target locals σ major type name [] []
  | field (recipe : GradedFieldRecipe env U registry target locals σ major name index request)
      (tail : MixedRecordQuery env U registry target locals σ major type name requests footprint) :
      MixedRecordQuery env U registry target locals σ major type name
        ((index, request) :: requests) (recipe.raw.footprint ++ footprint)
  | empty (recipe : EmptyFieldRecipe env U registry target σ major type name index request)
      (tail : MixedRecordQuery env U registry target locals σ major type name requests footprint) :
      MixedRecordQuery env U registry target locals σ major type name
        ((index, request) :: requests) footprint

private theorem MixedRecordQuery.seedWitness
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {requests : List (Nat × DataRequest (Profile n))}
    {left right type : VExpr}
    (query : MixedRecordQuery env U registry target locals σ left type name requests footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available)
    (meaningful : ∃ entry ∈ requests, Profile.Nonempty entry.2.input) :
    ∃ entry ∈ requests, Nonempty (RankedData.FieldRecordWitness env U registry
      (relations env U registry n) target (left.subst σ) (right.subst τ) (type.subst σ)
      name [entry]) := by
  induction query with
  | nil => obtain ⟨entry, member, _⟩ := meaningful; cases member
  | field recipe tail ih =>
    obtain ⟨next, nextResources, witness⟩ := recipe.transfer original henv hscoped closed formed
      context tails substitutions fundamental
      (fun i need member => resources i need (List.mem_append_left _ member))
    exact ⟨_, List.mem_cons_self, witness⟩
  | @empty grade index request requests footprint recipe tail ih =>
    have smaller : ∃ entry ∈ requests, Profile.Nonempty entry.2.input := by
      obtain ⟨entry, member, nonempty⟩ := meaningful
      rcases List.mem_cons.mp member with rfl | member
      · exact False.elim (nonempty recipe.empty)
      · exact ⟨entry, member, nonempty⟩
    obtain ⟨entry, member, witness⟩ := ih resources smaller
    exact ⟨entry, List.mem_cons_of_mem _ member, witness⟩

private theorem MixedRecordQuery.transferAppend
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {requests : List (Nat × DataRequest (Profile n))}
    {left right type : VExpr}
    (query : MixedRecordQuery env U registry target locals σ left type name requests footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available)
    (accumulator : RankedData.FieldRecordWitness env U registry (relations env U registry n)
      target (left.subst σ) (right.subst τ) (type.subst σ) name before) :
    ∃ nextFootprint,
      Nonempty (MixedRecordQuery env U registry target locals τ right type name requests nextFootprint) ∧
      nextFootprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name (before ++ requests)) := by
  induction query with
  | nil => exact ⟨[], ⟨.nil⟩, (fun _ _ member => nomatch member), by simpa using ⟨accumulator⟩⟩
  | field recipe tail ih =>
    obtain ⟨next, nextResources, ⟨witness⟩⟩ := recipe.transfer original henv hscoped closed formed
      context tails substitutions fundamental
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨joined⟩ := accumulator.append henv
      ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩ witness
    obtain ⟨nextFootprint, ⟨nextTail⟩, tailResources, joined⟩ :=
      ih (fun i need member => resources i need (List.mem_append_right _ member)) joined
    exact ⟨next.raw.footprint ++ nextFootprint, ⟨.field next nextTail⟩,
      (fun i need member => (List.mem_append.mp member).elim
        (nextResources i need) (tailResources i need)), by simpa only [List.append_assoc,
          List.cons_append, List.nil_append] using joined⟩
  | empty recipe tail ih =>
    have raw := (original.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
    obtain ⟨next⟩ := recipe.transfer original henv below formed substitutions
    obtain ⟨joined⟩ := accumulator.appendEmpty henv recipe.origin recipe.bounded raw recipe.seed recipe.empty
    obtain ⟨nextFootprint, ⟨nextTail⟩, tailResources, joined⟩ := ih resources joined
    exact ⟨nextFootprint, ⟨.empty next nextTail⟩, tailResources,
      by simpa only [List.append_assoc, List.cons_append, List.nil_append] using joined⟩

/-- Complete finite field assembly. Empty fields may occur anywhere; the
final selection restores the literal original order and multiplicities.
Wholly empty records are deliberately not admitted by this value rule. -/
theorem MixedRecordQuery.transfer
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {requests : List (Nat × DataRequest (Profile n))}
    {left right type : VExpr}
    (query : MixedRecordQuery env U registry target locals σ left type name requests footprint)
    (original : Derivation sourceEnv U source left right type)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fundamental : DerivationFundamental env registry context original)
    (resources : footprint.Available available)
    (meaningful : ∃ entry ∈ requests, Profile.Nonempty entry.2.input) :
    ∃ nextFootprint,
      Nonempty (MixedRecordQuery env U registry target locals τ right type name requests nextFootprint) ∧
      nextFootprint.Available available ∧
      Nonempty (RankedData.FieldRecordWitness env U registry (relations env U registry n)
        target (left.subst σ) (right.subst τ) (type.subst σ) name requests) := by
  obtain ⟨entry, member, ⟨seed⟩⟩ := query.seedWitness original henv hscoped closed formed
    context tails substitutions fundamental resources meaningful
  obtain ⟨nextFootprint, next, nextResources, ⟨joined⟩⟩ := query.transferAppend original
    henv hscoped below closed formed context tails substitutions fundamental resources seed
  exact ⟨nextFootprint, next, nextResources,
    ⟨joined.select requests (fun _ member => List.mem_append_right _ member) meaningful⟩⟩

/-- An actual projected argument of the retained eta constructor premise
produces either kind of field query. The empty branch discharges its original
major comparison from the strict eta budget; it needs no semantic atom. -/
theorem ProjectionSeededFrame.etaFieldQuery
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {info : VProjectionInfo}
    {parameters : List VExpr} {levels : List VLevel} {expression : VExpr}
    (registered : sourceEnv.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation sourceEnv U source expression expression (mkApps (.const name levels) parameters))
    (constructor : Derivation sourceEnv U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (sourceFrame : OriginalQueryFrame env registry target initial locals σ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (comparisons : CoherenceBelow env U registry (schedule .fundamental (Closure.close
      (Derivation.structEta registered parameterCount noIndices major constructor).origin initial.closures).cost))
    {result : Profile n}
    (frame : ProjectionSeededFrame env registry target
      (etaProjectionArgument constructor index bound).node locals σ available B result)
    (request : DataRequest (Profile k)) (gradeBound : k ≤ frame.collected.rank)
    (adapter : NormalProfileAdapter env U registry target frame.input
      (raiseProfile frame.collected.rank gradeBound request.input))
    (alignment : DomainChain env U registry target request.input
      ((etaProjectionArgument constructor index bound).type.subst σ) request.domain)
    (seed : RankedData.RequestAdmission env U (relations env U registry k)
      target request ((VExpr.proj name index expression).subst σ)
        ((VExpr.proj name index expression).subst σ)) :
    ∃ footprint, Nonempty (MixedRecordQuery env U registry target locals σ expression
      (mkApps (.const name levels) parameters) name [(index, request)] footprint) ∧
      footprint.Available available := by
  classical
  by_cases meaningful : request.input.Nonempty
  · obtain ⟨recipe, resources⟩ := frame.gradedRecipe henv hscoped request gradeBound adapter alignment seed meaningful
    exact ⟨recipe.raw.footprint ++ [], ⟨.field recipe .nil⟩, by simpa using resources⟩
  · have empty : request.input = .empty := Classical.not_not.mp meaningful
    have comparison := comparisons
      (originalDisplay initial (.left major))
      (originalDisplay initial (.right (projectionHead (etaProjectionArgument constructor index bound).node).major))
      below below (etaProjectionOrigin_schedule registered parameterCount noIndices major constructor
        index bound initial)
    obtain ⟨recipe⟩ := EmptyFieldRecipe.ofOriginalProjection
      (projectionHead (etaProjectionArgument constructor index bound).node) (.left major)
      registered bound henv below initial sourceFrame closed formed comparison alignment seed empty
    exact ⟨[], ⟨.empty recipe .nil⟩, fun _ _ member => nomatch member⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
