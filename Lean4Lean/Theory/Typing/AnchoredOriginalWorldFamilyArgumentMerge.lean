import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData

/-! Merge an actual frozen family request with a newly replayed parameter
request. Both requests use the same original node and caller resources.
The actual raised union retains its world annotations; selecting either
request changes only a finite adapter around that one observer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem RichGradedResult.raiseRequest_controlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) (bound : n ≤ N) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (query.raiseRequest henv hscoped formed bound).observation)) :=
  ready.raise (Nat.le_max_left _ _)

private theorem RichGradedResult.union_controlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : RichGradedResult sourceEnv env U registry target node locals σ available (p : Profile n))
    (right : RichGradedResult sourceEnv env U registry target node locals σ available (q : Profile n))
    (leftReady : ControlledStoredQuery controls frontier (.observation left.observation))
    (rightReady : ControlledStoredQuery controls frontier (.observation right.observation)) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (left.union henv hscoped formed right).observation)) := by
  obtain ⟨a⟩ := leftReady.raise (Nat.le_max_left left.rank right.rank)
  obtain ⟨b⟩ := rightReady.raise (Nat.le_max_right left.rank right.rank)
  refine ⟨⟨.union a.annotation b.annotation, ?_, ?_⟩⟩
  · intro control active
    simpa only [StoredOriginalQuery.headDepth, RichGradedResult.union,
      RichGradedResult.raiseTo, RichObs.headDepth] using
      (Nat.max_le.mpr ⟨a.within control active, b.within control active⟩)
  · exact a.sponsored.merge b.sponsored

/-- This packet contains one observer for both actual requests. Its two
retractions below retain that observer, rather than choosing fresh queries. -/
structure WorldFamilyMergedArgument
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (node : EndpointState sourceEnv U source expression assigned)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (old : Profile n) (extra : Profile m) where
  query : RichGradedResult sourceEnv env U registry target node locals σ available
    ((raiseProfile (max n m) (Nat.le_max_left _ _) old).union
      (raiseProfile (max n m) (Nat.le_max_right _ _) extra))
  controlled : ControlledStoredQuery controls frontier (.observation query.observation)

section Retractions
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {node : EndpointState sourceEnv U source expression assigned}
  {old : Profile n} {extra : Profile m}

noncomputable def WorldFamilyMergedArgument.oldQuery
    (merged : WorldFamilyMergedArgument controls frontier node registry target locals σ available old extra) :
    RichGradedResult sourceEnv env U registry target node locals σ available old :=
  merged.query.localDemand ⟨_, old⟩ (Nat.le_max_left _ _) (by
    intro atom member
    have present : atom ∈ (raiseProfile (max n m) (Nat.le_max_left _ _) old).atoms := by
      simpa only [Need.atGrade, dif_pos (Nat.le_max_left _ _)] using member
    exact List.mem_append_left _ present)

noncomputable def WorldFamilyMergedArgument.extraQuery
    (merged : WorldFamilyMergedArgument controls frontier node registry target locals σ available old extra) :
    RichGradedResult sourceEnv env U registry target node locals σ available extra :=
  merged.query.localDemand ⟨_, extra⟩ (Nat.le_max_right _ _) (by
    intro atom member
    have present : atom ∈ (raiseProfile (max n m) (Nat.le_max_right _ _) extra).atoms := by
      simpa only [Need.atGrade, dif_pos (Nat.le_max_right _ _)] using member
    exact List.mem_append_right _ present)

theorem WorldFamilyMergedArgument.oldQuery_controlled
    (merged : WorldFamilyMergedArgument controls frontier node registry target locals σ available old extra) :
    Nonempty (ControlledStoredQuery controls frontier (.observation merged.oldQuery.observation)) :=
  ⟨merged.controlled⟩

theorem WorldFamilyMergedArgument.extraQuery_controlled
    (merged : WorldFamilyMergedArgument controls frontier node registry target locals σ available old extra) :
    Nonempty (ControlledStoredQuery controls frontier (.observation merged.extraQuery.observation)) :=
  ⟨merged.controlled⟩

end Retractions

/-- An actual extra replay is joined with the frozen request at the SAME
original argument. The frontier is unchanged; duplicate retained uses do
not duplicate the measured sponsors. -/
theorem WorldRichFamilySourceRequest.mergeAdditional
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (request : WorldRichFamilySourceRequest controls frontier root registry target locals σ available
      expression (input : DataRequest (Profile n)))
    (extra : RichGradedResult sourceEnv env U registry target request.argument.node locals σ available (wanted : Profile m))
    (extraReady : ControlledStoredQuery controls frontier (.observation extra.observation)) :
    ∃ merged : WorldFamilyMergedArgument controls frontier request.argument.node registry target locals σ available input.input wanted,
      (∀ policy, merged.query.observation.headDepth policy =
        max (request.argument.query.observation.headDepth policy) (extra.observation.headDepth policy)) ∧
      merged.query.footprint = request.argument.query.footprint ++ extra.footprint := by
  let left := request.argument.query.raiseRequest henv hscoped formed (Nat.le_max_left n m)
  let right := extra.raiseRequest henv hscoped formed (Nat.le_max_right n m)
  obtain ⟨leftReady⟩ := request.argument.query.raiseRequest_controlled henv hscoped formed
    request.controlled (Nat.le_max_left n m)
  obtain ⟨rightReady⟩ := extra.raiseRequest_controlled henv hscoped formed extraReady (Nat.le_max_right n m)
  obtain ⟨ready⟩ := left.union_controlled henv hscoped formed right leftReady rightReady
  refine ⟨⟨left.union henv hscoped formed right, ready⟩, ?_, rfl⟩
  intro policy
  simp only [RichGradedResult.union, RichGradedResult.raiseTo, RichObs.headDepth,
    RichObs.headDepth_raise, left, right, RichGradedResult.raiseRequest]

/-- The packed key covers the merged RAW observer, not necessarily the
advertised atoms after a general code action. These finite programs are
the checked connection from that actual key to both requested profiles. -/
structure FamilyPackedRequestAdapters
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (input : Profile N) (old : Profile n) (extra : Profile m) where
  oldBound : n ≤ N
  extraBound : m ≤ N
  oldAdapter : GeneralNormalProfileAdapter env U registry target input (raiseProfile N oldBound old)
  extraAdapter : GeneralNormalProfileAdapter env U registry target input (raiseProfile N extraBound extra)

/-- Consume the actual raw-input coverage returned by the extra-argument
Pi request. No literal containment of either advertised request is used. -/
noncomputable def WorldFamilyMergedArgument.packedAdapters
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {argument : EndpointState sourceEnv U source a A}
    {hu : u.WF U} {hv : v.WF U}
    {old : Profile n} {extra : Profile m}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (merged : WorldFamilyMergedArgument controls frontier argument registry target locals σ available old extra)
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant output)
    (rawBound : merged.query.rank ≤ packed.request.rank)
    (covered : ∀ atom ∈ (raiseProfile packed.request.rank rawBound merged.query.raw).atoms,
      atom ∈ packed.request.key.input.atoms) :
    FamilyPackedRequestAdapters env U registry target packed.request.key.input old extra := by
  have select : GeneralNormalProfileAdapter env U registry target packed.request.key.input
      (raiseProfile packed.request.rank rawBound merged.query.raw) :=
    GeneralProfileAdapter.select (by
      intro atom member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, covered original present, rfl⟩)
  refine ⟨Nat.le_trans merged.oldQuery.bound rawBound,
    Nat.le_trans merged.extraQuery.bound rawBound, ?_, ?_⟩
  · have lifted := merged.oldQuery.adapter.raise henv hscoped formed rawBound
    have composed := select.comp lifted
    simpa only [WorldFamilyMergedArgument.oldQuery, RichGradedResult.localDemand,
      RichGradedResult.restrict, raiseProfile_trans] using composed
  · have lifted := merged.extraQuery.adapter.raise henv hscoped formed rawBound
    have composed := select.comp lifted
    simpa only [WorldFamilyMergedArgument.extraQuery, RichGradedResult.localDemand,
      RichGradedResult.restrict, raiseProfile_trans] using composed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
