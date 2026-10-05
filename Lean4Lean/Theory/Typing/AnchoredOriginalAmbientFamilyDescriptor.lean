import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanResult
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureObservation

/-! A native family terminal consumes the actual active requests in its
selected original frame. Each frozen request and its admission is computed
from that frame's lookup. No unqueried capture is assigned a typing witness,
and no completed family relation is supplied to the constructor. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The same actual lookup produces both a terminal observer and its frozen
request. Raising the request leaves the actual source footprint unchanged. -/
theorem OriginalRichFrame.familyCapture
    {context : ContextDerivation headerEnv U source}
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (lookup : Lookup source index A) (need : Need)
    (present : need ∈ available index) (N : Nat) (bounded : need.rank ≤ N) :
    ∃ request : DataRequest (Profile N),
      request.input = need.atGrade N ∧ request.anchor = σ index ∧
      ∃ footprint, ∃ query : Obs env U registry target locals σ (.bvar index) request.input footprint,
        footprint.Available available ∧
        Nonempty (DomainChain env U registry target request.input request.domain (A.subst σ)) ∧
        RankedData.RequestAdmission env U (relations env U registry N) target request (σ index) (σ index) := by
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed present lookup
  have raw := (substitutions.lookup lookup).hasType.1
  have semantic : ∃ support : Profile need.rank,
      need.profile.HasType support ∧ support.HasType (.sort true) ∧
      TypeRelated env U registry target (A.subst σ) (A.subst σ) support ∧
      Related env U registry target (σ index) (σ index) (A.subst σ) need.profile support := by
    by_cases empty : need.profile = .empty
    · refine ⟨.empty, ?_, Profile.HasType.empty (Profile.WF.sort true), ?_, ?_⟩
      · rw [empty]; exact Profile.HasType.empty Profile.WF.empty
      · exact TypeRelated.of_singletons (fun _ member => nomatch member)
      · rw [empty]; exact Related.of_singletons (fun _ member => nomatch member)
    · exact ⟨entry.support, entry.typed, entry.certificate.formed,
        entry.related.typeCode henv hscoped formed empty, entry.related.left_diagonal⟩
  obtain ⟨support, typed, sorted, code, related⟩ := semantic
  let request : DataRequest (Profile need.rank) := ⟨⟨A.subst σ, σ index, need.profile⟩, support⟩
  have admission : RankedData.RequestAdmission env U (relations env U registry need.rank)
      target request (σ index) (σ index) := ⟨raw, raw, typed, sorted, code, related, related⟩
  let query := (Obs.var (env := env) (U := U) (registry := registry) (target := target)
    locals σ index need.profile).raise bounded
  refine ⟨raiseDataRequest N bounded request, ?_, rfl, [(index, need)], query, ?_, ⟨.refl _⟩,
    RankedData.RequestAdmission.raiseFamily henv bounded admission⟩
  · simp only [raiseDataRequest, raiseKey, request, Need.atGrade, dif_pos bounded]
  · intro slot required member
    cases List.mem_singleton.mp member
    exact present

/-- A finite demand list is traversed at one selected frame. The returned
keys retain the position and exact raised profile of every actual request. -/
theorem OriginalRichFrame.familyCaptures
    {context : ContextDerivation headerEnv U source}
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (demands : List (Nat × Need)) (N : Nat)
    (valid : ∀ demand ∈ demands, demand.1 < source.length)
    (present : ∀ demand ∈ demands, demand.2 ∈ available demand.1)
    (bounded : ∀ demand ∈ demands, demand.2.rank ≤ N) :
    ∃ keys : List (DataRequest (Profile N)), ∃ footprint,
      ∃ captures : FamilyCaptures env U registry target source locals σ
        (demands.map (fun demand => VExpr.bvar demand.1)) keys footprint,
      footprint.Available available ∧
      List.Forall₂ (fun demand request => request.input = demand.2.atGrade N ∧
        request.anchor = σ demand.1) demands keys := by
  induction demands with
  | nil => exact ⟨[], [], .nil, ⟨(fun _ _ member => nomatch member), .nil⟩⟩
  | cons demand demands ih =>
    obtain ⟨A, lookup⟩ := Lookup.ofLt (valid demand List.mem_cons_self)
    obtain ⟨request, inputEq, anchorEq, footprint, query, resources, ⟨alignment⟩, admission⟩ :=
      frame.familyCapture henv hscoped formed substitutions lookup demand.2
        (present demand List.mem_cons_self) N (bounded demand List.mem_cons_self)
    obtain ⟨keys, tailFootprint, tail, tailResources, selected⟩ := ih
      (fun item member => valid item (List.mem_cons_of_mem _ member))
      (fun item member => present item (List.mem_cons_of_mem _ member))
      (fun item member => bounded item (List.mem_cons_of_mem _ member))
    exact ⟨request :: keys, footprint ++ tailFootprint,
      .cons lookup query (.refl _) alignment admission tail,
      fun index need member => (List.mem_append.mp member).elim (resources index need) (tailResources index need),
      .cons ⟨inputEq, anchorEq⟩ selected⟩

/-- At saturation the concrete active requests become a real native family
plan terminal, with its actual original result node and computed support.
The demand positions must be the declaration variables in telescope order;
only resource membership, never a semantic family answer, is required. -/
theorem RichFamilyPlanResult.terminalFromFrame
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation headerEnv U source}
    {node : EndpointState headerEnv U source signature.result assigned}
    (frame : OriginalRichFrame headerEnv env U registry target context
      (List.range arguments.length) σ τ available)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (saturated : arguments.length = signature.domains.length)
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (demands : List (Nat × Need)) (N : Nat)
    (positions : demands.map (fun demand => VExpr.bvar demand.1) = constantCaptureVariables arguments.length)
    (valid : ∀ demand ∈ demands, demand.1 < source.length)
    (present : ∀ demand ∈ demands, demand.2 ∈ available demand.1)
    (bounded : ∀ demand ∈ demands, demand.2.rank ≤ N) :
    ∃ keys : List (DataRequest (Profile N)),
      Nonempty (RichFamilyPlanResult env U registry target header name levels signature context node σ arguments available
        (n := N+1) (.family ⟨name, levels, relevant, keys⟩)) ∧
      List.Forall₂ (fun demand request => request.input = demand.2.atGrade N ∧
        request.anchor = σ demand.1) demands keys := by
  obtain ⟨keys, footprint, captures, resources, selected⟩ := frame.familyCaptures
    henv hscoped formed substitutions demands N valid present bounded
  rw [positions] at captures
  exact ⟨keys, ⟨RichFamilyPlanResult.terminal saturated resultSort relevance captures resources⟩, selected⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
