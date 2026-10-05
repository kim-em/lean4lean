import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank

/-! Exact finite variable demands, attached only to actual original nodes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- The exact finite result of a variable-demand recursion. The raw need and
adapter come from the same selected reply, including when its grade grows. -/
structure WorldVariableDemand (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (available : Valuation) (index : Nat) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  adapter : GeneralNormalProfileAdapter env U registry target raw (raiseProfile rank bound requested)
  member : Need.mk rank raw ∈ available index
  live : Profile.Live env U registry target raw

noncomputable def WorldVariableDemand.ofQuery
    (query : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (footprint : query.footprint = [(index, Need.mk query.rank query.raw)]) :
    WorldVariableDemand env U registry target available index requested := {
  rank := query.rank, bound := query.bound, raw := query.raw, adapter := query.adapter, live := query.live
  member := query.resources index _ (by rw [footprint]; exact List.mem_singleton_self _) }

noncomputable def WorldVariableDemand.availableMono
    (demand : WorldVariableDemand env U registry target available index requested)
    (included : ∀ i need, need ∈ available i → need ∈ next i) :
    WorldVariableDemand env U registry target next index requested :=
  { demand with member := included index _ demand.member }

noncomputable def WorldVariableDemand.push
    (demand : WorldVariableDemand env U registry target available index requested) (needs : List Need) :
    WorldVariableDemand env U registry target (available.push needs) (index + 1) requested :=
  { demand with member := demand.member }

/-- Attach the finite demand only to the actual destination original node.
No variable derivation is manufactured in a shortened source context. -/
noncomputable def WorldVariableDemand.atNode
    (demand : WorldVariableDemand env U registry target available index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned) (locals : List Nat) (σ : Subst) :
    RichGradedResult sourceEnv env U registry target node locals σ available requested := {
  rank := demand.rank, bound := demand.bound, raw := demand.raw
  footprint := [(index, Need.mk demand.rank demand.raw)]
  observation := .legacy (.legacy (.var locals σ index demand.raw))
  adapter := demand.adapter, live := demand.live
  resources := by intro i need member; cases List.mem_singleton.mp member; exact demand.member }

noncomputable def WorldVariableDemand.atNode_controlled
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (demand : WorldVariableDemand env U registry target available index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned) (locals : List Nat) (σ : Subst) :
    ControlledStoredQuery controls frontier (.observation (demand.atNode node locals σ).observation) := {
  annotation := .var
  within := by
    intro control active
    simp only [WorldVariableDemand.atNode, StoredOriginalQuery.headDepth, RichObs.headDepth, SortableObs.headDepth]
    rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
    exact Nat.zero_le _
  sponsored := by intro child member; cases member }

private theorem realizeVariableTail
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (replayable : generated.Replayable) (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier) :
    ∃ realization : OriginalCaptureRealization graph env registry target locals left right available,
    ∃ actual : WorldGenerated strata P base caps left right graph realization.frame.raw controls,
      actual.Replayable ∧ Nonempty (actual.Controlled frontier) ∧
      actual.UsesControlPrefix controls.cutoff controls.fuel ∧ Nonempty (actual.Hereditary frontier) ∧
      actual.worlds = generated.worlds ∧
      (∀ ordered, realization.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered) := by
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, replayable, ⟨ready⟩, compatible, ⟨hereditary⟩, rfl, fun _ => rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
