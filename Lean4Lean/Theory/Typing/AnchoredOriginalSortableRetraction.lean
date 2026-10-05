import Lean4Lean.Theory.Typing.AnchoredOriginalSortableQuery

/-! Sortable observations retract to their exact requested profile at either
relevance flag. In particular, a Prop-family request retains its complete
frozen parameter tuple rather than lowering to an empty rank-zero demand. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Obs.sortable_of_adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {raw requested : Profile n} {footprint : Footprint} {available : Valuation}
    (henv : env.Ordered)
    (observation : Obs env U registry target locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry target raw requested)
    (sortable : requested.HasType (.sort relevant))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ selectedFootprint,
      Nonempty (Obs env U registry target locals σ expression requested selectedFootprint) ∧
      selectedFootprint.Atomizes footprint ∧ selectedFootprint.Available available := by
  obtain ⟨normalizedFootprint, ⟨normalized⟩, normalization⟩ := observation.normalize henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable sortable
  have adapter' : ProfileAdapter env U registry target (AdapterNormal.profile raw) requested := canonical ▸ adapter
  obtain ⟨selectedFootprint, ⟨selected⟩, selection⟩ :=
    normalized.subprofile (adapter'.sortable_subset sortable)
  have selection := selection.trans normalization
  exact ⟨selectedFootprint, ⟨selected⟩, selection, selection.available_closed resources closed⟩

/-- Restore the exact incoming grade and every original family parameter
request after the fundamental theorem changes the intermediate grade. -/
theorem SortableQueryResult.exactObservation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right : VExpr} {requested : Profile n}
    (answer : SortableQueryResult env U registry target locals σ τ available left right requested)
    (henv : env.Ordered) (closed : available.AtomClosed)
    (sortable : requested.HasType (.sort relevant)) :
    ∃ footprint, Nonempty (Obs env U registry target locals τ right requested footprint) ∧
      footprint.Available available := by
  obtain ⟨footprint, ⟨observation⟩, _, resources⟩ := answer.result.observation.sortable_of_adapter
    henv answer.result.adapter (Profile.HasType.raise_sort answer.result.bound sortable)
    answer.result.resources closed
  exact ⟨footprint, ⟨observation.lower answer.result.bound⟩, resources⟩

theorem Obs.transferSortableExact
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right assigned : VExpr} {profile : Profile n} {footprint : Footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (observation : Obs env U registry target locals σ left profile footprint)
    (sortable : profile.HasType (.sort relevant))
    (resources : footprint.Available available)
    (transfer : GradedTransfer env U registry target locals σ τ available left right assigned) :
    ∃ nextFootprint, Nonempty (Obs env U registry target locals τ right profile nextFootprint) ∧
      nextFootprint.Available available ∧
      TypeRelated env U registry target (left.subst σ) (right.subst τ) profile := by
  obtain ⟨answer⟩ := observation.transferSortable henv hscoped formed sortable resources transfer
  obtain ⟨nextFootprint, next, nextResources⟩ := answer.exactObservation henv closed sortable
  exact ⟨nextFootprint, next, nextResources, answer.related⟩

end Lean4Lean.AnchoredSource.Adapted
