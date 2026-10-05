import Lean4Lean.Theory.Typing.AnchoredSortableSubstitution
import Lean4Lean.Theory.Typing.AnchoredSortableScope

/-! Pi row input adaptation replays its actual finite local leaves through
identity substitution in the full sortable certificate syntax. External
resources and exact result demands survive, including proof-family rows. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private rebindSupply from Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind
set_option backward.isDefEq.respectTransparency false

theorem SortableCert.rebind_local
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (certificate : SortableCert env U registry Γ locals σ B relevant result required)
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      Nonempty (SortableCert env U registry Γ locals σ B relevant result footprint) ∧
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨supply⟩ := rebindSupply henv hscoped hΓ replay replayAvailable oldLive pack covered
    outsideAvailable outsideLive closed
  obtain ⟨changed⟩ := certificate.substitute henv hscoped hΓ Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed _) supply.toSortable
  have cert : SortableCert env U registry Γ locals σ B relevant result changed.footprint := by
    simpa only [subst_id] using changed.certificate
  obtain ⟨newPacked, externalFootprint, newPack, newCovered, externalAvailable⟩ :=
    Footprint.pack_available changed.resources
      (fun need member => (rowInputNeeds_bounded newInput need member).1)
      (fun need member => (rowInputNeeds_bounded newInput need member).2)
  exact ⟨changed.footprint, externalFootprint, newPacked, ⟨cert⟩, newPack, newCovered, externalAvailable⟩

end Lean4Lean.AnchoredSource.Adapted
