import Lean4Lean.Theory.Typing.AnchoredSortableDepthInputReplay
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private selectNormal_allDepth from Lean4Lean.Theory.Typing.AnchoredSortableDepthInputReplay
set_option backward.isDefEq.respectTransparency false
private theorem rebindSupply_allDepth
    {oldInput packed : Profile n} {newInput : Profile m}
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (replayDepth : ∀ current, replay.nativeDepth current = 0)
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside) :
    Nonempty (AllDepth.GradedSupply budget env U registry Γ locals σ Subst.id
      (Valuation.push (rowInputNeeds newInput) available) required) := by
  induction pack with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    have included : ∀ atom ∈ (raiseProfile n bound need.profile).atoms,
        atom ∈ oldInput.atoms := by
      intro atom member
      apply covered atom (List.mem_append_left _ ?_)
      simpa only [Need.atGrade, dif_pos bound] using member
    obtain ⟨tail⟩ := ih (fun atom hm => covered atom (List.mem_append_right _ hm))
      outsideAvailable outsideLive
    exact ⟨.cons {
      rank := n
      bound := bound
      raw := oldInput
      footprint := replayFootprint
      observation := .legacy replay
      adapter := selectNormal_allDepth included
      resources := replayAvailable
      live := oldLive
      bounded := by intro current; simp only [SortableObs.nativeDepth, replayDepth]; exact Nat.zero_le _ } tail⟩
  | external index need rest ih =>
    obtain ⟨tail⟩ := ih covered
      (fun i need hm => outsideAvailable i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => outsideLive i need (List.mem_cons_of_mem _ hm))
    have resources : Footprint.Available [(index + 1, need)]
        (Valuation.push (rowInputNeeds newInput) available) := by
      intro i wanted hm
      cases List.mem_singleton.mp hm
      exact outsideAvailable index need List.mem_cons_self
    exact ⟨.cons (AllDepth.GradedResult.exact (.legacy (.var locals σ (index + 1) need.profile)) resources
      (outsideLive index need List.mem_cons_self)
      (by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _)) tail⟩

theorem SortableCert.rebind_local_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (certificate : SortableCert env U registry Γ locals σ B relevant result required)
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (replayDepth : ∀ current, replay.nativeDepth current = 0)
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      ∃ output : SortableCert env U registry Γ locals σ B relevant result footprint,
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available ∧
      ∀ current, output.nativeDepth current ≤ certificate.nativeDepth current := by
  obtain ⟨supply⟩ := rebindSupply_allDepth (budget := certificate.nativeDepth) replay replayAvailable replayDepth oldLive pack covered outsideAvailable outsideLive
  obtain ⟨changed⟩ := AllDepth.SortableCert.substitute henv hscoped hΓ certificate (fun _ => Nat.le_refl _) Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed [⟨m, newInput⟩]) supply
  obtain ⟨changedFootprint, changedCertificate, changedResources, changedBound⟩ := changed
  obtain ⟨packed', outside', pack', covered', resources⟩ :=
    Footprint.pack_available changedResources
      (fun need hm => (rowInputNeeds_bounded newInput need hm).1)
      (fun need hm atom ha => (rowInputNeeds_bounded newInput need hm).2 atom ha)
  have restored : ∃ output : SortableCert env U registry Γ locals σ (B.subst Subst.id) relevant result changedFootprint,
      ∀ current, output.nativeDepth current ≤ certificate.nativeDepth current := ⟨changedCertificate, changedBound⟩
  rw [subst_id] at restored
  obtain ⟨output, outputBound⟩ := restored
  exact ⟨changedFootprint, outside', packed', output, pack', covered', resources, outputBound⟩

end Lean4Lean.AnchoredSource.Adapted
