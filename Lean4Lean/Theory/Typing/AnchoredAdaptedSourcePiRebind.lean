import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope

/-! Finite identity substitution replays original Pi-row local demands at a
new input. External demands retain their actual existing Fits evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def rowInputNeeds (input : Profile n) : List Need :=
  [⟨n, input⟩] ++ ([⟨n, input⟩] : List Need).flatMap Need.singletons

theorem rowInputNeeds_bounded (input : Profile n) :
    ∀ need ∈ rowInputNeeds input, need.rank ≤ n ∧
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms := by
  intro need member
  rcases List.mem_append.mp member with whole | singleton
  · cases List.mem_singleton.mp whole
    exact ⟨Nat.le_refl n, by simp [Need.atGrade]⟩
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at singleton
    obtain ⟨atom, atomMember, equality⟩ := List.mem_map.mp singleton
    cases equality
    refine ⟨Nat.le_refl n, ?_⟩
    intro other belongs
    have equal : other = atom := by
      simpa [Need.atGrade, Profile.atoms, Profile.singleton, Profile.mk] using belongs
    exact equal ▸ atomMember

def variableProfileView (view : ProfileView env U registry Γ input output)
    (locals : List Nat) (σ : Subst) :
    Obs env U registry Γ locals σ (.bvar 0) output
      (input.map fun atom => (0, ⟨_, Profile.singleton atom⟩)) := by
  match input, output, view with
  | _, _, .nil => exact .empty
  | _, _, .cons head tail =>
    exact .union (.view (.var locals σ 0 _) head) (variableProfileView tail locals σ)
termination_by sizeOf view

theorem variableProfileView_available (input : Profile n) (available : Valuation) :
    Footprint.Available (input.map fun atom => (0, ⟨n, Profile.singleton atom⟩))
      (Valuation.push (rowInputNeeds input) available) := by
  intro index need member
  obtain ⟨atom, atomMember, equality⟩ := List.mem_map.mp member
  cases equality
  apply List.mem_append_right
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩

private theorem rebindSupply
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    Nonempty (GradedSupply env U registry Γ locals σ Subst.id
      (Valuation.push (rowInputNeeds newInput) available) required) := by
  have localClosed := Valuation.push_atomized_closed closed [⟨m, newInput⟩]
  induction pack with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    have inclusion : List.Subset (raiseProfile n bound need.profile) oldInput := by
      intro atom member
      apply covered atom (List.mem_append_left _ ?_)
      simpa only [Need.atGrade, dif_pos bound, Profile.atoms] using member
    obtain ⟨footprint, ⟨selected⟩, selection⟩ := replay.subprofile inclusion
    have observation := selected.lower bound
    have live : Profile.Live env U registry Γ need.profile :=
      (raiseProfile_live_iff bound need.profile).mp (oldLive.subset inclusion)
    have resources := selection.available_closed replayAvailable localClosed
    obtain ⟨tail⟩ := ih (fun atom member => covered atom (List.mem_append_right _ member))
      outsideAvailable outsideLive
    exact ⟨.cons (GradedResult.exact observation resources live) tail⟩
  | external index need rest ih =>
    obtain ⟨tail⟩ := ih covered
      (fun i need hm => outsideAvailable i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => outsideLive i need (List.mem_cons_of_mem _ hm))
    have resources : Footprint.Available [(index + 1, need)]
        (Valuation.push (rowInputNeeds newInput) available) := by
      intro i wanted hm
      cases List.mem_singleton.mp hm
      exact outsideAvailable index need List.mem_cons_self
    exact ⟨.cons (GradedResult.exact (.var locals σ (index + 1) need.profile) resources
      (outsideLive index need List.mem_cons_self)) tail⟩

/-- The source expression, result code profile, and external valuation stay
fixed. Only the actual local variable observations are replayed. -/
theorem CodeCert.rebind_local
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (certificate : CodeCert env U registry Γ locals σ B result required)
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      Nonempty (CodeCert env U registry Γ locals σ B result footprint) ∧
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨supply⟩ := rebindSupply henv hscoped hΓ replay replayAvailable oldLive pack covered
    outsideAvailable outsideLive closed
  obtain ⟨changed⟩ := certificate.substitute henv hscoped hΓ Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed _) supply
  have cert : CodeCert env U registry Γ locals σ B result changed.footprint := by
    simpa only [subst_id] using changed.certificate
  obtain ⟨newPacked, externalFootprint, newPack, newCovered, externalAvailable⟩ :=
    Footprint.pack_available changed.resources
      (fun need member => (rowInputNeeds_bounded newInput need member).1)
      (fun need member => (rowInputNeeds_bounded newInput need member).2)
  exact ⟨changed.footprint, externalFootprint, newPacked, ⟨cert⟩, newPack, newCovered, externalAvailable⟩

end Lean4Lean.AnchoredSource.Adapted
