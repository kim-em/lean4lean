import Lean4Lean.Theory.Typing.AnchoredBoundedSubstitution
import Lean4Lean.Theory.Typing.AnchoredBoundedBetaExpansion
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceInputReplay

/-! Eta's changed-input row replay uses finite bounded variable replacements.
The old code demand is retained exactly, including through high-grade adapters.
No semantic interpretation callback or fresh source-typing premise is used. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem rebindSupplyBounded
    {current : Name → Bool} {fuel : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayBound : replay.nativeDepth current ≤ fuel)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    Nonempty (Staged.Substitution.GradedSupply current fuel env U registry Γ locals σ Subst.id
      (Valuation.push (rowInputNeeds newInput) available) required) := by
  have localClosed := Valuation.push_atomized_closed closed [⟨m, newInput⟩]
  induction pack with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    have inclusion : List.Subset (raiseProfile n bound need.profile) oldInput := by
      intro atom member
      apply covered atom (List.mem_append_left _ ?_)
      simpa only [Need.atGrade, dif_pos bound, Profile.atoms] using member
    obtain ⟨footprint, selected, selection, selectedBound⟩ := replay.subprofile_bounded (current := current) inclusion
    let observation := selected.lower bound
    have live : Profile.Live env U registry Γ need.profile :=
      (raiseProfile_live_iff bound need.profile).mp (oldLive.subset inclusion)
    have resources := selection.available_closed replayAvailable localClosed
    obtain ⟨tail⟩ := ih (fun atom member => covered atom (List.mem_append_right _ member))
      outsideAvailable outsideLive
    exact ⟨.cons (Staged.Substitution.GradedResult.exact observation resources live (by simpa only [observation, Obs.nativeDepth_lower] using Nat.le_trans selectedBound replayBound)) tail⟩
  | external index need rest ih =>
    obtain ⟨tail⟩ := ih covered
      (fun i need hm => outsideAvailable i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => outsideLive i need (List.mem_cons_of_mem _ hm))
    have resources : Footprint.Available [(index + 1, need)]
        (Valuation.push (rowInputNeeds newInput) available) := by
      intro i wanted hm
      cases List.mem_singleton.mp hm
      exact outsideAvailable index need List.mem_cons_self
    exact ⟨.cons (Staged.Substitution.GradedResult.exact (.var locals σ (index + 1) need.profile) resources
      (outsideLive index need List.mem_cons_self) (by simp only [Obs.nativeDepth]; omega)) tail⟩

/-- The source expression, result code profile, and external valuation stay
fixed. Only the actual local variable observations are replayed. -/
theorem CodeCert.rebind_localBounded
    {current : Name → Bool} {fuel : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput packed : Profile n} {newInput : Profile m}
    (certificate : CodeCert env U registry Γ locals σ B result required)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (replay : Obs env U registry Γ locals σ (.bvar 0) oldInput replayFootprint)
    (replayBound : replay.nativeDepth current ≤ fuel)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (oldLive : Profile.Live env U registry Γ oldInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      (∃ body : CodeCert env U registry Γ locals σ B result footprint, body.nativeDepth current ≤ fuel) ∧
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨supply⟩ := rebindSupplyBounded henv hscoped hΓ replay replayBound replayAvailable oldLive pack covered
    outsideAvailable outsideLive closed
  obtain ⟨changed⟩ := Staged.Substitution.CodeCert.substitute henv hscoped hΓ certificate certificateBound Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed _) supply
  obtain ⟨changedFootprint, changedCertificate, changedResources, changedBound⟩ := changed
  have certData : ∃ body : CodeCert env U registry Γ locals σ (B.subst Subst.id) result changedFootprint,
      body.nativeDepth current ≤ fuel := ⟨changedCertificate, changedBound⟩
  rw [subst_id] at certData
  obtain ⟨newPacked, externalFootprint, newPack, newCovered, externalAvailable⟩ :=
    Footprint.pack_available changedResources
      (fun need member => (rowInputNeeds_bounded newInput need member).1)
      (fun need member => (rowInputNeeds_bounded newInput need member).2)
  exact ⟨changedFootprint, externalFootprint, newPacked, certData, newPack, newCovered, externalAvailable⟩

private noncomputable def selectNormal {p q : Profile n}
    (included : ∀ atom ∈ q.atoms, atom ∈ p.atoms) :
    NormalProfileAdapter env U registry Γ p q := by
  have normalized : List.Subset (AdapterNormal.profile q) (AdapterNormal.profile p) := by
    intro atom hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨a, included a ha, rfl⟩
  change ProfileAdapter env U registry Γ (AdapterNormal.profile p) (AdapterNormal.profile q)
  generalize AdapterNormal.profile q = target at normalized ⊢
  induction target with
  | nil => exact .nil _
  | cons a rest ih =>
    exact .cons (normalized List.mem_cons_self) (.refl a)
      (ih (fun _ h => normalized (List.mem_cons_of_mem _ h)))

private theorem replaySupplyBounded
    {current : Name → Bool} {fuel : Nat}
    {oldInput newInput packed : Profile n}
    (adapter : NormalProfileAdapter env U registry Γ newInput oldInput)
    (newLive : Profile.Live env U registry Γ newInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside) :
    Nonempty (Staged.Substitution.GradedSupply current fuel env U registry Γ locals σ Subst.id
      (Valuation.push (rowInputNeeds newInput) available) required) := by
  induction pack with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    have included : ∀ atom ∈ (raiseProfile n bound need.profile).atoms,
        atom ∈ oldInput.atoms := by
      intro atom member
      apply covered atom (List.mem_append_left _ ?_)
      simpa only [Need.atGrade, dif_pos bound] using member
    have resources : Footprint.Available [(0, ⟨n, newInput⟩)]
        (Valuation.push (rowInputNeeds newInput) available) := by
      intro i wanted hm
      cases List.mem_singleton.mp hm
      exact List.mem_append_left _ List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun atom hm => covered atom (List.mem_append_right _ hm))
      outsideAvailable outsideLive
    exact ⟨.cons {
      rank := n
      bound := bound
      raw := newInput
      footprint := [(0, ⟨n, newInput⟩)]
      observation := .var locals σ 0 newInput
      adapter := adapter.comp (selectNormal included)
      resources := resources
      live := newLive
      observationBound := by simp only [Obs.nativeDepth]; omega } tail⟩
  | external index need rest ih =>
    obtain ⟨tail⟩ := ih covered
      (fun i need hm => outsideAvailable i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => outsideLive i need (List.mem_cons_of_mem _ hm))
    have resources : Footprint.Available [(index + 1, need)]
        (Valuation.push (rowInputNeeds newInput) available) := by
      intro i wanted hm
      cases List.mem_singleton.mp hm
      exact outsideAvailable index need List.mem_cons_self
    exact ⟨.cons (Staged.Substitution.GradedResult.exact (.var locals σ (index + 1) need.profile) resources
      (outsideLive index need List.mem_cons_self) (by simp only [Obs.nativeDepth]; omega)) tail⟩

theorem CodeCert.replayInputBounded
    {current : Name → Bool} {fuel : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput newInput packed : Profile n}
    (certificate : CodeCert env U registry Γ locals σ B result required)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (adapter : NormalProfileAdapter env U registry Γ newInput oldInput)
    (newLive : Profile.Live env U registry Γ newInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      (∃ body : CodeCert env U registry Γ locals σ B result footprint, body.nativeDepth current ≤ fuel) ∧
      BinderPack n packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨supply⟩ := replaySupplyBounded (current := current) (fuel := fuel) adapter newLive pack covered outsideAvailable outsideLive
  obtain ⟨changed⟩ := Staged.Substitution.CodeCert.substitute henv hscoped hΓ certificate certificateBound Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed [⟨n, newInput⟩]) supply
  obtain ⟨changedFootprint, changedCertificate, changedResources, changedBound⟩ := changed
  obtain ⟨packed', outside', pack', covered', resources⟩ :=
    Footprint.pack_available changedResources
      (fun need hm => (rowInputNeeds_bounded newInput need hm).1)
      (fun need hm atom ha => (rowInputNeeds_bounded newInput need hm).2 atom ha)
  have certData : ∃ body : CodeCert env U registry Γ locals σ (B.subst Subst.id) result changedFootprint,
      body.nativeDepth current ≤ fuel := ⟨changedCertificate, changedBound⟩
  rw [subst_id] at certData
  exact ⟨changedFootprint, outside', packed', certData, pack', covered', resources⟩

end Lean4Lean.AnchoredSource.Adapted
