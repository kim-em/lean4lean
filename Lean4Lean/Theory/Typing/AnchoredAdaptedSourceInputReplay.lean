import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind

/-! Directional input adapters replay actual certificate leaves by finite
identity substitution. They never request observations at a new source type. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

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

private theorem replaySupply
    {oldInput newInput packed : Profile n}
    (adapter : NormalProfileAdapter env U registry Γ newInput oldInput)
    (newLive : Profile.Live env U registry Γ newInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside) :
    Nonempty (GradedSupply env U registry Γ locals σ Subst.id
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
      live := newLive } tail⟩
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

theorem CodeCert.replayInput
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {oldInput newInput packed : Profile n}
    (certificate : CodeCert env U registry Γ locals σ B result required)
    (adapter : NormalProfileAdapter env U registry Γ newInput oldInput)
    (newLive : Profile.Live env U registry Γ newInput)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (outsideLive : Footprint.Live env U registry Γ outside)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      Nonempty (CodeCert env U registry Γ locals σ B result footprint) ∧
      BinderPack n packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨supply⟩ := replaySupply adapter newLive pack covered outsideAvailable outsideLive
  obtain ⟨changed⟩ := certificate.substitute henv hscoped hΓ Subst.id σ
    (by funext i; rfl) locals (Valuation.push (rowInputNeeds newInput) available)
    (Valuation.push_atomized_closed closed [⟨n, newInput⟩]) supply
  obtain ⟨packed', outside', pack', covered', resources⟩ :=
    Footprint.pack_available changed.resources
      (fun need hm => (rowInputNeeds_bounded newInput need hm).1)
      (fun need hm atom ha => (rowInputNeeds_bounded newInput need hm).2 atom ha)
  exact ⟨changed.footprint, outside', packed',
    ⟨by simpa only [subst_id] using changed.certificate⟩, pack', covered', resources⟩

end Lean4Lean.AnchoredSource.Adapted
