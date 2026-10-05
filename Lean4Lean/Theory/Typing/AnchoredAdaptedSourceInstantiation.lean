import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution

/-! Actual beta replacements come from one original argument result. Each
local request selects only its requested adapter endpoint; the whole actual
argument observation and its source resources remain unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def GradedResult.restrict
    (result : GradedResult env U registry Γ locals σ available expression (input : Profile n))
    (included : ∀ atom ∈ (requested : Profile n).atoms, atom ∈ input.atoms) :
    GradedResult env U registry Γ locals σ available expression requested where
  rank := result.rank
  bound := result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := ProfileAdapter.comp result.adapter (ProfileAdapter.select (by
    intro atom member
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨original, raiseProfile_subset result.bound included original hm, rfl⟩))
  resources := result.resources
  live := result.live

noncomputable def GradedResult.localDemand
    (result : GradedResult env U registry Γ locals σ available expression (input : Profile n))
    (need : Need) (bound : need.rank ≤ n)
    (included : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    GradedResult env U registry Γ locals σ available expression need.profile := by
  let selected := result.restrict included
  refine ⟨selected.rank, Nat.le_trans bound selected.bound, selected.raw,
    selected.footprint, selected.observation, ?_, selected.resources, selected.live⟩
  have adapter := selected.adapter
  simpa only [Need.atGrade, dif_pos bound, raiseProfile_trans] using adapter

theorem GradedSupply.instantiate
    (argument : GradedResult env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (GradedSupply env U registry Γ locals σ (.one a) available required) := by
  induction normal with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    obtain ⟨tail⟩ := ih (fun atom hm => included atom (List.mem_append_right _ hm)) resources live
    exact ⟨.cons (argument.localDemand need bound
      (fun atom hm => included atom (List.mem_append_left _ hm))) tail⟩
  | external index need rest ih =>
    obtain ⟨tail⟩ := ih included
      (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => live i need (List.mem_cons_of_mem _ hm))
    have oneAvailable : Footprint.Available [(index, need)] available := by
      intro i original hm
      cases List.mem_singleton.mp hm
      exact resources index need List.mem_cons_self
    exact ⟨.cons (GradedResult.exact (.var _ _ index need.profile) oneAvailable
      (live index need List.mem_cons_self)) tail⟩

private theorem one_realized (argument : VExpr) (realization : Subst) :
    (Subst.one argument).comp realization = realization.cons (argument.subst realization) := by
  funext index
  cases index <;> rfl

theorem Obs.instantiate
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (observation : Obs env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression demand required)
    (argument : GradedResult env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (GradedResult env U registry Γ locals σ available (expression.inst a) demand) := by
  obtain ⟨supply⟩ := GradedSupply.instantiate argument normal included resources live
  simpa only [inst_eq] using observation.substitute henv hscoped hΓ (.one a) σ
    (one_realized a σ) locals available closed supply

theorem CodeCert.instantiate
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (certificate : CodeCert env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression demand required)
    (argument : GradedResult env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (CertificateResult env U registry Γ locals σ available (expression.inst a) demand) := by
  obtain ⟨supply⟩ := GradedSupply.instantiate argument normal included resources live
  simpa only [inst_eq] using certificate.substitute henv hscoped hΓ (.one a) σ
    (one_realized a σ) locals available closed supply

end Lean4Lean.AnchoredSource.Adapted
