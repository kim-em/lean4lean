import Lean4Lean.Theory.Typing.AnchoredSortableDepthSubstitution
import Lean4Lean.Theory.Typing.AnchoredSortableInstantiation

/-! Known beta instantiation preserves every declaration control on the same
returned source observer or certificate. The bound is computed from the two
actual incoming payloads, with no semantic reconstruction assumption. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace AllDepth
noncomputable def GradedResult.localDemand
    (result : GradedResult budget env U registry Γ locals σ available expression (input : Profile n))
    (need : Need) (bound : need.rank ≤ n)
    (included : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    GradedResult budget env U registry Γ locals σ available expression need.profile :=
  { result.toSortableGradedResult.localDemand need bound included with bounded := result.bounded }

theorem GradedSupply.instantiate
    (argument : GradedResult budget env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (GradedSupply budget env U registry Γ locals σ (.one a) available required) := by
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
    exact ⟨.cons (GradedResult.exact (.legacy (.var _ _ index need.profile)) oneAvailable
      (live index need List.mem_cons_self)
      (by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _)) tail⟩

private theorem one_realized (argument : VExpr) (realization : Subst) :
    (Subst.one argument).comp realization = realization.cons (argument.subst realization) := by
  funext index
  cases index <;> rfl

theorem SortableObs.instantiate
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (observation : SortableObs env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression demand required)
    (depth : ∀ current, observation.nativeDepth current ≤ budget current)
    (argument : GradedResult budget env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (GradedResult budget env U registry Γ locals σ available (expression.inst a) demand) := by
  obtain ⟨supply⟩ := GradedSupply.instantiate argument normal included resources live
  simpa only [inst_eq] using SortableObs.substitute henv hscoped hΓ observation depth (.one a) σ
    (one_realized a σ) locals available closed supply

theorem SortableCert.instantiate
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (certificate : SortableCert env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression relevant demand required)
    (depth : ∀ current, certificate.nativeDepth current ≤ budget current)
    (argument : GradedResult budget env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    Nonempty (CertificateResult budget env U registry Γ locals σ available (expression.inst a) relevant demand) := by
  obtain ⟨supply⟩ := GradedSupply.instantiate argument normal included resources live
  simpa only [inst_eq] using SortableCert.substitute henv hscoped hΓ certificate depth (.one a) σ
    (one_realized a σ) locals available closed supply

end AllDepth

theorem SortableObs.instantiate_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (observation : SortableObs env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression demand required)
    (argument : SortableGradedResult env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    ∃ result : SortableGradedResult env U registry Γ locals σ available (expression.inst a) demand,
      ∀ current, result.observation.nativeDepth current ≤
        max (observation.nativeDepth current) (argument.observation.nativeDepth current) := by
  let budget : AllDepth.Budget := fun current =>
    max (observation.nativeDepth current) (argument.observation.nativeDepth current)
  let boundedArgument : AllDepth.GradedResult budget env U registry Γ locals σ available a input :=
    { argument with bounded := fun _ => Nat.le_max_right _ _ }
  obtain ⟨result⟩ := AllDepth.SortableObs.instantiate henv hscoped hΓ closed observation
    (fun _ => Nat.le_max_left _ _) boundedArgument normal included resources live
  exact ⟨result.toSortableGradedResult, result.bounded⟩

theorem SortableCert.instantiate_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (certificate : SortableCert env U registry Γ (Locals.push locals)
      (σ.cons (a.subst σ)) expression relevant demand required)
    (argument : SortableGradedResult env U registry Γ locals σ available a (input : Profile n))
    (normal : BinderPack n packed required outside)
    (included : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : outside.Available available)
    (live : Footprint.Live env U registry Γ outside) :
    ∃ result : SortableCertificateResult env U registry Γ locals σ available (expression.inst a) relevant demand,
      ∀ current, result.certificate.nativeDepth current ≤
        max (certificate.nativeDepth current) (argument.observation.nativeDepth current) := by
  let budget : AllDepth.Budget := fun current =>
    max (certificate.nativeDepth current) (argument.observation.nativeDepth current)
  let boundedArgument : AllDepth.GradedResult budget env U registry Γ locals σ available a input :=
    { argument with bounded := fun _ => Nat.le_max_right _ _ }
  obtain ⟨result⟩ := AllDepth.SortableCert.instantiate henv hscoped hΓ closed certificate
    (fun _ => Nat.le_max_left _ _) boundedArgument normal included resources live
  exact ⟨⟨result.footprint, result.certificate, result.resources⟩, result.bounded⟩

end Lean4Lean.AnchoredSource.Adapted
