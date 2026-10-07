import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Staged

/-! # Head separation from the glued model

A chain of sort-typed equalities carries the observations of its left end into those of its
right end, up to subsumption (`Model.chain_sub`). Subsumption keeps the head constructor of
`sort` and `piDom` observations. A sort has a `sort` observation and a Pi type a `piDom`
observation. Neither a Pi type has a `sort` observation, nor does a spine of a rigid constant
have a `sort` or a `piDom` observation. So no chain relates a sort to a Pi type or to a rigid
spine, or a Pi type to a rigid spine. These are the separation fields `sort_forallE`,
`sort_rigid` and `forallE_rigid` of `VEnv.HeadInversion`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat}

/-- A Pi type has no `sort` observation. -/
theorem forallE_not_sort {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets}
    (h : Obs env U Δ σ S (.forallE A B) (.sort z)) : False := by
  rcases Obs.forallE_iff.1 h with h | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ <;>
    cases h

/-- A spine of a rigid constant has neither a `sort` nor a `piDom` observation. -/
theorem rigid_spine_not {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob}
    (hrig : env.Rigid c) (h : Obs env U Δ σ S (.mkApps (.const c ls) args) o)
    (ho : (∃ z, o = .sort z) ∨ ∃ D, o = .piDom D) : False := by
  have hna : o.NotApp := by rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial
  obtain ⟨keys, -, hw⟩ := wrap_of_obs_mkApps h
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩
  · obtain ⟨-, rfl⟩ := wrap_inj e hna hr.notApp
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)
  · have hrn : r.NotApp := by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨-, rfl⟩ := wrap_inj e hna hrn
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig df hdf lsP)

theorem sort_forallE (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.sort u) (.forallE A B)) : False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact forallE_not_sort ho

theorem sort_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact rigid_spine_not hrig ho (.inl ⟨_, rfl⟩)

theorem forallE_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (.piDom (A := A) (B := B))
  rw [l.piDom_inv] at ho
  exact rigid_spine_not hrig ho (.inr ⟨_, rfl⟩)

end Model

/-- The separation fields of `VEnv.HeadInversion` (`HeadInversion.lean`, which this file must
not import), stated identically. -/
structure HeadSeparation (env : VEnv) : Prop where
  sort_forallE : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : ∀ {U Γ c u ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : ∀ {U Γ c A B ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)

/-- **Head separation from soundness** of the observation model. -/
theorem WF.headSeparation_of_sound {env : VEnv} (henv : env.WF) (hnr : Model.SoundEnv env) :
    env.HeadSeparation where
  sort_forallE hΓ h := Model.sort_forallE henv.ordered hnr hΓ h
  sort_rigid hΓ hrig h := Model.sort_rigid henv.ordered hnr hΓ hrig h
  forallE_rigid hΓ hrig h := Model.forallE_rigid henv.ordered hnr hΓ hrig h

/-- **Head separation** for well-formed environments without projections (the scope of
stages B, D and E; `ProjFree` is dropped when stage C lands). -/
theorem WF.headSeparationModel {env : VEnv} (henv : env.WF) (hB : env.ProjFree) :
    env.HeadSeparation := by
  obtain ⟨ds, H⟩ := henv
  have hvalid := WF'.ruleValid ⟨ds, H⟩ hB.projections H .rfl (fun _ h _ _ _ _ => h)
  exact WF.headSeparation_of_sound ⟨ds, H⟩ fun hΔ H' =>
    Model.sound (VEnv.WF.ordered ⟨ds, H⟩) hΔ .rfl hvalid.1 hB.projections
      ⟨fun _ _ _ h1 h2 => VEnv.WF.eliminators_unique ⟨ds, H⟩ h1 h2, hvalid.2⟩ H'

end VEnv
end Lean4Lean
