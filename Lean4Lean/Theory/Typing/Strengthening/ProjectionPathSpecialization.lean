import Lean4Lean.Theory.Typing.Strengthening.PrefixHeadPreservation

/-! # Specializing finite computation of constructor projections

Until a projection contracts, its constructor arguments compute pointwise.
After contraction, only the selected original field matters. This classification
handles arbitrary fields and actual prefix paths without a confluence premise.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Select a related field from two pointwise-related lists. -/
theorem forall₂_selected {k : Nat} {R : α → β → Prop} (H : List.Forall₂ R xs ys)
    (hg : xs[k]? = some x) : ∃ y, ys[k]? = some y ∧ R x y := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hg
  have hk' : k < ys.length := by rw [← H.length_eq]; exact hk
  have HR := H.getElem_of k hk hk'
  rw [he] at HR
  exact ⟨_, by simp [hk'], HR⟩

/-- Beta/delta below a projection preserves its outer spine and computes only
its constructor arguments. -/
theorem Compute.projection_spine_paths
    (R : Compute D (.proj family index (VExpr.mkApps (.const c ls) args)) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = .proj family index (VExpr.mkApps (.const c ls) args') ∧
      List.Forall₂ (Compute D) args args' := by
  generalize he : VExpr.proj family index (VExpr.mkApps (.const c ls) args) = source at R
  induction R generalizing args with
  | refl => exact ⟨_, he.symm, List.forall₂_of_getElem rfl (fun _ _ _ => .refl)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨args1, h1, HA⟩ := ih1 he
    obtain ⟨args2, h2, HB⟩ := ih2 h1.symm
    exact ⟨args2, h2, HA.trans (fun _ _ _ h h' => h.trans h') HB⟩
  | proj R =>
    cases he
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths hn
    exact ⟨args', congrArg _ h, HA⟩
  | beta | delta | app | lam | forallE => cases he

variable [Params]

/-- A finite projection-computation path either retains the original outer
projection and pointwise major paths, or computes the selected original field. -/
theorem ProjectionCompute.projection_spine_cases
    (R : ProjectionCompute D (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) out)
    (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hg : args[info.nparams + index]? = some field) :
    (∃ args', out = .proj family index (VExpr.mkApps (.const info.ctorName ls) args') ∧
      List.Forall₂ (ProjectionCompute D) args args') ∨ ProjectionCompute D field out := by
  generalize he : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = source at R
  induction R generalizing args field with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.projection_spine_paths hn
    exact .inl ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans R1 R2 ih1 ih2 =>
    rcases ih1 hg he with ⟨args1, h1, HA⟩ | H
    · obtain ⟨field1, hg1, HF⟩ := forall₂_selected HA hg
      rcases ih2 hg1 h1.symm with ⟨args2, h2, HB⟩ | H
      · exact .inl ⟨args2, h2, HA.trans (fun _ _ _ h h' => h.trans h') HB⟩
      · exact .inr (HF.trans H)
    · exact .inr (H.trans R2)
  | projIota hi' _ hg' =>
    obtain ⟨hfamily, hindex, hmajor⟩ := VExpr.proj.inj he
    cases hfamily
    cases hindex
    cases henv.ordered.projections_unique hi hi'
    have hargs := congrArg getAppArgs hmajor
    simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at hargs
    cases hargs
    cases Option.some.inj (hg.symm.trans hg')
    exact .inr (.base .refl)
  | proj R =>
    cases he
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths hn
    exact .inl ⟨args', congrArg _ h, HA⟩
  | app | lam | forallE => cases he

theorem PatternCompute.projection_spine_cases
    (R : PatternCompute D (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) out)
    (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hg : args[info.nparams + index]? = some field) :
    (∃ args', out = .proj family index (VExpr.mkApps (.const info.ctorName ls) args') ∧
      List.Forall₂ (PatternCompute D) args args') ∨ PatternCompute D field out := by
  generalize he : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = source at R
  induction R generalizing args field with
  | base R =>
    rw [← he] at R
    rcases R.projection_spine_cases hi hn hg with ⟨args', h, HA⟩ | H
    · exact .inl ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
    · exact .inr (.base H)
  | trans R1 R2 ih1 ih2 =>
    rcases ih1 hg he with ⟨args1, h1, HA⟩ | H
    · obtain ⟨field1, hg1, HF⟩ := forall₂_selected HA hg
      rcases ih2 hg1 h1.symm with ⟨args2, h2, HB⟩ | H
      · exact .inl ⟨args2, h2, HA.trans (fun _ _ _ h h' => h.trans h') HB⟩
      · exact .inr (HF.trans H)
    · exact .inr (H.trans R2)
  | pattern hp hm _ =>
    rw [← he] at hm
    obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
    cases hh
  | proj R =>
    cases he
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi) hn
    exact .inl ⟨args', congrArg _ h, HA⟩
  | app | lam | forallE => cases he

/-- Actual prefix paths admit the same specialization. In particular, later
computation of an exposed field need not terminate or have a normal form. -/
theorem PrefixCompute.projection_spine_cases
    (R : PrefixCompute D Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) out)
    (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hg : args[info.nparams + index]? = some field) :
    (∃ args', out = .proj family index (VExpr.mkApps (.const info.ctorName ls) args') ∧
      List.Forall₂ (PrefixCompute D Γ) args args') ∨ PrefixCompute D Γ field out := by
  generalize he : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = source at R
  induction R generalizing args field with
  | base R =>
    rw [← he] at R
    rcases R.projection_spine_cases hi hn hg with ⟨args', h, HA⟩ | H
    · exact .inl ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
    · exact .inr (.base H)
  | trans R1 R2 ih1 ih2 =>
    rcases ih1 hg he with ⟨args1, h1, HA⟩ | H
    · obtain ⟨field1, hg1, HF⟩ := forall₂_selected HA hg
      rcases ih2 hg1 h1.symm with ⟨args2, h2, HB⟩ | H
      · exact .inl ⟨args2, h2, HA.trans (fun _ _ _ h h' => h.trans h') HB⟩
      · exact .inr (HF.trans H)
    · exact .inr (H.trans R2)
  | proj R =>
    cases he
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi) hn
    exact .inl ⟨args', congrArg _ h, HA⟩
  | singleton | quotient =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | app | lam | forallE => cases he

/-- Complete any finite computation of a saturated constructor projection to
a computation of the selected original field. Only a possibly still-pending
outer projection is contracted on the right. -/
theorem PrefixCompute.projection_complete
    (R : PrefixCompute D Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) out)
    (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hlen : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams + index]? = some field) :
    ∃ field', PrefixCompute D Γ field field' ∧ PrefixCompute D Γ out field' := by
  rcases R.projection_spine_cases hi hn hg with ⟨args', rfl, HA⟩ | H
  · obtain ⟨field', hg', HF⟩ := forall₂_selected HA hg
    exact ⟨field', HF, .base (.base (.projIota hi (HA.length_eq.symm.trans hlen) hg'))⟩
  · exact ⟨out, H, .refl⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
