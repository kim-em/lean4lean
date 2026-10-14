import Lean4Lean.Theory.Typing.Strengthening.PrefixConstructorFixed

/-! # Computational completion preserves exposed type heads

Actual prefix computation cannot remove a Pi head or change a rigid constant
spine's head, universe instance, or arity. These facts let a further computation
on the right of a phase representation retain the head needed for type repair.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params

/-- Beta and closed declaration computation preserve an exposed Pi. -/
theorem Compute.pi_shape (R : Compute D (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' := by
  generalize he : VExpr.forallE A B = source at R
  induction R generalizing A B with
  | refl => exact ⟨_, _, he.symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, h⟩ := ih1 he
    exact ih2 h.symm
  | forallE => cases he; exact ⟨_, _, rfl⟩
  | beta | delta | app | lam | proj => cases he

/-- The exact head, levels and arity of a non-unfolding constant spine survive. -/
theorem Compute.rigid_spine_paths (R : Compute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (Compute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | refl => exact ⟨_, he.symm, List.forall₂_of_getElem rfl (fun _ _ _ => .refl)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | delta hd =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
    exact (hn _ _ hd).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | beta | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh


theorem Compute.rigid_spine (R : Compute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ args'.length = args.length := by
  obtain ⟨args', he, HA⟩ := R.rigid_spine_paths hn
  exact ⟨args', he, HA.length_eq.symm⟩

variable [Params]

theorem ProjectionCompute.pi_shape (R : ProjectionCompute D (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' := by
  generalize he : VExpr.forallE A B = source at R
  induction R generalizing A B with
  | base R => rw [← he] at R; exact R.pi_shape
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, h⟩ := ih1 he
    exact ih2 h.symm
  | forallE => cases he; exact ⟨_, _, rfl⟩
  | projIota | app | lam | proj => cases he

theorem ProjectionCompute.rigid_spine_paths
    (R : ProjectionCompute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (ProjectionCompute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths hn
    exact ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | projIota | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh


theorem ProjectionCompute.rigid_spine
    (R : ProjectionCompute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ args'.length = args.length := by
  obtain ⟨args', he, HA⟩ := R.rigid_spine_paths hn
  exact ⟨args', he, HA.length_eq.symm⟩

theorem PatternCompute.pi_shape (R : PatternCompute D (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' := by
  generalize he : VExpr.forallE A B = source at R
  induction R generalizing A B with
  | base R => rw [← he] at R; exact R.pi_shape
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, h⟩ := ih1 he
    exact ih2 h.symm
  | pattern hp hm _ =>
    rw [← he] at hm
    obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
    cases hh
  | forallE => cases he; exact ⟨_, _, rfl⟩
  | app | lam | proj => cases he

theorem PatternCompute.rigid_spine_paths
    (R : PatternCompute D (VExpr.mkApps (.const c ls) args) out)
    (hr : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (PatternCompute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths hn
    exact ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | pattern hp hm _ =>
    rw [← he] at hm
    exact (Params.not_rigid_match hr hp hm (us := ls)
      (by rw [← getAppFn_eq_fst]; simp [getAppFn_mkApps, getAppFn])).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh


theorem PatternCompute.rigid_spine
    (R : PatternCompute D (VExpr.mkApps (.const c ls) args) out)
    (hr : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ args'.length = args.length := by
  obtain ⟨args', he, HA⟩ := R.rigid_spine_paths hr hn
  exact ⟨args', he, HA.length_eq.symm⟩

/-- Every singleton prefix is headed by a non-rigid name, as witnessed by its
actual stored iota equation. No restriction on indices or supplied arity occurs. -/
theorem prefixUnfold_not_rigid
    (H : PrefixUnfold env univs recursorData Γ name levels args out)
    (hrigid : env.Rigid name) : False := by
  cases H with
  | intro _ hr hname _ _ _ hg _ =>
    obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨r, ru, hc, hof, hp⟩ := hr.singletonEquation hseq
    obtain ⟨index, howner, hgen⟩ := RecursorData.singletonEquation_eq hseq
    have hhead := hr.equation_head howner hgen
    have hrec := hof.2.1
    rw [lamBody_eq_stripLams, VExpr.headConst?_eq_some] at hrec
    obtain ⟨us, hrec⟩ := hrec
    rw [VExpr.getAppFn_eq_fst, hhead] at hrec
    have hrname := (VExpr.const.inj hrec).1.symm
    exact hrigid.pats _ _ hp (by rw [SimplePattern.iota_headConst, hrname, hname])

/-- Actual compatible prefix computation retains an exposed Pi. -/
theorem PrefixCompute.pi_shape (R : PrefixCompute D Γ (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' := by
  generalize he : VExpr.forallE A B = source at R
  induction R generalizing A B with
  | base R => rw [← he] at R; exact R.pi_shape
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, h⟩ := ih1 he
    exact ih2 h.symm
  | forallE => cases he; exact ⟨_, _, rfl⟩
  | singleton | quotient =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | app | lam | proj => cases he

/-- Actual compatible prefix computation preserves rigid spine heads and
arity, even though every argument may compute independently. -/
theorem PrefixCompute.rigid_spine_paths
    (R : PrefixCompute D Γ (VExpr.mkApps (.const c ls) args) out)
    (hr : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (PrefixCompute D Γ) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.rigid_spine_paths hr hn
    exact ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | singleton H =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases (VExpr.const.inj hh).1
    exact (prefixUnfold_not_rigid H hr).elim
  | quotient H =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases (VExpr.const.inj hh).1
    exact (hr.defeqs quotDefEq H.registered.equation [.param 0, .param 1] rfl).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh


theorem PrefixCompute.rigid_spine
    (R : PrefixCompute D Γ (VExpr.mkApps (.const c ls) args) out)
    (hr : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ args'.length = args.length := by
  obtain ⟨args', he, HA⟩ := R.rigid_spine_paths hr hn
  exact ⟨args', he, HA.length_eq.symm⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
