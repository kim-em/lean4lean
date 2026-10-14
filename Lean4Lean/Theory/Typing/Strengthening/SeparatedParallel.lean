import Lean4Lean.Theory.Typing.Strengthening.SeparatedPatternComputation

/-! # Parallel computation with separated ordinary patterns

The head-separation certificate is preserved under substitution and parallel
capture computation. Every rigid constant retains its complete argument spine.
This is the parallel presentation used to join the remaining ordinary roots.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Parallel contraction develops only redexes already present in the source.
A delta step does not recursively develop its possibly recursive value. -/
inductive SeparatedPar (D : Definitions) : VExpr → VExpr → Prop where
  | bvar : SeparatedPar D (.bvar i) (.bvar i)
  | sort : SeparatedPar D (.sort u) (.sort u)
  | const : SeparatedPar D (.const c ls) (.const c ls)
  | delta : D.unfolds c ls rhs → SeparatedPar D (.const c ls) rhs
  | app : SeparatedPar D f f' → SeparatedPar D a a' → SeparatedPar D (.app f a) (.app f' a')
  | lam : SeparatedPar D A A' → SeparatedPar D b b' → SeparatedPar D (.lam A b) (.lam A' b')
  | forallE : SeparatedPar D A A' → SeparatedPar D B B' → SeparatedPar D (.forallE A B) (.forallE A' B')
  | proj : SeparatedPar D m m' → SeparatedPar D (.proj s i m) (.proj s i m')
  | projIota : Params.env.projections s info → args.length = info.nparams + info.numFields →
      args[info.nparams + index]? = some field → SeparatedPar D field field' →
      SeparatedPar D (.proj s index (mkApps (.const info.ctorName ls) args)) field'
  | pattern {p : Pattern} {r : p.RHS × p.Check} {levels : List VLevel}
      {captures captures' : p.Path → VExpr} :
      Pat p r → p.Matches e levels captures → CheckFromTyping env univs p r levels →
      (∀ rhs, ¬ D.unfolds p.headConst levels rhs) →
      (∀ path, SeparatedPar D (captures path) (captures' path)) →
      SeparatedPar D e (r.1.apply levels captures')
  | beta : SeparatedPar D b b' → SeparatedPar D a a' → SeparatedPar D (.app (.lam A b) a) (b'.inst a')

variable {D : Definitions}

theorem SeparatedPar.refl (e : VExpr) : SeparatedPar D e e := by
  induction e with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ _ _ ih => exact .proj ih

/-- Closed delta bodies remain fixed by every binder lift. -/
theorem SeparatedPar.liftN (R : SeparatedPar D e e') (n k : Nat) :
    SeparatedPar D (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | bvar => exact .refl _
  | sort => exact .sort
  | const => exact .const
  | delta H => rw [(D.closed H).liftN_eq (Nat.zero_le k)]; exact .delta H
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k+1))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 k) (ih2 (k+1))
  | proj _ ih => exact .proj (ih k)
  | projIota hi hl hg _ ih =>
    simp only [VExpr.liftN, VExpr.liftN_mkApps]
    exact .projIota hi (by simpa using hl) (by simp [List.getElem?_map, hg]) (ih k)
  | pattern hp hm hc hn _ ih =>
    rw [Pattern.RHS.liftN_apply]
    exact .pattern hp (Pattern.matches_liftN.2 ⟨_, hm, funext_iff.1 rfl⟩) hc hn (fun p => ih p k)
  | beta _ _ ih1 ih2 => rw [liftN_inst_hi]; exact .beta (ih1 (k+1)) (ih2 k)

/-- Parallel computation is compatible with parallel substitution, including
substitution into a newly contracted beta redex. -/
theorem SeparatedPar.subst (R : SeparatedPar D e e')
    (H : ∀ i, SeparatedPar D (σ i) (τ i)) : SeparatedPar D (e.subst σ) (e'.subst τ) := by
  have hlift {σ τ : VExpr.Subst} (H : ∀ i, SeparatedPar D (σ i) (τ i)) :
      ∀ i, SeparatedPar D (σ.lift i) (τ.lift i) := by
    intro i
    cases i with
    | zero => exact .bvar
    | succ i => exact (H i).liftN 1 0
  induction R generalizing σ τ with
  | bvar => exact H _
  | sort => exact .sort
  | const => exact .const
  | delta h => rw [(D.closed h).subst_eq (by intro i hi; omega)]; exact .delta h
  | app _ _ ih1 ih2 => exact .app (ih1 H) (ih2 H)
  | lam _ _ ih1 ih2 => exact .lam (ih1 H) (ih2 (hlift H))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 H) (ih2 (hlift H))
  | proj _ ih => exact .proj (ih H)
  | projIota hi hl hg _ ih =>
    simp only [subst_proj, subst_mkApps, subst_const]
    exact .projIota hi (by simpa using hl) (by simp [List.getElem?_map, hg]) (ih H)
  | pattern hp hm hc hn _ ih =>
    rw [Pattern.RHS.subst_apply]
    exact .pattern hp (Pattern.matches_subst hm) hc hn (fun p => ih p H)
  | beta _ _ ih1 ih2 => rw [subst_inst]; exact .beta (ih1 (hlift H)) (ih2 H)

theorem SeparatedPar.inst (R : SeparatedPar D e e') (H : SeparatedPar D a a') :
    SeparatedPar D (e.inst a) (e'.inst a') := by
  rw [inst_eq, inst_eq]
  apply R.subst
  intro i
  cases i with
  | zero => exact H
  | succ => exact .bvar


/-- A non-unfolding constructor retains its full application spine in a parallel
step, and every argument has its own parallel step. -/
theorem SeparatedPar.rigid_spine_paths
    (R : SeparatedPar D (mkApps (.const c ls) args) out)
    (hr : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = mkApps (.const c ls) args' ∧ List.Forall₂ (SeparatedPar D) args args' := by
  generalize he : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | const =>
    obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj (as' := []) he
    exact ⟨[], rfl, .nil⟩
  | delta hd =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
    exact (hn _ _ hd).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | pattern hp hm _ _ _ _ =>
    exact (Params.not_rigid_match (us := ls) hr hp hm
      (by rw [← he, ← getAppFn_eq_fst]; simp [getAppFn_mkApps, getAppFn])).elim
  | bvar | sort | beta | lam | forallE | proj | projIota =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Computing captures computes an instantiated RHS in parallel. -/
theorem SeparatedPar.apply_pat {p : Pattern} (r : p.RHS)
    {captures captures' : p.Path → VExpr}
    (H : ∀ path, SeparatedPar D (captures path) (captures' path)) :
    SeparatedPar D (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .refl _
  | var => exact H _
  | app _ _ ih1 ih2 => exact .app ih1 ih2

private theorem separated_apply_pat {p : Pattern} (r : p.RHS)
    {captures captures' : p.Path → VExpr}
    (H : ∀ path, SeparatedPatternCompute D (captures path) (captures' path)) :
    SeparatedPatternCompute D (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .base (.base .refl)
  | var => exact H _
  | app _ _ ih1 ih2 => exact .app ih1 ih2

/-- Parallel steps serialize into the separated finite relation. -/
theorem SeparatedPar.toCompute (R : SeparatedPar D e e') : SeparatedPatternCompute D e e' := by
  induction R with
  | bvar | sort | const => exact .base (.base .refl)
  | delta H => exact .base (.base (.delta H))
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | projIota hi hl hg _ ih => exact (SeparatedPatternCompute.base (.projIota hi hl hg)).trans ih
  | pattern hp hm hc hn _ ih => exact (SeparatedPatternCompute.pattern hp hm hc hn).trans (separated_apply_pat _ ih)
  | beta _ _ ih1 ih2 =>
    exact (SeparatedPatternCompute.app (.lam (.base (.base .refl)) ih1) ih2).trans (.base (.base .beta))

end Lean4Lean.VEnv.Strengthening.PureObservation
