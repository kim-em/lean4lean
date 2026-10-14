import Lean4Lean.Theory.Typing.Strengthening.DeclarationConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProjectionPathSpecialization

/-! # Parallel beta, delta and constructor projection computation

Projection contraction develops only its selected field. Constructor rigidity
ensures a competing compatible reduction preserves the constructor spine and
its argument positions. All statements concern raw syntax, with no typing or
strengthening premise.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Parallel contraction develops only redexes already present in the source.
A delta step does not recursively develop its possibly recursive value. -/
inductive ProjectionPar (D : Definitions) : VExpr → VExpr → Prop where
  | bvar : ProjectionPar D (.bvar i) (.bvar i)
  | sort : ProjectionPar D (.sort u) (.sort u)
  | const : ProjectionPar D (.const c ls) (.const c ls)
  | delta : D.unfolds c ls rhs → ProjectionPar D (.const c ls) rhs
  | app : ProjectionPar D f f' → ProjectionPar D a a' → ProjectionPar D (.app f a) (.app f' a')
  | lam : ProjectionPar D A A' → ProjectionPar D b b' → ProjectionPar D (.lam A b) (.lam A' b')
  | forallE : ProjectionPar D A A' → ProjectionPar D B B' → ProjectionPar D (.forallE A B) (.forallE A' B')
  | proj : ProjectionPar D m m' → ProjectionPar D (.proj s i m) (.proj s i m')
  | projIota : Params.env.projections s info → args.length = info.nparams + info.numFields →
      args[info.nparams + index]? = some field → ProjectionPar D field field' →
      ProjectionPar D (.proj s index (mkApps (.const info.ctorName ls) args)) field'
  | beta : ProjectionPar D b b' → ProjectionPar D a a' → ProjectionPar D (.app (.lam A b) a) (b'.inst a')

variable {D : Definitions}

theorem ProjectionPar.refl (e : VExpr) : ProjectionPar D e e := by
  induction e with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ _ _ ih => exact .proj ih

/-- Closed delta bodies remain fixed by every binder lift. -/
theorem ProjectionPar.liftN (R : ProjectionPar D e e') (n k : Nat) :
    ProjectionPar D (e.liftN n k) (e'.liftN n k) := by
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
  | beta _ _ ih1 ih2 => rw [liftN_inst_hi]; exact .beta (ih1 (k+1)) (ih2 k)

/-- Parallel computation is compatible with parallel substitution, including
substitution into a newly contracted beta redex. -/
theorem ProjectionPar.subst (R : ProjectionPar D e e')
    (H : ∀ i, ProjectionPar D (σ i) (τ i)) : ProjectionPar D (e.subst σ) (e'.subst τ) := by
  have hlift {σ τ : VExpr.Subst} (H : ∀ i, ProjectionPar D (σ i) (τ i)) :
      ∀ i, ProjectionPar D (σ.lift i) (τ.lift i) := by
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
  | beta _ _ ih1 ih2 => rw [subst_inst]; exact .beta (ih1 (hlift H)) (ih2 H)

theorem ProjectionPar.inst (R : ProjectionPar D e e') (H : ProjectionPar D a a') :
    ProjectionPar D (e.inst a) (e'.inst a') := by
  rw [inst_eq, inst_eq]
  apply R.subst
  intro i
  cases i with
  | zero => exact H
  | succ => exact .bvar


/-- A non-unfolding constructor retains its full application spine in a parallel
step, and every argument has its own parallel step. -/
theorem ProjectionPar.rigid_spine_paths
    (R : ProjectionPar D (mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ args', out = mkApps (.const c ls) args' ∧ List.Forall₂ (ProjectionPar D) args args' := by
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
  | bvar | sort | beta | lam | forallE | proj | projIota =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Every parallel projection development serializes into finite computation. -/
theorem ProjectionPar.toCompute (R : ProjectionPar D e e') : ProjectionCompute D e e' := by
  induction R with
  | bvar | sort | const => exact .base .refl
  | delta H => exact .base (.delta H)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | projIota hi hl hg _ ih => exact (ProjectionCompute.projIota hi hl hg).trans ih
  | beta _ _ ih1 ih2 => exact (ProjectionCompute.app (.lam (.base .refl) ih1) ih2).trans (.base .beta)

end Lean4Lean.VEnv.Strengthening.PureObservation
