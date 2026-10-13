import Lean4Lean.Theory.Typing.Strengthening.ProjectionEtaCancellation

/-! # Exposed structure constructors cannot become Pi or sort heads

For the new computational relation, a constant not unfolded by the declaration
collection retains its head through every path. Actual registered structure
constructors have this property by environment rigidity. Consequently a structure
eta expansion cannot itself expose a Pi or sort; a surrounding eliminator is needed.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- A rigid constant cannot be a left side of the environment's closed equations. -/
theorem Definitions.ofEnv_no_rigid {env : VEnv} (henv : env.WF) (hr : env.Rigid c) :
    ¬ (Definitions.ofEnv env U henv).unfolds c ls rhs := by
  rintro ⟨df, us, hd, _, _, he, _⟩
  have hshape : ∃ levels, df.lhs = .const c levels := by
    cases hh : df.lhs <;> simp [hh, instL] at he
    obtain ⟨rfl, _⟩ := he
    exact ⟨_, rfl⟩
  obtain ⟨levels, hh⟩ := hshape
  exact hr.defeqs df hd levels (by rw [hh]; rfl)

/-- Compatible beta/delta computation preserves a non-unfolding constant head. -/
theorem Compute.rigid_head (R : Compute D e out)
    (hn : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hh : e.getAppFn = .const c ls) :
    out.getAppFn = .const c ls := by
  induction R with
  | refl => exact hh
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hh)
  | delta hd => cases hh; exact (hn _ _ hd).elim
  | app _ _ ihf _ => exact ihf hh
  | beta | lam | forallE | proj => cases hh

variable [Params]

/-- Projection computation likewise preserves a non-unfolding constant head:
root projection redexes have projection heads, not constant heads. -/
theorem ProjectionCompute.rigid_head (R : ProjectionCompute D e out)
    (hn : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hh : e.getAppFn = .const c ls) :
    out.getAppFn = .const c ls := by
  induction R with
  | base h => exact h.rigid_head hn hh
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hh)
  | app _ _ ihf _ => exact ihf hh
  | projIota | lam | forallE | proj => cases hh

/-- An exposed structure expansion cannot itself compute to a Pi head, even if
its parameters or projected fields contain arbitrary computational redexes. -/
theorem ProjectionCompute.struct_no_pi
    (hinfo : env.projections s info)
    (R : ProjectionCompute (Definitions.ofEnv env univs henv)
      (structExpand s info ls ps e) (.forallE A B)) : False := by
  have hh := R.rigid_head (c := info.ctorName) (ls := ls)
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hinfo))
    (by simp [structExpand, getAppFn_mkApps, getAppFn])
  cases hh

/-- The analogous exclusion for sort exposure from a displayed structure value. -/
theorem ProjectionCompute.struct_no_sort
    (hinfo : env.projections s info)
    (R : ProjectionCompute (Definitions.ofEnv env univs henv)
      (structExpand s info ls ps e) (.sort u)) : False := by
  have hh := R.rigid_head (c := info.ctorName) (ls := ls)
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hinfo))
    (by simp [structExpand, getAppFn_mkApps, getAppFn])
  cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
