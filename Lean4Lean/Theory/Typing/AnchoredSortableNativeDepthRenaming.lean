import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthCast
import Lean4Lean.Theory.Typing.AnchoredSortableRenaming

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
private theorem max_eq {a b c d : Nat} (ha : a = b) (hb : c = d) : max a c = max b d := by
  cases ha; cases hb; rfl

mutual
@[simp] theorem SortableObs.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry target locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (observation.renameSource ρ τ realized newLocals).nativeDepth current = observation.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : observation with
  | .family .. =>
    intro ρ τ realized newLocals
    simp only [SortableObs.renameSource, SortableObs.nativeDepth]
  | .legacy child =>
    intro ρ τ realized newLocals
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
  | .code _ child =>
    intro ρ τ realized newLocals
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
  | .app fn arg adapter admitted =>
    intro ρ τ realized newLocals
    have hf := fn.nativeDepth_renameSource current ρ τ realized newLocals
    have ha := arg.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth_rec, SortableObs.nativeDepth, SortableObs.nativeDepth_mpr, SortableObs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hf ha
  | .lam (key := key) domain guard body pack covered =>
    intro ρ τ realized newLocals
    have hd := domain.nativeDepth_renameSource current ρ τ realized newLocals
    have hb := body.nativeDepth_renameSource current ρ.cons (τ.cons key.anchor) (by
      funext i; cases i <;> simp only [Subst.lift_l, Lift.liftVar, Subst.cons]
      exact congrFun realized _) (Locals.push newLocals)
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth_rec, SortableObs.nativeDepth, SortableObs.nativeDepth_mpr, SortableObs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hd hb
  | .union left right =>
    intro ρ τ realized newLocals
    have hl := left.nativeDepth_renameSource current ρ τ realized newLocals
    have hr := right.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth_rec, SortableObs.nativeDepth, SortableObs.nativeDepth_mpr, SortableObs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hl hr
  | .action child _ | .view child _ | .pad child | .unpad child | .rowShift child =>
    intro ρ τ realized newLocals
    simpa only [SortableObs.renameSource, SortableObs.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> subst_eqs <;> simp_wf <;> omega)

@[simp] theorem SortableCert.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (certificate.renameSource ρ τ realized newLocals).nativeDepth current = certificate.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : certificate with
  | .ofCode observation formed | .seed observation formed | .observe observation formed =>
    intro ρ τ realized newLocals
    simpa only [SortableCert.renameSource, SortableCert.nativeDepth] using
      observation.nativeDepth_renameSource current ρ τ realized newLocals
  | .pi domain guard bodies =>
    intro ρ τ realized newLocals
    have hd := domain.nativeDepth_renameSource current ρ τ realized newLocals
    have hb := bodies.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [SortableCert.renameSource, SortableCert.nativeDepth_rec, SortableCert.nativeDepth, SortableCert.nativeDepth_mpr, SortableCert.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hd hb
  | .union left right =>
    intro ρ τ realized newLocals
    have hl := left.nativeDepth_renameSource current ρ τ realized newLocals
    have hr := right.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [SortableCert.renameSource, SortableCert.nativeDepth_rec, SortableCert.nativeDepth, SortableCert.nativeDepth_mpr, SortableCert.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hl hr
  | .sortPad child | .support _ child | .pad child | .familyPad child | .unpad child | .down child | .map _ child | .select child _ | .focusMinimal child _ _ =>
    intro ρ τ realized newLocals
    simpa only [SortableCert.renameSource, SortableCert.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> subst_eqs <;> simp_wf <;> omega)

@[simp] theorem SortableRows.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry target locals σ A B relevant ambient rows footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (bodies.renameSource ρ τ realized newLocals).nativeDepth current = bodies.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : bodies with
  | .nil => intro ρ τ realized newLocals; simp only [SortableRows.renameSource, SortableRows.nativeDepth]
  | .cons (key := key) guard body pack covered tail =>
    intro ρ τ realized newLocals
    have hb := body.nativeDepth_renameSource current ρ.cons (τ.cons key.anchor) (by
      funext i; cases i <;> simp only [Subst.lift_l, Lift.liftVar, Subst.cons]
      exact congrFun realized _) (Locals.push newLocals)
    have ht := tail.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [SortableRows.renameSource, SortableRows.nativeDepth_rec, SortableRows.nativeDepth, SortableRows.nativeDepth_mpr, SortableRows.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hb ht
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> subst_eqs <;> simp_wf <;> omega)
end

end Lean4Lean.AnchoredSource.Adapted
