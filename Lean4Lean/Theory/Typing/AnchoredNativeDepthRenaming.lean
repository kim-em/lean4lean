import Lean4Lean.Theory.Typing.AnchoredNativeDepthTransport

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
private theorem max_eq {a b c d : Nat} (ha : a = b) (hb : c = d) : max a c = max b d := by
  cases ha; cases hb; rfl

mutual
@[simp] theorem Obs.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (observation.renameSource ρ τ realized newLocals).nativeDepth current = observation.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : observation with
  | .delta .. | .native .. | .family .. | .constructor .. | .var .. | .empty | .sort .. =>
    intro ρ τ realized newLocals
    simp only [Obs.renameSource, Obs.nativeDepth]
  | .app fn arg adapter admitted =>
    intro ρ τ realized newLocals
    have hf := fn.nativeDepth_renameSource current ρ τ realized newLocals
    have ha := arg.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [Obs.renameSource, Obs.nativeDepth_rec, Obs.nativeDepth, Obs.nativeDepth_mpr, Obs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hf ha
  | .lam (key := key) domain guard body pack covered =>
    intro ρ τ realized newLocals
    have hd := domain.nativeDepth_renameSource current ρ τ realized newLocals
    have hb := body.nativeDepth_renameSource current ρ.cons (τ.cons key.anchor) (by
      funext i; cases i <;> simp only [Subst.lift_l, Lift.liftVar, Subst.cons]
      exact congrFun realized _) (Locals.push newLocals)
    simpa only [Obs.renameSource, Obs.nativeDepth_rec, Obs.nativeDepth, Obs.nativeDepth_mpr, Obs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hd hb
  | .pi domain guard bodies =>
    intro ρ τ realized newLocals
    have hd := domain.nativeDepth_renameSource current ρ τ realized newLocals
    have hb := bodies.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [Obs.renameSource, Obs.nativeDepth_rec, Obs.nativeDepth, Obs.nativeDepth_mpr, Obs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hd hb
  | .union left right =>
    intro ρ τ realized newLocals
    have hl := left.nativeDepth_renameSource current ρ τ realized newLocals
    have hr := right.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [Obs.renameSource, Obs.nativeDepth_rec, Obs.nativeDepth, Obs.nativeDepth_mpr, Obs.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hl hr
  | .view child _ | .pad child | .unpad child | .rowShift child =>
    intro ρ τ realized newLocals
    simpa only [Obs.renameSource, Obs.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

@[simp] theorem CodeCert.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (certificate.renameSource ρ τ realized newLocals).nativeDepth current = certificate.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : certificate with
  | .seed observation formed =>
    intro ρ τ realized newLocals
    simpa only [CodeCert.renameSource, CodeCert.nativeDepth] using
      observation.nativeDepth_renameSource current ρ τ realized newLocals
  | .union left right =>
    intro ρ τ realized newLocals
    have hl := left.nativeDepth_renameSource current ρ τ realized newLocals
    have hr := right.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [CodeCert.renameSource, CodeCert.nativeDepth_rec, CodeCert.nativeDepth, CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hl hr
  | .pad child | .familyPad child | .unpad child | .down child | .map _ child | .select child _ | .focusMinimal child _ _ =>
    intro ρ τ realized newLocals
    simpa only [CodeCert.renameSource, CodeCert.nativeDepth] using
      child.nativeDepth_renameSource current ρ τ realized newLocals
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

@[simp] theorem PiRows.nativeDepth_renameSource (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry target locals σ A B ambient rows footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    (bodies.renameSource ρ τ realized newLocals).nativeDepth current = bodies.nativeDepth current := by
  revert ρ τ realized newLocals
  match original : bodies with
  | .nil => intro ρ τ realized newLocals; simp only [PiRows.renameSource, PiRows.nativeDepth]
  | .cons (key := key) guard body pack covered tail =>
    intro ρ τ realized newLocals
    have hb := body.nativeDepth_renameSource current ρ.cons (τ.cons key.anchor) (by
      funext i; cases i <;> simp only [Subst.lift_l, Lift.liftVar, Subst.cons]
      exact congrFun realized _) (Locals.push newLocals)
    have ht := tail.nativeDepth_renameSource current ρ τ realized newLocals
    simpa only [PiRows.renameSource, PiRows.nativeDepth_rec, PiRows.nativeDepth, PiRows.nativeDepth_mpr, PiRows.nativeDepth_mp, Footprint.sourceLift_append] using max_eq hb ht
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega
end

end Lean4Lean.AnchoredSource.Adapted
