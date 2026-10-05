import Lean4Lean.Theory.Typing.AnchoredNativeDepthCast
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRenaming

/-! Structural transport preserves the current declaration block's native
nesting depth. Ambient source substitution never enters a closed native leaf. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}

private theorem max_eq {a b c d : Nat} (ha : a = b) (hb : c = d) : max a c = max b d := by
  cases ha; cases hb; rfl

mutual
@[simp] theorem Obs.nativeDepth_realizePrefix (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint} {count : Nat}
    (observation : Obs env U registry target locals σ expression demand footprint)
    (scope : expression.ClosedN count) (τ : Subst) (agree : ∀ i < count, σ i = τ i) :
    (observation.realizePrefix scope τ agree).nativeDepth current = observation.nativeDepth current := by
  revert scope τ agree
  match original : observation with
  | .delta .. | .native .. | .family .. | .constructor .. =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
  | .var .. =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
  | .empty =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
  | .sort .. =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
  | .app fn arg adapter admitted =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact max_eq (fn.nativeDepth_realizePrefix current scope.1 τ agree)
      (arg.nativeDepth_realizePrefix current scope.2 τ agree)
  | .lam domain guard body pack covered =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact max_eq (domain.nativeDepth_realizePrefix current scope.1 τ agree)
      (body.nativeDepth_realizePrefix current scope.2 _ _)
  | .pi domain guard bodies =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact max_eq (domain.nativeDepth_realizePrefix current scope.1 τ agree)
      (bodies.nativeDepth_realizePrefix current scope.1 scope.2 τ agree)
  | .union left right =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact max_eq (left.nativeDepth_realizePrefix current scope τ agree)
      (right.nativeDepth_realizePrefix current scope τ agree)
  | .view child view =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact child.nativeDepth_realizePrefix current scope τ agree
  | .pad child =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact child.nativeDepth_realizePrefix current scope τ agree
  | .unpad child =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact child.nativeDepth_realizePrefix current scope τ agree
  | .rowShift child =>
    intro scope τ agree
    simp only [Obs.realizePrefix, Obs.nativeDepth]
    exact child.nativeDepth_realizePrefix current scope τ agree
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

@[simp] theorem CodeCert.nativeDepth_realizePrefix (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint} {count : Nat}
    (certificate : CodeCert env U registry target locals σ expression demand footprint)
    (scope : expression.ClosedN count) (τ : Subst) (agree : ∀ i < count, σ i = τ i) :
    (certificate.realizePrefix scope τ agree).nativeDepth current = certificate.nativeDepth current := by
  revert scope τ agree
  match original : certificate with
  | .seed observation formed =>
    intro scope τ agree
    simp only [CodeCert.realizePrefix, CodeCert.nativeDepth]
    exact observation.nativeDepth_realizePrefix current scope τ agree
  | .union left right =>
    intro scope τ agree
    simp only [CodeCert.realizePrefix, CodeCert.nativeDepth]
    exact max_eq (left.nativeDepth_realizePrefix current scope τ agree)
      (right.nativeDepth_realizePrefix current scope τ agree)
  | .pad child | .familyPad child | .unpad child | .down child | .map _ child | .select child _ | .focusMinimal child _ _ =>
    intro scope τ agree
    simp only [CodeCert.realizePrefix, CodeCert.nativeDepth]
    exact child.nativeDepth_realizePrefix current scope τ agree
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

@[simp] theorem PiRows.nativeDepth_realizePrefix (current : Name → Bool)
    {locals : List Nat} {σ : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint} {count : Nat}
    (bodies : PiRows env U registry target locals σ A B ambient rows footprint)
    (scopeA : A.ClosedN count) (scopeB : B.ClosedN (count + 1))
    (τ : Subst) (agree : ∀ i < count, σ i = τ i) :
    (bodies.realizePrefix scopeA scopeB τ agree).nativeDepth current = bodies.nativeDepth current := by
  revert scopeA scopeB τ agree
  match original : bodies with
  | .nil =>
    intro scopeA scopeB τ agree
    simp only [PiRows.realizePrefix, PiRows.nativeDepth]
  | .cons guard body pack covered tail =>
    intro scopeA scopeB τ agree
    simp only [PiRows.realizePrefix, PiRows.nativeDepth]
    exact max_eq (body.nativeDepth_realizePrefix current scopeB _ _)
      (tail.nativeDepth_realizePrefix current scopeA scopeB τ agree)
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

@[simp] theorem FamilyCaptures.nativeDepth_realizePrefix (current : Name → Bool)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (scope : CtxClosed source)
    (τ : Subst) (agree : ∀ i < source.length, σ i = τ i) :
    (captures.realizePrefix scope τ agree).nativeDepth current = captures.nativeDepth current := by
  revert scope τ agree
  match captures with
  | .nil => intro scope τ agree; simp only [FamilyCaptures.realizePrefix, FamilyCaptures.nativeDepth]
  | .cons lookup value adapter alignment anchor tail =>
    intro scope τ agree
    simp only [FamilyCaptures.realizePrefix, FamilyCaptures.nativeDepth]
    exact max_eq (value.nativeDepth_realizePrefix current _ τ agree)
      (tail.nativeDepth_realizePrefix current _ τ agree)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega
end

end Lean4Lean.AnchoredSource.Adapted
