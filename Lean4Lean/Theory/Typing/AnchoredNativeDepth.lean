import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBinder

/-! Declaration staging counts nesting of the CURRENT block's source unfolding
heads. Grade changes, unions and old-block wrappers do not spend this fuel.
Every actual certificate and capture child is included in the measure. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}

mutual
def Obs.nativeDepth (current : Name → Bool)
    (observation : Obs env U registry target locals σ expression demand footprint) : Nat :=
  match observation with
  | .delta (name := name) _ _ _ _ _ _ _ _ _ certificate _ body =>
    max (body.nativeDepth current) (certificate.nativeDepth current) + if current name then 1 else 0
  | .native (name := name) _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.nativeDepth current) (certificate.nativeDepth current) + if current name then 1 else 0
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree
  | .constructor _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.nativeDepth current) (certificate.nativeDepth current)
  | .var .. | .empty | .sort .. => 0
  | .app fn arg _ _ => max (fn.nativeDepth current) (arg.nativeDepth current)
  | .lam domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .pi domain _ bodies => max (domain.nativeDepth current) (bodies.nativeDepth current)
  | .union left right => max (left.nativeDepth current) (right.nativeDepth current)
  | .view source _ | .pad source | .unpad source | .rowShift source => source.nativeDepth current
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

def CodeCert.nativeDepth (current : Name → Bool)
    (certificate : CodeCert env U registry target locals σ expression demand footprint) : Nat :=
  match certificate with
  | .seed observation _ => observation.nativeDepth current
  | .union left right => max (left.nativeDepth current) (right.nativeDepth current)
  | .pad source | .familyPad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ => source.nativeDepth current
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

def PiRows.nativeDepth (current : Name → Bool)
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ body _ _ tail => max (body.nativeDepth current) (tail.nativeDepth current)
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

def NativeCaptures.nativeDepth (current : Name → Bool)
    (captures : NativeCaptures env U registry target program witnesses index required outside) : Nat :=
  match captures with
  | .prefix _ => 0
  | .index natural _ declared _ _ _ _ _ _ _ _ _ previous =>
    max (natural.nativeDepth current) (max (declared.nativeDepth current) (previous.nativeDepth current))
  | .proof _ _ _ _ _ _ previous => previous.nativeDepth current
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

def NativePlan.nativeDepth (current : Name → Bool)
    (plan : NativePlan env U registry target signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ _ _ _ _ _ _ _ _ _ body captures =>
    max (body.nativeDepth current) (captures.nativeDepth current)
  | .binder _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

def FamilyCaptures.nativeDepth (current : Name → Bool)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) : Nat :=
  match captures with
  | .nil => 0
  | .cons _ value _ _ _ tail => max (value.nativeDepth current) (tail.nativeDepth current)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

def FamilyPlan.nativeDepth (current : Name → Bool)
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.nativeDepth current
  | .binder _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .view source _ | .pad source => source.nativeDepth current
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega
def ConstructorPlan.nativeDepth (current : Name → Bool)
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures resultCode => max (captures.nativeDepth current) (resultCode.nativeDepth current)
  | .binder _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .view source _ | .pad source => source.nativeDepth current
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end

theorem Obs.nativeDepth_cast (current : Name → Bool)
    {n : Nat} {p q : Profile n} (profiles : p = q)
    (equal : Obs env U registry target locals σ expression p footprint =
      Obs env U registry target locals σ expression q footprint)
    (observation : Obs env U registry target locals σ expression p footprint) :
    (cast equal observation).nativeDepth current = observation.nativeDepth current := by
  cases profiles
  cases equal
  rfl

theorem CodeCert.nativeDepth_cast (current : Name → Bool)
    {n : Nat} {p q : Profile n} (profiles : p = q)
    (equal : CodeCert env U registry target locals σ expression p footprint =
      CodeCert env U registry target locals σ expression q footprint)
    (certificate : CodeCert env U registry target locals σ expression p footprint) :
    (cast equal certificate).nativeDepth current = certificate.nativeDepth current := by
  cases profiles
  cases equal
  rfl

@[simp] theorem Obs.nativeDepth_raise (current : Name → Bool) {n N : Nat} {demand : Profile n}
    (bound : n ≤ N) (observation : Obs env U registry target locals σ expression demand footprint) :
    (observation.raise bound).nativeDepth current = observation.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [Obs.raise, Nat.recAux, dite_true]
      exact Obs.nativeDepth_cast current (raiseProfile_self ..).symm _ observation
    · simp only [Obs.raise, Nat.recAux, dif_neg hn]
      refine (Obs.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (Obs.pad (observation.raise (show n ≤ N by omega))).nativeDepth current = _
      simpa only [Obs.nativeDepth] using ih (by omega)

@[simp] theorem CodeCert.nativeDepth_raise (current : Name → Bool) {n N : Nat} {demand : Profile n}
    (bound : n ≤ N) (certificate : CodeCert env U registry target locals σ expression demand footprint) :
    (certificate.raise bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [CodeCert.raise, Nat.recAux, dite_true]
      exact CodeCert.nativeDepth_cast current (raiseProfile_self ..).symm _ certificate
    · simp only [CodeCert.raise, Nat.recAux, dif_neg hn]
      refine (CodeCert.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (CodeCert.pad (certificate.raise (show n ≤ N by omega))).nativeDepth current = _
      simpa only [CodeCert.nativeDepth] using ih (by omega)

@[simp] theorem CodeCert.nativeDepth_lower (current : Name → Bool) {n N : Nat} {demand : Profile N}
    (bound : n ≤ N) (certificate : CodeCert env U registry target locals σ expression demand footprint) :
    (certificate.lower n bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [CodeCert.lower, Nat.recAux, dite_true]
      exact CodeCert.nativeDepth_cast current (lowerProfile_self ..).symm _ certificate
    · simp only [CodeCert.lower, Nat.recAux, dif_neg hn]
      refine (CodeCert.nativeDepth_cast current
        (lowerProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (certificate.down.lower n (show n ≤ N by omega)).nativeDepth current = _
      simpa only [CodeCert.nativeDepth] using ih (by omega) (.down certificate)

end Lean4Lean.AnchoredSource.Adapted
