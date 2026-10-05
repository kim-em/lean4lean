import Lean4Lean.Theory.Typing.AnchoredNativeDepth
import Lean4Lean.Theory.Typing.EquationStratifiedFuel

/-! Finite depth with an explicit computational-head policy. Every actual
source query/certificate child is traversed; only a named delta/native head
can mask its recursively computed child depth. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Higher computational heads mask lower caller controls. The pointwise
policy is exactly the checked opening/return algebra. -/
def stratifiedHeadPolicy (rank : Name → Nat) (control : Nat) (name : Name) (children : Nat) : Nat :=
  EquationStratifiedFuel.headDepth (rank name) (fun _ => children) control

mutual
def Obs.headDepth (policy : Name → Nat → Nat)
    (observation : Obs env U registry target locals σ expression demand footprint) : Nat :=
  match observation with
  | .delta (name := name) _ _ _ _ _ _ _ _ _ certificate _ body =>
    policy name (max (body.headDepth policy) (certificate.headDepth policy))
  | .native (name := name) _ _ _ _ _ _ _ _ _ certificate _ tree =>
    policy name (max (tree.headDepth policy) (certificate.headDepth policy))
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree
  | .constructor _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.headDepth policy) (certificate.headDepth policy)
  | .var .. | .empty | .sort .. => 0
  | .app fn arg _ _ => max (fn.headDepth policy) (arg.headDepth policy)
  | .lam domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .pi domain _ bodies => max (domain.headDepth policy) (bodies.headDepth policy)
  | .union left right => max (left.headDepth policy) (right.headDepth policy)
  | .view source _ | .pad source | .unpad source | .rowShift source => source.headDepth policy
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

def CodeCert.headDepth (policy : Name → Nat → Nat)
    (certificate : CodeCert env U registry target locals σ expression demand footprint) : Nat :=
  match certificate with
  | .seed observation _ => observation.headDepth policy
  | .union left right => max (left.headDepth policy) (right.headDepth policy)
  | .pad source | .familyPad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ => source.headDepth policy
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

def PiRows.headDepth (policy : Name → Nat → Nat)
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ body _ _ tail => max (body.headDepth policy) (tail.headDepth policy)
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

def NativeCaptures.headDepth (policy : Name → Nat → Nat)
    (captures : NativeCaptures env U registry target program witnesses index required outside) : Nat :=
  match captures with
  | .prefix _ => 0
  | .index natural _ declared _ _ _ _ _ _ _ _ _ previous =>
    max (natural.headDepth policy) (max (declared.headDepth policy) (previous.headDepth policy))
  | .proof _ _ _ _ _ _ previous => previous.headDepth policy
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

def NativePlan.headDepth (policy : Name → Nat → Nat)
    (plan : NativePlan env U registry target signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ _ _ _ _ _ _ _ _ _ body captures =>
    max (body.headDepth policy) (captures.headDepth policy)
  | .binder _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

def FamilyCaptures.headDepth (policy : Name → Nat → Nat)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) : Nat :=
  match captures with
  | .nil => 0
  | .cons _ value _ _ _ tail => max (value.headDepth policy) (tail.headDepth policy)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

def FamilyPlan.headDepth (policy : Name → Nat → Nat)
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.headDepth policy
  | .binder _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .view source _ | .pad source => source.headDepth policy
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega
def ConstructorPlan.headDepth (policy : Name → Nat → Nat)
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures resultCode => max (captures.headDepth policy) (resultCode.headDepth policy)
  | .binder _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .view source _ | .pad source => source.headDepth policy
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end

mutual
theorem Obs.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (observation : Obs env U registry target locals σ expression demand footprint) : observation.headDepth policy = 0 := by
  match observation with
  | .delta (name := name) _ _ _ _ _ _ _ _ _ certificate _ body =>
    rw [Obs.headDepth]
    change policy name (max (body.headDepth policy) (certificate.headDepth policy)) = 0
    simp only [body.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .native (name := name) _ _ _ _ _ _ _ _ _ certificate _ tree =>
    rw [Obs.headDepth]
    change policy name (max (tree.headDepth policy) (certificate.headDepth policy)) = 0
    simp only [tree.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree
  | .constructor _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    rw [Obs.headDepth]
    change max (tree.headDepth policy) (certificate.headDepth policy) = 0
    simp only [tree.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .var .. | .empty | .sort .. => simp only [Obs.headDepth]
  | .app fn arg _ _ =>
    rw [Obs.headDepth]
    change max (fn.headDepth policy) (arg.headDepth policy) = 0
    simp only [fn.headDepth_zero policy zero, arg.headDepth_zero policy zero, Nat.max_self, zero]
  | .lam domain _ body _ _ =>
    rw [Obs.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .pi domain _ bodies =>
    rw [Obs.headDepth]
    change max (domain.headDepth policy) (bodies.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, bodies.headDepth_zero policy zero, Nat.max_self, zero]
  | .union left right =>
    rw [Obs.headDepth]
    change max (left.headDepth policy) (right.headDepth policy) = 0
    simp only [left.headDepth_zero policy zero, right.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source | .unpad source | .rowShift source =>
    rw [Obs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem CodeCert.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (certificate : CodeCert env U registry target locals σ expression demand footprint) : certificate.headDepth policy = 0 := by
  match certificate with
  | .seed observation _ =>
    rw [CodeCert.headDepth]
    change observation.headDepth policy = 0
    simp only [observation.headDepth_zero policy zero, Nat.max_self, zero]
  | .union left right =>
    rw [CodeCert.headDepth]
    change max (left.headDepth policy) (right.headDepth policy) = 0
    simp only [left.headDepth_zero policy zero, right.headDepth_zero policy zero, Nat.max_self, zero]
  | .pad source | .familyPad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ =>
    rw [CodeCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem PiRows.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint) : rows.headDepth policy = 0 := by
  match rows with
  | .nil => simp only [PiRows.headDepth]
  | .cons _ body _ _ tail =>
    rw [PiRows.headDepth]
    change max (body.headDepth policy) (tail.headDepth policy) = 0
    simp only [body.headDepth_zero policy zero, tail.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem NativeCaptures.headDepth_zero {index : Nat} (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (captures : NativeCaptures env U registry target program witnesses index required outside) : captures.headDepth policy = 0 := by
  match captures with
  | .prefix _ => simp only [NativeCaptures.headDepth]
  | .index natural _ declared _ _ _ _ _ _ _ _ _ previous =>
    rw [NativeCaptures.headDepth]
    change max (natural.headDepth policy) (max (declared.headDepth policy) (previous.headDepth policy)) = 0
    simp only [natural.headDepth_zero policy zero, declared.headDepth_zero policy zero, previous.headDepth_zero policy zero, Nat.max_self, zero]
  | .proof _ _ _ _ _ _ previous =>
    rw [NativeCaptures.headDepth]
    change previous.headDepth policy = 0
    simp only [previous.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf captures
decreasing_by all_goals simp_wf <;> omega

theorem NativePlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : NativePlan env U registry target signature arguments demand footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ _ _ _ _ _ _ _ _ _ body captures =>
    rw [NativePlan.headDepth]
    change max (body.headDepth policy) (captures.headDepth policy) = 0
    simp only [body.headDepth_zero policy zero, captures.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ domain _ body _ _ =>
    rw [NativePlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem FamilyCaptures.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) : captures.headDepth policy = 0 := by
  match captures with
  | .nil => simp only [FamilyCaptures.headDepth]
  | .cons _ value _ _ _ tail =>
    rw [FamilyCaptures.headDepth]
    change max (value.headDepth policy) (tail.headDepth policy) = 0
    simp only [value.headDepth_zero policy zero, tail.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf captures
decreasing_by all_goals simp_wf <;> omega

theorem FamilyPlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ captures =>
    rw [FamilyPlan.headDepth]
    change captures.headDepth policy = 0
    simp only [captures.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ domain _ body _ _ =>
    rw [FamilyPlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source =>
    rw [FamilyPlan.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem ConstructorPlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ captures resultCode =>
    rw [ConstructorPlan.headDepth]
    change max (captures.headDepth policy) (resultCode.headDepth policy) = 0
    simp only [captures.headDepth_zero policy zero, resultCode.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ domain _ body _ _ =>
    rw [ConstructorPlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source =>
    rw [ConstructorPlan.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

end

def Obs.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (observation : Obs env U registry target locals σ expression demand footprint) : Nat :=
  observation.headDepth (stratifiedHeadPolicy rank control)
def CodeCert.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (certificate : CodeCert env U registry target locals σ expression demand footprint) : Nat :=
  certificate.headDepth (stratifiedHeadPolicy rank control)
def PiRows.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint) : Nat :=
  rows.headDepth (stratifiedHeadPolicy rank control)
def NativeCaptures.stratifiedDepth {index : Nat} (rank : Name → Nat) (control : Nat)
    (captures : NativeCaptures env U registry target program witnesses index required outside) : Nat :=
  captures.headDepth (stratifiedHeadPolicy rank control)
def NativePlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : NativePlan env U registry target signature arguments demand footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)
def FamilyCaptures.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) : Nat :=
  captures.headDepth (stratifiedHeadPolicy rank control)
def FamilyPlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)
def ConstructorPlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)

theorem Obs.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (observation : Obs env U registry target locals σ expression demand footprint) : observation.stratifiedDepth rank control = 0 := by
  apply observation.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem CodeCert.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (certificate : CodeCert env U registry target locals σ expression demand footprint) : certificate.stratifiedDepth rank control = 0 := by
  apply certificate.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem PiRows.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint) : rows.stratifiedDepth rank control = 0 := by
  apply rows.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem NativeCaptures.stratifiedDepth_above {index : Nat} {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (captures : NativeCaptures env U registry target program witnesses index required outside) : captures.stratifiedDepth rank control = 0 := by
  apply captures.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem NativePlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : NativePlan env U registry target signature arguments demand footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem FamilyCaptures.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) : captures.stratifiedDepth rank control = 0 := by
  apply captures.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem FamilyPlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem ConstructorPlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

end Lean4Lean.AnchoredSource.Adapted
