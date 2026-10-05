import Lean4Lean.Theory.Typing.AnchoredNativeCaptureAgreement
import Lean4Lean.Theory.Typing.AnchoredNativeForwardLevels

/-! Routed data fields are literal variables of the original equation.
Their finite agreement survives both a universe packet change and the caller's
actual realization; arbitrary proof witnesses stay unrestricted. -/
namespace Lean4Lean.VEnv.CapturePlan
open VExpr

theorem IndexAgreement.role {index position : Nat} {plan : CapturePlan declared}
    (agree : plan.IndexAgreement arguments witnesses)
    (selected : plan.roles.reverse[index]? = some (some position)) :
    witnesses index = arguments position := by
  induction plan generalizing witnesses index with
  | nil => cases selected
  | index previous copied ih =>
    cases index with
    | zero =>
      simp only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      exact agree.2
    | succ index =>
      apply ih agree.1
      simpa only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.getElem?_cons_succ] using selected
  | proof previous ih =>
    cases index with
    | zero => simp [roles] at selected
    | succ index =>
      apply ih agree
      simpa only [roles, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.getElem?_cons_succ] using selected

theorem IndexAgreement.witnesses {plan : CapturePlan declared}
    (agree : plan.IndexAgreement arguments first)
    (same : ∀ i < declared.length, first i = second i) :
    plan.IndexAgreement arguments second := by
  apply plan.indexAgreement_of_roles
  intro i position selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.length_reverse, roles_length] at bound
  rw [← same i bound]
  exact agree.role selected

end Lean4Lean.VEnv.CapturePlan

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem prefix_role_bound (offset : Nat) (domains : List VExpr)
    (member : some position ∈ (nativePrefixPlan offset domains).roles) :
    position < offset + domains.length := by
  induction domains generalizing offset with
  | nil => cases member
  | cons domain rest ih =>
    rcases List.mem_append.mp member with before | last
    · have h := ih (offset + 1) before
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · have same := List.mem_singleton.mp last
      cases same
      simp

/-- Every copied slot is an actual native argument, including the fixed
parameter/motive/minor prefix. -/
theorem NativeSupportedReplay.rolesBound
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (member : some position ∈ plan.roles) : position < argumentSource.length := by
  induction replay with
  | nil => cases member
  | commonPrefix source literal count added captures =>
    rw [literal] at member
    have h := prefix_role_bound _ _ member
    simpa only [source, List.length_append] using h
  | index previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    rcases List.mem_append.mp member with before | last
    · exact ih before
    · cases List.mem_singleton.mp last
      exact lookup.lt
  | proof previous formation inhabitant localNeeds n bounded empty ih =>
    rcases List.mem_append.mp member with before | last
    · exact ih before
    · cases List.mem_singleton.mp last

private theorem capture_relevel {first second : List VExpr}
    (equal : List.Forall₂ (EqUpToLevels U) first second)
    (bound : position < first.length) :
    EqUpToLevels U (nativeCaptureSubst first position) (nativeCaptureSubst second position) := by
  have lengths : first.length = second.length := by clear bound; induction equal <;> simp_all
  have next : position < second.length := by rw [← lengths]; exact bound
  simp only [nativeCaptureSubst, dif_pos bound, dif_pos next]
  have value := Lean4Lean.List.Forall₂.getElem_of equal (first.length - 1 - position)
    (by omega) (by rw [← lengths]; omega)
  simpa only [lengths] using value

/-- A variable-only capture agreement is independent of equivalent universe
syntax in the unused or computed native arguments. -/
theorem NativeSupportedReplay.agreementLevels
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    {first second : List VExpr} (length : first.length = argumentSource.length)
    (equal : List.Forall₂ (EqUpToLevels U) first second)
    (agree : plan.IndexAgreement (nativeCaptureSubst first) .id) :
    plan.IndexAgreement (nativeCaptureSubst second) .id := by
  apply plan.indexAgreement_of_roles
  intro i position selected
  have membership : some position ∈ plan.roles := List.mem_reverse.mp
    (List.mem_of_getElem? selected)
  have bound : position < first.length := by rw [length]; exact replay.rolesBound membership
  have h := capture_relevel equal bound
  rw [← agree.role selected] at h
  have literal : ∀ {e : VExpr}, EqUpToLevels U (.bvar i) e → e = .bvar i := by
    intro e same
    cases same
    rfl
  exact (literal h).symm

/-- Realize the same original field variables in the caller target context. -/
theorem NativeSupportedReplay.agreementRealized
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    {first : List VExpr} (length : first.length = argumentSource.length)
    (agree : plan.IndexAgreement (nativeCaptureSubst first) .id) (σ : Subst) :
    plan.IndexAgreement (nativeCaptureSubst (first.map (·.subst σ))) σ := by
  apply plan.indexAgreement_of_roles
  intro i position selected
  have membership : some position ∈ plan.roles := List.mem_reverse.mp
    (List.mem_of_getElem? selected)
  have bound : position < first.length := by rw [length]; exact replay.rolesBound membership
  have equality := congrArg (·.subst σ) (agree.role selected)
  simpa only [Subst.id, subst_bvar, nativeCaptureSubst, dif_pos bound,
    List.length_map, List.getElem_map] using equality

end Lean4Lean.AnchoredSource.Adapted
