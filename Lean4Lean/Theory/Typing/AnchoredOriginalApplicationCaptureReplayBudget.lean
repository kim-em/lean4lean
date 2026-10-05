import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationBody
import Lean4Lean.Theory.Typing.AnchoredSortableScope

/-! A used captured demand rules out the sole unit-weight original source
shape: a literal universe. Consequently the existing application reserve
also pays for replay of a returned capture owner to its original argument. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

mutual
theorem RichCert.sortScoped
    {node : EndpointState sourceEnv U source (.sort level) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    Footprint.Scoped 0 footprint := by
  match query with
  | .legacy source => exact source.scoped trivial
  | .observe source _ => exact source.sortScoped
  | .route _ source | .pad source | .down source | .map _ source | .support _ source | .select source _ =>
    exact source.sortScoped
  | .union left right => exact Footprint.Scoped.append left.sortScoped right.sortScoped
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.sortScoped
    {node : EndpointState sourceEnv U source (.sort level) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint) :
    Footprint.Scoped 0 footprint := by
  match query with
  | .legacy source => exact source.scoped trivial
  | .code source => exact source.sortScoped
  | .route _ source | .view source _ | .action source _ | .select source _ | .pad source | .unpad source =>
    exact source.sortScoped
  | .union left right => exact Footprint.Scoped.append left.sortScoped right.sortScoped
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega
end

private theorem rule_two (first : Origin) (rest : List Origin) :
    2 ≤ (Origin.rule (first :: rest)).weight := by
  have positive := first.weight_pos
  simp only [Origin.weight, List.map_cons, List.sum_cons]
  omega

private theorem binder_two (domain : Origin) (bodies rest : List Origin) :
    2 ≤ (Origin.binder domain bodies rest).weight := by
  simp only [Origin.weight]
  omega

theorem Derivation.dependency_small_sorts
    (ordered : sourceEnv.Ordered)
    (original : Derivation sourceEnv U source left right assigned)
    (small : (original.dependencyOrigin ordered).weight < 2) :
    ∃ leftLevel rightLevel, left = .sort leftLevel ∧ right = .sort rightLevel := by
  cases original
  case sortDF => exact ⟨_, _, rfl, rfl⟩
  all_goals
    exfalso
    apply Nat.not_le_of_lt small
    rw [Derivation.dependencyOrigin.eq_def]
    first | exact rule_two _ _ | exact binder_two _ _ _

theorem EndpointState.dependency_small_sort
    (ordered : sourceEnv.Ordered)
    (node : EndpointState sourceEnv U source expression assigned)
    (small : (node.dependencyOrigin ordered).weight < 2) :
    ∃ level, expression = .sort level := by
  cases node with
  | ref reference =>
    cases reference with
    | left original =>
      obtain ⟨leftLevel, rightLevel, leftEq, rightEq⟩ := Derivation.dependency_small_sorts ordered original small
      exact ⟨leftLevel, leftEq⟩
    | right original =>
      obtain ⟨leftLevel, rightLevel, leftEq, rightEq⟩ := Derivation.dependency_small_sorts ordered original small
      exact ⟨rightLevel, rightEq⟩
  | sort => exact ⟨_, rfl⟩
  | bvar | proj | convert =>
    exfalso
    exact Nat.not_le_of_lt small (rule_two _ _)
  | lam | pi =>
    exfalso
    exact Nat.not_le_of_lt small (binder_two _ _ _)
  | app =>
    exfalso
    apply Nat.not_le_of_lt small
    simp only [EndpointState.dependencyOrigin, capturedApplicationOrigin, Origin.weight]
    omega

/-- This bound uses a real queried footprint occurrence, not surplus values
in a generated frame. In particular an unqueried sort does not consume a
capture replay budget. -/
theorem RichCert.usedFootprint_weight
    {node : EndpointState sourceEnv U source expression assigned}
    (ordered : sourceEnv.Ordered)
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (member : (index, need) ∈ footprint) :
    2 ≤ (node.dependencyOrigin ordered).weight := by
  by_cases used : 2 ≤ (node.dependencyOrigin ordered).weight
  · exact used
  have small : (node.dependencyOrigin ordered).weight < 2 := by omega
  obtain ⟨level, same⟩ := EndpointState.dependency_small_sort ordered node small
  subst expression
  have impossible := query.sortScoped index need member
  omega

/-- Any returned owner closure below the captured-body frame budget can
be compared to the original argument, once an actual body demand is used.
The application origin already contains the necessary product reserve. -/
theorem application_capture_cost_replay_schedule
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (query : RichCert sourceEnv env U registry target body locals σ relevant profile footprint)
    (member : (index, need) ∈ footprint)
    (previous : List Closure) (ownerCost : Nat)
    (ownerBound : ownerCost ≤ environmentCost
      (Closure.bundle (.close (argument.dependencyOrigin ordered) previous)
        (.close (domain.dependencyOrigin ordered) previous) :: previous)) :
    richSchedule .expressionReindex
      (ownerCost + (Closure.close (argument.dependencyOrigin ordered) previous).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        previous).cost := by
  have used := query.usedFootprint_weight ordered member
  have argPositive := (argument.dependencyOrigin ordered).weight_pos
  have domPositive := (domain.dependencyOrigin ordered).weight_pos
  have product : 2 * (1 + (argument.dependencyOrigin ordered).weight + (domain.dependencyOrigin ordered).weight) ≤
      (body.dependencyOrigin ordered).weight *
        (1 + (argument.dependencyOrigin ordered).weight + (domain.dependencyOrigin ordered).weight) :=
    Nat.mul_le_mul_right _ used
  have coefficient :
      2 * (argument.dependencyOrigin ordered).weight + (domain.dependencyOrigin ordered).weight <
      ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered).weight := by
    simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, capturedApplicationOrigin, Origin.weight] at *
    omega
  have previousBound : environmentCost previous ≤
      (Closure.close (argument.dependencyOrigin ordered) previous).cost +
      (Closure.close (domain.dependencyOrigin ordered) previous).cost := by
    have first : 1 + environmentCost previous ≤
        (Closure.close (argument.dependencyOrigin ordered) previous).cost :=
      Nat.le_mul_of_pos_left _ argPositive
    omega
  have ownerBound' : ownerCost ≤
      (Closure.close (argument.dependencyOrigin ordered) previous).cost +
      (Closure.close (domain.dependencyOrigin ordered) previous).cost := by
    change ownerCost ≤ max ((Closure.close (argument.dependencyOrigin ordered) previous).cost +
      (Closure.close (domain.dependencyOrigin ordered) previous).cost) (environmentCost previous) at ownerBound
    rwa [Nat.max_eq_left previousBound] at ownerBound
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right ownerBound' _)
  have scaled := Nat.mul_lt_mul_of_pos_right coefficient (Nat.zero_lt_succ (environmentCost previous))
  simpa only [Closure.cost, Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_one,
    Nat.mul_comm 2, Nat.mul_two, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scaled

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
