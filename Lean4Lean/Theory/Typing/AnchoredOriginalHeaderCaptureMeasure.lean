import Lean4Lean.Theory.Typing.AnchoredOriginalEndpointFactor

/-! A finite bound for earlier-header replay with captures at actual current
field/major descendants. Domain formations are retained original header
locations; repeated lookup may re-enter captures but cannot exceed the same
finite environment reserve. No production origin measure is changed here.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure LocatedOrigin (root : EndpointRef env U source expression assigned) where
  context : List VExpr
  expression : VExpr
  assigned : VExpr
  node : EndpointState env U context expression assigned
  location : Located root node

def LocatedOrigin.closure (entry : LocatedOrigin root) (initial : List Closure) : Closure :=
  .close entry.node.origin (entry.location.environment initial)

theorem LocatedOrigin.cost_le (entry : LocatedOrigin root) (initial : List Closure) :
    (entry.closure initial).cost ≤ (Closure.close root.origin initial).cost := entry.location.cost_le initial

theorem LocatedOrigin.weight_le (entry : LocatedOrigin root) : entry.node.origin.weight ≤ root.origin.weight := by
  have h := entry.cost_le []
  have low : entry.node.origin.weight ≤ (entry.closure []).cost := by
    change _ ≤ entry.node.origin.weight * (1 + environmentCost _)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left entry.node.origin.weight
      (show 1 ≤ 1 + environmentCost (entry.location.environment []) by omega)
  exact Nat.le_trans low (by simpa only [Closure.cost, environmentCost, Nat.add_zero, Nat.mul_one] using h)

structure HeaderCaptureStep
    (header : EndpointRef headerEnv U headerSource headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType) where
  domain : LocatedOrigin header
  argument : Option (Sum (LocatedOrigin field) (LocatedOrigin major))

def HeaderCaptureStep.argumentClosure (step : HeaderCaptureStep header field major)
    (initial : List Closure) : Option Closure :=
  match step.argument with
  | none => none
  | some (.inl entry) => some (entry.closure initial)
  | some (.inr entry) => some (entry.closure initial)

theorem HeaderCaptureStep.argument_bound (step : HeaderCaptureStep header field major)
    (initial : List Closure) :
    ((step.argumentClosure initial).map Closure.cost).getD 0 ≤
      (field.origin.weight + major.origin.weight) * (1 + environmentCost initial) := by
  cases eq : step.argument with
  | none => simp [argumentClosure, eq]
  | some argument =>
    cases argument with
    | inl entry =>
      simp only [argumentClosure, eq, Option.map_some, Option.getD_some]
      exact Nat.le_trans (entry.cost_le initial)
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    | inr entry =>
      simp only [argumentClosure, eq, Option.map_some, Option.getD_some]
      exact Nat.le_trans (entry.cost_le initial)
        (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

def headerCaptureEnvironment
    (steps : List (HeaderCaptureStep header field major)) (initial : List Closure) : List Closure :=
  match steps with
  | [] => []
  | step :: rest =>
    let previous := headerCaptureEnvironment rest initial
    match step.argumentClosure initial with
    | none => .close step.domain.node.origin previous :: previous
    | some argument => .bundle argument (.close step.domain.node.origin previous) :: previous

def headerCaptureReserve (headerWeight fieldWeight majorWeight count : Nat) : Nat :=
  (headerWeight + 2) ^ count * (1 + fieldWeight + majorWeight)

theorem headerCaptureReserve_positive : 0 < headerCaptureReserve h f m count := by
  unfold headerCaptureReserve
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)

theorem headerCaptureReserve_base_le : f + m ≤ headerCaptureReserve h f m count := by
  have power : 1 ≤ (h + 2) ^ count := Nat.pow_pos (by omega)
  have bound := Nat.mul_le_mul_right (1 + f + m) power
  simp only [Nat.one_mul] at bound
  exact Nat.le_trans (by omega) bound

theorem headerCaptureEnvironment_bound
    (steps : List (HeaderCaptureStep header field major)) (initial : List Closure) :
    1 + environmentCost (headerCaptureEnvironment steps initial) ≤
      headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight steps.length *
        (1 + environmentCost initial) := by
  induction steps with
  | nil =>
    simp only [headerCaptureEnvironment, environmentCost, List.length_nil, headerCaptureReserve,
      Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  | cons step rest ih =>
    let R := headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight rest.length
    let S := 1 + environmentCost initial
    have positive : 1 ≤ R * S := Nat.mul_pos headerCaptureReserve_positive (by dsimp [S]; omega)
    have argBound : ((step.argumentClosure initial).map Closure.cost).getD 0 ≤ R * S :=
      Nat.le_trans (step.argument_bound initial) (Nat.mul_le_mul_right S headerCaptureReserve_base_le)
    have domainBound : (Closure.close step.domain.node.origin (headerCaptureEnvironment rest initial)).cost ≤
        header.origin.weight * (R * S) :=
      Nat.mul_le_mul step.domain.weight_le ih
    change 1 + environmentCost (headerCaptureEnvironment rest initial) ≤ R * S at ih
    have previousBound : environmentCost (headerCaptureEnvironment rest initial) ≤ R * S := by omega
    have joined : 1 + max (((step.argumentClosure initial).map Closure.cost).getD 0 +
        (Closure.close step.domain.node.origin (headerCaptureEnvironment rest initial)).cost)
        (environmentCost (headerCaptureEnvironment rest initial)) ≤
        (header.origin.weight + 2) * (R * S) := by
      rw [Nat.add_mul, Nat.two_mul]
      omega
    cases eq : step.argumentClosure initial <;>
      simpa only [headerCaptureEnvironment, eq, environmentCost, Closure.cost, List.length_cons,
        Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, Nat.zero_add,
        headerCaptureReserve, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, R, S] using joined

/-- Both sides of header reindex, including all repeated capture lookups,
fit this explicit finite original-data reserve. -/
theorem header_reindex_pair_bound
    (steps : List (HeaderCaptureStep header field major))
    (selectedHeader : LocatedOrigin header) (selectedField : LocatedOrigin field)
    (initial : List Closure) :
    (selectedField.closure initial).cost +
      (Closure.close selectedHeader.node.origin (headerCaptureEnvironment steps initial)).cost ≤
    (field.origin.weight + header.origin.weight *
      headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight steps.length) *
        (1 + environmentCost initial) := by
  have h := Nat.mul_le_mul selectedHeader.weight_le (headerCaptureEnvironment_bound steps initial)
  have sum := Nat.add_le_add (selectedField.cost_le initial) h
  simpa only [Closure.cost, Nat.add_mul, Nat.mul_assoc] using sum

/-- A concrete strict projection reserve for this exact finite prefix.
The count is the original declaration prefix length, not query-tree size. -/
theorem header_reindex_strict_reserve
    (steps : List (HeaderCaptureStep header field major))
    (selectedHeader : LocatedOrigin header) (selectedField : LocatedOrigin field)
    (initial : List Closure) :
    schedule .coherence
      ((selectedField.closure initial).cost +
       (Closure.close selectedHeader.node.origin (headerCaptureEnvironment steps initial)).cost) <
    schedule .fundamental
      ((1 + field.origin.weight + major.origin.weight + header.origin.weight *
        headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight steps.length) *
          (1 + environmentCost initial)) := by
  apply schedule_strict
  apply Nat.lt_of_le_of_lt (header_reindex_pair_bound steps selectedHeader selectedField initial)
  apply Nat.mul_lt_mul_of_pos_right
  · omega
  · omega

/-- Header lookup may re-enter a current-source argument. Its full captured
closure and the original header-domain formation together are already below
the lookup closure, without any declaration-stage comparison. -/
theorem header_capture_head_lookup
    (step : HeaderCaptureStep header field major)
    (rest : List (HeaderCaptureStep header field major))
    (initial : List Closure) (lookupOrigin : Origin) :
    ((step.argumentClosure initial).map Closure.cost).getD 0 +
      (Closure.close step.domain.node.origin (headerCaptureEnvironment rest initial)).cost <
    (Closure.close lookupOrigin (headerCaptureEnvironment (step :: rest) initial)).cost := by
  cases eq : step.argumentClosure initial with
  | none =>
    simpa only [headerCaptureEnvironment, eq, Option.map_none, Option.getD_none, Nat.zero_add] using
      (variable_lookup lookupOrigin (List.mem_cons_self :
        Closure.close step.domain.node.origin (headerCaptureEnvironment rest initial) ∈
        _ :: headerCaptureEnvironment rest initial))
  | some argument =>
    simpa only [headerCaptureEnvironment, eq, Option.map_some, Option.getD_some, Closure.cost] using
      (variable_lookup lookupOrigin (List.mem_cons_self :
        Closure.bundle argument (.close step.domain.node.origin (headerCaptureEnvironment rest initial)) ∈
        _ :: headerCaptureEnvironment rest initial))

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
