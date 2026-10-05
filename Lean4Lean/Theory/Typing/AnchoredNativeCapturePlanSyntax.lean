import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Typing.NativeCaptureRoles
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Exact correspondence between the canonical capture plan and the pure
saturated program. Only the finite registered domain prefix is inspected;
unused substitution tails need not be identified. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem capture_append (values : List VExpr) (value : VExpr) :
    nativeCaptureSubst (values ++ [value]) = (nativeCaptureSubst values).cons value := by
  funext i
  cases i with
  | zero => simp [nativeCaptureSubst, Subst.cons]
  | succ i =>
    simp only [nativeCaptureSubst, List.length_append, List.length_singleton, Subst.cons]
    by_cases hi : i < values.length
    · rw [dif_pos (by omega), dif_pos hi, List.getElem_append_left (by omega)]
      congr 1 <;> omega
    · rw [dif_neg (by omega), dif_neg hi]
      congr 1 <;> omega

private theorem capture_map_lift (values : List VExpr) (i : Nat) (hi : i < values.length) :
    nativeCaptureSubst (values.map VExpr.lift) i = (nativeCaptureSubst values i).lift := by
  simp only [nativeCaptureSubst, List.length_map, dif_pos hi, List.getElem_map]

private theorem plan_added_length (plan : CapturePlan declared) (arguments : Subst) :
    (plan.added arguments).length = plan.count := by
  induction plan with
  | nil => rfl
  | index _ _ ih => exact ih
  | proof _ ih => exact congrArg (· + 1) ih

structure NativePlanMatches (arguments : Subst) {declared : List VExpr}
    (plan : CapturePlan declared) (state : SaturatedCaptureState) : Prop where
  added : state.added = plan.added arguments
  length : state.captures.length = declared.length
  captures : ∀ i < declared.length, nativeCaptureSubst state.captures i = plan.captures arguments i

theorem NativePlanMatches.index {indices : List VExpr} {slot position : Nat}
    (matched : NativePlanMatches arguments plan state)
    (selected : indices[slot]? = some (arguments position)) :
    NativePlanMatches arguments (CapturePlan.index (domain := domain) plan position)
      { state with captures := state.captures ++ [(arguments position).liftN state.added.length] } := by
  constructor
  · exact matched.added
  · simp [matched.length]
  · intro i hi
    rw [capture_append]
    cases i with
    | zero =>
      simp only [Subst.cons, CapturePlan.captures]
      rw [matched.added, plan_added_length]
    | succ i =>
      exact matched.captures i (by simpa using hi)

theorem NativePlanMatches.proof
    (matched : NativePlanMatches arguments plan state)
    (scope : domain.ClosedN state.captures.length) :
    NativePlanMatches arguments (CapturePlan.proof (domain := domain) plan)
      { added := instantiateParams domain state.captures :: state.added
        captures := state.captures.map VExpr.lift ++ [.bvar 0] } := by
  have domainEq : instantiateParams domain state.captures = domain.subst (plan.captures arguments) := by
    change domain.subst (nativeCaptureSubst state.captures) = _
    apply subst_congr_closedN scope
    intro i hi
    exact matched.captures i (matched.length ▸ hi)
  constructor
  · simp only [CapturePlan.added, domainEq, matched.added]
  · simp [matched.length]
  · intro i hi
    rw [capture_append]
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Subst.cons, CapturePlan.captures]
      rw [capture_map_lift _ i (by rw [matched.length]; simpa using hi),
        matched.captures i (by simpa using hi)]
      rfl

/-- Each exact registered field domain is scoped over the preceding
captures. This is the finite syntax consequence of its retained formation. -/
inductive NativeInstructionsScoped : Nat → List CaptureInstruction → Prop where
  | nil : NativeInstructionsScoped count []
  | cons : instruction.domain.ClosedN count → NativeInstructionsScoped (count + 1) rest →
      NativeInstructionsScoped count (instruction :: rest)

/-- A successful pure run extends the same exact capture plan. Slot lookup
is related to the full native-variable numbering explicitly; no typing,
semantic closure, or reconstructed-head equality is assumed. -/
theorem SaturatedCaptureState.run_plan_roles
    {arguments : Subst} {declared : List VExpr} {plan : CapturePlan declared}
    {state final : SaturatedCaptureState} {indices : List VExpr}
    {instructions : List CaptureInstruction}
    (matched : NativePlanMatches arguments plan state)
    (scope : NativeInstructionsScoped state.captures.length instructions)
    (position : Nat → Nat)
    (selectors : ∀ slot value, indices[slot]? = some value → arguments (position slot) = value)
    (run : state.run indices instructions = some final) :
    ∃ (resultContext : List VExpr) (resultPlan : CapturePlan resultContext),
      resultContext = (instructions.map CaptureInstruction.domain).reverse ++ declared ∧
      NativePlanMatches arguments resultPlan final ∧
      resultPlan.roles = plan.roles ++ instructions.map (fun instruction =>
        match instruction with | .index _ slot => some (position slot) | .proof _ => none) := by
  induction instructions generalizing declared state plan with
  | nil =>
    cases Option.some.inj run
    exact ⟨declared, plan, rfl, matched, by simp⟩
  | cons instruction rest ih =>
    cases scope with
    | cons domainScope restScope =>
      simp only [SaturatedCaptureState.run, bind, Option.bind_eq_some_iff] at run
      obtain ⟨next, step, run⟩ := run
      cases instruction with
      | index domain slot =>
        simp only [SaturatedCaptureState.step, bind, Option.bind_eq_some_iff] at step
        obtain ⟨value, selected, he⟩ := step
        cases he
        have hv := selectors slot value selected
        subst value
        obtain ⟨ctx, nextPlan, hc, hm, roles⟩ := ih (matched.index selected)
          (by simpa using restScope) run
        refine ⟨ctx, nextPlan, ?_, hm, ?_⟩
        · simpa only [List.map_cons, CaptureInstruction.domain, List.reverse_cons,
            List.append_assoc, List.singleton_append] using hc
        · simpa only [CapturePlan.roles, List.map_cons, List.append_assoc,
            List.singleton_append] using roles
      | proof domain =>
        simp only [SaturatedCaptureState.step, Option.some.injEq] at step
        cases step
        obtain ⟨ctx, nextPlan, hc, hm, roles⟩ := ih (matched.proof domainScope)
          (by simpa using restScope) run
        refine ⟨ctx, nextPlan, ?_, hm, ?_⟩
        · simpa only [List.map_cons, CaptureInstruction.domain, List.reverse_cons,
            List.append_assoc, List.singleton_append] using hc
        · simpa only [CapturePlan.roles, List.map_cons, List.append_assoc,
            List.singleton_append] using roles

theorem SaturatedCaptureState.run_plan
    {arguments : Subst} {declared : List VExpr} {plan : CapturePlan declared}
    {state final : SaturatedCaptureState} {indices : List VExpr}
    {instructions : List CaptureInstruction}
    (matched : NativePlanMatches arguments plan state)
    (scope : NativeInstructionsScoped state.captures.length instructions)
    (position : Nat → Nat)
    (selectors : ∀ slot value, indices[slot]? = some value → arguments (position slot) = value)
    (run : state.run indices instructions = some final) :
    ∃ (resultContext : List VExpr) (resultPlan : CapturePlan resultContext),
      resultContext = (instructions.map CaptureInstruction.domain).reverse ++ declared ∧
      NativePlanMatches arguments resultPlan final := by
  obtain ⟨context, resultPlan, contextEq, matched, _⟩ :=
    SaturatedCaptureState.run_plan_roles matched scope position selectors run
  exact ⟨context, resultPlan, contextEq, matched⟩

end Lean4Lean.AnchoredSource.Adapted
