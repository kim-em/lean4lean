import Lean4Lean.Theory.Typing.AnchoredNativeChosenReplay
import Lean4Lean.Theory.Typing.AnchoredNativeInitialTerminal
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupportReplay

/-! Literal capture agreement comes from the finite original field origins.
It applies to every replay carrying the same generated ordered roles. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem NativeCaptureOrigins.indexOccurrences
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (origins : NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments count)
    {field slot : Nat} {domain : VExpr} (bound : field < count)
    (instruction : program.instructions[field]? = some (.index domain slot)) :
    ∃ expression, nativeArguments[data.indexOffset + slot]? = some expression ∧
      captureArguments[data.indexOffset + field]? = some expression := by
  induction origins with
  | «prefix» same enough => omega
  | @index templates index declared nativeOccurrence captureOccurrence lookup
      declaredOrigin declaredScope previous ih =>
    by_cases before : field < templates.field
    · exact ih before
    · have same : field = templates.field := by omega
      subst field
      have selected := templates.declaredOrigin
      rw [instruction] at selected
      cases selected
      exact ⟨_, nativeOccurrence, captureOccurrence⟩
  | @proof field' argument proposition domain' selected captureOccurrence originalProposition
      originalArgument sourceProof propositionOrigin domainScope previous ih =>
    have before : field < field' := by
      by_cases h : field < field'
      · exact h
      have same : field = field' := by omega
      subst field
      rw [instruction] at selected
      cases selected
    exact ih before

private theorem prefix_roles (offset : Nat) (domains : List VExpr) :
    (nativePrefixPlan offset domains).roles =
      (List.range domains.length).map (fun i => some (offset + domains.length - 1 - i)) := by
  induction domains generalizing offset with
  | nil => rfl
  | cons A rest ih =>
    simp only [nativePrefixPlan, CapturePlan.roles, ih, List.length_cons, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      congr 1
      omega
    · congr 2
      omega

private theorem capture_at {values : List VExpr} {index : Nat} {value : VExpr}
    (atIndex : values[index]? = some value) :
    nativeCaptureSubst values (values.length - 1 - index) = value := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp atIndex
  rw [nativeCaptureSubst, dif_pos (by omega)]
  have indexEq : values.length - 1 - (values.length - 1 - index) = index := by omega
  simpa only [indexEq] using same

/-- Every data choice of an actual supported replay agrees with the original
constructor-equation fields. Proof witnesses impose no agreement condition. -/
theorem NativeCaptureOrigins.indexAgreement
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {source : List VExpr} {nativeArguments captureArguments : List VExpr} {count : Nat}
    (origins : NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments count)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (nativeLength : nativeArguments.length = program.prefixArgs.length)
    (captureLength : data.indexOffset + count ≤ captureArguments.length)
    {witnesses : List VExpr} {available : Valuation} {required : Footprint}
    (result : NativeCaptureReplayResult sourceEnv env U registry target program signature
      witnesses available count required) (σ : Subst) :
    result.plan.IndexAgreement (nativeCaptureSubst (nativeArguments.map (·.subst σ)))
      (nativeCaptureSubst ((captureArguments.take (data.indexOffset + count)).map (·.subst σ))) := by
  have spec := saturatedProgram_spec selected
  have domainLength : signature.domains.length = program.prefixArgs.length :=
    (takeForalls_length signature.telescope).trans spec.2.2.1.symm
  have offsetBound : data.indexOffset ≤ signature.domains.length := by
    rw [domainLength, spec.2.2.1, majorOffset]
    omega
  have prefixLength : (signature.domains.take data.indexOffset).reverse.length = data.indexOffset := by
    simp only [List.length_reverse, List.length_take, Nat.min_eq_left offsetBound]
  have roles := result.roles
  rw [nativeCaptureRoles, prefix_roles, prefixLength] at roles
  have roleLength := result.plan.roles_length
  have fieldsBound : count ≤ program.instructions.length := by
    have captureCount := initialCaptureLength selected
    have domainsLength : ((program.equationBody.domains.take (data.indexOffset + count)).map
        (·.instL program.levels)).reverse.length = data.indexOffset + count := by
      have bound : count ≤ program.instructions.length := by
        induction origins with
        | «prefix» => omega
        | @index templates _ _ _ _ _ _ _ _ ih =>
          have h := (List.getElem?_eq_some_iff.mp templates.declaredOrigin).1
          omega
        | @proof field _ _ _ instruction _ _ _ _ _ _ _ ih =>
          have h := (List.getElem?_eq_some_iff.mp instruction).1
          omega
      simp only [List.length_reverse, List.length_map, List.length_take,
        Nat.min_eq_left (by omega : data.indexOffset + count ≤ program.equationBody.domains.length)]
    rw [domainsLength] at roleLength
    rw [roles] at roleLength
    simp only [List.length_append, List.length_map, List.length_range, List.length_take] at roleLength
    omega
  have rolesLength : result.plan.roles.length = data.indexOffset + count := by
    rw [roles]
    simp only [List.length_append, List.length_map, List.length_range, List.length_take,
      Nat.min_eq_left fieldsBound]
  apply result.plan.indexAgreement_of_roles
  intro i position occurrence
  obtain ⟨iBound, atReverse⟩ := List.getElem?_eq_some_iff.mp occurrence
  have forwardBound : result.plan.roles.length - 1 - i < result.plan.roles.length := by
    simp only [List.length_reverse] at iBound
    omega
  have atForward : result.plan.roles[result.plan.roles.length - 1 - i]? = some (some position) := by
    rw [List.getElem?_eq_getElem forwardBound]
    simpa only [List.getElem_reverse] using congrArg some atReverse
  let index := data.indexOffset + count - 1 - i
  have indexBound : index < data.indexOffset + count := by
    dsimp [index]
    simp only [List.length_reverse, rolesLength] at iBound
    omega
  rw [rolesLength] at atForward
  have atRole : result.plan.roles[index]? = some (some position) := atForward
  rw [roles] at atRole
  have valueIndex : (captureArguments.take (data.indexOffset + count)).length = data.indexOffset + count :=
    List.length_take_of_le captureLength
  have realizeAt {expression : VExpr}
      (cap : captureArguments[index]? = some expression)
      {nativeIndex : Nat} (arg : nativeArguments[nativeIndex]? = some expression)
      (positionEq : position = nativeArguments.length - 1 - nativeIndex) :
      nativeCaptureSubst (List.map (fun x => x.subst σ) (List.take (data.indexOffset + count) captureArguments)) i =
        nativeCaptureSubst (List.map (fun x => x.subst σ) nativeArguments) position := by
    have cap' : ((captureArguments.take (data.indexOffset + count)).map (·.subst σ))[index]? =
        some (expression.subst σ) := by
      rw [List.getElem?_map, List.getElem?_take, if_pos indexBound, cap]
      rfl
    have arg' := congrArg (Option.map (·.subst σ)) arg
    rw [← List.getElem?_map] at arg'
    have left := capture_at cap'
    have right := capture_at arg'
    have leftIndex : ((captureArguments.take (data.indexOffset + count)).map (·.subst σ)).length - 1 - index = i := by
      simp only [List.length_map, valueIndex]
      dsimp [index]
      simp only [List.length_reverse, rolesLength] at iBound
      omega
    rw [leftIndex] at left
    rw [positionEq, ← List.length_map (f := fun e : VExpr => e.subst σ) (as := nativeArguments)]
    exact left.trans right.symm
  by_cases inPrefix : index < data.indexOffset
  · rw [List.getElem?_append_left (by simpa only [List.length_map, List.length_range] using inPrefix),
      List.getElem?_map, List.getElem?_range inPrefix] at atRole
    simp only [Option.map_some, Option.some.injEq] at atRole
    have enough := origins.prefix_eq
    have capBound : index < captureArguments.length := by omega
    have argBound : index < nativeArguments.length := by rw [nativeLength]; omega
    have same := congrArg (fun es : List VExpr => es[index]?) enough
    simp only [List.getElem?_take, if_pos inPrefix] at same
    apply realizeAt (List.getElem?_eq_getElem capBound)
      (same.symm.trans (List.getElem?_eq_getElem capBound))
    rw [← atRole, nativeLength]
    omega
  · rw [List.getElem?_append_right (by simpa only [List.length_map, List.length_range] using Nat.le_of_not_gt inPrefix)] at atRole
    simp only [List.length_map, List.length_range] at atRole
    rw [List.getElem?_map, List.getElem?_take, if_pos (by omega)] at atRole
    cases hInstruction : program.instructions[index - data.indexOffset]? with
    | none => simp only [hInstruction, Option.map_none] at atRole; contradiction
    | some chosen =>
      cases chosen with
      | proof domain => simp only [hInstruction, Option.map_some] at atRole; cases atRole
      | index domain slot =>
        simp only [hInstruction, Option.map_some, Option.some.injEq] at atRole
        obtain ⟨expression, arg, cap⟩ := origins.indexOccurrences (by omega) hInstruction
        have sum : data.indexOffset + (index - data.indexOffset) = index := by omega
        rw [sum] at cap
        apply realizeAt cap arg
        simpa only [nativeLength] using atRole.symm

end Lean4Lean.AnchoredSource.Adapted
