import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Iterated source binders, including their exact local positions. -/
def pushedLocals : Nat → List Nat → List Nat
  | 0, locals => locals
  | n + 1, locals => Locals.push (pushedLocals n locals)

/-- Keep the selected binder itself while peeling its entire preceding prefix. -/
theorem OriginalRichFrame.focusLocation
    {context : ContextDerivation sourceEnv U source}
    {tailContext : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tailContext domain)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available) :
    ∃ focusedLocals,
      ∃ focused : OriginalRichFrame sourceEnv env U registry target (.cons tailContext domain) focusedLocals
        (fun i => left (i + location.prefix.length)) (fun i => right (i + location.prefix.length))
        (fun i => available (i + location.prefix.length)),
      pushedLocals location.prefix.length focusedLocals = locals ∧
      ∀ ordered, environmentCost (focused.dependencyEnvironment ordered) ≤
        environmentCost (frame.dependencyEnvironment ordered) := by
  induction location generalizing locals left right available with
  | here => exact ⟨locals, frame, rfl, fun _ => Nat.le_refl _⟩
  | @there source context tailSource tailContext A level domain B otherLevel newDomain location ih =>
    obtain ⟨suffix, bound⟩ := frame.peelMeasured
    obtain ⟨focusedLocals, focused, positions, focusedBound⟩ := ih suffix.frame
    have previousBound : ∀ ordered, environmentCost (suffix.frame.dependencyEnvironment ordered) ≤
        environmentCost (frame.dependencyEnvironment ordered) := by
      intro ordered
      have positive := (newDomain.dependencyOrigin ordered).weight_pos
      have le := bound ordered
      simp only [Closure.cost] at le
      have reserve := Nat.mul_le_mul_right (1 + environmentCost (suffix.frame.dependencyEnvironment ordered)) positive
      omega
    have positions' := (congrArg Locals.push positions).trans suffix.positions
    have bound' := fun ordered => Nat.le_trans (focusedBound ordered) (previousBound ordered)
    have answer : ∃ f : OriginalRichFrame sourceEnv env U registry target (.cons tailContext domain) focusedLocals
          (fun i => left (i + location.prefix.length + 1))
          (fun i => right (i + location.prefix.length + 1))
          (fun i => available (i + location.prefix.length + 1)),
        Locals.push (pushedLocals location.prefix.length focusedLocals) = locals ∧
          ∀ ordered, environmentCost (f.dependencyEnvironment ordered) ≤
            environmentCost (frame.dependencyEnvironment ordered) := ⟨focused, positions', bound'⟩
    have shift {α : Sort _} (f : Nat → α) :
        (fun i => f (i + location.prefix.length + 1)) =
        (fun i => f (i + (location.prefix.length + 1))) := by
      funext i
      congr 1
    rw [shift left, shift right, shift available] at answer
    exact ⟨focusedLocals, answer⟩

/-- A full resource suffix at an actual retained original context location. -/
theorem OriginalRichFrame.fullSuffix
    {context : ContextDerivation sourceEnv U source}
    {tailContext : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tailContext domain)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available) :
    ∃ tailLocals,
      ∃ tailFrame : OriginalRichFrame sourceEnv env U registry target tailContext tailLocals
        (fun i => left (i + (location.prefix.length + 1)))
        (fun i => right (i + (location.prefix.length + 1)))
        (fun i => available (i + (location.prefix.length + 1))),
      pushedLocals (location.prefix.length + 1) tailLocals = locals ∧
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (tailFrame.dependencyEnvironment ordered)).cost ≤ environmentCost (frame.dependencyEnvironment ordered) := by
  induction location generalizing locals left right available with
  | here =>
    obtain ⟨suffix, bound⟩ := frame.peelMeasured
    exact ⟨suffix.tailLocals, suffix.frame, suffix.positions, bound⟩
  | @there source context tailSource tailContext A level domain B otherLevel newDomain location ih =>
    obtain ⟨suffix, bound⟩ := frame.peelMeasured
    obtain ⟨tailLocals, tailFrame, positions, tailBound⟩ := ih suffix.frame
    have previousBound : ∀ ordered, environmentCost (suffix.frame.dependencyEnvironment ordered) ≤
        environmentCost (frame.dependencyEnvironment ordered) := by
      intro ordered
      have positive := (newDomain.dependencyOrigin ordered).weight_pos
      have le := bound ordered
      simp only [Closure.cost] at le
      have reserve := Nat.mul_le_mul_right (1 + environmentCost (suffix.frame.dependencyEnvironment ordered)) positive
      omega
    have positions' := (congrArg Locals.push positions).trans suffix.positions
    have bound' := fun ordered => Nat.le_trans (tailBound ordered) (previousBound ordered)
    have answer : ∃ f : OriginalRichFrame sourceEnv env U registry target tailContext tailLocals
          (fun i => left (i + (location.prefix.length + 1) + 1))
          (fun i => right (i + (location.prefix.length + 1) + 1))
          (fun i => available (i + (location.prefix.length + 1) + 1)),
        Locals.push (pushedLocals (location.prefix.length + 1) tailLocals) = locals ∧
          ∀ ordered, (Closure.close (domain.dependencyOrigin ordered) (f.dependencyEnvironment ordered)).cost ≤
            environmentCost (frame.dependencyEnvironment ordered) := ⟨tailFrame, positions', bound'⟩
    have shift {α : Sort _} (f : Nat → α) :
        (fun i => f (i + (location.prefix.length + 1) + 1)) =
        (fun i => f (i + (location.prefix.length + 1 + 1))) := by
      funext i
      congr 1
    rw [shift left, shift right, shift available] at answer
    exact ⟨tailLocals, answer⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
