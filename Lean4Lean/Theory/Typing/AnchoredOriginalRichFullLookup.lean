import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameSuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericVariable

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem pushedLocals_push (n : Nat) (locals : List Nat) :
    pushedLocals n (Locals.push locals) = pushedLocals (n+1) locals := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Locals.push ih

/-- Lookup returns a closed *full* suffix, not a possibly non-closed branch
chosen from a merged frame. The assigned domain certificate is selected again
at the retained original context location under that full suffix. -/
theorem OriginalRichFrame.lookupFull
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (closed : available.AtomClosed)
    (member : need ∈ available index) (lookup : Lookup source index sourceType) :
    ∃ entry : OriginalRichEntry frame index need sourceType,
      entry.tailAvailable.AtomClosed ∧
      (∀ i, entry.tailAvailable i = available (i + (index + 1))) ∧
      pushedLocals (index + 1) entry.tailLocals = locals := by
  obtain ⟨old, _⟩ := frame.lookup_allDepth henv formed member lookup
  have length : old.originalLocation.prefix.length = index := by
    rw [old.originalFront_eq, ← old.index_eq]
  obtain ⟨focusedLocals, focused, positions, focusedBound⟩ := frame.focusLocation old.originalLocation
  have headMember : need ∈ (fun i => available (i + old.originalLocation.prefix.length)) 0 := by
    simpa only [Nat.zero_add, length] using member
  obtain ⟨answer⟩ := focused.headCode henv formed headMember
  obtain ⟨suffix, suffixBound⟩ := focused.peelMeasured
  have localsEq : focused.peel.tailLocals = suffix.tailLocals :=
    (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
      (List.cons.inj (focused.peel.positions.trans suffix.positions.symm)).2
  let changed : OriginalRichHeadCode (env := env) (registry := registry) (target := target)
      old.originalDomain suffix.tailLocals
      (fun i => left (i + old.originalLocation.prefix.length))
      (fun i => right (i + old.originalLocation.prefix.length))
      (fun i => available (i + old.originalLocation.prefix.length)) need := localsEq ▸ answer
  refine ⟨{
    front := old.front, tailSource := old.tailSource, domain := old.domain
    source_eq := old.source_eq, index_eq := old.index_eq, sourceType_eq := old.sourceType_eq
    tailContext := old.tailContext, tailLocals := suffix.tailLocals
    tailLeft := _, tailRight := _, tailAvailable := _, tailFrame := suffix.frame
    level := old.level, originalDomain := old.originalDomain
    originalLocation := old.originalLocation, originalFront_eq := old.originalFront_eq
    left_eq := ?_, right_eq := ?_, available_le := ?_
    support := changed.support, footprint := changed.footprint, certificate := changed.certificate
    resources := changed.resources, typed := changed.typed, related := ?_
    environment_le := fun ordered => Nat.le_trans (suffixBound ordered) (focusedBound ordered) }, ?_⟩
  · funext i
    simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.tail, length, Nat.add_assoc, Nat.add_comm]
  · funext i
    simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.tail, length, Nat.add_assoc, Nat.add_comm]
  · intro i need member
    have same : i + 1 + old.originalLocation.prefix.length = i + (index + 1) := by omega
    exact same ▸ member
  · have same : old.domain.subst (fun i => left (i + 1 + old.originalLocation.prefix.length)) =
        sourceType.subst left := by
      calc
        _ = old.domain.subst old.tailLeft := by
          congr 1
          funext i
          have h := congrFun old.left_eq i
          simpa [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, length,
            Nat.add_assoc, Nat.add_comm] using h
        _ = sourceType.subst left := old.realizedType
    have related := changed.related
    simp only [Subst.head, Nat.zero_add] at related
    change Related env U registry target (left old.originalLocation.prefix.length)
      (right old.originalLocation.prefix.length)
      (old.domain.subst (fun i => left (i + 1 + old.originalLocation.prefix.length)))
      need.profile changed.support at related
    rw [same] at related
    simpa only [length] using related

  · refine ⟨?_, ?_, ?_⟩
    · intro i wanted hm atom ha
      exact closed (i + 1 + old.originalLocation.prefix.length) wanted hm atom ha
    · intro i
      change available (i + 1 + old.originalLocation.prefix.length) = available (i + (index + 1))
      congr 1
      omega
    · have result := (congrArg (pushedLocals old.originalLocation.prefix.length) suffix.positions).trans positions
      simpa only [pushedLocals_push, length] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
