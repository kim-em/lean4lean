import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedSourceSuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalVariableFreeze

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem pushedLocals_injective (n : Nat) : Function.Injective (pushedLocals n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro first second same
    apply ih
    exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp (List.cons.inj same).2

noncomputable def CappedSourceSuffix.variableDomainDisplay
    {locals : List Nat}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    (substitutions : Ctx.SubstEq env U target left right source)
    (suffix : CappedSourceSuffix (common := source) (frame.captureBase substitutions)
      (frame.captureBase substitutions).initialCaps left right .id locals available entry.originalLocation) :
    OriginalNestedDisplay U source sourceType (.sort entry.level) where
  sourceEnv := sourceEnv
  source := entry.tailSource
  sourceExpression := entry.domain
  sourceType := .sort entry.level
  context := entry.tailContext
  node := .ref entry.originalDomain
  provenance := ⟨_, _, _, entry.originalDomain, entry.tailContext, .here, rfl⟩
  raw := suffix.raw
  graph := suffix.graph
  expression_eq := by
    have rawEq : suffix.raw = Subst.lift_l (.skipN .refl (index+1)) .id := by
      rw [suffix.raw_eq]
      funext i
      have length : entry.originalLocation.prefix.length = index := by
        rw [entry.originalFront_eq, ← entry.index_eq]
      simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.id, length, Nat.add_assoc]
    exact entry.domainDisplay.expression_eq.trans
      (subst_id.symm.trans (subst_lift'.trans (congrArg (entry.domain.subst ·) rawEq.symm)))
  type_eq := rfl

/-- The actual variable domain query is a capped generated source under
repeated identity tails. No separate ordinary-source reindex mode is needed. -/
theorem OriginalRichEntry.generatedSource
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    (substitutions : Ctx.SubstEq env U target left right source)
    (closed : available.AtomClosed)
    (positions : pushedLocals (index+1) entry.tailLocals = locals) :
    ∃ suffix : CappedSourceSuffix (common := source) (frame.captureBase substitutions)
        (frame.captureBase substitutions).initialCaps left right .id locals available entry.originalLocation,
      Nonempty (RichCert sourceEnv env U registry target (.ref entry.originalDomain)
        suffix.locals (suffix.raw.comp left) true entry.support entry.footprint) ∧
      entry.footprint.Available (fun i => available (i + (entry.originalLocation.prefix.length+1))) ∧
      Valuation.AtomClosed (fun i => available (i + (entry.originalLocation.prefix.length+1))) ∧
      Ctx.SubstEq env U target (suffix.raw.comp left) (suffix.raw.comp right) entry.tailSource ∧
      ∀ ordered, (Closure.close (entry.originalDomain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost ≤ environmentCost (frame.dependencyEnvironment ordered) := by
  let base := frame.captureBase substitutions
  obtain ⟨suffix, bound⟩ := CappedCaptureGenerated.sourceSuffix (graph := .identity context)
    (commonLeft := left) (commonRight := right) entry.originalLocation frame base.identityCapped
  have length : entry.originalLocation.prefix.length = index := by
    rw [entry.originalFront_eq, ← entry.index_eq]
  have localsEq : entry.tailLocals = suffix.locals :=
    pushedLocals_injective (index+1) (positions.trans (by simpa only [length] using suffix.positions.symm))
  have leftEq : entry.tailLeft = suffix.raw.comp left := by
    rw [← entry.left_eq, suffix.raw_eq]
    funext i
    simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.comp, Subst.id, length, Nat.add_assoc]
  have rightEq : entry.tailRight = suffix.raw.comp right := by
    rw [← entry.right_eq, suffix.raw_eq]
    funext i
    simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.comp, Subst.id, length, Nat.add_assoc]
  refine ⟨suffix, ⟨?_, ?_, ?_, ?_, bound⟩⟩
  · exact ⟨localsEq ▸ leftEq ▸ entry.certificate⟩
  · intro i wanted hm
    simpa only [length] using entry.available_le i wanted (entry.resources i wanted hm)
  · intro i wanted hm atom ha
    exact closed _ _ hm atom ha
  · simpa only [leftEq, rightEq] using entry.tailSubstitutions substitutions

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
