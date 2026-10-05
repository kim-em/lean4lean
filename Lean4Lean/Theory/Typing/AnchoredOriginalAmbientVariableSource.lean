import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedVariableSource
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientSourceSuffix

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private pushedLocals_injective from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedVariableSource
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The actual variable domain query is a capped generated source under
repeated identity tails. No separate ordinary-source reindex mode is needed. -/
theorem OriginalRichEntry.generatedSourceAmbient
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals left right available}
    (entry : OriginalRichEntry frame index need sourceType)
    (ambient : frame.Ambient)
    (substitutions : Ctx.SubstEq env U target left right source)
    (closed : available.AtomClosed)
    (positions : pushedLocals (index+1) entry.tailLocals = locals) :
    ∃ suffix : CappedSourceSuffix (common := source) (frame.captureBase substitutions)
        (frame.captureBase substitutions).initialCaps left right .id locals available entry.originalLocation,
      AmbientCaptureGenerated (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
        left right suffix.graph suffix.frame.raw ∧
      Nonempty (RichCert sourceEnv env U registry target (.ref entry.originalDomain)
        suffix.locals (suffix.raw.comp left) true entry.support entry.footprint) ∧
      entry.footprint.Available (fun i => available (i + (entry.originalLocation.prefix.length+1))) ∧
      Valuation.AtomClosed (fun i => available (i + (entry.originalLocation.prefix.length+1))) ∧
      Ctx.SubstEq env U target (suffix.raw.comp left) (suffix.raw.comp right) entry.tailSource ∧
      ∀ ordered, (Closure.close (entry.originalDomain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost ≤ environmentCost (frame.dependencyEnvironment ordered) := by
  let base := frame.captureBase substitutions
  obtain ⟨suffix, suffixGenerated, bound⟩ := AmbientCaptureGenerated.sourceSuffix (graph := .identity context)
    (commonLeft := left) (commonRight := right) entry.originalLocation frame (.identity (base := base) ambient)
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
  refine ⟨suffix, suffixGenerated, ⟨?_, ?_, ?_, ?_, bound⟩⟩
  · exact ⟨localsEq ▸ leftEq ▸ entry.certificate⟩
  · intro i wanted hm
    simpa only [length] using entry.available_le i wanted (entry.resources i wanted hm)
  · intro i wanted hm atom ha
    exact closed _ _ hm atom ha
  · simpa only [leftEq, rightEq] using entry.tailSubstitutions substitutions

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
