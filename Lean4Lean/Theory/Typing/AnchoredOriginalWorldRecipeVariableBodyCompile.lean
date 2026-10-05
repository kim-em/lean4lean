import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableBodyCompile
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem raiseQueryAnnotation
    {strata : EquationStratification env} {profile : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (annotation : WorldObsProvenance strata query) (bound : n ≤ N) :
    ∃ output : WorldObsProvenance strata (query.raise bound), output.worlds = annotation.worlds := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ⟨annotation, rfl⟩
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.raise, Nat.recAux]
      rw [dif_pos rfl]
      exact ⟨.castProfile (raiseProfile_self ..).symm annotation, rfl⟩
    · have previous : n ≤ N := by omega
      obtain ⟨output, worlds⟩ := ih previous
      simp only [RichObs.raise, Nat.recAux]
      rw [dif_neg equal]
      exact ⟨.castProfile (raiseProfile_step previous profile).symm (.pad output), worlds⟩

/-- A real ordinary destination certificate, on the SAME selected argument
frame. The retained row contributes only its finite adapter; no captured
frame, raw-factorization assertion or semantic output is stored in the result. -/
theorem RecipeVariableDemand.compileControlled
    {strata : EquationStratification env}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (demand : RecipeVariableDemand env U registry target keyInput output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sorted : output.HasType (.sort relevant))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable demand.input)
    (controls : OriginalWorldControls strata controlSource)
    (ready : ControlledStoredQuery controls frontier (.observation argument.observation)) :
    ∃ footprint, ∃ certificate : RichCert argumentEnv env U registry target argumentNode
      argumentLocals argumentσ relevant output footprint,
    ∃ next : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available argumentAvailable ∧ next.annotation.worlds ⊆ ready.annotation.worlds ∧
      ∀ policy, certificate.headDepth policy ≤ argument.observation.headDepth policy := by
  let N := max argument.rank demand.rank
  have ha : argument.rank ≤ N := Nat.le_max_left _ _
  let replayed := demand.replay henv hscoped formed argument
  obtain ⟨raised, worlds⟩ := raiseQueryAnnotation argument.observation ready.annotation ha
  let replayAnnotation : WorldObsProvenance strata replayed.observation := raised
  obtain ⟨footprint, certificate, annotation, resources, included, depth⟩ :=
    replayed.code_worlds_depth henv replayAnnotation sorted
  have annotationWorlds : annotation.worlds ⊆ ready.annotation.worlds := by
    intro world member
    change world ∈ WorldObsProvenance.worlds ready.annotation
    rw [← worlds]
    exact included member
  have certificateDepth : ∀ policy, certificate.headDepth policy ≤ argument.observation.headDepth policy := by
    intro policy
    have bounded := depth policy
    simpa only [replayed, RecipeVariableDemand.replay, RichGradedResult.raiseTo,
      RichObs.headDepth_raise] using bounded
  refine ⟨footprint, certificate, ⟨annotation, ?_, ?_⟩, resources, annotationWorlds, certificateDepth⟩
  · intro control active
    exact Nat.le_trans (certificateDepth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (annotationWorlds member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
