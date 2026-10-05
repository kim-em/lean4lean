import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Finite query wrappers preserve the SAME stored annotation and controls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def ControlledStoredQuery.code
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.observation (.code certificate)) where
  annotation := .code ready.annotation
  within := by
    intro control active
    simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using ready.within control active
  sponsored := ready.sponsored

theorem RichObs.raise_worlds
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

theorem ControlledStoredQuery.raise
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {query : RichObs sourceEnv env U registry target node locals σ (profile : Profile n) footprint}
    (ready : ControlledStoredQuery controls frontier (.observation query)) (bound : n ≤ N) :
    Nonempty (ControlledStoredQuery controls frontier (.observation (query.raise bound))) := by
  obtain ⟨annotation, worlds⟩ := query.raise_worlds ready.annotation bound
  refine ⟨⟨annotation, ?_, ?_⟩⟩
  · intro control active
    simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth_raise] using ready.within control active
  · change Sponsored frontier annotation.worlds
    rw [worlds]
    exact ready.sponsored


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
