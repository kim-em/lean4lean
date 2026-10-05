import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantValuePruning
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda

/-! A graded function demand selects an actual nonsortable raw atom. Its
original annotation is pruned jointly; arbitrary extra returned code atoms
are discarded, while the actual finite adapter is retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private lowerSort from Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantValuePruning
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem RichGradedResult.pruneConstantFunctionWorld
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (result : RichGradedResult sourceEnv env U registry target node locals σ available
      (Profile.fn key output))
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.observation result.observation))
    (henv : env.Ordered)
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) (nextAvailable : Valuation) :
    ∃ moved : RichGradedResult sourceEnv env U registry target destination newLocals τ nextAvailable
      (Profile.fn key output),
    ∃ next : ControlledStoredQuery controls frontier (.observation moved.observation),
      moved.footprint = [] ∧ moved.rank = result.rank ∧
      next.annotation.worlds ⊆ ready.annotation.worlds ∧
      ∀ policy, moved.observation.headDepth policy ≤ result.observation.headDepth policy := by
  have adapter := result.adapter
  simp only [Profile.fn, raiseProfile_singleton] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst normal
  have nonsortable : ∀ flag, ¬ (Profile.singleton original).HasType (.sort flag) := by
    intro flag formed
    have normalized := (AtomAction.view (AdapterNormal.view (U := U) (registry := registry)
      (Γ := target) henv original)).sortable formed
    have mapped := entry.sortable normalized
    have unnormalized := (AtomAction.view ((AdapterNormal.view (U := U) (registry := registry)
      (Γ := target) henv (raiseAtom result.rank result.bound (.fn key output))).inverse henv)).sortable mapped
    have raised : (raiseProfile result.rank result.bound (Profile.fn key output)).HasType (.sort flag) := by
      simpa only [Profile.fn, raiseProfile_singleton] using unnormalized
    have lowered := Profile.HasType.lower result.bound raised
    rw [lowerSort] at lowered
    obtain ⟨cover, member, impossible⟩ := lowered.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction
  obtain ⟨query, annotation, worlds, depth⟩ := ready.annotation.pruneConstantValue
    originalMember nonsortable destination newLocals τ
  let moved : RichGradedResult sourceEnv env U registry target destination newLocals τ nextAvailable
      (Profile.fn key output) := {
    rank := result.rank, bound := result.bound, raw := .singleton original, footprint := []
    observation := query
    adapter := by
      simp only [Profile.fn, raiseProfile_singleton]
      exact .cons (List.mem_singleton_self _) entry (.nil _)
    resources := fun _ _ member => nomatch member
    live := Profile.Live.singleton_iff.mpr (result.live original originalMember) }
  let next : ControlledStoredQuery controls frontier (.observation moved.observation) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  exact ⟨moved, next, rfl, rfl, worlds, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
