import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstLegacyProducer
import Lean4Lean.Theory.Typing.AnchoredAtomActionCode

/-! Function-valued constant observations do not need the general code
recipe compiler: a selected nonsortable atom cannot come from `RichObs.code`.
Prune only that actual selected value, then relocate its closed payload.
This does not assert that arbitrary rich constant footprints are empty. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- An actual independent constant endpoint receives only the selected
value observation. Sortable siblings and their recipe resources are discarded.
Every retained closed head keeps its exact policy charge. -/
theorem RichObs.pruneConstantValueAux
    {n : Nat} {profile : Profile n} {atom : Atom n}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (fuel : Nat) (bounded : sizeOf query < fuel)
    (selected : atom ∈ profile.atoms)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ
      (.singleton atom) [],
      ∀ policy, result.headDepth policy ≤ query.headDepth policy := by
  cases hquery : query with
  | rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed =>
    refine ⟨.select (.rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed) selected, ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    refine ⟨.select (.family origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree) selected, ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | constructor origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    refine ⟨.select (.constructor origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree) selected, ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | canonicalDelta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    refine ⟨.select (.canonicalDelta (name := name) (levels := levels) 
      lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
      certificate typed body) selected, ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | canonicalConst origin realization child resources =>
    refine ⟨.select (.canonicalConst (name := name) (levels := levels)
      origin realization child resources) selected, ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | legacy child =>
    have empty : footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry member
      obtain ⟨index, need⟩ := entry
      have impossible := child.scoped (show (VExpr.const name levels).Closed from trivial) index need member
      omega
    cases empty
    obtain ⟨moved, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.select (.legacy moved) selected, fun policy => by
      simp only [RichObs.headDepth, depth]; exact Nat.le_refl _⟩
  | code child => exact (nonsortable _ (child.formed.singleton_of_mem selected)).elim
  | route _ child =>
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) selected nonsortable destination newLocals τ
    exact ⟨result, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | union left right =>
    rcases List.mem_append.mp selected with member | member
    · obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux left (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) member nonsortable destination newLocals τ
      exact ⟨result, fun policy => by simpa only [RichObs.headDepth] using Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
    · obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux right (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) member nonsortable destination newLocals τ
      exact ⟨result, fun policy => by simpa only [RichObs.headDepth] using Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
  | view child change =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) List.mem_cons_self
      (fun flag formed => nonsortable flag ((AtomAction.view change).sortable formed)) destination newLocals τ
    exact ⟨.view result change, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | action child change =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) List.mem_cons_self
      (fun flag formed => nonsortable flag (change.sortable formed)) destination newLocals τ
    exact ⟨.action result change, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | select child member =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) member nonsortable destination newLocals τ
    exact ⟨result, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | pad child =>
    obtain ⟨old, member, equal⟩ := List.mem_map.mp selected
    cases equal
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) member
      (fun flag formed => nonsortable flag formed.pad_sort) destination newLocals τ
    exact ⟨.pad result, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | unpad child =>
    obtain ⟨result, depth⟩ := RichObs.pruneConstantValueAux child (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) (List.mem_map_of_mem selected)
      (fun flag formed => nonsortable flag (by
        have hp : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using formed
        simpa only [Profile.down_sort] using hp.pad_inv)) destination newLocals τ
    exact ⟨.unpad result, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
termination_by fuel
decreasing_by all_goals omega

/-- Public pruning has no size-fuel premise; the fuel is computed from the actual input. -/
theorem RichObs.pruneConstantValue
    {n : Nat} {profile : Profile n} {atom : Atom n}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (selected : atom ∈ profile.atoms)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ
      (.singleton atom) [],
      ∀ policy, result.headDepth policy ≤ query.headDepth policy :=
  pruneConstantValueAux query (sizeOf query + 1) (Nat.lt_succ_self _)
    selected nonsortable destination newLocals τ

theorem RichObs.pruneConstantFunction
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint)
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ
      (Profile.fn key output) [],
      ∀ policy, result.headDepth policy ≤ query.headDepth policy := by
  apply RichObs.pruneConstantValueAux query (sizeOf query + 1) (Nat.lt_succ_self _) List.mem_cons_self
  intro flag sorted
  obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ List.mem_cons_self
  cases List.mem_singleton.mp member
  contradiction

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel

/-- Construct the closed canonical input from an arbitrary rich function query.
Only its selected function value is retained; code-only siblings are irrelevant. -/
theorem canonicalConstSiteOfFunction
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U source (.const name levels) assigned)
    (query : RichObs owner.selected.origin.source env U registry target node locals σ
      (Profile.fn key output) footprint) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output),
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      ∀ policy, packet.query.headDepth policy ≤ query.headDepth policy := by
  let head := constantPrefix node
  obtain ⟨closed⟩ := EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive
  obtain ⟨moved, depth⟩ := query.pruneConstantFunction (.ref closed.site) [] σ
  let origin : CanonicalConstOrigin env U registry strata name levels := {
    ownerName := ownerName
    owner := owner
    info := closed.info
    lookup := closed.lookup
    assignedLevels := closed.assignedLevels
    assignedWF := closed.assignedWF
    levelsWF := closed.levelsWF
    equivalent := closed.equivalent
    typeClosed := owner.selected.origin.ordered.closedC closed.lookup
    site := closed.site }
  let packet := CanonicalConstSitePacket.ofOrigin (target := target) origin σ moved (by
    intro index need member
    cases member)
  exact ⟨packet, rfl, HEq.rfl, depth⟩

end Lean4Lean.AnchoredSource.Adapted
