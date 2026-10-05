import Lean4Lean.Theory.Typing.AnchoredPadding
import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Batteries.Tactic.OpenPrivate

/-! Literal family descriptors can move to the next finite rank while keeping
all raw keys and padding both their value demands and exact type supports. -/
namespace Lean4Lean.AnchoredProfiles
open VExpr
set_option backward.isDefEq.respectTransparency false

def DataRequest.pad (request : DataRequest (Profile n)) : DataRequest (Profile (n + 1)) :=
  request.map id Profile.pad

def FamilyData.pad (data : FamilyData (Profile n)) : FamilyData (Profile (n + 1)) :=
  data.map id Profile.pad

theorem DataRequest.pad_rename (request : DataRequest (Profile n)) (ρ : Lift) :
    (request.pad).rename ρ = (request.rename ρ).pad := by
  unfold pad rename
  rw [DataRequest.map_map, DataRequest.map_map]
  congr 1
  funext profile
  exact (Profile.pad_rename profile ρ).symm

theorem FamilyData.pad_rename (data : FamilyData (Profile n)) (ρ : Lift) :
    (data.pad).rename ρ = (data.rename ρ).pad := by
  unfold pad rename
  rw [FamilyData.map_map, FamilyData.map_map]
  congr 1
  funext profile
  exact (Profile.pad_rename profile ρ).symm

open private AtomWF FamilyWF RequestWF AtomTyped checks from Lean4Lean.Theory.Typing.AnchoredProfiles

/-- Literal family promotion preserves its original relevance and every
request's intrinsic input/support formation. -/
theorem Profile.HasType.familyPad {family : FamilyData (Profile n)}
    (formed : (Profile.singleton (n := n + 1) (.family family)).HasType (.sort relevant)) :
    (Profile.singleton (n := n + 2) (.family family.pad)).HasType (.sort relevant) := by
  have old := formed.wf_value (.family family) (List.mem_singleton_self _)
  refine ⟨?_, Profile.WF.sort (n := n + 2) relevant, ?_⟩
  · intro atom member
    cases List.mem_singleton.mp member
    change ∀ request ∈ family.pad.arguments,
      request.input.WF ∧ request.support.WF
    intro request member
    simp only [FamilyData.pad, FamilyData.map] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨Profile.WF.pad (show original.input.WF from (old original originalMember).1),
      Profile.WF.pad (show original.support.WF from (old original originalMember).2)⟩
  · intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    exact ⟨.sort relevant, List.mem_singleton_self _, typed⟩

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem RequestAdmission.pad (henv : env.Ordered)
    {request : DataRequest (Profile n)}
    (admitted : RequestAdmission env U (relations env U registry n) Γ request left right) :
    RequestAdmission env U (relations env U registry (n + 1)) Γ request.pad left right := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admitted
  exact ⟨anchor, pair, typed.pad, formed.pad_sort,
    TypeRelated.pad henv code, Related.pad henv first, Related.pad henv last⟩

theorem Arguments.pad (henv : env.Ordered)
    (arguments : Arguments env U (relations env U registry n) Γ requests left right) :
    Arguments env U (relations env U registry (n + 1)) Γ
      (requests.map DataRequest.pad) left right := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.pad henv) ih

def FamilyWitness.pad (henv : env.Ordered)
    {demand : FamilyData (Profile n)}
    (W : FamilyWitness env U registry (relations env U registry n) Γ left right demand) :
    FamilyWitness env U registry (relations env U registry (n + 1)) Γ left right demand.pad :=
  { W with
    arguments := by
      have args := W.arguments.pad henv
      simpa only [FamilyData.pad, FamilyData.map, List.map_map, Function.comp_def,
        DataRequest.rename, DataRequest.pad, DataRequest.map_map, Profile.pad_rename, id_eq] using args }

theorem FamilyRelation.pad (henv : env.Ordered)
    {demand : FamilyData (Profile n)}
    (related : FamilyRelation env U registry (relations env U registry n) Γ left right demand) :
    FamilyRelation env U registry (relations env U registry (n + 1)) Γ left right demand.pad := by
  intro Δ ρ future
  obtain ⟨W⟩ := related Δ ρ future
  exact ⟨by simpa only [FamilyData.pad_rename] using W.pad henv⟩

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.familyPad
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {family : FamilyData (Profile n)}
    (code : TypeRelated env U registry Γ left right (Profile.singleton (n := n + 1) (.family family))) :
    TypeRelated env U registry Γ left right (Profile.singleton (n := n + 2) (.family family.pad)) := by
  intro Δ ρ future atom member
  change atom ∈ [Atom.rename (n := n + 2) ρ (.family family.pad)] at member
  cases List.mem_singleton.mp member
  have witness := code Δ ρ future _ (List.mem_singleton_self _)
  obtain ⟨W⟩ := witness
  change RankedData.FamilyWitness env U registry (relations env U registry n) Δ
    (left.lift' ρ) (right.lift' ρ) (family.rename ρ) at W
  change Nonempty (RankedData.FamilyWitness env U registry (relations env U registry (n + 1)) Δ
    (left.lift' ρ) (right.lift' ρ) (family.pad.rename ρ))
  rw [FamilyData.pad_rename]
  exact ⟨W.pad henv⟩

end Lean4Lean.AnchoredSemantics
