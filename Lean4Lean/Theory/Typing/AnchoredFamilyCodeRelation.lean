import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport
import Lean4Lean.Theory.Typing.AnchoredFamilyCodeWitness

/-! The future closure of the finite family-code clause. Constructor result
bridges use exactly this closure, which is the family counterpart of
`TypeRelated`: each query produces a concrete finite witness at the same frozen
descriptor. Context transport retains both actual traces and all lower inputs.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def FamilyCodeDemand.rename (demand : FamilyCodeDemand n) (ρ : Lift) : FamilyCodeDemand n :=
  { demand with
    arguments := demand.arguments.map (·.rename ρ)
    bounded := by
      intro key member
      obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp member
      change original.rank < n
      exact demand.bounded original oldMember }

theorem FamilyKey.rename_refl (key : FamilyKey) : key.rename .refl = key := by
  cases key
  simp only [FamilyKey.rename, Key.rename, lift'_refl, Profile.rename_refl]

theorem FamilyCodeDemand.rename_refl (demand : FamilyCodeDemand n) : demand.rename .refl = demand := by
  cases demand
  simp only [rename, FamilyKey.rename_refl]
  congr
  exact List.map_id _

theorem FamilyCodeDemand.rename_comp (demand : FamilyCodeDemand n) (ρ τ : Lift) :
    (demand.rename ρ).rename τ = demand.rename (ρ.comp τ) := by
  cases demand
  simp only [rename, List.map_map, Function.comp_def, FamilyKey.rename_comp]

noncomputable def FamilyCodeWitness.changeBase
    (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (witness : FamilyCodeWitness env U registry Γ left right demand) :
    FamilyCodeWitness env U registry Γ' left right demand :=
  { witness with
    leftExposure := witness.leftExposure.context henv chain
    rightExposure := witness.rightExposure.context henv chain }

/-- The exact future closure used for a frozen family support. Recursive
queries remain in the lower argument keys of each concrete witness. -/
def FamilyCodeRelation (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (demand : FamilyCodeDemand n) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    Nonempty (FamilyCodeWitness env U registry Δ (left.lift' ρ) (right.lift' ρ) (demand.rename ρ))

namespace FamilyCodeRelation

theorem atBase (formed : OnCtx Γ (env.IsType U))
    (related : FamilyCodeRelation env U registry Γ left right demand) :
    Nonempty (FamilyCodeWitness env U registry Γ left right demand) := by
  simpa only [lift'_refl, FamilyCodeDemand.rename_refl] using related Γ .refl (.refl formed)

theorem trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : FamilyCodeRelation env U registry Γ left middle demand)
    (second : FamilyCodeRelation env U registry Γ middle right demand) :
    FamilyCodeRelation env U registry Γ left right demand := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  exact before.trans henv hscoped after

theorem symm (henv : env.Ordered) (hscoped : registry.Scoped)
    (related : FamilyCodeRelation env U registry Γ left right demand) :
    FamilyCodeRelation env U registry Γ right left demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact witness.symm henv hscoped

theorem left_diagonal (related : FamilyCodeRelation env U registry Γ left right demand) :
    FamilyCodeRelation env U registry Γ left left demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact ⟨witness.left_diagonal⟩

/-- Generated proof insertions and terminal declaration changes transport
the entire bridge by querying its actual future closure. -/
theorem mixed (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (related : FamilyCodeRelation env U registry Γ left right demand) :
    FamilyCodeRelation env U registry Δ (left.lift' ρ) (right.lift' ρ) (demand.rename ρ) := by
  intro Ω τ future
  obtain ⟨base, extended, changed⟩ := route.pullFuture henv future
  obtain ⟨witness⟩ := related base (ρ.comp τ) extended
  simpa only [lift'_comp, FamilyCodeDemand.rename_comp] using
    (show Nonempty _ from ⟨witness.changeBase henv changed⟩)

end FamilyCodeRelation

end Lean4Lean.AnchoredSemantics
