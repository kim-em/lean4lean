import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandObservation

/-! # Actual computation at a bare stored alias

The erased primitive relation has two presentations of delta: selected stored
equations and concrete fixed-template patterns. Both select the same installed
body. Capture and iota patterns cannot match a bare constant.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Definitions)
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A typed bare constant's ordinary erased primitive is its actual stored
unfolding. This includes the fixed-template presentation of definition patterns. -/
theorem erased_stored_constant_root
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.const name levels) T)
    (R : ErasedIotaPrimitive (Definitions.ofEnv env univs henv) (.const name levels) out) :
    ∃ rhs, (Definitions.ofEnv env univs henv).unfolds name levels rhs ∧
      out = proofErase [] rhs := by
  rcases R with (R | R) | R
  · cases R with
    | delta HD => exact ⟨_, HD, rfl⟩
  · cases R with
    | select hp hc hm => cases hm; contradiction
    | apply hp hc hm => cases hm; contradiction
  · cases R with
    | @intro ls T source p check paths captures rhs hclosed hp hc hr hm =>
      cases hm
      cases paths with
      | cons path paths => cases path
      | nil =>
        simp only [List.map_nil, List.foldl_nil] at hp
        have HP := hcon hp
        rcases HP with HP | HP | HP
        · cases HP with
          | @intro value hlookup hclosed =>
            obtain ⟨constant, hconstant, hw, hl⟩ := (show VExpr.WF env univs Γ _ from ⟨_, ht⟩).const_inv henv hΓ
            have hreg := (definitionRegistry_registered hlookup).1
            cases Option.some.inj (hconstant.symm.trans hreg.1)
            exact ⟨_, ⟨value.toDefEq, _, hreg.2, hw, hl,
              by simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl], rfl⟩, rfl⟩
        · cases HP
        · cases HP

namespace AliasDemandProfile
open DemandProfile

/-- At an observed alias, any actual ordinary primitive selects the body
already certified by the observation. Determinism uses the environment registry. -/
theorem Obs.alias_root
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (HT : Typing Δ (.const name []) .sort)
    (HD : (Definitions.ofEnv env univs henv).unfolds name [] rhs)
    (HB : Obs c arity Δ S (proofErase [] rhs) .sort .pi)
    (R : ErasedIotaPrimitive (Definitions.ofEnv env univs henv) (.const name []) out) :
    Obs c arity Δ S out .sort .pi := by
  obtain ⟨Γ, e, T, hΓ, _, ht, _, EE⟩ := HT
  obtain rfl := erase_const_inv EE
  obtain ⟨rhs', HD', rfl⟩ := erased_stored_constant_root hcon hΓ ht R
  cases Definitions.ofEnv_unique henv HD HD'
  exact HB

end AliasDemandProfile
end Lean4Lean.VEnv.Strengthening
