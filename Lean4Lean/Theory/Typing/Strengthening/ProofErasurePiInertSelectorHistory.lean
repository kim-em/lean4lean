import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary

/-! # Selector histories retain no evidence of an assigned result conversion

An empty-structure argument guard compares two neutral selector bodies. Full
core computation and arbitrary ambient substitution preserve that certificate,
even when the assigned result carrier is hidden by semantic conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private selector_typing from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary
variable [Params] {D : Definitions}

/-- Selector lambdas compare after all independent full-core paths. Their
bound function remains neutral, while its domain may change universe levels
and both selected arguments may compute arbitrarily. -/
theorem pi_inert_unit_selector_interpret
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    PiInertInterpret D n (.compare true) Δ
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) a))
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) b)) := by
  intro left right RL RR
  obtain ⟨D', body, rfl, RD, RB⟩ := RL.level_core_lam_inv
  obtain ⟨E', body', rfl, _, RB'⟩ := RR.level_core_lam_inv
  obtain ⟨S', T', rfl, RS, RT⟩ := RD.pi_parts (fun R => erased_level_core_no_pi R)
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) family := by
    intro Δ ls args out R
    exact erased_level_recovered_stage_spine_levels heq (henv.projectionRigid hi) hD 0 (Δ := Δ) R
  obtain ⟨ls', ps', rfl, _, Hps⟩ := (RS.scoped (Δ := Δ) (fun R => .base R)).const_spine_levels
    (args := []) @hroot
  cases Hps
  obtain ⟨ls'', ps'', rfl, _, Hps'⟩ := (RT.scoped (Δ := Δ) (fun R => .base R)).const_spine_levels
    (args := []) @hroot
  cases Hps'
  obtain ⟨a', rfl, _⟩ := RB.level_core_bvar_app_inv
  obtain ⟨b', rfl, _⟩ := RB'.level_core_bvar_app_inv
  apply ComputedJointCheck.lamCommon
  apply ComputedJointCheck.appCarrier (A := .const family ls') (B := .const family ls'')
  · exact .bvar
  · exact .leaf .refl
  · exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- Ambient future substitutions leave the bound selector function fixed.
Thus the selector certificate is a full Pi-inert evidence value, not merely a
beta-stable certificate from the older comparison grammar. -/
theorem pi_inert_unit_selector_evidence
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    PiInertEvidence D n (.compare true) Δ
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) a))
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) b)) := by
  refine ⟨pi_inert_unit_selector_interpret heq hi hp hx hf hD, ?_⟩
  intro Δ' τ W left right RL RR
  exact pi_inert_unit_selector_interpret heq hi hp hx hf hD RL RR

/-- Actual selectors have full carrier histories at an arbitrarily supplied
raw carrier. Neither this construction nor its future stability records the
conversion used to assign a different actual result type to the selectors. -/
theorem pi_inert_unit_selector_carrier_history
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) :
    let F := VExpr.forallE (.const family ls) (.const family ls)
    PiInertCarrierHistory D n (proofEraseCtx Γ) C
      (proofErase Γ (.lam F (.app (.bvar 0) (.bvar (i+1)))))
      (proofErase Γ (.lam F (.app (.bvar 0) (.bvar (j+1))))) := by
  dsimp only
  rw [(selector_typing hΓ hS hiT).2, (selector_typing hΓ hS hjT).2]
  exact (pi_inert_unit_selector_evidence heq hi hp hx hf hD).carrier_history

end Lean4Lean.VEnv.Strengthening
