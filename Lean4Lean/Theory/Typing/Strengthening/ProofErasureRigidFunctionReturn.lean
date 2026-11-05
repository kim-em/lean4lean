import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionCanonical
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Full family return with a retained function parameter

A rigid family with a literal stored (Unit -> Unit) -> Type header retains its
function demand through arbitrary whole-application computation. Context-indexed
readout then returns to the family at a literal canonical function. Stored
header equality is explicit; ordinary assigned typing alone is not substituted
for this condition.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom)
variable [Params] {D : PureObservation.Definitions}

/-- Erasure of the closed unit-function type is literal in every context. -/
theorem unit_arrow_erasure
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.forallE (.const s []) (.const s [])) = .forallE (.const s []) (.const s []) := by
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have hSS : env.HasType univs (VExpr.const s [] :: Γ) (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (.forallE hSΓ hSS))]
  rw [show proofErase Γ (.const s []) = .const s [] from if_neg (not_isProof_of_sort hΓ hSΓ),
    show proofErase (VExpr.const s [] :: Γ) (.const s []) = .const s [] from if_neg (not_isProof_of_sort hΓS hSS)]

/-- Actual literal declaration data supplies the same native caller header in
any raw context. This is not inferred from an ordinarily equal assignment. -/
theorem literal_family_native
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type = .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))) := by
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.const r []) (proofErase [] (ci.type.instL [])) :=
    .const hc (by simp) (by simp [hU])
  have EI : ci.type.instL [] = .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)) := by
    simp [hT, VExpr.instL, VLevel.inst]
  have hSS : env.HasType univs [VExpr.const s []] (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hQ := HasType.forallE hS hSS
  have hΓQ : OnCtx [VExpr.forallE (.const s []) (.const s [])] (env.IsType univs) := ⟨trivial, _, hQ⟩
  have hV : env.HasType univs [VExpr.forallE (.const s []) (.const s [])] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have ET : proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))) =
      .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)) := by
    rw [show proofErase [] (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort (Γ := []) trivial (.forallE hQ hV)),
      unit_arrow_erasure hS (Γ := []) trivial]
    exact congrArg (ProofShape.forallE _) (if_neg (not_isProof_of_sort hΓQ hV))
  rwa [EI, ET] at RN

/-- Every whole-family continuation at an actual unit-function lookup returns
to one fixed function-parameter instance. All compatible beta, eta, native
identity, structure and annotation computation interleavings are allowed. -/
theorem family_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type = .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam (.const s []) (.const info.ctorName []))) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  let V : AtomicControl.Sets := fun j t o => j = i ∧ t = .arrow .atom .atom ∧ o = .app [.pi] .pi
  have hx₀ : env.HasType univs Γ (.bvar i) (.forallE (.const s []) (.const s [])) := .bvar hl
  have EX : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓ hx₀)
  have HX : AtomicControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.arrow .atom .atom) := ⟨Γ, _, hΓ, rfl, hx₀, EX⟩
  have hf : env.HasType univs Γ (.const r []) (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))) := by
    have H := HasType.const (U := univs) (Γ := Γ) hc (ls := []) (by simp) (by simp [hU])
    simpa only [hT, VExpr.instL, List.map_nil, VLevel.inst] using H
  have EF : proofErase Γ (.const r []) = .const r [] := if_neg (not_isProof_function_to_sort hΓ hf)
  have ht : env.HasType univs Γ (.app (.const r []) (.bvar i)) (.sort (.succ .zero)) := .app hf hx₀
  have EE : proofErase Γ (.app (.const r []) (.bvar i)) = .app (.const r []) (.bvar i) := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓ ht), EF, EX]
  have HV : V.Typed (proofEraseCtx Γ) := by rintro j t o ⟨rfl, rfl, rfl⟩; exact HX
  have HK : AtomicControl.Demand (.arrow .atom .atom) (.app [.pi] .pi) :=
    .fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .atom) .atom
  have HO : Obs info.ctorName r (.succ .zero) (proofEraseCtx Γ) V
      (.app (.const r []) (.bvar i)) (.sort (.succ .zero)) .pi := by
    refine .app ⟨Γ, _, hΓ, rfl, ht, EE⟩ (.rigid ⟨Γ, _, hΓ, rfl, hf, EF⟩) ?_
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var HX HK ⟨rfl, rfl, rfl⟩
  have H := HO.static_structure_union heq hs hi hz rfl (henv.projectionCtorRigid hi) hD hr hDr R HV
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (.forallE (.const s []) (.const s [])) := by
    have RR := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
      hΓ hl (AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓ hx₀) .refl
    rwa [EX, unit_arrow_erasure hS hΓ] at RR
  have HR := H.world_computes (union_world_rename heq hs) (fun t τ => canonical_subst t)
    (target := canonical info.ctorName r s) rfl
    (fun _ => family_world hi hp hx hz rfl hS (literal_family_native hS hc hU hT))
    ContextRenaming.identity.interpretation (σ := Subst.id) (by
      rintro j t key ⟨rfl, rfl, rfl⟩
      exact native_unit_function_world heq hs hi hp hx hz RN)
  simpa only [ProofShape.subst_id, WorldComputes, canonical] using HR

/-- Independently computed family instances at any two unit-function lookups
have a fixed common output. This is a full-continuation type join for this
literal-header fragment, not a general type-conversion completeness theorem. -/
theorem family_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type = .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (hlj : Lookup Γ j (.forallE (.const s []) (.const s [])))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar j)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.lam (.const s []) (.const info.ctorName []))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.lam (.const s []) (.const info.ctorName []))) :=
  ⟨family_return heq hs hi hp hx hz hD hS hr hDr hc hU hT hΓ hli RL,
    family_return heq hs hi hp hx hz hD hS hr hDr hc hU hT hΓ hlj RR⟩

/-- Actual environment definitions automatically respect the two rigid heads. -/
theorem environment_family_return
    (heq : env.HasCanonicalEq)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type = .forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam (.const s []) (.const info.ctorName []))) :=
  family_return heq EnvironmentCore.sound hi hp hx hz (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    hS hr (EnvironmentCore.no_rigid hr) hc hU hT hΓ hl R

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
