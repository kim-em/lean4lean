import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionSelectedReturn
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
  have hf₀ : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))) := by
    have H := HasType.const (U := univs) (Γ := []) hc (ls := []) (by simp) (by simp [hU])
    simpa only [hT, VExpr.instL, List.map_nil, VLevel.inst] using H
  exact family_return_selected heq hs hi hp hx hz hD hS hr hDr hf₀
    (literal_family_native hS hc hU hT) hΓ hl R

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
