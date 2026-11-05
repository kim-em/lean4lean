import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidUnitReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaSquares

/-! # Common native structure pivots with a retained unit parameter

Full family-history return aligns the native guard at the unit constructor.
This removes the parameter-chain joining premise from the structure square
for one looked-up unit parameter; all dependent fields remain unrestricted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- A common native output with the assigned unit-indexed family can be
converted to its canonical parameter. The entire assigned-type history is
allowed, and no exact native recovery at the old unit variable is required. -/
theorem static_structure_common_native_unit_parameter
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) commonType) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      pivot (.app (.const r []) (.const info.ctorName [])) :=
  RN.convert (static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hl RT)

/-- Common native output discharges the structure pivot square when its
single parameter is a looked-up closed positive unit. The registered structure
may have arbitrary dependent retained fields. Full parameter histories are
handled by family return, with no parameter-chain joining or global type-fork
premise. Existence of the supplied common native output remains explicit. -/
theorem common_native_structure_unit_parameter_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (ha : (rinfo.resultLevel.inst []).IsNeverZero ∨ StructureReplay.ProofFields env univs rinfo [])
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot target)
    (Rβ : BetaRed source target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) commonType) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original
        (nativeStructureOutput r rinfo [] [.const info.ctorName []] target) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (nativeStructureOutput r rinfo [] [.bvar i] source)
        (nativeStructureOutput r rinfo [] [.const info.ctorName []] target) := by
  have RNP := static_structure_common_native_unit_parameter heq hs hi hp hx hz hD hS
    (henv.projectionRigid hR) hDr hΓ hF hl RN RT
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot
      (nativeStructureOutput r rinfo [] [.const info.ctorName []] pivot) :=
    .base (erased_static_structure_eta_expansion_union_structure
      (.intro hR hrx ha (by simpa using hrp.symm) RNP))
  have RP := static_structure_unit_lookup_compute (D := D) hi hp hx hz hS hΓ hl
  exact ⟨Rbefore.trans (RE.trans (nativeStructureOutput_compute (.cons .refl .nil) Rafter)),
    nativeStructureOutput_compute (.cons RP .nil) (.beta Rβ)⟩

end Lean4Lean.VEnv.Strengthening
