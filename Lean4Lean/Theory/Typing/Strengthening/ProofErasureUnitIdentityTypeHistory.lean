import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerTypeHistory

/-! # Canonical unit-family results after identity-type computation

The constructor frame supplies its annotation's ancestry. Arbitrary computation
of the resulting identity-arrow type can change both components and introduce
dependent codomain syntax. Ordinary argument substitution removes that binder
and retains the lower ancestry, so every later result-type continuation returns
to the canonical unit-family type without a native argument certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A ground type history rooted at a unit-family lookup returns to the
canonical family after the temporary control prefix has been removed. -/
theorem LowerTypeHistory.unit_family_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : LowerTypeHistory D Γ (proofErase Γ (.app (.const r []) (.bvar i)))
      0 (proofEraseCtx Γ) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  obtain ⟨A, _, _, _, E, _, R⟩ := H
  rw [ProofShape.liftN_zero] at E
  exact E ▸ static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hl R

/-- A native annotation selected from a constructor frame remains anchored
after its entire identity-arrow type computes, a new ordinary argument is
substituted into the exposed codomain, and that result type computes further.
The argument may lack exact native recovery at both old and new domains.
This concerns computation of the function's type; preservation of this demand
through arbitrary computation of the function term is a separate open step. -/
theorem constructor_frame_identity_type_result_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : ConstructorFrameHistory D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) source)
    (hA : env.HasType univs Γ A (.sort w))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source (proofErase Γ A))
    (hxC : env.HasType univs Γ x C)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A A.lift)) (.forallE (proofErase Γ C) Y))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (Y.inst (proofErase Γ x)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have HA := H.lower_type_history heq hs hΓ hR hrp hrx HH RN
  have HB := computed_identity_type_inst_history heq hs hΓ hA HA hxC RT
  exact (HB.compute heq hs hΓ hΓ (Ctx.LiftN.zero []) RC).unit_family_return
    heq hs hi hp hx hz hD hS (henv.projectionRigid hR) hDr hΓ hF hl

end Lean4Lean.VEnv.Strengthening
