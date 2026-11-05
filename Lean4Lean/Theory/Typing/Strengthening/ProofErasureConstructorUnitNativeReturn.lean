import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidUnitReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructureHeader
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePositiveHeaderRegistration

/-! # All selected native outputs of unit-parameter constructor histories join

A computed family header supplies ancestry for every selected native output.
Rigid-family continuation return sends that ancestry to one canonical type,
even when parameters and arbitrary dependent fields evolve independently.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- The literal positive phantom-family declaration used in the retained
parameter boundary satisfies the header premise by reflexive computation.
This certifies that concrete declaration, not arbitrary registered headers. -/
theorem positive_unit_parameter_family_header
    (hc : env.constants r = some
      (PositiveHeaderRegistration.family 0 [.const s []]
        (.forallE (.const s []) (.sort (.succ .zero))) r c).toVConstant) :
    ComputedStructureFamilyHeader D r (PositiveHeaderRegistration.info 0 [.const s []] r c) [] ∧
      env.HasType univs Γ (.const r []) (.forallE (.const s []) (.sort (.succ .zero))) := by
  have HH : LiteralStructureFamilyHeader r (PositiveHeaderRegistration.info 0 [.const s []] r c) [] :=
    LiteralStructureFamilyHeader.of_declarations (info := PositiveHeaderRegistration.info 0 [.const s []] r c)
      (ps := [.const s []]) (tail := .app (.const r []) (.bvar 0)) hc rfl rfl rfl rfl
  exact ⟨HH.computed (by simp), HasType.const hc (by simp) rfl⟩

omit [Params] in
private theorem beta_constant_argument
    (R : BetaRed (.app (.const r ls) p) (.app (.const r ls) q)) : BetaRed p q := by
  obtain ⟨args, E, H⟩ := R.const_spine (args := [p])
  cases H with
  | cons HP H =>
    cases H
    obtain ⟨_, rfl⟩ := ProofShape.app.inj E
    exact HP

/-- A retained parameter exposed by a complete rigid-family computation
returns to the unit constructor. This extracts an actual parameter path from
the family history, rather than assuming forward ancestry of that parameter. -/
theorem static_structure_rigid_unit_parameter_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) (.app (.const r []) parameter)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      parameter (.const info.ctorName []) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have ht : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have hFi := HasType.app hF ht
  have EF : proofErase Γ (.const r []) = .const r [] :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .atom) hΓ ht)
  have EFi : proofErase Γ (.app (.const r []) (.bvar i)) = .app (.const r []) (.bvar i) := by
    rw [show proofErase Γ (.app (.const r []) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hFi), EF, EI]
  rw [EFi] at R
  rcases RigidUnitObservation.application_readout heq hs hi hz rfl hD hr hDr
      ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, ht, EI⟩ ⟨Γ, _, hΓ, rfl, hFi, EFi⟩ R with HB | HB
  · exact (ScopedCompute.beta (beta_constant_argument HB)).trans
      (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl)
  · exact .beta (beta_constant_argument HB)

/-- Every native output selected after independent constructor-argument
computations returns to the canonical unit-parameter family. This includes
all conversions before and between applications and after the final result.
The declaration's computed-header certificate and the original parameter's
unit ancestry are explicit; no native argument or type-fork premise is used. -/
theorem computed_header_unit_constructor_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const rinfo.ctorName []) (p :: fields)) T)
    (hl : Lookup Γ i (.const family []))
    (Rstart : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ p))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) parameter)
    (RF : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fieldImages)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have RO := registered_computed_header_raw_origin heq hs hΓ hR hrx HH
    (args := [p]) (by simpa using hrp.symm) hlen ht (List.Forall₂.cons RP .nil) RF RN
  have hFi := HasType.app hF (HasType.bvar hl)
  have EE : proofErase Γ (.app (.const r []) (.bvar i)) =
      .app (.const r []) (proofErase Γ (.bvar i)) := by
    simpa [VExpr.mkApps, ProofShape.mkApps] using proofErase_const_spine
      (c := r) (ls := []) (args := [.bvar i]) hΓ hFi (not_isProof_of_sort hΓ hFi)
  apply static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hR) hDr hΓ hF hl
  rw [EE]
  exact (ScopedCompute.app ScopedCompute.refl Rstart).trans RO

/-- A family parameter selected by any native history of the computed
constructor itself returns to the unit constructor. Native type conversions
may have changed that parameter; its path is derived from the complete header
and argument history, not required as an additional guard premise. -/
theorem computed_header_unit_constructor_guard_parameter_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const rinfo.ctorName []) (p :: fields)) T)
    (hl : Lookup Γ i (.const family []))
    (Rstart : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ p))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) parameter)
    (RF : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fieldImages)) (.app (.const r []) selectedParameter)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      selectedParameter (.const info.ctorName []) := by
  have RO := registered_computed_header_raw_origin heq hs hΓ hR hrx HH
    (args := [p]) (by simpa using hrp.symm) hlen ht (List.Forall₂.cons RP .nil) RF RN
  have hFi := HasType.app hF (HasType.bvar hl)
  have EE : proofErase Γ (.app (.const r []) (.bvar i)) =
      .app (.const r []) (proofErase Γ (.bvar i)) := by
    simpa [VExpr.mkApps, ProofShape.mkApps] using proofErase_const_spine
      (c := r) (ls := []) (args := [.bvar i]) hΓ hFi (not_isProof_of_sort hΓ hFi)
  apply static_structure_rigid_unit_parameter_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hR) hDr hΓ hF hl
  rw [EE]
  exact (ScopedCompute.app ScopedCompute.refl Rstart).trans RO

/-- Arbitrary independent parameter/field histories, native selections and
subsequent type continuations join at one fixed family. The parameters and
fields need no native certificates at their intermediate images. The supplied
header condition is not claimed to follow from arbitrary registration. -/
theorem computed_header_unit_constructor_native_histories_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const rinfo.ctorName []) (p :: fields)) T)
    (hl : Lookup Γ i (.const family []))
    (Rstart : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ p))
    (RP₁ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) parameter₁)
    (RP₂ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) parameter₂)
    (RF₁ : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages₁)
    (RF₂ : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages₂)
    (RN₁ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter₁ :: fieldImages₁)) out₁)
    (RN₂ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter₂ :: fieldImages₂)) out₂)
    (RC₁ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₁ left)
    (RC₂ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₂ right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.const info.ctorName [])) :=
  ⟨computed_header_unit_constructor_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hlen hΓ hF ht hl Rstart RP₁ RF₁ (RN₁.convert RC₁),
    computed_header_unit_constructor_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hlen hΓ hF ht hl Rstart RP₂ RF₂ (RN₂.convert RC₂)⟩

end Lean4Lean.VEnv.Strengthening
