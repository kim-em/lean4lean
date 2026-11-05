import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitParameterPivot

/-! # Constructor-reaching unit pivots construct their common native output

A complete source path reaches a constructor with arbitrary fields. A complete
unit-parameter ancestry gives the canonical family guard there. Assigned-family
computation then supplies common coverage rather than taking it as a premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Reaching a constructor and tracing its one retained parameter to a unit
lookup supplies the canonical native family. The whole source path is allowed;
fields need neither histories nor native recovery. Parameter ancestry is an
explicit computational premise, not inferred from ordinary equality. -/
theorem computed_constructor_unit_parameter_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hl : Lookup Γ i (.const family []))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) parameter)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))
      (.app (.const r []) (.const info.ctorName [])) := by
  have RC := static_structure_unit_variable_return heq hs hi hp hx hz hD hS hΓ hl RP
  apply computed_constructor_image_native_parameters
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hR hrx
    (by simp [hrp, hlen, Nat.add_comm]) ht RE (params := [.const info.ctorName []])
  simpa only [hrp, List.take_succ_cons, List.take_zero] using List.Forall₂.cons RC List.Forall₂.nil

/-- The reached constructor and an independently assigned family at another
unit variable share the canonical native output. This constructs the guard
pair used by the common-native square without any coverage hypothesis. -/
theorem computed_constructor_unit_parameter_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (ht : env.HasType univs Γ e (.app (.const r []) (.bvar j)))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) parameter)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))
        (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.const r []) (.bvar j)))
        (.app (.const r []) (.const info.ctorName [])) := by
  have hj : env.HasType univs Γ (.bvar j) (.const family []) := .bvar hlj
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have EF : proofErase Γ (.const r []) = .const r [] :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EJ : proofErase Γ (.bvar j) = .bvar j :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .atom) hΓ hj)
  refine ⟨computed_constructor_unit_parameter_native heq hs hi hp hx hz hD hS
    hR hrp hrx hlen hΓ ht hli RP RE, ?_⟩
  rw [show proofErase Γ (.app (.const r []) (.bvar j)) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.app hF hj)), EF, EJ]
  exact .app .refl (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hlj)

/-- A constructor-reaching major supplies the common guard needed for the
unit-parameter structure square. The source path and following major path are
arbitrary; fields are unrestricted. The remaining input is an explicit unit
ancestry for the constructor parameter, not a native-output or coverage axiom. -/
theorem computed_constructor_unit_parameter_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (ha : (rinfo.resultLevel.inst []).IsNeverZero ∨ StructureReplay.ProofFields env univs rinfo [])
    (hlen : fields.length = rinfo.numFields)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) parameter)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields)))
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields)) target)
    (Rβ : BetaRed source target) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e)
        (nativeStructureOutput r rinfo [] [.const info.ctorName []] target) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (nativeStructureOutput r rinfo [] [.bvar j] source)
        (nativeStructureOutput r rinfo [] [.const info.ctorName []] target) := by
  have RN := computed_constructor_unit_parameter_native heq hs hi hp hx hz hD hS
    hR hrp hrx hlen hΓ ht hli RP RE
  have RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))
      (nativeStructureOutput r rinfo [] [.const info.ctorName []]
        (ProofShape.mkApps (.const rinfo.ctorName []) (parameter :: fields))) :=
    .base (erased_static_structure_eta_expansion_union_structure
      (.intro hR hrx ha (by simpa using hrp.symm) RN))
  exact ⟨RE.trans (RX.trans (nativeStructureOutput_compute (.cons .refl .nil) Rafter)),
    nativeStructureOutput_compute
      (.cons (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hlj) .nil) (.beta Rβ)⟩

end Lean4Lean.VEnv.Strengthening
