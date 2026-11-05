import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonStructureHeader
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRegisteredHeaderBoundary

/-! # Common header checkpoints strictly extend the directed condition

The actual registered prefix refuting directed alignment satisfies the common
header condition. Thus its family can start a native history at a shared typed
checkpoint, even though the constructor's original prefix cannot be selected
as that checkpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ExplicitHeaderBoundary

/-- The fixed registered example has a common header: unit eta computes the
constructor's chosen parameter header to the family's stored header. -/
theorem explicit_registered_header_common [Params] {D : PureObservation.Definitions}
    (hi : env.projections s oldInfo) (hp : oldInfo.nparams = 0)
    (hx : oldInfo.nindices = 0) (hz : oldInfo.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hc : env.constants t = some
      (HeaderRegistration.family 0 (parameters s) (storedHeader s oldInfo.ctorName) t c).toVConstant) :
    CommonStructureFamilyHeader D t (HeaderRegistration.info 0 (parameters s) t c) [] := by
  apply CommonStructureFamilyHeader.of_reverse (ps := parameters s) (u := .zero)
    (tail := etaOpen (parameters s).length (.const t []))
  · rfl
  · exact hc
  · rfl
  · exact ⟨_, (header_equal hi hp hx hz hS).choose_spec.hasType.2⟩
  · exact header_forward hi hp hx hz hS

/-- Common header alignment is strictly more permissive than the directed
certificate on genuine well-formed registered prefixes retaining canonical Eq.
The same full environment core is used for both conditions. This separates
alignment conditions only: no sufficiency or strict-smallness claim relative
to PropFront or strengthening is made. -/
theorem exists_registered_common_header_not_computed
    {base : VEnv} (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hi : base.projections s oldInfo) (hp : oldInfo.nparams = 0)
    (hx : oldInfo.nindices = 0) (hz : oldInfo.numFields = 0)
    (hS : base.HasType 0 [] (.const s []) (.sort (.succ .zero)))
    (ht : base.constants t = none) (hc : base.constants c = none) (hne : t ≠ c) :
    ∃ E : VEnv, ∃ hE : E.WF, base ≤ E ∧ E.HasCanonicalEq ∧
      E.projections t (HeaderRegistration.info 0 (parameters s) t c) ∧
      (letI := hE.params 0
       CommonStructureFamilyHeader EnvironmentCore.definitions t
         (HeaderRegistration.info 0 (parameters s) t c) [] ∧
       ¬ ComputedStructureFamilyHeader EnvironmentCore.definitions t
         (HeaderRegistration.info 0 (parameters s) t c) []) := by
  letI := hbase.params 0
  have HE := header_equal hi hp hx hz hS
  obtain ⟨envT, envC, hT, hC⟩ := HeaderRegistration.exists_constants
    (U := 0) (ps := parameters s) (T := storedHeader s oldInfo.ctorName) ht hc hne
  let entry : VProjectionEntry := { typeName := t, info := HeaderRegistration.info 0 (parameters s) t c }
  let E := envC.addProjections [entry]
  have hE : E.WF := HeaderRegistration.register_wf hbase hne HE hT hC
  have hle : base ≤ E := (VEnv.addConstVals_le hT).trans
    ((VEnv.addConstVals_le hC).trans VEnv.addProjections_le)
  have hlookup : E.constants t = some
      (HeaderRegistration.family 0 (parameters s) (storedHeader s oldInfo.ctorName) t c).toVConstant :=
    ((VEnv.addConstVals_le hC).trans VEnv.addProjections_le).constants
      (VEnv.addConstVals_get hT (ci := (HeaderRegistration.family 0 (parameters s)
        (storedHeader s oldInfo.ctorName) t c).toVConstVal) (by simp))
  refine ⟨E, hE, hle, heq.mono hle, ?_, ?_⟩
  · exact VEnv.addProjections_iff.2 (.inl ⟨entry, by simp, rfl, rfl⟩)
  · letI := hE.params 0
    exact ⟨explicit_registered_header_common (hle.projections hi) hp hx hz (hS.mono hle) hlookup,
      explicit_registered_header_not_computed (heq.mono hle) EnvironmentCore.sound
        (hle.projections hi) hp hx hz (hS.mono hle) hlookup⟩

end Lean4Lean.VEnv.Strengthening
