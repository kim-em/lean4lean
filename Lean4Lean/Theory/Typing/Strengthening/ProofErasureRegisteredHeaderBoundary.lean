import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeaderRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Confluence.Params

/-! # A registered family without a directed computed-header certificate

The ordinary family/constructor alignment accepted by the projection-stage
judgment does not imply the directed certificate used by the exact native
history theorem. The witness is installed in a genuine well-formed extension
and retains canonical Eq and all the original environment's declarations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ExplicitHeaderBoundary

/-- The fixed stored header cannot supply the computed-family-header
certificate, even though its constructor prefix is an ordinarily equal,
closed, sort-ending header. The result sort in the certificate is unrestricted. -/
theorem explicit_registered_header_not_computed [Params] {D : PureObservation.Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s oldInfo) (hp : oldInfo.nparams = 0)
    (hx : oldInfo.nindices = 0) (hz : oldInfo.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hc : env.constants t = some
      (HeaderRegistration.family 0 (parameters s) (storedHeader s oldInfo.ctorName) t c).toVConstant) :
    ¬ ComputedStructureFamilyHeader D t (HeaderRegistration.info 0 (parameters s) t c) [] := by
  rintro ⟨ps, tail, fi, v, Htake, hfi, _, hT, R⟩
  have hInst : (HeaderRegistration.info 0 (parameters s) t c).ctorType.instL [] =
      VExpr.wrapForalls (parameters s) (etaOpen (parameters s).length (.const t [])) := rfl
  rw [hInst] at Htake
  change (VExpr.wrapForalls (parameters s) _).takeForalls (parameters s).length = _ at Htake
  rw [VExpr.takeForalls_wrapForalls] at Htake
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Htake)
  rw [hc] at hfi
  cases Option.some.inj hfi
  have EI : (HeaderRegistration.family 0 (parameters s)
      (storedHeader s oldInfo.ctorName) t c).type.instL [] = storedHeader s oldInfo.ctorName := rfl
  change ScopedCompute _ _ (proofErase [] ((HeaderRegistration.family 0 (parameters s)
    (storedHeader s oldInfo.ctorName) t c).type.instL [])) _ at R
  rw [EI] at R
  exact no_header_compute heq hs hi hp hx hz hS hT R

/-- Given a canonical-Eq environment with a positive empty structure and two
fresh names, install a new family and its fieldless constructor, and register
their actual projection entry. The extension is well formed and canonical-Eq,
but the new registered family has no computed-header certificate even for the
full environment core. Thus general registration cannot discharge that extra
premise of the exact native-history theorem. This is a projection-stage
prefix; no claim about a generated recursor or strengthening failure is made. -/
theorem exists_registered_header_without_computed
    {base : VEnv} (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hi : base.projections s oldInfo) (hp : oldInfo.nparams = 0)
    (hx : oldInfo.nindices = 0) (hz : oldInfo.numFields = 0)
    (hS : base.HasType 0 [] (.const s []) (.sort (.succ .zero)))
    (ht : base.constants t = none) (hc : base.constants c = none) (hne : t ≠ c) :
    ∃ E : VEnv, ∃ hE : E.WF, base ≤ E ∧ E.HasCanonicalEq ∧
      E.projections t (HeaderRegistration.info 0 (parameters s) t c) ∧
      (HeaderRegistration.info 0 (parameters s) t c).nindices = 0 ∧
      (HeaderRegistration.info 0 (parameters s) t c).numFields = 0 ∧
      (letI := hE.params 0
       ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx [])
         (proofErase [] (chosenHeader s)) (proofErase [] (storedHeader s oldInfo.ctorName)) ∧
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
  refine ⟨E, hE, hle, heq.mono hle, ?_, rfl, rfl, ?_⟩
  · exact VEnv.addProjections_iff.2 (.inl ⟨entry, by simp, rfl, rfl⟩)
  · letI := hE.params 0
    exact ⟨header_forward (hle.projections hi) hp hx hz (hS.mono hle),
      explicit_registered_header_not_computed (heq.mono hle) EnvironmentCore.sound
        (hle.projections hi) hp hx hz (hS.mono hle) hlookup⟩

end Lean4Lean.VEnv.Strengthening
