import Lean4Lean.Theory.Typing.Strengthening.StructureEtaParameterReduction
import Lean4Lean.Theory.Typing.Strengthening.SymmetricFamilyArguments

/-! # Structure eta overlaps from a phase between family instances

Family argument inversion turns a comparison of the exposed constructor's
family instance with the output instance into the parameter certificates
required by exact field joining. The family phase remains an explicit premise;
ordinary conversion has not been promoted to a phase.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- A family phase between the exposed and final constructor instances suffices
for the complete root structure-eta/computation overlap. Parameters may be data.
The phase premise is stronger than the conversion supplied by typing alone. -/
theorem structure_eta_compute_family_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hpc : ctorParams.length = info.nparams) (hfc : ctorFields.length = info.numFields)
    (hpo : outParams.length = info.nparams)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (ht : env.HasType univs Γ (structExpand family info levels params major) T)
    (HM : PrefixCompute actualD Γ major
      (mkApps (.const info.ctorName ctorLevels) (ctorParams ++ ctorFields)))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major)
      (mkApps (.const info.ctorName levels) (outParams ++ outFields)))
    (HF : PrefixEtaJoin actualD Γ (mkApps (.const family ctorLevels) ctorParams)
      (mkApps (.const family levels) outParams))
    (hleft : env.IsType univs Γ (mkApps (.const family ctorLevels) ctorParams))
    (hright : env.IsType univs Γ (mkApps (.const family levels) outParams)) :
    PrefixEtaJoin actualD Γ major
      (mkApps (.const info.ctorName levels) (outParams ++ outFields)) := by
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  obtain ⟨u, hu⟩ := hleft
  obtain ⟨v, hv⟩ := hright
  have HP := (HF.family_arguments hs hΓ hi
    (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionRigid hi)) hu hv).2
  exact structure_eta_compute_parameter_phase hcon hΓ hi hp hpc hfc hpo hm ht HM R HP

end Lean4Lean.VEnv.Strengthening.PureObservation
