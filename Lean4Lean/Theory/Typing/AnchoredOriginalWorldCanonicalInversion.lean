import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidAdequacy
import Lean4Lean.Theory.Typing.CanonicalRegistryOfWF

/-! Fix the actual canonical environment data from public well-formedness.
The conditional inversion entry adds only the operative world banks, without
supplied registry tables, rigidity, scope, or equation stratification. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
variable {env : VEnv}

noncomputable def worldAdequacyRegistry (henv : env.WF) : CanonicalHead.Registry :=
  Classical.choose (Classical.choose_spec henv.canonicalRegistry)

theorem worldAdequacyRegistry_contract (henv : env.WF) :
    CanonicalDataHead.Registry.EnvironmentContract (worldAdequacyRegistry henv) env
      (Classical.choose henv.canonicalRegistry) :=
  Classical.choose_spec (Classical.choose_spec henv.canonicalRegistry)

/-- Exact rigid-application inversion for the canonical registry and equation
stratification actually constructed from the original public hypothesis. -/
theorem rawRigidInversionOfCanonicalWorldBanks
    (henv : env.WF) (formed : OnCtx Γ (env.IsType U)) (rigid : env.Rigid name)
    (unary : ∀ budget, WorldBoundedUnaryAt env U (worldAdequacyRegistry henv)
      henv.ordered.equationStrata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U (worldAdequacyRegistry henv)
      henv.ordered.equationStrata (fun _ => True) budget)
    (equal : env.IsDefEqU U Γ (mkApps (.const name levels) arguments)
      (mkApps (.const name rightLevels) rightArguments))
    (typed : env.HasType U Γ (mkApps (.const name levels) arguments) (.sort level)) :
    List.Forall₂ (· ≈ ·) levels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) arguments rightArguments := by
  have contract := worldAdequacyRegistry_contract henv
  exact rawRigidInversionOfWorldBanks henv.ordered.equationStrata henv contract.scope
    contract.rigid formed rigid unary replay equal typed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
