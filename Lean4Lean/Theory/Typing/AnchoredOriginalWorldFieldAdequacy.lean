import Lean4Lean.Theory.Typing.FieldAdequacy
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUniqueTyping
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidAdequacy

/-! Exact field inversion from operative all-budget banks and the canonical
registry's syntactic rigid-head registration. All inversion inputs are derived
internally; no admitted inversion theorem is invoked. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics

theorem fieldTypeInvStratifiedOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (rigidHeads : ∀ name, env.Rigid name → CanonicalDataHead.HeadInert registry name)
    (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections typeName info)
    (hlevels₁ : ∀ l ∈ levels₁, l.WF U) (huvars₁ : levels₁.length = info.uvars)
    (hparams₁ : params₁.length = info.nparams) (hindices₁ : indexArgs₁.length = info.nindices)
    (hfield₁ : info.fieldType typeName levels₁ params₁ index sourceMajor₁ = some fieldType₁)
    (hsource₁ : env.HasType U Γ sourceMajor₁
      (mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁)))
    (hlevels₂ : ∀ l ∈ levels₂, l.WF U) (huvars₂ : levels₂.length = info.uvars)
    (hparams₂ : params₂.length = info.nparams) (hindices₂ : indexArgs₂.length = info.nindices)
    (hfield₂ : info.fieldType typeName levels₂ params₂ index sourceMajor₂ = some fieldType₂)
    (hsource₂ : env.HasType U Γ sourceMajor₂
      (mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)))
    (hclosed : info.ctorType.Closed)
    (hmajor : env.IsDefEqU U Γ sourceMajor₁ sourceMajor₂)
    (htypes : env.IsDefEqU U Γ
      (mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁))
      (mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)))
    (hF₁ : env.HasTypeStratified U Γ fieldType₁ (.sort fieldLevel₁) true n)
    (hF₂ : env.HasTypeStratified U Γ fieldType₂ (.sort fieldLevel₂) true n') :
    env.IsDefEq U Γ fieldType₁ fieldType₂ (.sort fieldLevel₁) ∧
      fieldLevel₁ ≈ fieldLevel₂ := by
  have compatible : AssignedTypeCompatibility env U := by
    intro context expression A B formed left right
    exact rawUniqueTypingOfWorldBanks strata henv formed replay left right
  have sorts : ∀ {context u v}, OnCtx context (env.IsType U) →
      env.IsDefEqU U context (.sort u) (.sort v) → u ≈ v := by
    intro context u v formed equal
    exact rawSortLevelsOfWorldBanks strata henv hscoped formed unary equal
  have rigid : ∀ {Γ c ls ls' args args' u}, OnCtx Γ (env.IsType U) → env.Rigid c →
      env.IsDefEqU U Γ (mkApps (.const c ls) args) (mkApps (.const c ls') args') →
      env.HasType U Γ (mkApps (.const c ls) args) (.sort u) →
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' := by
    intro context name levels rightLevels arguments rightArguments level formed inert equal typed
    exact rawRigidInversionOfWorldBanks strata henv hscoped rigidHeads formed inert unary replay equal typed
  exact fieldTypeInvStratifiedOfCompatibility henv compatible rigid sorts hΓ hinfo
    hlevels₁ huvars₁ hparams₁ hindices₁ hfield₁ hsource₁
    hlevels₂ huvars₂ hparams₂ hindices₂ hfield₂ hsource₂ hclosed hmajor htypes hF₁ hF₂

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
