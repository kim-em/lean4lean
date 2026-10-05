import Lean4Lean.Theory.Typing.AnchoredDataDiagonal
import Lean4Lean.Theory.Typing.AnchoredDiagonal
import Lean4Lean.Theory.Typing.AnchoredDataLaws
import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection
import Batteries.Tactic.OpenPrivate

/-! Actual inert family syntax determines the displayed argument list.
Its exact fixed requests descend along literal lifts from the real private
world. This extracts parameter evidence for the original source seed. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
open private family_lift family_spine from Lean4Lean.Theory.Typing.AnchoredDataLaws
set_option backward.isDefEq.respectTransparency false

private theorem rawEqBack (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (equal : env.IsDefEq U Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)) :
    env.IsDefEq U Γ left right type := by
  induction route generalizing left right type with
  | proof insertion =>
    obtain ⟨embedding, map⟩ := insertion.toEmbedding henv
    have result := equal.subst henv embedding.typed (hΓ₀ := embedding.baseWF)
    simpa only [← map, embedding.leftInv] using result
  | context chain =>
    apply (chain.symm henv).eq henv
    simpa only [lift'_refl] using equal
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp] using equal

namespace RankedData

theorem RequestAdmission.mixedBack
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (route : MixedInsertion env U Γ Δ ρ)
    (admitted : RequestAdmission env U (relations env U registry n) Δ
      (request.rename ρ) (left.lift' ρ) (right.lift' ρ)) :
    RequestAdmission env U (relations env U registry n) Γ request left right := by
  obtain ⟨anchor, pair, typed, formed, code, first, second⟩ := admitted
  refine ⟨rawEqBack henv route anchor, rawEqBack henv route pair,
    Profile.rename_hasType_iff.mp typed, ?_, route.codeBack henv hscoped code,
    route.termBack henv first, route.termBack henv second⟩
  apply (Profile.rename_hasType_iff (ρ := ρ)).mp
  simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using formed

theorem Arguments.mixedBack
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (route : MixedInsertion env U Γ Δ ρ)
    (arguments : Arguments env U (relations env U registry n) Δ
      (requests.map (DataRequest.rename ρ)) (left.map (·.lift' ρ)) (right.map (·.lift' ρ))) :
    Arguments env U (relations env U registry n) Γ requests left right := by
  induction requests generalizing left right with
  | nil => cases left <;> cases right <;> cases arguments; exact .nil
  | cons request requests ih =>
    cases left with
    | nil => cases arguments
    | cons x xs =>
      cases right with
      | nil => cases arguments
      | cons y ys =>
        cases arguments with
        | cons head tail => exact .cons (head.mixedBack henv hscoped route) (ih tail)

private theorem literalHead
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (witness : FamilyWitness env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) right family) :
    (mkApps (.const family.name levels) params).lift' witness.map =
      mkApps (.const family.name witness.leftLevels) witness.leftArguments := by
  have stopped : CanonicalDataHead.step registry witness.leftExposure.result = none := by
    have terminal := witness.leftTerminal
    rw [← witness.leftExposure.result_eq, CanonicalDataHead.step_rename registry hscoped] at terminal
    exact Option.map_eq_none_iff.mp terminal
  have literalStopped := witness.headInert.step levels params
  have literalTrace : CanonicalDataHead.Trace registry
      (mkApps (.const family.name levels) params) [] (mkApps (.const family.name levels) params) := .refl
  obtain ⟨sameAdded, sameResult⟩ :=
    literalTrace.terminal_unique witness.leftExposure.trace literalStopped stopped
  have sameMap := witness.leftExposure.map_eq
  rw [← sameAdded] at sameMap
  simp only [List.length_nil, Lift.skipN, Lift.refl_comp] at sameMap
  have sameHead := witness.leftExposure.result_eq
  simpa only [← sameResult, sameMap] using sameHead

theorem FamilyWitness.literalArguments
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (witness : FamilyWitness env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) right family) :
    Arguments env U (relations env U registry n) Γ family.arguments params params := by
  have sameHead := literalHead henv hscoped witness
  rw [family_lift] at sameHead
  have sameArguments : params.map (·.lift' witness.map) = witness.leftArguments := by
    simpa only [family_spine] using congrArg Prod.snd (congrArg VExpr.getAppFnArgs sameHead)
  have arguments := witness.arguments.left_diagonal
    (fun _ _ _ _ _ _ related => Related.left_diagonal related)
  rw [← sameArguments] at arguments
  exact arguments.mixedBack henv hscoped (witness.leftExposure.insertion henv)

theorem FamilyWitness.literalFormation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (witness : FamilyWitness env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) right family) :
    ∃ level, Relevant level family.relevant ∧
      env.HasType U Γ (mkApps (.const family.name levels) params) (.sort level) ∧
      List.Forall₂ (· ≈ ·) family.levels levels := by
  have head := literalHead henv hscoped witness
  have typed := witness.leftType
  rw [← head] at typed
  have raw : env.HasType U Γ (mkApps (.const family.name levels) params) (.sort witness.leftLevel) := by
    apply rawEqBack henv (witness.leftExposure.insertion henv)
    simpa only [HasType, lift'] using typed
  rw [family_lift] at head
  have same : levels = witness.leftLevels := by
    have same := congrArg Prod.fst (congrArg VExpr.getAppFnArgs head)
    simp only [family_spine] at same
    exact (VExpr.const.inj same).2
  exact ⟨witness.leftLevel, witness.leftRelevance, raw, same ▸ witness.leftUniverses⟩

theorem FamilyRelation.literalArguments
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (related : FamilyRelation env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) right family) :
    Arguments env U (relations env U registry n) Γ family.arguments params params := by
  obtain ⟨witness⟩ := related.atBase formed
  exact witness.literalArguments henv hscoped

theorem FamilyRelation.literalFormation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (related : FamilyRelation env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) right family) :
    ∃ level, Relevant level family.relevant ∧
      env.HasType U Γ (mkApps (.const family.name levels) params) (.sort level) ∧
      List.Forall₂ (· ≈ ·) family.levels levels := by
  obtain ⟨witness⟩ := related.atBase formed
  exact witness.literalFormation henv hscoped

theorem FamilyRelation.typeConversion
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)}
    (related : FamilyRelation env U registry (relations env U registry n) Γ left right family) :
    TypeConversion env U Γ left right := by
  obtain ⟨witness⟩ := related.atBase formed
  exact (witness.leftExposure.insertion henv).pathBack henv witness.path

end RankedData
end Lean4Lean.AnchoredSemantics
