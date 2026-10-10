import Lean4Lean.Verify.Inductive.RecursorInput
import Lean4Lean.Verify.Inductive.Constructor.Tails

/-! # What the recursor phase reads of the constructor check

The source branch's `RecursorInput` carried its header-phase data directly (`sourceContext`,
`statsWF`, `parameterScope`, `recursorHeaders`, ...). On the scaffold's interface these are
reached through `CheckedFormation.headers : HeaderEnvironment`; this file names them as the
recursor port reads them. The constructor telescope data (`parameterPrefixes`, `constructorTails`,
`ownerNormalForms`) are fields of `RecursorInput`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RecursorInput

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

/-- The source context of the header phase. -/
abbrev sourceContext (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ContextWF c := R.headers.sourceContext

theorem sourceContextVEnv (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.sourceContext.venv = sourceEnv := R.headers.sourceContextVEnv

/-- The main local context of the header environment. -/
abbrev headerMLCtx (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : TypeChecker.MLCtx := R.headers.context.mlctx

/-- The header statistics over the header environment. -/
abbrev statsWF (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) :
    checkInductiveTypes.loopInd.HeaderStatsWF R.headerVEnv c.lparams R.headerMLCtx.vlctx stats
      decl depth := R.headers.statsWF

/-- The common parameters of the declaration. -/
abbrev params (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : List VExpr := R.headers.headers.params

/-- The parameter scope of the header phase. -/
abbrev parameterScope (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : VLCtx := R.headers.statsWF.parameterScope

/-- The header statistics over the source environment. -/
abbrev sourceStatsWF (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) :
    checkInductiveTypes.loopInd.HeaderStatsWF R.sourceContext.venv c.lparams
      R.sourceContext.mlctx.vlctx stats decl depth := R.headers.sourceStatsWF

theorem sourceHeaderParams (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.sourceStatsWF.headers.params = R.params := R.headers.sourceHeaderParams

theorem sourceParameterScope (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.sourceStatsWF.parameterScope = R.parameterScope :=
  R.headers.parameterScopeEq.symm

theorem checkedParameterScope (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.statsWF.parameterScope = R.parameterScope := rfl

theorem sourceLE (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : sourceEnv ≤ R.headerVEnv := VEnv.addConstVals_le R.headers.typesAdded

theorem checkedParams (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.statsWF.headers.params = R.params := R.headers.headerParams

theorem formationParams (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : R.formation.headers.params = R.params := R.params_eq

theorem headerLE (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : R.headerVEnv ≤ R.ctorVEnv := VEnv.addConstVals_le R.core.ctorsAdded

theorem ctorLE (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : R.ctorVEnv ≤ R.context.venv := by
  rw [R.contextVEnv]; exact VEnv.addProjections_le

/-- Transport the retained checked headers to the valid constructor environment, at the start
of the recursor phase. -/
def recursorHeaders (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) :
    checkInductiveTypes.loopInd.HeaderStatsWF
      R.context.venv c.lparams R.context.mlctx.vlctx stats decl depth := by
  let M := R.statsWF.mono (R.headerLE.trans R.ctorLE)
  exact {
    headers := M.headers
    normalizedSources := M.normalizedSources
    normalizedShapes := M.normalizedShapes
    isNotZero := M.isNotZero
    commonLevel := M.commonLevel
    levels := M.levels
    levelParams := M.levelParams
    uvars := M.uvars
    consts := M.consts
    indices := M.indices
    params := by simpa only [R.contextMLCtx] using M.params
    paramFVars := M.paramFVars
    parameterScope := M.parameterScope
    ambientScope := M.ambientScope
    scopeDecomposition := by simpa only [R.contextMLCtx] using M.scopeDecomposition
    ambientLength := M.ambientLength
    cachedScope := M.cachedScope
    parameterEmbedding := by simpa only [R.contextMLCtx] using M.parameterEmbedding
    paramsContext := M.paramsContext
    suffixParams := M.suffixParams }

theorem recursorHeaders_parameterScope (R : RecursorInput c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv) : R.recursorHeaders.parameterScope = R.parameterScope := by
  simp [recursorHeaders, checkInductiveTypes.loopInd.HeaderStatsWF.mono]

end RecursorInput

/-- The base environment of a translated declaration contains none of the declaration's type
or constructor names (the source branch's `TrInductDeclCore.headerBaseAvoidsSourceNames`). -/
theorem TrInductDeclCore.baseAvoidsSourceNames
    (H : TrInductDeclCore base lparams declNParams types isUnsafe decl envTypes envCtors)
    {name : Name} {ci : VConstant} (hlookup : base.constants name = some ci) :
    name ∉ decl.sourceNames := by
  intro hname
  have Hadd : base.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  have Hfresh := (VEnv.addConstVals_names_fresh Hadd).2
  unfold VInductDecl.sourceNames at hname
  simp only [List.mem_append] at hname
  rcases hname with htype | hctor
  · rcases List.mem_map.mp htype with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_left _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction
  · rcases List.mem_map.mp hctor with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_right _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction

namespace RecursorInput

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

private theorem forall₂_map_eq {α β γ} {P : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, P a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → l₁.map f = l₂.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp [hfg _ _ h, forall₂_map_eq hfg t]

/-- The kernel names of the header infos are the declaration's type names. -/
theorem headerInfoNames (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) :
    (R.headers.infos.map ConstantInfo.inductInfo).map (·.name) =
      decl.typeConstants.map (·.name) := by
  rw [List.map_map, VInductDecl.typeConstants, List.map_map]
  exact forall₂_map_eq (fun _ _ h => h.1.2) R.headers.trHeaders

/-- The kernel names of the new constructors are the declaration's constructor names. -/
theorem ctorInfoNames (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) :
    (R.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map (·.name) =
      decl.constructorConstants.map (·.name) := by
  rw [VInductDecl.constructorConstants, List.map_flatMap, List.map_flatMap]
  have h := forall₂_map_eq (f := fun iv : InductiveVal × List ConstructorVal =>
      (iv.2.map ConstantInfo.ctorInfo).map (·.name))
    (g := fun t : VInductiveType => t.ctors.map (·.name))
    (fun iv t ht => by
      rw [List.map_map]
      exact forall₂_map_eq (fun _ _ h => h.1.2) ht.ctors) R.trTypes
  have key : ∀ (l₁ : List (InductiveVal × List ConstructorVal)) (l₂ : List VInductiveType),
      l₁.map (fun iv => (iv.2.map ConstantInfo.ctorInfo).map (·.name)) =
        l₂.map (fun t => t.ctors.map (·.name)) →
      l₁.flatMap (fun iv => (iv.2.map ConstantInfo.ctorInfo).map (·.name)) =
        l₂.flatMap (fun t => t.ctors.map (·.name)) := by
    intro l₁ l₂ h; rw [List.flatMap_def, List.flatMap_def, h]
  exact key _ _ h

/-- Every constant of the constructor environment is a constant of the source environment, a
new header, or a new constructor. -/
theorem find?_origin (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) {n : Name} {ci : ConstantInfo} (h : ctorEnv.find? n = some ci) :
    c.env.find? n = some ci ∨ ci ∈ R.headers.infos.map ConstantInfo.inductInfo ∨
      ci ∈ R.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo := by
  have hWFc : c.env.constants.WF := R.headers.sourceContext.checking.tr.map_wf
  have hWFh : R.headerEnv.constants.WF := R.headers.context.checking.map_wf
  have hWFo : ctorEnv.constants.WF := R.context.checking.tr.map_wf
  have hnodup := TrInductDeclCore.sourceNames_nodup R.core
  rw [VInductDecl.sourceNames] at hnodup
  have hndH := (List.nodup_append.mp hnodup).1
  have hndC := (List.nodup_append.mp hnodup).2.1
  rw [← R.headerInfoNames] at hndH
  rw [← R.ctorInfoNames] at hndC
  have hfreshC : ∀ d ∈ R.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo),
      R.headerEnv.constants.find? d.name = none := by
    intro d hd
    obtain ⟨iv, hiv, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hd
    have := R.fresh iv hiv cv hcv
    rwa [Kernel.Environment.find?, hWFh.find?'_eq_find?] at this
  have hfreshH : ∀ d ∈ R.headers.infos.map ConstantInfo.inductInfo,
      c.env.constants.find? d.name = none := by
    intro d hd
    obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hd
    have := R.headers.fresh info hinfo
    rwa [Kernel.Environment.find?, hWFc.find?'_eq_find?] at this
  rw [Kernel.Environment.find?, hWFo.find?'_eq_find?, R.map_eq] at h
  rcases insertConsts_find? hWFh hfreshC hndC h with h | ⟨hmem, -⟩
  · rw [R.headers.map_eq] at h
    rcases insertConsts_find? hWFc hfreshH hndH h with h | ⟨hmem, -⟩
    · exact .inl (by rwa [Kernel.Environment.find?, hWFc.find?'_eq_find?])
    · exact .inr (.inl hmem)
  · exact .inr (.inr hmem)

end RecursorInput

end VerifyInductive
end Lean4Lean
