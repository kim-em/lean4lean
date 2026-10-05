import Lean4Lean.Theory.Typing.FieldFormationCongruence
import Lean4Lean.Theory.Typing.ProjectionIndexBound
import Lean4Lean.Theory.Typing.AnchoredInversionReadback

/-! Exact field readback. High imports currently provide only pure telescope
syntax; the proof must be dependency-audited before foundation integration. -/
namespace Lean4Lean.VEnv
open VExpr
open private projectionParams_shape projectionFields_bound from
  Lean4Lean.Theory.Typing.ProjectionIndexBound

private theorem selectedFieldDomain {env : VEnv} {info : VProjectionInfo}
    {levels : List VLevel} {params : List VExpr}
    (ordered : env.Ordered) (registered : env.projections name info)
    (selected : info.fieldType name levels params index major = some field)
    (parameterCount : params.length = info.nparams) :
    ∃ domains result, info.ctorType = wrapForalls domains result ∧
      info.nparams + index < domains.length := by
  obtain ⟨decl, type, ctor, _, _, _, _, _, _, _, _, _, ctorType,
    _, _, _, raw, _⟩ := ordered.projectionShape registered
  obtain ⟨domains, result, shape, _, _, resultHead, _⟩ := raw.forallArity
  have result_eq : result = mkApps (.const type.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← resultHead]
    exact (mkApps_getAppFnArgs_eq result).symm
  refine ⟨domains, result, ctorType.symm.trans shape, ?_⟩
  unfold VProjectionInfo.fieldType at selected
  split at selected <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨tail, parameters, fields⟩ := selected
  rw [← ctorType, shape, result_eq, instL_wrapForalls, instL_mkApps] at parameters
  obtain ⟨remaining, arguments, rfl, remainingLength⟩ := projectionParams_shape parameters
  have fieldBound := projectionFields_bound fields
  simp only [Nat.zero_add] at fieldBound
  simp only [List.length_map] at remainingLength
  omega

private theorem levelsInstOuter
    (comparison : EqUpToLevels U left right)
    (arguments : ∀ argument ∈ args, EqUpToLevels U argument argument) :
    EqUpToLevels U (left.instOuter args) (right.instOuter args) := by
  induction args generalizing left right with
  | nil => exact comparison
  | cons a args ih =>
    exact ih (EqUpToLevels.instN (arguments a (by simp)) comparison)
      (fun argument member => arguments argument (by simp [member]))

private theorem rightParameterTyped {env : VEnv}
    (parameters : List.Forall₂ (env.IsDefEqU U Γ) leftParams rightParams) :
    ∀ x ∈ rightParams, ∃ A, env.HasType U Γ x A := by
  induction parameters with
  | nil => simp
  | cons equal rest ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨_, equal⟩ := equal
      exact ⟨_, equal.hasType.2⟩
    · exact ih x hx

theorem fieldTypeCongruenceOfCompatibility
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (formed : OnCtx Γ (env.IsType U))
    (registered : env.projections name info)
    (leftWF : ∀ l ∈ leftLevels, l.WF U) (rightWF : ∀ l ∈ rightLevels, l.WF U)
    (levels : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (leftCount : leftLevels.length = info.uvars) (rightCount : rightLevels.length = info.uvars)
    (leftParamsCount : leftParams.length = info.nparams)
    (rightParamsCount : rightParams.length = info.nparams)
    (parameters : List.Forall₂ (env.IsDefEqU U Γ) leftParams rightParams)
    (majors : env.IsDefEqU U Γ leftMajor rightMajor)
    (leftSelected : info.fieldType name leftLevels leftParams index leftMajor = some leftField)
    (rightSelected : info.fieldType name rightLevels rightParams index rightMajor = some rightField)
    (typed : env.HasType U Γ leftField assigned) :
    env.IsDefEq U Γ leftField rightField assigned := by
  obtain ⟨domains, result, shape, bound⟩ := selectedFieldDomain ordered registered leftSelected leftParamsCount
  have leftShape := Option.some.inj (leftSelected.symm.trans
    (info.fieldType_eq_instOuter shape leftCount leftParamsCount bound))
  have rightShape := Option.some.inj (rightSelected.symm.trans
    (info.fieldType_eq_instOuter shape rightCount rightParamsCount bound))
  let template := domains[info.nparams + index]
  let rightArgs := rightParams ++ (List.range index).map (fun j => .proj name j rightMajor)
  have first := fieldTemplateCongruence ordered compatible parameters majors
    (template.instL leftLevels) name index formed
    (by rw [leftShape, instOuter_eq_subst] at typed; exact typed)
  have first' : env.IsDefEq U Γ leftField
      ((template.instL leftLevels).instOuter rightArgs) assigned := by
    apply IsDefEqU.atLeftTypeOfCompatibility compatible formed typed
    rw [leftShape, instOuter_eq_subst, instOuter_eq_subst]
    exact first
  have contextStrong := CtxStrong.strong ordered formed
  have contextLevels := contextStrong.levelWF
  have argsLevels : ∀ argument ∈ rightArgs, EqUpToLevels U argument argument := by
    intro argument member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨_, argumentTyped⟩ := rightParameterTyped parameters argument member
      exact (EqUpToLevels.refl contextLevels (argumentTyped.strong ordered formed)).1
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
      obtain ⟨_, equal⟩ := majors
      exact .proj (EqUpToLevels.refl contextLevels (equal.strong ordered formed)).2
  have levelChange := levelsInstOuter (EqUpToLevels.instL_expr template leftWF rightWF levels) argsLevels
  have original := first'.strong ordered formed
  have comparison := EqUpToLevels.defeq ordered ordered.strong
    (CtxStrong.strong ordered formed) original (EqUpToLevels.refl contextLevels original).1 levelChange
  simpa only [rightShape, template, rightArgs] using comparison.defeq

/-- The exact public field-inversion conclusion. Compatibility, rigid-head
inversion and sort inversion are explicit independent adequacy inputs; no
primitive projection of the selected field is assumed to be permitted. -/
theorem fieldTypeInvStratifiedOfCompatibility
    (henv : env.WF) (compatible : AssignedTypeCompatibility env U)
    (rigid : ∀ {Γ c ls ls' args args' u}, OnCtx Γ (env.IsType U) → env.Rigid c →
      env.IsDefEqU U Γ (mkApps (.const c ls) args) (mkApps (.const c ls') args') →
      env.HasType U Γ (mkApps (.const c ls) args) (.sort u) →
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args')
    (sorts : ∀ {Γ u v}, OnCtx Γ (env.IsType U) →
      env.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v)
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
  obtain ⟨_, familyTyped⟩ := hsource₁.isType henv.ordered hΓ
  obtain ⟨levelEqual, arguments⟩ := rigid hΓ (henv.projectionRigid hinfo) htypes familyTyped
  have parameters := (Lean4Lean.List.forall₂_append_split arguments
    (hparams₁.trans hparams₂.symm)).1
  have equal := fieldTypeCongruenceOfCompatibility henv.ordered compatible hΓ hinfo
    hlevels₁ hlevels₂ levelEqual huvars₁ huvars₂ hparams₁ hparams₂ parameters hmajor
    hfield₁ hfield₂ hF₁.hasType
  obtain ⟨_, levelPath⟩ := compatible hΓ equal.hasType.2 hF₂.hasType
  exact ⟨equal, sorts hΓ ⟨_, levelPath⟩⟩

end Lean4Lean.VEnv
