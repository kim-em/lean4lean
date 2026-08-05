import Lean4Lean.Theory.Inductive

namespace Lean4Lean.Tests.InductiveTheory

open Lean4Lean

def enumCtor : VConstVal where
  name := `Enum0.mk
  uvars := 0
  type := .const `Enum0 []

def enumType : VInductiveType where
  name := `Enum0
  uvars := 0
  type := .sort (.succ .zero)
  numIndices := 0
  resultLevel := .succ .zero
  ctors := [enumCtor]

def enumDecl : VInductDecl where
  uvars := 0
  nparams := 0
  types := [enumType]
  isUnsafe := false

def enumTypesEnv : VEnv where
  constants := fun n => if `Enum0 = n then some enumType.toVConstant else none
  defeqs := fun _ => False

def enumCtorsEnv : VEnv where
  constants := fun n =>
    if `Enum0.mk = n then some enumCtor.toVConstant else enumTypesEnv.constants n
  defeqs := fun _ => False

theorem enumDecl_wf : enumDecl.WF .empty := by
  unfold VInductDecl.WF VInductDecl.SourceWF VInductDecl.FormationWF
  have haddType : VEnv.empty.addConsts enumDecl.typeConstants = some enumTypesEnv := by
    simp [enumDecl, enumType, enumTypesEnv, VInductDecl.typeConstants,
      VEnv.addConsts, VEnv.addConst, VEnv.empty]
  have haddCtor : enumTypesEnv.addConsts enumDecl.constructorConstants = some enumCtorsEnv := by
    simp [enumDecl, enumType, enumCtor, enumTypesEnv, enumCtorsEnv,
      VInductDecl.constructorConstants, VEnv.addConsts, VEnv.addConst]
  have htype : enumType.toVConstant.WF VEnv.empty := by
    exact ⟨_, .sortDF (by trivial) (by trivial) (by rfl)⟩
  have hlookup : enumTypesEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [enumTypesEnv]
  have hctor : enumCtor.toVConstant.WF enumTypesEnv := by
    exact ⟨_, .constDF hlookup nofun nofun rfl .nil⟩
  constructor
  · refine ⟨by simp [enumDecl], by simp [enumDecl, VInductDecl.sourceNames,
      VInductDecl.typeConstants, VInductDecl.constructorConstants, enumType, enumCtor], ?_, ?_,
      enumTypesEnv, enumCtorsEnv, haddType, haddCtor, ?_, ?_⟩
    · simp [enumDecl, enumType]
    · simp [enumDecl, enumType, enumCtor, VInductDecl.constructorConstants]
    · intro type hmem
      simp only [enumDecl, List.mem_singleton] at hmem
      subst type
      exact htype
    · intro ctor hmem
      simp only [enumDecl, enumType, VInductDecl.constructorConstants,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hmem
      subst ctor
      exact hctor
  · refine ⟨[], .succ .zero, enumTypesEnv, haddType, ?_, ?_⟩
    · intro type hmem
      simp [enumDecl] at hmem
      subst type
      refine ⟨rfl, .sort (.succ .zero), [], .sort (.succ .zero), [],
        .sort (.succ .zero), .sort (.succ (.succ .zero)), ?_, rfl, rfl, ?_, ?_⟩
      · exact .sortDF (by trivial) (by trivial) rfl
      · exact .zero
      · exact .sortDF (by trivial) (by trivial) rfl
    · intro type htypeMem ctor hctorMem
      simp [enumDecl] at htypeMem
      subst type
      simp [enumType] at hctorMem
      subst ctor
      refine ⟨.const `Enum0 [], [], .const `Enum0 [], .sort (.succ .zero), ?_, rfl, .zero, ?_⟩
      · exact .constDF hlookup nofun nofun rfl .nil
      · apply VInductDecl.CtorTailWF.result
          (result' := .const `Enum0 []) (type := .sort (.succ .zero))
        · simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, enumDecl, enumType,
            VExpr.getAppFnArgs.go, VInductDecl.paramVars]
        · exact .constDF hlookup nofun nofun rfl .nil

theorem recursiveOccurrence_positive :
    enumDecl.SyntacticallyPositive {} [] 0 (.const `Enum0 []) := by
  apply VInductDecl.SyntacticallyPositive.recursive
  simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
    enumDecl, enumType, VInductDecl.paramVars]

theorem negativeOccurrence_not_positive :
    ¬enumDecl.SyntacticallyPositive {} [] 0
      (.forallE (.const `Enum0 []) (.const `Enum0 [])) := by
  intro h
  cases h with
  | nonrecursive h => simp [VExpr.containsAnyConst, enumDecl, enumType] at h
  | forallE h _ _ _ => simp [VExpr.containsAnyConst, enumDecl, enumType] at h
  | recursive h =>
    simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
      enumDecl, enumType] at h

def enumRecursor : VConstVal where
  name := `Enum0.rec
  uvars := 0
  type := .forallE (.sort (.succ .zero))
    (.forallE (.sort .zero)
      (.forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))))

def enumRecursorShape : enumDecl.RecursorShape enumType enumRecursor where
  ownerIdx := 0
  owner_lt := by simp [enumDecl]
  owner_eq := rfl
  name := by simp [enumRecursor, VInductDecl.recursorName, enumType]
  uvars := Or.inl rfl
  params := []
  motives := [.sort (.succ .zero)]
  minors := [.sort .zero]
  indices := []
  major := [.const `Enum0 []]
  afterParams := enumRecursor.type
  afterMotives := .forallE (.sort .zero)
    (.forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0)))
  afterMinors := .forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))
  afterIndices := .forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))
  result := .app (.bvar 2) (.bvar 0)
  params_take := rfl
  motives_take := rfl
  minors_take := rfl
  indices_take := rfl
  major_take := rfl
  result_eq := by
    simp [VInductDecl.recursorResult, enumDecl, enumType, VExpr.mkApps]

def enumRule : VDefEq where
  uvars := 0
  lhs := .lam (.sort (.succ .zero)) (.lam (.sort .zero)
    (VExpr.mkApps (.const `Enum0.rec [])
      [.bvar 1, .bvar 0, .const `Enum0.mk []]))
  rhs := .lam (.sort (.succ .zero)) (.lam (.sort .zero) (.bvar 0))
  type := .forallE (.sort (.succ .zero))
    (.forallE (.sort .zero) (.sort .zero))

def enumBlock : VInductBlock where
  types := enumDecl.typeConstants
  ctors := enumDecl.constructorConstants
  recursors := [enumRecursor]
  rules := [enumRule]

def enumIota : enumDecl.IotaRule enumBlock enumType enumCtor enumRule where
  recursor := enumRecursor
  recursor_mem := by simp [enumBlock]
  recursor_name := by simp [enumRecursor, VInductDecl.recursorName, enumType]
  rule_uvars := rfl
  domains := [.sort (.succ .zero), .sort .zero]
  lhsBody := VExpr.mkApps (.const `Enum0.rec [])
    [.bvar 1, .bvar 0, .const `Enum0.mk []]
  rhsBody := .bvar 0
  typeBody := .sort .zero
  lhs_wrapped := rfl
  rhs_wrapped := rfl
  type_wrapped := rfl
  recursorLevels := []
  leadingArgs := [.bvar 1, .bvar 0]
  ctorLevels := []
  ctorArgs := []
  lhs_pattern := rfl
  recursor_levels := rfl
  ctor_levels := rfl
  leading_arity := rfl
  constructor_arity := by simp [enumDecl]
  parameter_args := rfl
  domains_arity := rfl
  fieldVars := []
  fieldVars_eq := rfl
  fields_in_scope := by simp
  rhs_guarded := .bvar

theorem enumOrdinaryCompilation : enumDecl.OrdinaryCompilation enumBlock where
  types := rfl
  ctors := rfl
  recursors := by
    exact .cons ⟨enumRecursorShape⟩ .nil
  rules := by
    exact .cons ⟨enumIota⟩ .nil
  names := by
    simp [enumBlock, enumDecl, enumType, enumCtor, enumRecursor,
      VInductDecl.typeConstants, VInductDecl.constructorConstants]

theorem enumCompiles : VInductDecl.CompilesTo .empty enumDecl enumBlock :=
  .ordinary enumOrdinaryCompilation

end Lean4Lean.Tests.InductiveTheory
