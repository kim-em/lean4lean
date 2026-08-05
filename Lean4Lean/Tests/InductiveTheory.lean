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
    enumDecl.SyntacticallyPositive 0 (.const `Enum0 []) := by
  apply VInductDecl.SyntacticallyPositive.recursive
  simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
    enumDecl, enumType, VInductDecl.paramVars]

theorem negativeOccurrence_not_positive :
    ¬enumDecl.SyntacticallyPositive 0
      (.forallE (.const `Enum0 []) (.const `Enum0 [])) := by
  intro h
  cases h with
  | nonrecursive h => simp [VExpr.containsAnyConst, enumDecl, enumType] at h
  | forallE h _ => simp [VExpr.containsAnyConst, enumDecl, enumType] at h
  | recursive h =>
    simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
      enumDecl, enumType] at h

def enumRecursor : VConstVal where
  name := `Enum0.rec
  uvars := 0
  type := .sort (.succ .zero)

def enumRule : VDefEq where
  uvars := 0
  lhs := .lam (.sort .zero)
    (.app (.const `Enum0.rec []) (.const `Enum0.mk []))
  rhs := .lam (.sort .zero) (.bvar 0)
  type := .forallE (.sort .zero) (.sort .zero)

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
  domains := [.sort .zero]
  lhsBody := .app (.const `Enum0.rec []) (.const `Enum0.mk [])
  rhsBody := .bvar 0
  typeBody := .sort .zero
  lhs_wrapped := rfl
  rhs_wrapped := rfl
  type_wrapped := rfl
  recursorLevels := []
  leadingArgs := []
  ctorLevels := []
  ctorArgs := []
  lhs_pattern := rfl
  fieldVars := []
  fields_in_scope := by simp
  rhs_guarded := .bvar

theorem enumOrdinaryCompilation : enumDecl.OrdinaryCompilation enumBlock where
  types := rfl
  ctors := rfl
  recursors := by
    exact .cons (by simp [enumRecursor, enumDecl, enumType,
      VInductDecl.recursorName]) .nil
  rules := by
    exact .cons ⟨enumIota⟩ .nil
  names := by
    simp [enumBlock, enumDecl, enumType, enumCtor, enumRecursor,
      VInductDecl.typeConstants, VInductDecl.constructorConstants]

theorem enumCompiles : VInductDecl.CompilesTo .empty enumDecl enumBlock :=
  .ordinary enumOrdinaryCompilation

end Lean4Lean.Tests.InductiveTheory
