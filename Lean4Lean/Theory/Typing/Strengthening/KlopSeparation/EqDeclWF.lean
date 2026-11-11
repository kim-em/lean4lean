import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqDecl
import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped

/-! # Well-formedness of the hand-built declaration of `Eq`

Work in progress towards `exists_minimalKlopEnv`: the declaration `eqDecl`, its staged
environments, and (so far) its source judgment. Follows `Tests/InductiveTheory.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

def eqCtor : VConstVal where
  name := ``Eq.refl
  uvars := 1
  type := canonicalEqReflType

def eqType : VInductiveType where
  name := ``Eq
  uvars := 1
  type := canonicalEqType
  numIndices := 1
  resultLevel := .zero
  ctors := [eqCtor]

/-- The kernel's rule of `Eq.rec`: on `Eq.refl`, return the minor premise. -/
def eqRecRule : VRecRule where
  ctor := ``Eq.refl
  ctorParams := 2
  nfields := 0
  rhs := eqRule.rhs

/-- The kernel's recursor of `Eq`, with its rule. -/
def eqVRec : VRecursor :=
  { eqRecursor with
    all := [``Eq]
    numParams := 2
    numMotives := 1
    numMinors := 1
    numIndices := 1
    k := true
    rules := [eqRecRule] }

def eqDecl : VInductDecl where
  uvars := 1
  nparams := 2
  types := [eqType]
  isUnsafe := false
  recs := [eqVRec]

def eqTypesEnv : VEnv where
  constants := fun n => if ``Eq = n then some eqType.toVConstant else none
  defeqs := fun _ => False
  pats := fun _ _ => False

def eqCtorsEnv : VEnv where
  constants := fun n =>
    if ``Eq.refl = n then some eqCtor.toVConstant else eqTypesEnv.constants n
  defeqs := fun _ => False
  pats := fun _ _ => False

theorem addEqTypes : VEnv.empty.addConstVals eqDecl.typeConstants = some eqTypesEnv := by
  simp [eqDecl, eqType, eqTypesEnv, VInductDecl.typeConstants,
    VEnv.addConstVals, VEnv.addConst, VEnv.empty]

theorem addEqConstructors :
    eqTypesEnv.addConstVals eqDecl.constructorConstants = some eqCtorsEnv := by
  simp [eqDecl, eqType, eqCtor, eqTypesEnv, eqCtorsEnv,
    VInductDecl.constructorConstants, VEnv.addConstVals, VEnv.addConst]

/-- `Eq.{u} : ∀ α : Sort u, α → α → Prop` is a type in any environment. -/
theorem eqTypeTyping {env : VEnv} {U : Nat} (hU : 0 < U) (Γ : List VExpr) :
    env.HasType U Γ canonicalEqType
      (.sort (.imax (.succ (.param 0)) (.imax (.param 0) (.imax (.param 0) (.succ .zero))))) := by
  have hp : (VLevel.param 0).WF U := hU
  refine .forallEDF (.sortDF hp hp rfl) (.forallEDF (.bvar .zero) (.forallEDF ?_ ?_))
  · exact .bvar (.succ .zero)
  · exact .sortDF trivial trivial rfl

/-- `@Eq.{u} α a b : Prop`, from the lookup of `Eq`. -/
theorem eqAppTyping {env : VEnv} {U : Nat} {Γ : List VExpr} {u : VLevel} {α a b : VExpr}
    (h : env.constants ``Eq = some eqType.toVConstant) (hu : u.WF U)
    (hα : env.HasType U Γ α (.sort u)) (ha : env.HasType U Γ a α) (hb : env.HasType U Γ b α) :
    env.HasType U Γ (.app (.app (.app (.const ``Eq [u]) α) a) b) (.sort .zero) := by
  have hc : env.HasType U Γ (.const ``Eq [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    have := HasType.const (env := env) (U := U) (Γ := Γ) h (ls := [u]) (by simpa using hu) rfl
    simpa [eqType, canonicalEqType, VExpr.instL, VLevel.inst] using this
  have h1 := hc.app hα
  simp only [VExpr.inst, VExpr.instVar] at h1
  have h2 := HasType.app (by simpa using h1) ha
  simp only [VExpr.inst] at h2
  have h3 := HasType.app (by simpa [VExpr.inst_lift] using h2) hb
  simpa [VExpr.inst] using h3

theorem eqCtorTyping : eqCtor.toVConstant.WF eqTypesEnv := by
  have hl : eqTypesEnv.constants ``Eq = some eqType.toVConstant := by simp [eqTypesEnv]
  have hp : (VLevel.param 0).WF 1 := by decide
  have h : eqTypesEnv.HasType 1 [.bvar 0, .sort (.param 0)]
      (.app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
    eqAppTyping hl hp (.bvar (.succ .zero)) (.bvar .zero) (.bvar .zero)
  exact ⟨_, .forallEDF (.sortDF hp hp rfl) (.forallEDF (.bvar .zero) h)⟩

theorem eqDecl_source : eqDecl.SourceWF .empty := by
  refine ⟨by simp [eqDecl], by simp [eqDecl, VInductDecl.sourceNames,
      VInductDecl.typeConstants, VInductDecl.constructorConstants, eqType, eqCtor], ?_, ?_,
      eqTypesEnv, eqCtorsEnv, addEqTypes, addEqConstructors, ?_, ?_⟩
  · simp [eqDecl, eqType]
  · simp [eqDecl, eqType, eqCtor, VInductDecl.constructorConstants]
  · intro type hmem
    simp only [eqDecl, List.mem_singleton] at hmem
    subst type
    exact ⟨_, eqTypeTyping (by decide) []⟩
  · intro ctor hmem
    simp only [eqDecl, eqType, VInductDecl.constructorConstants,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hmem
    subst ctor
    exact eqCtorTyping

/-- The common parameter telescope `(α : Sort u) (a : α)`. -/
def eqParams : List VExpr := [.sort (.param 0), .bvar 0]

/-- `@Eq α a a` under the parameters. -/
def eqReflResult : VExpr :=
  .app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)

theorem eqParamsDefEq {env : VEnv} : eqDecl.ParamsDefEq env eqParams eqParams := by
  have hp : (VLevel.param 0).WF 1 := by decide
  exact .succ (.succ .zero (.sortDF hp hp rfl)) (.bvar .zero)

theorem eqReflResultTyping :
    eqTypesEnv.HasType 1 [.bvar 0, .sort (.param 0)] eqReflResult (.sort .zero) :=
  eqAppTyping (by simp [eqTypesEnv]) (by decide) (.bvar (.succ .zero)) (.bvar .zero)
    (.bvar .zero)

theorem eqReflResult_valid : eqDecl.ValidIndAppAt (some ``Eq) 0 eqReflResult := by
  simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, eqDecl, eqType, eqReflResult,
    VExpr.getAppFnArgs.go, VInductDecl.paramVars]
  exact ⟨by decide, .bvar 0⟩

theorem eqFormation : VInductDecl.OrdinaryFormationWF .empty eqDecl := by
  have hp : (VLevel.param 0).WF 1 := by decide
  refine ⟨eqParams, .zero, eqTypesEnv, addEqTypes, ?_, ?_, ?_⟩
  · intro type hmem
    simp [eqDecl] at hmem
    subst type
    refine ⟨rfl, canonicalEqType, eqParams, .forallE (.bvar 1) (.sort .zero), [.bvar 1],
      .sort .zero, _, eqTypeTyping (by decide) [], rfl, rfl, eqParamsDefEq, ?_⟩
    exact .sortDF trivial trivial rfl
  · intro type htype ctor hctor
    simp [eqDecl] at htype
    subst type
    simp [eqType] at hctor
    subst ctor
    refine ⟨⟨eqParams, eqReflResult, rfl, eqParamsDefEq⟩, ?_⟩
    refine ⟨canonicalEqReflType, eqParams, eqReflResult, _, eqParams.reverse,
      eqCtorTyping.choose_spec, rfl, eqParamsDefEq, eqParamsDefEq, ?_⟩
    exact .result eqReflResult_valid eqReflResultTyping
  · intro type htype ctor hctor
    simp [eqDecl] at htype
    subst type
    simp [eqType] at hctor
    subst ctor
    refine ⟨eqParams, eqReflResult, rfl, by simp [eqDecl, eqParams], ?_, rfl⟩
    exact eqReflResult_valid.raw

end VEnv.Strengthening
end Lean4Lean
