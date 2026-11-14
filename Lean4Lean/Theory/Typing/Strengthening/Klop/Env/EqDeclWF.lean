import Lean4Lean.Theory.Typing.Strengthening.Klop.Env.EqDecl
import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped

/-! # The environment with `Eq` alone

`eqDecl` is a well-formed inductive declaration over the empty environment (`eqDecl_WF`), and
installing it gives a well-formed environment `eqEnv` (`eqEnv_wf`) with canonical `Eq`
(`eqEnv_hasCanonicalEq`) whose constants, patterns and projection metadata are listed
exactly. The proof follows the generic one in `Tests/InductiveTheory.lean`, specialised to
one declaration; the syntactic side conditions are decided by evaluation.
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

def eqBlock : VInductBlock where
  types := eqDecl.typeConstants
  ctors := eqDecl.constructorConstants
  recursors := [eqRecursor]
  rules := [eqRule]
  projections := eqDecl.projectionEntries

/-- The constructor-stage environment with the projection metadata of `Eq`. -/
def eqProjEnv : VEnv := eqCtorsEnv.addProjections eqBlock.projections

theorem eqProjEnv_Eq : eqProjEnv.constants ``Eq = some eqType.toVConstant := by
  simp [eqProjEnv, eqCtorsEnv, eqTypesEnv, VEnv.addProjections_constants]

theorem eqProjEnv_refl : eqProjEnv.constants ``Eq.refl = some eqCtor.toVConstant := by
  simp [eqProjEnv, eqCtorsEnv, VEnv.addProjections_constants]

theorem eqCanonicalCompilation : InductiveSignature.Compiles .empty eqDecl eqBlock := by
  have hp : (VLevel.param 0).WF 1 := by decide
  refine ⟨eqSignature, eqInstance, eqTypesEnv, ?_, addEqTypes, ?_, ?_, ?_, rfl, rfl⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_, Or.inr ?_, ?_⟩
    · change List.Forall₂ _ [eqType] [eqType]
      exact .cons ⟨rfl, rfl, rfl, (by rfl), rfl⟩ .nil
    · refine ⟨eqTypesEnv, addEqTypes, ?_⟩
      change List.Forall₂ _ [eqCtor] [eqCtor]
      exact .cons ⟨rfl, rfl, _, eqCtorTyping.choose_spec⟩ .nil
    · refine ⟨eqTypesEnv, addEqTypes, ?_⟩
      intro ctor hctor i hi
      have hctor := List.mem_singleton.mp hctor
      subst ctor
      exact (Nat.not_lt_zero i hi).elim
    · intro ctor hctor
      have hctor := List.mem_singleton.mp hctor
      subst ctor
      rfl
  · refine ⟨rfl, ?_, ?_, Or.inr (Or.inr ⟨⟨rfl, by decide, ?_⟩, 0, rfl, ?_⟩)⟩
    · intro level hl
      have := List.mem_singleton.mp hl
      subst level
      decide
    · decide
    · intro ctor hctor i hi
      have hctor := List.mem_singleton.mp hctor
      subst ctor
      exact (Nat.not_lt_zero i hi).elim
    · intro l hl ls u
      have := List.mem_singleton.mp hl
      subst l
      cases ls with
      | nil => rfl
      | cons a as => rfl
  · refine ⟨eqCtorsEnv, addEqConstructors, ?_, ?_⟩
    · intro index j hj
      rcases index with ⟨_ | k, hk⟩
      · have h0 : (InductiveSignature.Instance.recursiveFields
            eqSignature.constructors[(⟨0, hk⟩ : Fin eqSignature.constructors.size)]).length = 0 :=
          rfl
        omega
      · simp [eqSignature] at hk
    · intro owner
      have h : owner = (⟨0, by decide⟩ : Fin eqSignature.families.size) := by
        apply Fin.ext
        have hi : owner.val < 1 := owner.isLt
        change owner.val = 0
        omega
      subst owner
      have hΓ : OnCtx [VExpr.bvar 1, .bvar 0, .sort (.param 0)]
          ((eqCtorsEnv.addProjections eqDecl.projectionEntries).IsType 1) :=
        ⟨⟨⟨trivial, _, .sortDF hp hp rfl⟩, _, .bvar .zero⟩, _, .bvar (.succ .zero)⟩
      refine ⟨hΓ, ?_⟩
      exact eqAppTyping (env := eqCtorsEnv.addProjections eqDecl.projectionEntries)
        eqProjEnv_Eq hp (.bvar (.succ (.succ .zero))) (.bvar (.succ .zero)) (.bvar .zero)
  · intro owner
    have h : owner = (⟨0, by decide⟩ : Fin eqSignature.families.size) := by
      apply Fin.ext
      have hi : owner.val < 1 := owner.isLt
      change owner.val = 0
      omega
    subst owner
    rfl

/-! ### Typing of the recursor -/

section RecTyping
variable {env : VEnv} {U : Nat}

/-- `@Eq.refl.{u} α a : @Eq α a a`, from the lookups of `Eq.refl`. -/
theorem eqReflAppTyping {Γ : List VExpr} {u : VLevel} {α a : VExpr}
    (h : env.constants ``Eq.refl = some eqCtor.toVConstant) (hu : u.WF U)
    (hα : env.HasType U Γ α (.sort u)) (ha : env.HasType U Γ a α) :
    env.HasType U Γ (.app (.app (.const ``Eq.refl [u]) α) a)
      (.app (.app (.app (.const ``Eq [u]) α) a) a) := by
  have hc : env.HasType U Γ (.const ``Eq.refl [u])
      (.forallE (.sort u) (.forallE (.bvar 0)
        (.app (.app (.app (.const ``Eq [u]) (.bvar 1)) (.bvar 0)) (.bvar 0)))) := by
    have := HasType.const (env := env) (U := U) (Γ := Γ) h (ls := [u]) (by simpa using hu) rfl
    simpa [eqCtor, canonicalEqReflType, VExpr.instL, VLevel.inst] using this
  have h1 := hc.app hα
  simp only [VExpr.inst, VExpr.instVar] at h1
  have h2 := HasType.app (by simpa using h1) ha
  simpa [VExpr.inst, VExpr.instVar, VExpr.inst_lift] using h2

/-- The motive type of `Eq.rec` is a type under `α`, `a`. -/
theorem eqRecMotiveTyping {Γ : List VExpr}
    (hE : env.constants ``Eq = some eqType.toVConstant) (h0 : (VLevel.param 0).WF U)
    (h1 : (VLevel.param 1).WF U) :
    env.HasType U (.bvar 0 :: .sort (.param 1) :: Γ) canonicalEqRecMotive
      (.sort (.imax (.param 1) (.imax .zero (.succ (.param 0))))) := by
  refine .forallEDF (.bvar (.succ .zero)) (.forallEDF ?_ (.sortDF h0 h0 rfl))
  exact eqAppTyping hE h1 (.bvar (.succ (.succ .zero))) (.bvar (.succ .zero)) (.bvar .zero)

/-- The minor premise type of `Eq.rec` is a type under `α`, `a`, the motive. -/
theorem eqRecMinorTyping {Γ : List VExpr}
    (hR : env.constants ``Eq.refl = some eqCtor.toVConstant) (h1 : (VLevel.param 1).WF U) :
    env.HasType U (canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ)
      canonicalEqRecMinor (.sort (.param 0)) := by
  have hm : env.HasType U (canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ) (.bvar 0)
      (.forallE (.bvar 2) (.forallE
        (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 3)) (.bvar 2)) (.bvar 0))
        (.sort (.param 0)))) := by
    have := HasType.bvar (env := env) (U := U)
      (Lookup.zero (ty := canonicalEqRecMotive) (Γ := .bvar 0 :: .sort (.param 1) :: Γ))
    simpa [canonicalEqRecMotive, VExpr.lift, VExpr.liftN, liftVar] using this
  have ha : env.HasType U (canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ) (.bvar 1)
      (.bvar 2) := .bvar (.succ .zero)
  have hα : env.HasType U (canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ) (.bvar 2)
      (.sort (.param 1)) := .bvar (.succ (.succ .zero))
  have h2 := hm.app ha
  simp only [VExpr.inst, VExpr.instVar] at h2
  have h3 := HasType.app (by simpa using h2) (eqReflAppTyping hR h1 hα ha)
  simpa [canonicalEqRecMinor, VExpr.inst] using h3

/-- The type of the major premise of `Eq.rec`, under `α`, `a`, motive, minor, `b`. -/
def eqRecMajorType : VExpr :=
  .app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.bvar 3)) (.bvar 0)

/-- The context of `Eq.rec` up to and including the major premise. -/
def eqRecCtx (Γ : List VExpr) : List VExpr :=
  eqRecMajorType :: .bvar 3 :: canonicalEqRecMinor :: canonicalEqRecMotive :: .bvar 0 ::
    .sort (.param 1) :: Γ

theorem eqRecMajorTyping {Γ : List VExpr}
    (hE : env.constants ``Eq = some eqType.toVConstant) (h1 : (VLevel.param 1).WF U) :
    env.HasType U (.bvar 3 :: canonicalEqRecMinor :: canonicalEqRecMotive :: .bvar 0 ::
      .sort (.param 1) :: Γ) eqRecMajorType (.sort .zero) :=
  eqAppTyping hE h1 (.bvar (.succ (.succ (.succ (.succ .zero)))))
    (.bvar (.succ (.succ (.succ .zero)))) (.bvar .zero)

/-- The result `motive b t` of `Eq.rec` in its full context. -/
theorem eqRecResultTyping {Γ : List VExpr} :
    env.HasType U (eqRecCtx Γ) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
      (.sort (.param 0)) := by
  have hm : env.HasType U (eqRecCtx Γ) (.bvar 3)
      (.forallE (.bvar 5) (.forallE
        (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 6)) (.bvar 5)) (.bvar 0))
        (.sort (.param 0)))) := by
    have := HasType.bvar (env := env) (U := U)
      (Lookup.succ (A := eqRecMajorType) (Lookup.succ (A := .bvar 3)
        (Lookup.succ (A := canonicalEqRecMinor)
          (Lookup.zero (ty := canonicalEqRecMotive) (Γ := .bvar 0 :: .sort (.param 1) :: Γ)))))
    simpa [eqRecCtx, canonicalEqRecMotive, VExpr.lift, VExpr.liftN, liftVar] using this
  have hb : env.HasType U (eqRecCtx Γ) (.bvar 1) (.bvar 5) := .bvar (.succ .zero)
  have ht : env.HasType U (eqRecCtx Γ) (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 5)) (.bvar 4)) (.bvar 1)) := by
    have := HasType.bvar (env := env) (U := U)
      (Lookup.zero (ty := eqRecMajorType) (Γ := .bvar 3 :: canonicalEqRecMinor ::
        canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ))
    simpa [eqRecCtx, eqRecMajorType, VExpr.lift, VExpr.liftN, liftVar] using this
  have h2 := hm.app hb
  simp only [VExpr.inst, VExpr.instVar] at h2
  have h3 := HasType.app (by simpa using h2) ht
  simpa [VExpr.inst] using h3

/-- The type of `Eq.rec` is a type, given `Eq` and `Eq.refl`. -/
theorem eqRecTypeTyping
    (hE : env.constants ``Eq = some eqType.toVConstant)
    (hR : env.constants ``Eq.refl = some eqCtor.toVConstant)
    (h0 : (VLevel.param 0).WF U) (h1 : (VLevel.param 1).WF U) :
    env.IsType U [] canonicalEqRecType :=
  ⟨_, .forallEDF (.sortDF h1 h1 rfl) (.forallEDF (.bvar .zero)
    (.forallEDF (eqRecMotiveTyping hE h0 h1) (.forallEDF (eqRecMinorTyping hR h1)
      (.forallEDF (.bvar (.succ (.succ (.succ .zero))))
        (.forallEDF (eqRecMajorTyping hE h1) eqRecResultTyping)))))⟩

theorem HasType.app_dom' {Γ : List VExpr} {f a A A' B : VExpr}
    (h1 : env.HasType U Γ f (.forallE A' B)) (hA : A' = A)
    (h2 : env.HasType U Γ a A) : env.HasType U Γ (.app f a) (B.inst a) := by
  subst hA; exact h1.app h2

/-- The context of the ι rule of `Eq.rec`: `α`, `a`, motive, minor. -/
def eqRuleCtx (Γ : List VExpr) : List VExpr :=
  canonicalEqRecMinor :: canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ

/-- The generic redex `Eq.rec α a motive refl a (Eq.refl α a)` is typed at
`motive a (Eq.refl α a)`. -/
theorem eqRecRedexTyping {Γ : List VExpr}
    (hR : env.constants ``Eq.refl = some eqCtor.toVConstant)
    (hRec : env.constants ``Eq.rec = some eqRecursor.toVConstant)
    (h0 : (VLevel.param 0).WF U) (h1 : (VLevel.param 1).WF U) :
    env.HasType U (eqRuleCtx Γ)
      (.app (.app (.app (.app (.app (.app (.const ``Eq.rec [.param 0, .param 1])
        (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2)))
      (.app (.app (.bvar 1) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2))) := by
  have hα : env.HasType U (eqRuleCtx Γ) (.bvar 3) (.sort (.param 1)) :=
    .bvar (.succ (.succ (.succ .zero)))
  have ha : env.HasType U (eqRuleCtx Γ) (.bvar 2) (.bvar 3) := .bvar (.succ (.succ .zero))
  have hM : env.HasType U (eqRuleCtx Γ) (.bvar 1)
      (.forallE (.bvar 3) (.forallE
        (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.bvar 3)) (.bvar 0))
        (.sort (.param 0)))) := by
    have := HasType.bvar (env := env) (U := U)
      (Lookup.succ (A := canonicalEqRecMinor)
        (Lookup.zero (ty := canonicalEqRecMotive) (Γ := .bvar 0 :: .sort (.param 1) :: Γ)))
    simpa [eqRuleCtx, canonicalEqRecMotive, VExpr.lift, VExpr.liftN, liftVar] using this
  have hm : env.HasType U (eqRuleCtx Γ) (.bvar 0)
      (.app (.app (.bvar 1) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2))) := by
    have := HasType.bvar (env := env) (U := U)
      (Lookup.zero (ty := canonicalEqRecMinor)
        (Γ := canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ))
    simpa [eqRuleCtx, canonicalEqRecMinor, VExpr.lift, VExpr.liftN, liftVar] using this
  have hrefl := eqReflAppTyping hR h1 hα ha
  have hc : env.HasType U (eqRuleCtx Γ) (.const ``Eq.rec [.param 0, .param 1])
      canonicalEqRecType := by
    have := HasType.const (env := env) (U := U) (Γ := eqRuleCtx Γ) hRec
      (ls := [.param 0, .param 1]) (by simp; exact ⟨h0, h1⟩) rfl
    simpa [eqRecursor_type, canonicalEqRecType, canonicalEqRecMotive, canonicalEqRecMinor,
      VExpr.instL, VLevel.inst] using this
  have s1 := HasType.app_dom' (A := .sort (.param 1)) (by simpa [canonicalEqRecType] using hc)
    rfl hα
  simp only [VExpr.inst, VExpr.instVar, canonicalEqRecMotive, canonicalEqRecMinor] at s1
  have s2 := HasType.app_dom' (A := .bvar 3) (by simpa using s1) rfl ha
  simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s2
  have s3 := HasType.app_dom' (by simpa using s2) rfl hM
  simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s3
  have s4 := HasType.app_dom' (by simpa using s3) rfl hm
  simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s4
  have s5 := HasType.app_dom' (by simpa using s4) rfl ha
  simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s5
  have s6 := HasType.app_dom' (by simpa using s5) rfl hrefl
  simpa [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] using s6

/-- The minor premise variable in the rule context. -/
theorem eqRuleMinorVar {Γ : List VExpr} :
    env.HasType U (eqRuleCtx Γ) (.bvar 0)
      (.app (.app (.bvar 1) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2))) := by
  have := HasType.bvar (env := env) (U := U)
    (Lookup.zero (ty := canonicalEqRecMinor)
      (Γ := canonicalEqRecMotive :: .bvar 0 :: .sort (.param 1) :: Γ))
  simpa [eqRuleCtx, canonicalEqRecMinor, VExpr.lift, VExpr.liftN, liftVar] using this

/-- Both sides of the generated equation of `Eq.rec` are typed at its type. -/
theorem eqRuleTyping
    (hE : env.constants ``Eq = some eqType.toVConstant)
    (hR : env.constants ``Eq.refl = some eqCtor.toVConstant)
    (hRec : env.constants ``Eq.rec = some eqRecursor.toVConstant) :
    eqRule.WF env := by
  have h0 : (VLevel.param 0).WF 2 := by decide
  have h1 : (VLevel.param 1).WF 2 := by decide
  constructor
  · exact .lamDF (.sortDF h1 h1 rfl) (.lamDF (.bvar .zero)
      (.lamDF (eqRecMotiveTyping hE h0 h1) (.lamDF (eqRecMinorTyping hR h1)
        (eqRecRedexTyping (Γ := []) hR hRec h0 h1))))
  · exact .lamDF (.sortDF h1 h1 rfl) (.lamDF (.bvar .zero)
      (.lamDF (eqRecMotiveTyping hE h0 h1) (.lamDF (eqRecMinorTyping hR h1)
        (eqRuleMinorVar (Γ := [])))))

end RecTyping

/-! ### The recursor stage and the block -/

/-- The recursor-stage environment. -/
def eqRecsEnv : VEnv where
  constants := fun n => if ``Eq.rec = n then some eqRecursor.toVConstant
    else eqProjEnv.constants n
  defeqs := eqProjEnv.defeqs
  pats := eqProjEnv.pats
  projections := eqProjEnv.projections

theorem addEqRecursor : eqProjEnv.addConstVals eqBlock.recursors = some eqRecsEnv := by
  simp [eqBlock, VEnv.addConstVals, VEnv.addConst, eqRecursor,
    InductiveSignature.Instance.recursor, eqInstance, eqRecsEnv,
    eqProjEnv, eqCtorsEnv, eqTypesEnv]

theorem eqRecsEnv_Eq : eqRecsEnv.constants ``Eq = some eqType.toVConstant := by
  simp [eqRecsEnv, eqProjEnv_Eq]

theorem eqRecsEnv_refl : eqRecsEnv.constants ``Eq.refl = some eqCtor.toVConstant := by
  simp [eqRecsEnv, eqProjEnv_refl]

theorem eqRecsEnv_rec : eqRecsEnv.constants ``Eq.rec = some eqRecursor.toVConstant := by
  simp [eqRecsEnv]

theorem eqRecursorTyping : eqRecursor.toVConstant.WF eqProjEnv :=
  eqRecTypeTyping (U := 2) eqProjEnv_Eq eqProjEnv_refl (by decide) (by decide)

theorem eqBlockWellFormed : eqBlock.WF .empty := by
  refine ⟨eqTypesEnv, eqCtorsEnv, eqRecsEnv,
    addEqTypes, addEqConstructors, addEqRecursor, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    change ci ∈ [eqType.toVConstVal] at hci
    have := List.mem_singleton.mp hci
    subst ci
    exact ⟨_, eqTypeTyping (by decide) []⟩
  · intro ci hci
    change ci ∈ [eqCtor] at hci
    have := List.mem_singleton.mp hci
    subst ci
    exact eqCtorTyping
  · intro ci hci
    have := List.mem_singleton.mp hci
    subst ci
    exact eqRecursorTyping
  · intro df hdf
    have := List.mem_singleton.mp hdf
    subst df
    exact eqRuleTyping eqRecsEnv_Eq eqRecsEnv_refl eqRecsEnv_rec

theorem eqCompiles : eqDecl.CompilesTo .empty eqBlock :=
  CompiledInductive.ordinary eqDecl_source eqFormation
    eqCanonicalCompilation eqBlockWellFormed rfl rfl rfl (by
      simp [eqBlock, eqDecl, eqType, eqCtor, eqRecursor,
        VInductDecl.typeConstants, VInductDecl.constructorConstants,
        InductiveSignature.Instance.recursor, eqInstance])

/-! ### The full judgment -/

theorem eqRecsOf : eqDecl.RecsOf eqBlock where
  recursors := rfl
  rules := by
    intro r hr ru hru
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    simp only [eqVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨eqRule, List.mem_singleton_self _, rfl, rfl, rfl, _, rfl, rfl, rfl⟩
  rules_total := by
    intro df hdf
    simp only [eqBlock, List.mem_singleton] at hdf
    subst df
    exact ⟨eqVRec, List.mem_singleton_self _, eqRecRule, List.mem_singleton_self _,
      rfl, rfl, rfl, _, rfl, rfl, rfl⟩

theorem addEqTypesCtors : eqDecl.addTypesCtors .empty = some eqCtorsEnv := by
  simp only [VInductDecl.addTypesCtors, VInductDecl.addTypes_eq_addConstVals, addEqTypes,
    Option.bind_eq_bind, Option.bind_some, VInductDecl.addCtors_eq_addConstVals,
    addEqConstructors]

theorem addEqTypesCtorsProjs : eqDecl.addTypesCtorsProjs .empty = some eqProjEnv := by
  simp only [VInductDecl.addTypesCtorsProjs, addEqTypesCtors, Option.map_some]
  rfl

theorem addEqTypesCtorsProjsRecs : eqDecl.addTypesCtorsProjsRecs .empty = some eqRecsEnv := by
  simp only [VInductDecl.addTypesCtorsProjsRecs, addEqTypesCtorsProjs, Option.bind_eq_bind,
    Option.bind_some]
  simpa [VInductDecl.addRecs, eqDecl, eqBlock, VEnv.addConstVals, eqVRec] using
    addEqRecursor

/-- The rule of `Eq.rec` is a typed ι rule of the recursor-stage environment. -/
theorem eqRulePatTyped (hc : eqRecRule.rhs.Closed) :
    eqRecsEnv.PatTyped
      (SimplePattern.iota ``Eq.rec (2 + 1 + 1 + 1) ``Eq.refl (2 + 0)).toPattern
      (SimplePattern.iotaRHS' ``Eq.rec ``Eq.refl 4 1 2 0 eqRecRule.rhs hc, .true) := by
  have h0 : (VLevel.param 0).WF 2 := by decide
  have h1' : (VLevel.param 1).WF 2 := by decide
  let recArgs : List VExpr := [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2]
  let ctorArgs : List VExpr := [.bvar 3, .bvar 2]
  have h1 : recArgs.length = 4 + 1 := rfl
  have h2 : ctorArgs.length = 2 + 0 := rfl
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := ``Eq.rec)
    (ls := [.param 0, .param 1]) _ _ h1
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := ``Eq.refl) (ls := [.param 1]) _ _ h2
  have hpaths := SimplePattern.iotaPaths_map (m2 := Sum.elim g1 g2) h1 h2 hg1 hg2
  have happ := SimplePattern.iotaRHS'_apply ``Eq.rec ``Eq.refl 4 1 2 0 eqRecRule.rhs hc
    (VLevel.params 2)
    (Sum.elim g1 g2) h1 h2 hg1 hg2
  refine ⟨2, eqRuleCtx [], _, Sum.elim g1 g2,
    .app (.app (.bvar 1) (.bvar 2))
      (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2)),
    .app hm1 hm2, ?_, ?_, ?_⟩
  · exact Pattern.RHS.generic_foldl_var (hpaths.trans rfl)
  · exact eqRecRedexTyping (Γ := []) eqRecsEnv_refl eqRecsEnv_rec h0 h1'
  · dsimp only
    rw [happ]
    have hlam : eqRecsEnv.HasType 2 (eqRuleCtx []) eqRecRule.rhs eqRule.type :=
      .lamDF (.sortDF h1' h1' rfl) (.lamDF (.bvar .zero)
        (.lamDF (eqRecMotiveTyping eqRecsEnv_Eq h0 h1')
          (.lamDF (eqRecMinorTyping eqRecsEnv_refl h1')
          eqRuleMinorVar)))
    have hα : eqRecsEnv.HasType 2 (eqRuleCtx []) (.bvar 3) (.sort (.param 1)) :=
      .bvar (.succ (.succ (.succ .zero)))
    have ha : eqRecsEnv.HasType 2 (eqRuleCtx []) (.bvar 2) (.bvar 3) :=
      .bvar (.succ (.succ .zero))
    have hM : eqRecsEnv.HasType 2 (eqRuleCtx []) (.bvar 1)
        (.forallE (.bvar 3) (.forallE
          (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.bvar 3)) (.bvar 0))
          (.sort (.param 0)))) := by
      have := HasType.bvar (env := eqRecsEnv) (U := 2)
        (Lookup.succ (A := canonicalEqRecMinor)
          (Lookup.zero (ty := canonicalEqRecMotive) (Γ := [.bvar 0, .sort (.param 1)])))
      simpa [eqRuleCtx, canonicalEqRecMotive, VExpr.lift, VExpr.liftN, liftVar] using this
    have s1 := HasType.app_dom' (A := .sort (.param 1))
      (by simpa [eqRule_eq, canonicalEqRecRule] using hlam) rfl hα
    simp only [VExpr.inst, VExpr.instVar, canonicalEqRecMotive, canonicalEqRecMinor] at s1
    have s2 := HasType.app_dom' (A := .bvar 3) (by simpa using s1) rfl ha
    simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s2
    have s3 := HasType.app_dom' (by simpa using s2) rfl hM
    simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s3
    have s4 := HasType.app_dom' (by simpa using s3) rfl (eqRuleMinorVar (Γ := []))
    simp only [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] at s4
    exact s4

/-- **The hand-built declaration of `Eq` is well formed in the empty environment.** -/
theorem eqDecl_WF : eqDecl.WF .empty where
  source := eqDecl_source
  formation := .ordinary eqFormation
  recsCompiled := ⟨eqBlock, eqCompiles, eqRecsOf, eqBlockWellFormed⟩
  recs_wf := by
    intro envP hP r hr
    rw [addEqTypesCtorsProjs] at hP
    cases hP
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    exact eqRecursorTyping
  rec_shape := by
    intro r hr
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    decide
  rules_nodup := by
    intro r hr
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    decide
  rules_ctor := by
    intro envC hC r hr ru hru
    rw [addEqTypesCtors] at hC
    cases hC
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    simp only [eqVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨eqCtor.toVConstant, by simp [eqCtorsEnv, eqRecRule], by decide⟩
  rules_ctorParams := by
    intro r hr ru hru
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    simp only [eqVRec, List.mem_singleton] at hru
    subst ru
    exact Or.inl ⟨eqCtor, by simp [eqDecl, eqType, VInductDecl.constructorConstants],
      rfl, rfl⟩
  rule_shape := by
    intro r hr ru hru
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    simp only [eqVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨0, by decide, canonicalEqRecMinor, rfl, by decide, by decide, by decide⟩
  rules_wf := by
    intro envR hR r hr ru hru hc
    rw [addEqTypesCtorsProjsRecs] at hR
    cases hR
    simp only [eqDecl, List.mem_singleton] at hr
    subst r
    simp only [eqVRec, List.mem_singleton] at hru
    subst ru
    exact eqRulePatTyped hc

/-! ### Installation -/

theorem eqRecRule_closed : eqRecRule.rhs.Closed := by decide

/-- The environment containing exactly the inductive declaration of `Eq`. -/
def eqEnv : VEnv :=
  eqRecsEnv.addPat
    (SimplePattern.iota ``Eq.rec (2 + 1 + 1 + 1) ``Eq.refl (2 + 0)).toPattern
    (SimplePattern.iotaRHS ``Eq.rec ``Eq.refl 2 1 1 1 2 0 eqRecRule.rhs eqRecRule_closed, .true)

theorem eqInstalls : VEnv.empty.addInduct eqDecl = some eqEnv := by
  simp only [VEnv.addInduct, Option.bind_eq_bind,
    eqDecl, eqVRec]
  rfl

/-- **The `Eq`-only environment is well formed.** -/
theorem eqEnv_wf : eqEnv.WF :=
  ⟨_, .decl (.induct eqDecl_WF eqInstalls) .empty⟩

theorem eqEnv_constants (n : Name) :
    eqEnv.constants n =
      if ``Eq.rec = n then some ⟨2, canonicalEqRecType⟩
      else if ``Eq.refl = n then some ⟨1, canonicalEqReflType⟩
      else if ``Eq = n then some ⟨1, canonicalEqType⟩ else none := by
  simp only [eqEnv, VEnv.addPat_constants, eqRecsEnv, eqProjEnv, VEnv.addProjections_constants,
    eqCtorsEnv, eqTypesEnv]
  rfl

/-- **The `Eq`-only environment has canonical `Eq`.** -/
theorem eqEnv_hasCanonicalEq : eqEnv.HasCanonicalEq := by
  refine ⟨by rw [eqEnv_constants]; rfl, by rw [eqEnv_constants]; rfl,
    by rw [eqEnv_constants]; rfl,
    [.sort (.param 1), .bvar 0, canonicalEqRecMotive, canonicalEqRecMinor], eqRecRule_closed,
    rfl, ?_⟩
  exact .inl ⟨rfl, rfl⟩

end VEnv.Strengthening
end Lean4Lean
