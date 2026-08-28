import Lean4Lean.Verify.Inductive.PrimitiveConstructors

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem primitiveTarget_metadata
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    (henv : env.WF)
    (hdeclParams : decl.nparams = 0)
    (htype : target.type = .sort (.succ .zero))
    (Hshape : decl.TypeShape env [] target) :
    target.numIndices = 0 ∧ target.resultLevel ≈ .succ .zero := by
  rcases Hshape with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, hindicesTake, _hparams, hresult⟩
  rw [hdeclParams] at hparamsTake
  simp only [VExpr.takeForalls] at hparamsTake
  have hafter : afterParams = normalized :=
    (congrArg Prod.snd (Option.some.inj hparamsTake)).symm
  have hown : ownParams = [] :=
    (congrArg Prod.fst (Option.some.inj hparamsTake)).symm
  have hnormalizedSort : env.IsDefEqU decl.uvars [] normalized
      (.sort (.succ .zero)) := by
    refine ⟨exprType, ?_⟩
    rw [htype] at hnormalized
    exact hnormalized.symm
  have hnindices : target.numIndices = 0 := by
    apply VExpr.takeForalls_eq_zero_of_defEqSort henv (by trivial)
      (by simpa [hafter] using hindicesTake)
      hnormalizedSort
  rw [hnindices] at hindicesTake
  simp only [VExpr.takeForalls] at hindicesTake
  have hresultEq : result = normalized := by
    simpa [hafter] using
      (congrArg Prod.snd (Option.some.inj hindicesTake)).symm
  have hindices : indices = [] := by
    simpa [hafter] using
      (congrArg Prod.fst (Option.some.inj hindicesTake)).symm
  subst result
  simp only [hindices, hown, List.reverse_nil, List.nil_append] at hresult
  have hsortDefEq : env.IsDefEqU decl.uvars []
      (.sort (.succ .zero)) (.sort target.resultLevel) :=
    hnormalizedSort.symm |>.trans henv (by trivial)
      ⟨_, hresult⟩
  have hlevels := VEnv.IsDefEqU.sort_inv henv (by trivial) hsortDefEq
  exact ⟨hnindices, hlevels.symm⟩

private theorem primitiveValidIndApp
    {decl : VInductDecl} {target : VInductiveType}
    (htypes : decl.types = [target]) (huvars : decl.uvars = 0)
    (hnparams : decl.nparams = 0) (hnindices : target.numIndices = 0)
    (depth : Nat) :
    decl.ValidIndAppAt (some target.name) depth (.const target.name []) := by
  refine ⟨target, by simp [htypes], Or.inr rfl, [], ?_⟩
  simp [huvars, hnparams, hnindices, VInductDecl.paramVars]

private theorem primitiveResultCtorShape
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    {ctor : VConstVal}
    (henv : env.WF) (htypes : decl.types = [target])
    (huvars : decl.uvars = 0) (hnparams : decl.nparams = 0)
    (htargetUvars : target.uvars = 0)
    (hnindices : target.numIndices = 0)
    (hctorType : ctor.type = .const target.name [])
    (hlookup : env.constants target.name = some target.toVConstant)
    (htargetType : target.type = .sort (.succ .zero)) :
    decl.CtorShape env [] target ctor := by
  have hconst : env.HasType decl.uvars [] (.const target.name [])
      (.sort (.succ .zero)) := by
    rw [huvars]
    have hc := VEnv.HasType.const (U := 0) (ls := []) (Γ := []) hlookup
      (by simp) (by simpa using htargetUvars.symm)
    simpa [htargetType, VExpr.instL, VLevel.inst] using hc
  refine ⟨ctor.type, [], ctor.type, .sort (.succ .zero), [], ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hctorType]
    exact hconst
  · rw [hnparams]
    rfl
  · exact .zero
  · exact .zero
  · apply VInductDecl.CtorTailWF.result
    · simpa [hctorType] using
        primitiveValidIndApp htypes huvars hnparams hnindices 0
    · rw [hctorType]
      exact hconst

private theorem primitiveTargetHasType
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    (huvars : decl.uvars = 0) (htargetUvars : target.uvars = 0)
    (hlookup : env.constants target.name = some target.toVConstant)
    (htargetType : target.type = .sort (.succ .zero))
    (ctx : List VExpr) :
    env.HasType decl.uvars ctx (.const target.name [])
      (.sort (.succ .zero)) := by
  rw [huvars]
  have hc := VEnv.HasType.const (U := 0) (ls := []) (Γ := ctx) hlookup
    (by simp) (by simpa using htargetUvars.symm)
  simpa [htargetType, VExpr.instL, VLevel.inst] using hc

private theorem primitiveResultTailCertificate
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    (htypes : decl.types = [target])
    (huvars : decl.uvars = 0) (hnparams : decl.nparams = 0)
    (htargetUvars : target.uvars = 0)
    (hnindices : target.numIndices = 0)
    (hlookup : env.constants target.name = some target.toVConstant)
    (htargetType : target.type = .sort (.succ .zero)) :
    ConstructorTailCertificate env decl target [] 0
      (.const target.name []) := by
  have htyped := primitiveTargetHasType huvars htargetUvars hlookup
    htargetType []
  exact {
    shape := .result
      (primitiveValidIndApp htypes huvars hnparams hnindices 0) htyped
    isType := ⟨.succ .zero, htyped⟩ }

private theorem primitiveNatSuccTailCertificate
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    (htypes : decl.types = [target]) (hname : target.name = ``Nat)
    (huvars : decl.uvars = 0) (hnparams : decl.nparams = 0)
    (htargetUvars : target.uvars = 0)
    (hnindices : target.numIndices = 0)
    (hresultLevel : target.resultLevel ≈ .succ .zero)
    (hlookup : env.constants target.name = some target.toVConstant)
    (htargetType : target.type = .sort (.succ .zero)) :
    ConstructorTailCertificate env decl target [] 0 (.forallE .nat .nat) := by
  have hdom : env.HasType decl.uvars [] .nat (.sort (.succ .zero)) := by
    simpa [VExpr.nat, hname] using
      primitiveTargetHasType huvars htargetUvars hlookup htargetType []
  have hbody : env.HasType decl.uvars [.nat] .nat
      (.sort (.succ .zero)) := by
    simpa [VExpr.nat, hname] using
      primitiveTargetHasType huvars htargetUvars hlookup htargetType [.nat]
  have hvalid0 := primitiveValidIndApp htypes huvars hnparams hnindices 0
  have hvalid1 := primitiveValidIndApp htypes huvars hnparams hnindices 1
  have hpositive : decl.Positive env [] 0 .nat :=
    .unfold hdom (.recursive (by simpa [VExpr.nat, hname] using
      hvalid0.forgetTarget))
  exact {
    shape := .field hdom
      (Or.inr (VLevel.le_antisymm_iff.mp hresultLevel).2)
      (Or.inr hpositive) hdom hbody
      (.result (by simpa [VExpr.nat, hname] using hvalid1) hbody)
    isType := ⟨.imax (.succ .zero) (.succ .zero),
      VEnv.IsDefEq.forallEDF hdom hbody⟩ }

private theorem primitiveTailReplay
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    {source : Constructor} {ctorVal : VConstVal}
    (huvars : Us.length = decl.uvars)
    (hparams : stats.params.size = 0)
    (hmem : ctorVal ∈ target.ctors)
    (htr : TrSourceConstRaw env Us source.name source.type ctorVal)
    (Htail : ConstructorTailCertificate env decl target [] 0 ctorVal.type) :
    CheckedConstructorTailReplayAt env Us [] stats decl target source := by
  have htailType : env.IsType Us.length [] ctorVal.type := by
    simpa [huvars] using Htail.isType
  have htailType' := htailType
  rcases htailType with ⟨u, htyped⟩
  refine ⟨ctorVal, source.type, ctorVal.type, [], hmem, htr,
    .done hparams.symm, ?_, htr.type, Htail, ?_⟩
  · simpa [hparams] using
      (CheckedConstructorParameterPrefix.zero :
        CheckedConstructorParameterPrefix env Us stats source.type
          0 source.type [] [])
  have hheader : env.IsDefEq Us.length []
      (constructorTelescopeTarget ctorVal).type ctorVal.type
      (.sort u) := by
    change env.IsDefEq Us.length [] ctorVal.type ctorVal.type (.sort u)
    exact htyped
  have Hsynthesis :=
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
      htailType' htailType' hheader
  simpa [hparams] using Nonempty.intro Hsynthesis

private theorem primitiveResultOwnerNormalForm
    (hparams : stats.params.size = 0)
    (hparamsArray : stats.params = #[])
    (hconsts : stats.indConsts = #[.const family []])
    (hindices : stats.nindices = #[0]) :
    CheckedConstructorOwnerNormalFormAt stats 0
      ({ name := ctorName, type := .const family [] } : Constructor) := by
  refine ⟨.const family [], .done hparams.symm, ⟨{
    arity := 0
    residual := .const family []
    telescope := .nil _
    maximal := rfl
    valid := ?_ }⟩⟩
  simp [AddInductive.isValidIndAppIdx, hparamsArray, hconsts, hindices,
    Expr.getAppFn, Expr.getAppArgs_eq, Expr.getAppArgsList, Id.run]

private theorem primitiveNatSuccOwnerNormalForm
    (hparams : stats.params.size = 0)
    (hparamsArray : stats.params = #[])
    (hconsts : stats.indConsts = #[.const ``Nat []])
    (hindices : stats.nindices = #[0]) :
    CheckedConstructorOwnerNormalFormAt stats 0 ({
      name := ``Nat.succ
      type := .forallE binderName (.const ``Nat []) (.const ``Nat [])
        binderInfo } : Constructor) := by
  let source : Expr :=
    .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo
  refine ⟨source, .done hparams.symm, ⟨{
    arity := 1
    residual := .const ``Nat []
    telescope := ?_
    maximal := rfl
    valid := ?_ }⟩⟩
  · exact Expr.ForallTelescope.cons (.nil _)
  · simp [AddInductive.isValidIndAppIdx, hparamsArray, hconsts, hindices,
      Expr.getAppFn, Expr.getAppArgs_eq, Expr.getAppArgsList, Id.run]

private theorem primitiveNatSuccCtorShape
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    {ctor : VConstVal}
    (henv : env.WF) (htypes : decl.types = [target])
    (hname : target.name = ``Nat)
    (huvars : decl.uvars = 0) (hnparams : decl.nparams = 0)
    (htargetUvars : target.uvars = 0)
    (hnindices : target.numIndices = 0)
    (hresultLevel : target.resultLevel ≈ .succ .zero)
    (hctorType : ctor.type = .forallE .nat .nat)
    (hlookup : env.constants target.name = some target.toVConstant)
    (htargetType : target.type = .sort (.succ .zero)) :
    decl.CtorShape env [] target ctor := by
  have htargetConstant : target.toVConstant =
      ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
    apply VConstant.eq_of_fields
    · exact htargetUvars
    · exact htargetType
  have hnatLookup : env.constants ``Nat = some
      ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
    rw [← hname, ← htargetConstant]
    exact hlookup
  have hconst : env.HasType decl.uvars [] .nat (.sort (.succ .zero)) := by
    rw [huvars]
    have hc := VEnv.HasType.const (U := 0) (ls := []) (Γ := []) hnatLookup
      (by simp) (by simp)
    simpa [VExpr.nat, VExpr.instL, VLevel.inst] using hc
  have hconstField : env.HasType decl.uvars [.nat] .nat
      (.sort (.succ .zero)) := by
    rw [huvars]
    have hc := VEnv.HasType.const (U := 0) (ls := []) (Γ := [.nat]) hnatLookup
      (by simp) (by simp)
    simpa [VExpr.nat, VExpr.instL, VLevel.inst] using hc
  have hforall : env.HasType decl.uvars [] (.forallE .nat .nat)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    VEnv.IsDefEq.forallEDF hconst hconstField
  have hvalid0 := primitiveValidIndApp htypes huvars hnparams hnindices 0
  have hvalid1 := primitiveValidIndApp htypes huvars hnparams hnindices 1
  have hpositive : decl.Positive env [] 0 .nat := by
    exact .unfold hconst
      (.recursive (by simpa [hname, VExpr.nat] using hvalid0.forgetTarget))
  refine ⟨ctor.type, [], ctor.type,
    .sort (.imax (.succ .zero) (.succ .zero)), [], ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hctorType]
    exact hforall
  · rw [hnparams]
    rfl
  · exact .zero
  · exact .zero
  · rw [hctorType]
    apply VInductDecl.CtorTailWF.field hconst
      (Or.inr (VLevel.le_antisymm_iff.mp hresultLevel).2)
      (Or.inr hpositive) hconst hconstField
    apply VInductDecl.CtorTailWF.result
      (by simpa [hname, VExpr.nat] using hvalid1)
    exact hconstField

/-- The abstract common-parameter telescope recovered from a canonical
primitive header is empty. -/
theorem PrimitiveDeclaredHeadersResult.headerParams_eq_nil
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    H.headers.params = [] := by
  rcases Hshape with ⟨_lparams, hnparams, _hunsafe, htypes⟩
  have hdeclParams : decl.nparams = 0 := H.translation.nparams.trans hnparams
  rcases htypes with hbool | ⟨binderName, binderInfo, hnat⟩
  · have Htypes := H.translation.types
    rw [hbool] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    have htarget : target ∈ decl.types := by simp [hdeclTypes]
    rcases H.headers.typeShapes target htarget with
      ⟨normalized, ownParams, afterParams, indices, result, exprType,
        _htype, htake, _hindices, hparams, _hresult⟩
    rw [hdeclParams] at htake
    simp only [VExpr.takeForalls] at htake
    have hown : ownParams = [] :=
      (congrArg Prod.fst (Option.some.inj htake)).symm
    have hlen := VEnv.IsDefEqCtx.length_eq hparams
    rw [hown] at hlen
    apply List.eq_nil_of_length_eq_zero
    simpa [VInductDecl.ParamsDefEq] using hlen
  · have Htypes := H.translation.types
    rw [hnat] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    have htarget : target ∈ decl.types := by simp [hdeclTypes]
    rcases H.headers.typeShapes target htarget with
      ⟨normalized, ownParams, afterParams, indices, result, exprType,
        _htype, htake, _hindices, hparams, _hresult⟩
    rw [hdeclParams] at htake
    simp only [VExpr.takeForalls] at htake
    have hown : ownParams = [] :=
      (congrArg Prod.fst (Option.some.inj htake)).symm
    have hlen := VEnv.IsDefEqCtx.length_eq hparams
    rw [hown] at hlen
    apply List.eq_nil_of_length_eq_zero
    simpa [VInductDecl.ParamsDefEq] using hlen

/-- With no common parameters, every canonical primitive constructor has the
identity recursor-prefix replay. -/
theorem PrimitiveDeclaredHeadersResult.parameterPrefixes
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    CheckedRecursorParameterPrefixes stats indTypes := by
  have hparams := H.params_size_eq_zero Hshape
  refine ⟨?_⟩
  intro familyIdx hfamily ctorIdx hctor
  exact ⟨_, .done hparams.symm⟩

/-- Finite, source-derived semantic evidence for the two constructor batches
which may be admitted through the primitive-name gate.  This proof uses the
canonical Bool/Nat source syntax and the staged header translation; it does
not claim that the header-only environment is a complete checking context. -/
theorem PrimitiveDeclaredHeadersResult.checkedConstructors
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    CheckedConstructorCertificate sourceEnv decl H.context.venv
      H.headers.params := by
  have hheaderParams := H.headerParams_eq_nil Hshape
  rcases Hshape with ⟨hlparams, hnparams, _hunsafe, htypes⟩
  have hdeclUvars : decl.uvars = 0 := by
    rw [H.translation.uvars, hlparams]
    rfl
  have hdeclParams : decl.nparams = 0 := H.translation.nparams.trans hnparams
  rcases htypes with hbool | ⟨binderName, binderInfo, hnat⟩
  · have Htypes := H.translation.types
    rw [hbool] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨falseVal, trueVal, htargetCtors, Hfalse, Htrue⟩
    have htargetTypeTr : TrExprS sourceEnv c.lparams []
        (.sort (.succ .zero)) (.sort (.succ .zero)) :=
      TrExprS.sort (by rw [hlparams]; rfl)
    have htargetType : target.type = .sort (.succ .zero) :=
      TrExprS.unique (by trivial) Htarget.header.type htargetTypeTr
    have htargetUvars : target.uvars = 0 := by
      simpa [hlparams] using Htarget.header.uvars
    have htargetLookup : H.context.venv.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.translation.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hcanonical : TrExprS H.context.venv c.lparams []
        (.const ``Bool []) .bool := by
      apply TrExprS.const
      · simpa [Htarget.header.name] using htargetLookup
      · simp [hlparams]
      · simp [htargetUvars, hlparams]
    have hfalseType : falseVal.type = .const target.name [] := by
      simpa [VExpr.bool, Htarget.header.name] using
        TrExprS.unique (by trivial) Hfalse.type hcanonical
    have htrueType : trueVal.type = .const target.name [] := by
      simpa [VExpr.bool, Htarget.header.name] using
        TrExprS.unique (by trivial) Htrue.type hcanonical
    have htargetShape := H.headers.typeShapes target (by simp [hdeclTypes])
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have hmetadata := primitiveTarget_metadata hsourceWF
      hdeclParams htargetType (by simpa [hheaderParams] using htargetShape)
    rcases hmetadata with ⟨hnindices, _hresultLevel⟩
    have hfalseShape := primitiveResultCtorShape H.context.checking.wf
      hdeclTypes hdeclUvars hdeclParams htargetUvars hnindices hfalseType
      htargetLookup htargetType
    have htrueShape := primitiveResultCtorShape H.context.checking.wf
      hdeclTypes hdeclUvars hdeclParams htargetUvars hnindices htrueType
      htargetLookup htargetType
    have hfalseIsType : H.context.venv.IsType decl.uvars [] falseVal.type := by
      refine ⟨.succ .zero, ?_⟩
      rw [hfalseType]
      exact primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
        htargetType []
    have htrueIsType : H.context.venv.IsType decl.uvars [] trueVal.type := by
      refine ⟨.succ .zero, ?_⟩
      rw [htrueType]
      exact primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
        htargetType []
    refine {
      formation := ⟨?_⟩
      types := ?_ }
    · intro owned howned
      rcases List.mem_flatMap.mp howned with ⟨family, hfamily, hctor⟩
      simp [hdeclTypes] at hfamily
      subst family
      simp only [List.mem_map] at hctor
      rcases hctor with ⟨ctor, hctor, rfl⟩
      rw [htargetCtors] at hctor
      rcases List.mem_cons.mp hctor with rfl | hctor
      · simpa [hheaderParams] using hfalseShape
      · have : ctor = trueVal := by simpa using hctor
        subst ctor
        simpa [hheaderParams] using htrueShape
    · intro ctor hctor
      simp only [VInductDecl.constructorConstants] at hctor
      rw [hdeclTypes] at hctor
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hctor
      rw [htargetCtors] at hctor
      rcases List.mem_cons.mp hctor with rfl | hctor
      · exact hfalseIsType
      · have : ctor = trueVal := by simpa using hctor
        subst ctor
        exact htrueIsType
  · have Htypes := H.translation.types
    rw [hnat] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨zeroVal, succVal, htargetCtors, Hzero, Hsucc⟩
    have htargetTypeTr : TrExprS sourceEnv c.lparams []
        (.sort (.succ .zero)) (.sort (.succ .zero)) :=
      TrExprS.sort (by rw [hlparams]; rfl)
    have htargetType : target.type = .sort (.succ .zero) :=
      TrExprS.unique (by trivial) Htarget.header.type htargetTypeTr
    have htargetUvars : target.uvars = 0 := by
      simpa [hlparams] using Htarget.header.uvars
    have htargetLookup : H.context.venv.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.translation.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hnatCanonical : TrExprS H.context.venv c.lparams []
        (.const ``Nat []) .nat := by
      apply TrExprS.const
      · simpa [Htarget.header.name] using htargetLookup
      · simp [hlparams]
      · simp [htargetUvars, hlparams]
    have hzeroType : zeroVal.type = .const target.name [] := by
      simpa [VExpr.nat, Htarget.header.name] using
        TrExprS.unique (by trivial) Hzero.type hnatCanonical
    have hsuccCanonical : TrExprS H.context.venv c.lparams []
        (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
        (.forallE .nat .nat) := by
      apply TrExprS.forallE
      · refine ⟨.succ .zero, ?_⟩
        have h := primitiveTargetHasType hdeclUvars htargetUvars
          htargetLookup htargetType []
        simpa only [VLCtx.toCtx, VExpr.nat, Htarget.header.name,
          H.translation.uvars] using h
      · refine ⟨.succ .zero, ?_⟩
        have h := primitiveTargetHasType hdeclUvars htargetUvars
          htargetLookup htargetType [.nat]
        simpa only [VLCtx.toCtx, VExpr.nat, Htarget.header.name,
          H.translation.uvars] using h
      · exact hnatCanonical
      · apply TrExprS.const
        · simpa [Htarget.header.name] using htargetLookup
        · simp [hlparams]
        · simp [htargetUvars, hlparams]
    have hsuccType : succVal.type = .forallE .nat .nat :=
      TrExprS.unique (by trivial) Hsucc.type hsuccCanonical
    have htargetShape := H.headers.typeShapes target (by simp [hdeclTypes])
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have hmetadata := primitiveTarget_metadata hsourceWF
      hdeclParams htargetType (by simpa [hheaderParams] using htargetShape)
    rcases hmetadata with ⟨hnindices, hresultLevel⟩
    have hzeroShape := primitiveResultCtorShape H.context.checking.wf
      hdeclTypes hdeclUvars hdeclParams htargetUvars hnindices hzeroType
      htargetLookup htargetType
    have hsuccShape := primitiveNatSuccCtorShape H.context.checking.wf
      hdeclTypes Htarget.header.name hdeclUvars hdeclParams htargetUvars
      hnindices hresultLevel hsuccType htargetLookup htargetType
    have hzeroIsType : H.context.venv.IsType decl.uvars [] zeroVal.type := by
      refine ⟨.succ .zero, ?_⟩
      rw [hzeroType]
      exact primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
        htargetType []
    have hsuccIsType : H.context.venv.IsType decl.uvars [] succVal.type := by
      refine ⟨.imax (.succ .zero) (.succ .zero), ?_⟩
      rw [hsuccType]
      have hdom : H.context.venv.IsDefEq decl.uvars [] .nat .nat
          (.sort (.succ .zero)) := by
        simpa only [VEnv.HasType, VExpr.nat, Htarget.header.name] using
          (primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
            htargetType [])
      have hbody : H.context.venv.IsDefEq decl.uvars [.nat] .nat .nat
          (.sort (.succ .zero)) := by
        simpa only [VEnv.HasType, VExpr.nat, Htarget.header.name] using
          (primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
            htargetType [.nat])
      exact VEnv.IsDefEq.forallEDF hdom hbody
    refine { formation := ⟨?_⟩, types := ?_ }
    · intro owned howned
      rcases List.mem_flatMap.mp howned with ⟨family, hfamily, hctor⟩
      simp [hdeclTypes] at hfamily
      subst family
      simp only [List.mem_map] at hctor
      rcases hctor with ⟨ctor, hctor, rfl⟩
      rw [htargetCtors] at hctor
      rcases List.mem_cons.mp hctor with rfl | hctor
      · simpa [hheaderParams] using hzeroShape
      · have : ctor = succVal := by simpa using hctor
        subst ctor
        simpa [hheaderParams] using hsuccShape
    · intro ctor hctor
      simp only [VInductDecl.constructorConstants] at hctor
      rw [hdeclTypes] at hctor
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hctor
      rw [htargetCtors] at hctor
      rcases List.mem_cons.mp hctor with rfl | hctor
      · exact hzeroIsType
      · have : ctor = succVal := by simpa using hctor
        subst ctor
        exact hsuccIsType

/-- Canonical primitive constructor tails replay in the empty cached-
parameter scope.  The abstract tail certificates are built directly above;
the executable source/target correspondence comes from the staged header
translation. -/
theorem PrimitiveDeclaredHeadersResult.constructorTails
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    CheckedRecursorConstructorTails H.context.venv c.lparams
      H.materialized.parameterScope stats decl indTypes := by
  have hparams := H.params_size_eq_zero Hshape
  have hscope := H.parameterScope_eq_nil Hshape
  have hheaderParams := H.headerParams_eq_nil Hshape
  rcases Hshape with ⟨hlparams, hnparams, _hunsafe, htypes⟩
  have hdeclUvars : decl.uvars = 0 := by
    rw [H.translation.uvars, hlparams]
    rfl
  have hdeclParams : decl.nparams = 0 := H.translation.nparams.trans hnparams
  rcases htypes with hbool | ⟨binderName, binderInfo, hnat⟩
  · have hindTypes : indTypes = #[{
        name := ``Bool
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Bool.false, type := .const ``Bool [] },
          { name := ``Bool.true, type := .const ``Bool [] }] }] := by
      apply Array.toList_inj.mp
      simpa using hbool
    have Htypes := H.translation.types
    rw [hbool] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨falseVal, trueVal, htargetCtors, Hfalse, Htrue⟩
    have htargetType : target.type = .sort (.succ .zero) := by
      apply TrExprS.unique (by trivial) Htarget.header.type
      exact TrExprS.sort (by rw [hlparams]; rfl)
    have htargetUvars : target.uvars = 0 := by
      simpa [hlparams] using Htarget.header.uvars
    have htargetLookup : H.context.venv.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.translation.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have htargetShape := H.headers.typeShapes target (by simp [hdeclTypes])
    have hmetadata := primitiveTarget_metadata hsourceWF hdeclParams
      htargetType (by simpa [hheaderParams] using htargetShape)
    rcases hmetadata with ⟨hnindices, _⟩
    have hfalseType : falseVal.type = .const target.name [] := by
      have hcanonical : TrExprS H.context.venv c.lparams []
          (.const ``Bool []) .bool := by
        apply TrExprS.const
        · simpa [Htarget.header.name] using htargetLookup
        · simp [hlparams]
        · simp [htargetUvars]
      simpa [VExpr.bool, Htarget.header.name] using
        TrExprS.unique (by trivial) Hfalse.type hcanonical
    have htrueType : trueVal.type = .const target.name [] := by
      have hcanonical : TrExprS H.context.venv c.lparams []
          (.const ``Bool []) .bool := by
        apply TrExprS.const
        · simpa [Htarget.header.name] using htargetLookup
        · simp [hlparams]
        · simp [htargetUvars]
      simpa [VExpr.bool, Htarget.header.name] using
        TrExprS.unique (by trivial) Htrue.type hcanonical
    have HfalseTail := primitiveResultTailCertificate hdeclTypes
      hdeclUvars hdeclParams htargetUvars hnindices htargetLookup htargetType
    have HtrueTail := primitiveResultTailCertificate hdeclTypes
      hdeclUvars hdeclParams htargetUvars hnindices htargetLookup htargetType
    refine { size_eq := by rw [hindTypes]; simp [hdeclTypes], replay := ?_ }
    intro familyIdx hfamily ctorIdx hctor
    have hfamilyIdx : familyIdx = 0 := by
      have : familyIdx < (#[{
          name := ``Bool
          type := .sort (.succ .zero)
          ctors := [
            { name := ``Bool.false, type := .const ``Bool [] },
            { name := ``Bool.true, type := .const ``Bool [] }] }] :
            Array InductiveType).size := by simpa [hindTypes] using hfamily
      simpa using this
    subst familyIdx
    have hctorBound : ctorIdx < 2 := by simpa [hindTypes] using hctor
    have hctorIdx : ctorIdx = 0 ∨ ctorIdx = 1 := by omega
    rcases hctorIdx with rfl | rfl
    · have HfalseTail' : ConstructorTailCertificate H.context.venv decl
          target [] 0 falseVal.type := by simpa [hfalseType] using HfalseTail
      simpa [hscope, hdeclTypes, hindTypes] using
        primitiveTailReplay H.translation.uvars.symm hparams
          (by simp [htargetCtors]) Hfalse HfalseTail'
    · have HtrueTail' : ConstructorTailCertificate H.context.venv decl
          target [] 0 trueVal.type := by simpa [htrueType] using HtrueTail
      simpa [hscope, hdeclTypes, hindTypes] using
        primitiveTailReplay H.translation.uvars.symm hparams
          (by simp [htargetCtors]) Htrue HtrueTail'
  · have hindTypes : indTypes = #[{
        name := ``Nat
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Nat.zero, type := .const ``Nat [] },
          { name := ``Nat.succ,
            type := .forallE binderName (.const ``Nat [])
              (.const ``Nat []) binderInfo }] }] := by
      apply Array.toList_inj.mp
      simpa using hnat
    have Htypes := H.translation.types
    rw [hnat] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨zeroVal, succVal, htargetCtors, Hzero, Hsucc⟩
    have htargetType : target.type = .sort (.succ .zero) := by
      apply TrExprS.unique (by trivial) Htarget.header.type
      exact TrExprS.sort (by rw [hlparams]; rfl)
    have htargetUvars : target.uvars = 0 := by
      simpa [hlparams] using Htarget.header.uvars
    have htargetLookup : H.context.venv.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.translation.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have htargetShape := H.headers.typeShapes target (by simp [hdeclTypes])
    have hmetadata := primitiveTarget_metadata hsourceWF hdeclParams
      htargetType (by simpa [hheaderParams] using htargetShape)
    rcases hmetadata with ⟨hnindices, hresultLevel⟩
    have hnatCanonical : TrExprS H.context.venv c.lparams []
        (.const ``Nat []) .nat := by
      apply TrExprS.const
      · simpa [Htarget.header.name] using htargetLookup
      · simp [hlparams]
      · simp [htargetUvars]
    have hzeroType : zeroVal.type = .const target.name [] := by
      simpa [VExpr.nat, Htarget.header.name] using
        TrExprS.unique (by trivial) Hzero.type hnatCanonical
    have hsuccCanonical : TrExprS H.context.venv c.lparams []
        (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
        (.forallE .nat .nat) := by
      apply TrExprS.forallE
      · refine ⟨.succ .zero, ?_⟩
        simpa only [VLCtx.toCtx, VExpr.nat, Htarget.header.name,
          H.translation.uvars] using
            primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
              htargetType []
      · refine ⟨.succ .zero, ?_⟩
        simpa only [VLCtx.toCtx, VExpr.nat, Htarget.header.name,
          H.translation.uvars] using
            primitiveTargetHasType hdeclUvars htargetUvars htargetLookup
              htargetType [.nat]
      · exact hnatCanonical
      · apply TrExprS.const
        · simpa [Htarget.header.name] using htargetLookup
        · simp [hlparams]
        · simp [htargetUvars]
    have hsuccType : succVal.type = .forallE .nat .nat :=
      TrExprS.unique (by trivial) Hsucc.type hsuccCanonical
    have HzeroTail := primitiveResultTailCertificate hdeclTypes
      hdeclUvars hdeclParams htargetUvars hnindices htargetLookup htargetType
    have HsuccTail := primitiveNatSuccTailCertificate hdeclTypes
      Htarget.header.name hdeclUvars hdeclParams htargetUvars hnindices
      hresultLevel htargetLookup htargetType
    refine { size_eq := by rw [hindTypes]; simp [hdeclTypes], replay := ?_ }
    intro familyIdx hfamily ctorIdx hctor
    have hfamilyIdx : familyIdx = 0 := by
      have : familyIdx < (#[{
          name := ``Nat
          type := .sort (.succ .zero)
          ctors := [
            { name := ``Nat.zero, type := .const ``Nat [] },
            { name := ``Nat.succ,
              type := .forallE binderName (.const ``Nat [])
                (.const ``Nat []) binderInfo }] }] : Array InductiveType).size := by
        simpa [hindTypes] using hfamily
      simpa using this
    subst familyIdx
    have hctorBound : ctorIdx < 2 := by simpa [hindTypes] using hctor
    have hctorIdx : ctorIdx = 0 ∨ ctorIdx = 1 := by omega
    rcases hctorIdx with rfl | rfl
    · have HzeroTail' : ConstructorTailCertificate H.context.venv decl
          target [] 0 zeroVal.type := by simpa [hzeroType] using HzeroTail
      simpa [hscope, hdeclTypes, hindTypes] using
        primitiveTailReplay H.translation.uvars.symm hparams
          (by simp [htargetCtors]) Hzero HzeroTail'
    · have HsuccTail' : ConstructorTailCertificate H.context.venv decl
          target [] 0 succVal.type := by simpa [hsuccType] using HsuccTail
      simpa [hscope, hdeclTypes, hindTypes] using
        primitiveTailReplay H.translation.uvars.symm hparams
          (by simp [htargetCtors]) Hsucc HsuccTail'

/-- The checker-independent canonical constructor syntax also fixes the owner
normal forms later consumed by recursor construction. -/
theorem PrimitiveDeclaredHeadersResult.ownerNormalForms
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    CheckedConstructorOwnerNormalForms stats indTypes := by
  have hparams := H.params_size_eq_zero Hshape
  have hparamsArray : stats.params = #[] :=
    Array.eq_empty_of_size_eq_zero hparams
  have hheaderParams := H.headerParams_eq_nil Hshape
  rcases Hshape with ⟨hlparams, hnparams, _hunsafe, htypes⟩
  have hdeclParams : decl.nparams = 0 := H.translation.nparams.trans hnparams
  have hlevels : stats.levels = [] := by
    rw [H.materialized.levelParams, hlparams]
    rfl
  rcases htypes with hbool | ⟨binderName, binderInfo, hnat⟩
  · have hindTypes : indTypes = #[{
        name := ``Bool
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Bool.false, type := .const ``Bool [] },
          { name := ``Bool.true, type := .const ``Bool [] }] }] := by
      apply Array.toList_inj.mp
      simpa using hbool
    have Htypes := H.translation.types
    rw [hbool] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    have htargetType : target.type = .sort (.succ .zero) := by
      apply TrExprS.unique (by trivial) Htarget.header.type
      exact TrExprS.sort (by rw [hlparams]; rfl)
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have hmetadata := primitiveTarget_metadata hsourceWF hdeclParams
      htargetType (by
        simpa [hheaderParams] using
          H.headers.typeShapes target (by simp [hdeclTypes]))
    rcases hmetadata with ⟨hnindices, _⟩
    have hstatsIndices : stats.nindices = #[0] := by
      apply Array.toList_inj.mp
      simpa [hdeclTypes, hnindices] using H.materialized.indices
    have hstatsConsts : stats.indConsts = #[.const ``Bool []] := by
      rw [H.materialized.consts, hlevels, hdeclTypes]
      simp [Htarget.header.name]
    rw [hindTypes]
    refine ⟨?_⟩
    intro familyIdx hfamily ctorIdx hctor
    have hfamilyIdx : familyIdx = 0 := by simpa using hfamily
    subst familyIdx
    have hctorBound : ctorIdx < 2 := by simpa using hctor
    have hctorIdx : ctorIdx = 0 ∨ ctorIdx = 1 := by omega
    rcases hctorIdx with rfl | rfl
    · exact primitiveResultOwnerNormalForm hparams hparamsArray
        hstatsConsts hstatsIndices
    · exact primitiveResultOwnerNormalForm hparams hparamsArray
        hstatsConsts hstatsIndices
  · have hindTypes : indTypes = #[{
        name := ``Nat
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Nat.zero, type := .const ``Nat [] },
          { name := ``Nat.succ,
            type := .forallE binderName (.const ``Nat [])
              (.const ``Nat []) binderInfo }] }] := by
      apply Array.toList_inj.mp
      simpa using hnat
    have Htypes := H.translation.types
    rw [hnat] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    have htargetType : target.type = .sort (.succ .zero) := by
      apply TrExprS.unique (by trivial) Htarget.header.type
      exact TrExprS.sort (by rw [hlparams]; rfl)
    have hsourceWF : sourceEnv.WF := by
      simpa [H.sourceContextVEnv] using H.sourceContext.checking.tr.wf
    have hmetadata := primitiveTarget_metadata hsourceWF hdeclParams
      htargetType (by
        simpa [hheaderParams] using
          H.headers.typeShapes target (by simp [hdeclTypes]))
    rcases hmetadata with ⟨hnindices, _⟩
    have hstatsIndices : stats.nindices = #[0] := by
      apply Array.toList_inj.mp
      simpa [hdeclTypes, hnindices] using H.materialized.indices
    have hstatsConsts : stats.indConsts = #[.const ``Nat []] := by
      rw [H.materialized.consts, hlevels, hdeclTypes]
      simp [Htarget.header.name]
    rw [hindTypes]
    refine ⟨?_⟩
    intro familyIdx hfamily ctorIdx hctor
    have hfamilyIdx : familyIdx = 0 := by simpa using hfamily
    subst familyIdx
    have hctorBound : ctorIdx < 2 := by simpa using hctor
    have hctorIdx : ctorIdx = 0 ∨ ctorIdx = 1 := by omega
    rcases hctorIdx with rfl | rfl
    · exact primitiveResultOwnerNormalForm hparams hparamsArray
        hstatsConsts hstatsIndices
    · exact primitiveNatSuccOwnerNormalForm hparams hparamsArray
        hstatsConsts hstatsIndices

/-- The executable constructor check is still run on the primitive branch;
when it succeeds, the finite canonical argument above supplies its first two
semantic products without requiring a valid header-only context. -/
theorem AddInductive.checkConstructors.primitiveCoreWF
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := headerEnv }).WF fun _ =>
        CheckedConstructorsResult sourceEnv decl H.context.venv
            H.headers.params stats indTypes c.lparams
            H.materialized.parameterScope ∧
          CheckedConstructorOwnerNormalForms stats indTypes := by
  intro _ _
  exact ⟨{
    checked := H.checkedConstructors Hshape
    parameterPrefixes := H.parameterPrefixes Hshape
    constructorTails := H.constructorTails Hshape },
    H.ownerNormalForms Hshape⟩

end VerifyInductive
end Lean4Lean
