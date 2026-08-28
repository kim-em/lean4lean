import Lean4Lean.Verify.Typing.ProjectionReadiness

namespace Lean4Lean

open Lean

/-- Semantic counterpart of the executable common-parameter loop in
`inferProj`.  Each step exposes a forall only up to definitional equality,
checks the supplied argument against its domain, and instantiates the body.
Consequently aliases normalized by `whnf` do not become syntactic premises
of the projection specification. -/
inductive ProjectionParameterSpine
    (env : VEnv) (U : Nat) (Gamma : List VExpr) :
    Nat → VExpr → List VExpr → VExpr → Prop
  | nil (H : env.IsDefEqU U Gamma source residual) :
      ProjectionParameterSpine env U Gamma 0 source [] residual
  | cons
      (Hforall : env.IsDefEqU U Gamma source (.forallE domain body))
      (Hargument : env.HasType U Gamma argument domain)
      (Htail : ProjectionParameterSpine env U Gamma count
        (body.inst argument) arguments residual) :
      ProjectionParameterSpine env U Gamma (count + 1) source
        (argument :: arguments) residual

/-- Semantic counterpart of exposing the constructor fields after common
parameters have been consumed.  Domains are retained outermost-first and in
the precise progressively extended contexts used by the canonical minor.
The final residual is retained for the constructor-result check. -/
inductive ProjectionFieldTelescope
    (env : VEnv) (U : Nat) :
    List VExpr → Nat → VExpr → List VExpr → VExpr → Prop
  | nil (H : env.IsDefEqU U Gamma source residual) :
      ProjectionFieldTelescope env U Gamma 0 source [] residual
  | cons
      (Hforall : env.IsDefEqU U Gamma source (.forallE domain body))
      (Htail : ProjectionFieldTelescope env U (domain :: Gamma)
        count body domains residual) :
      ProjectionFieldTelescope env U Gamma (count + 1) source
        (domain :: domains) residual

@[simp] theorem ProjectionFieldTelescope.domains_length
    (H : ProjectionFieldTelescope env U Gamma count source domains residual) :
    domains.length = count := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

@[simp] theorem ProjectionParameterSpine.arguments_length
    (H : ProjectionParameterSpine env U Gamma count source arguments residual) :
    arguments.length = count := by
  induction H with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- Transport a complete field telescope across an ordinary definitionally
equal context and a definitionally equal source.  The domains and residual
remain literal syntax; only their typing derivations are transported. -/
theorem ProjectionFieldTelescope.defeqCtxSource
    (henv : VEnv.WF env) (hGamma : OnCtx Gamma (env.IsType U))
    (Hctx : env.IsDefEqCtx U [] Gamma Gamma')
    (Hsource : env.IsDefEqU U Gamma' source' source)
    (H : ProjectionFieldTelescope env U Gamma count source domains residual) :
    ProjectionFieldTelescope env U Gamma' count source' domains residual := by
  induction H generalizing Gamma' source' with
  | @nil Gamma source residual Hresidual =>
      have hGamma' : OnCtx Gamma' (env.IsType U) :=
        (Hctx.symm henv.ordered).isType' (by trivial)
      exact .nil (Hsource.trans henv hGamma'
        (Hresidual.defeqDFC henv.ordered Hctx))
  | @cons Gamma source domain body count domains residual
      Hforall Htail ih =>
      have hGamma' : OnCtx Gamma' (env.IsType U) :=
        (Hctx.symm henv.ordered).isType' (by trivial)
      have Hforall' := Hforall.defeqDFC henv.ordered Hctx
      have Hwhole : env.IsDefEqU U Gamma' source'
          (.forallE domain body) :=
        Hsource.trans henv hGamma' Hforall'
      rcases Hforall with ⟨wholeType, HwholeTyped⟩
      have hdomain : env.IsType U Gamma domain :=
        (HwholeTyped.hasType.2.forallE_inv henv.ordered).1
      rcases hdomain with ⟨domainLevel, Hdomain⟩
      rcases Hforall' with ⟨wholeType', HwholeTyped'⟩
      have hparts' := HwholeTyped'.hasType.2.forallE_inv henv.ordered
      have HctxTail : env.IsDefEqCtx U []
          (domain :: Gamma) (domain :: Gamma') :=
        .succ Hctx Hdomain
      have HbodyWF : VExpr.WF env U (domain :: Gamma') body := by
        rcases hparts'.2 with ⟨bodyLevel, Hbody⟩
        exact ⟨_, Hbody⟩
      exact .cons Hwhole
        (ih (by exact ⟨hGamma, ⟨_, Hdomain⟩⟩) HctxTail
          (.refl HbodyWF))

/-- Formation of an installed constructor determines a finite complete field
telescope from its raw abstract tail.  The proof follows `CtorTailWF`; it does
not execute WHNF on fields after the selected projection. -/
theorem VInductDecl.CtorTailWF.projectionFieldTelescope
    {decl : VInductDecl} {target : VInductiveType}
    (H : VInductDecl.CtorTailWF env decl target Gamma depth source)
    (henv : VEnv.WF env)
    (hGamma : OnCtx Gamma (env.IsType decl.uvars))
    (Hsource : VExpr.WF env decl.uvars Gamma source) :
    ∃ count domains residual,
      ProjectionFieldTelescope env decl.uvars Gamma count source
        domains residual := by
  induction H with
  | @result depth result' ctx resultExpr resultType Hvalid Hresult =>
      exact ⟨0, [], resultExpr, .nil (.refl Hsource)⟩
  | @field ctx domain fieldLevel depth checkedDomain checkedLevel body
      checkedBody bodyType HdomainType Hlevel Hpositive Hdomain Hbody Htail ih =>
      have hcheckedDomain : env.IsType decl.uvars ctx checkedDomain := by
        exact ⟨_, Hdomain.hasType.2⟩
      have hcheckedCtx : OnCtx (checkedDomain :: ctx)
          (env.IsType decl.uvars) :=
        ⟨hGamma, hcheckedDomain⟩
      have hcheckedBody : VExpr.WF env decl.uvars
          (checkedDomain :: ctx) checkedBody := by
        have HctxForward : env.IsDefEqCtx decl.uvars []
            (domain :: ctx) (checkedDomain :: ctx) :=
          .succ (.refl hGamma) Hdomain
        exact ⟨_, Hbody.hasType.2.defeqDFC henv.ordered HctxForward⟩
      rcases ih hcheckedCtx hcheckedBody with
        ⟨count, domains, residual, Hfields⟩
      have Hctx : env.IsDefEqCtx decl.uvars []
          (checkedDomain :: ctx) (domain :: ctx) :=
        .succ (.refl hGamma) Hdomain.symm
      have Hfields' := Hfields.defeqCtxSource henv hcheckedCtx Hctx
        Hbody.toU
      exact ⟨count + 1, domain :: domains, residual,
        .cons (.refl Hsource) Hfields'⟩

/-- Parameter consumption is deterministic up to definitional equality.
This is the semantic uniqueness fact needed by a production-indexed
translation relation: different WHNF representatives of the same forall
spine cannot change the residual constructor type. -/
theorem ProjectionParameterSpine.residualDefEq
    (henv : VEnv.WF env) (hGamma : OnCtx Gamma (env.IsType U))
    (Hleft : ProjectionParameterSpine env U Gamma count
      leftSource arguments leftResidual)
    (Hright : ProjectionParameterSpine env U Gamma count
      rightSource arguments rightResidual)
    (Hsource : env.IsDefEqU U Gamma leftSource rightSource) :
    env.IsDefEqU U Gamma leftResidual rightResidual := by
  induction Hleft generalizing rightSource rightResidual with
  | nil Hleft =>
      cases Hright with
      | nil Hright =>
          exact (Hleft.symm.trans henv hGamma Hsource).trans
            henv hGamma Hright
  | @cons source domain body argument arguments residual count
      Hforall Hargument Htail ih =>
      cases Hright with
      | @cons _ rightDomain rightBody _ _ _ _ HrightForall
          _HrightArgument HrightTail =>
          have Hforalls : env.IsDefEqU U Gamma
              (.forallE domain body) (.forallE rightDomain rightBody) :=
            (Hforall.symm.trans henv hGamma Hsource).trans
              henv hGamma HrightForall
          rcases Hforalls.forallE_inv henv hGamma with
            ⟨⟨_, _Hdomains⟩, _, Hbodies⟩
          have Hbodies' : env.IsDefEqU U (domain :: Gamma)
              body rightBody := ⟨_, Hbodies⟩
          have Hinstantiated : env.IsDefEqU U Gamma
              (body.inst argument) (rightBody.inst argument) :=
            Hbodies'.instN henv.ordered .zero Hargument
          exact ih HrightTail Hinstantiated

/-- Split a pointwise translation at the same positional boundary on both
sides.  The standard library does not currently expose this `Forall₂`
projection, while projection inference must separate common parameters from
indices after the executable arity check. -/
theorem forall₂_splitAt
    (H : List.Forall₂ relation source target) (count : Nat) :
    ∃ targetPrefix targetSuffix,
      target = targetPrefix ++ targetSuffix ∧
      List.Forall₂ relation (source.take count) targetPrefix ∧
      List.Forall₂ relation (source.drop count) targetSuffix := by
  induction count generalizing source target with
  | zero => exact ⟨[], target, by simp, .nil, by simpa using H⟩
  | succ count ih =>
      cases H with
      | nil => exact ⟨[], [], by simp, .nil, .nil⟩
      | @cons sourceHead targetHead sourceTail targetTail hhead htail =>
          rcases ih htail with
            ⟨targetPrefix, targetSuffix, rfl, hprefix, hsuffix⟩
          exact ⟨targetHead :: targetPrefix, targetSuffix, by simp,
            .cons hhead hprefix, hsuffix⟩

/-- A strict translation preserves every syntactically visible leading
forall counted by production constructor metadata.  No normalization is
performed: the theorem only follows the literal source prefix and exposes the
corresponding literal abstract domains. -/
theorem TrExprS.constructorArityPrefix
    (H : TrExprS env Us Delta source target)
    (hcount : count ≤ AddInductive.constructorArity source) :
    ∃ domains residual,
      domains.length = count ∧
      target = VExpr.wrapForalls domains residual := by
  induction count generalizing Delta source target with
  | zero =>
      exact ⟨[], target, rfl, rfl⟩
  | succ count ih =>
      cases source <;>
        simp only [AddInductive.constructorArity] at hcount
      all_goals try omega
      case forallE binderName domain body binderInfo =>
        cases H with
        | @forallE targetDomain targetBody Delta domain body binderName
            binderInfo HdomainType HbodyType Hdomain Hbody =>
          have htail : count ≤ AddInductive.constructorArity body := by
            omega
          rcases ih Hbody htail with
            ⟨domains, residual, hlength, htarget⟩
          exact ⟨targetDomain :: domains, residual, by simp [hlength], by
            simp [htarget, VExpr.wrapForalls]⟩

namespace AppStack

/-- Recover the ordered abstract argument spine retained by `AppStack`.
Besides pointwise source translation, the result reconstructs the exact
abstract application represented by the stack. -/
theorem translatedArguments
    (H : AppStack env Us Delta fn fn' args) :
    ∃ args' : List VExpr,
      List.Forall₂ (TrExprS env Us Delta) args args' ∧
      TrExprS env Us Delta (fn.mkAppList args) (VExpr.mkApps fn' args') := by
  induction H with
  | head Hfn =>
      exact ⟨[], .nil, by simpa [VExpr.mkApps] using Hfn⟩
  | @app fn arg fn' arg' domain body args _ _ Hfn Harg Htail ih =>
      rcases ih with ⟨args', Hargs, Hfull⟩
      refine ⟨arg' :: args', .cons Harg Hargs, ?_⟩
      simpa [VExpr.mkApps] using Hfull

/-- A concrete constant-headed application translated through `AppStack`
has one exact translated universe spine and one ordered abstract term spine.
This is the structural decomposition needed immediately after `inferProj`'s
`whnf`/`withApp` branch. -/
theorem constantApplication
    (H : AppStack env Us Delta (.const name levels) abstractHead args) :
    ∃ translatedLevels translatedArgs,
      levels.mapM (VLevel.ofLevel Us) = some translatedLevels ∧
      abstractHead = VExpr.const name translatedLevels ∧
      List.Forall₂ (TrExprS env Us Delta) args translatedArgs ∧
      TrExprS env Us Delta
        ((Expr.const name levels).mkAppList args)
        (VExpr.mkApps (VExpr.const name translatedLevels) translatedArgs) := by
  have Hhead := H.tr
  cases Hhead with
  | const hlookup hlevels hlength =>
      rcases H.translatedArguments with ⟨translatedArgs, Hargs, Hfull⟩
      exact ⟨_, translatedArgs, hlevels, rfl, Hargs, Hfull⟩

/-- Split the translated major type application at the executable common
parameter boundary.  The suffix length is still stated using production
`numIndices`; identifying it with the installed source owner is the precise
`ProductionFamilyAlignment.numIndices` join supplied by header production. -/
theorem constantApplicationSplit
    (H : AppStack env Us Delta (Expr.const name levels) abstractHead args)
    (hargs : args.length = numParams + numIndices) :
    ∃ translatedLevels translatedParams translatedIndices,
      levels.mapM (VLevel.ofLevel Us) = some translatedLevels ∧
      abstractHead = VExpr.const name translatedLevels ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.take numParams) translatedParams ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.drop numParams) translatedIndices ∧
      translatedParams.length = numParams ∧
      translatedIndices.length = numIndices ∧
      TrExprS env Us Delta
        ((Expr.const name levels).mkAppList args)
        (VExpr.mkApps (VExpr.const name translatedLevels)
          (translatedParams ++ translatedIndices)) := by
  rcases H.constantApplication with
    ⟨translatedLevels, translatedArgs, hlevels, rfl, Hargs, Hfull⟩
  rcases forall₂_splitAt Hargs numParams with
    ⟨translatedParams, translatedIndices, rfl, Hparams, Hindices⟩
  have hparamsLength : translatedParams.length = numParams := by
    rw [← Lean4Lean.List.Forall₂.length_eq Hparams,
      List.length_take]
    omega
  have hindicesLength : translatedIndices.length = numIndices := by
    rw [← Lean4Lean.List.Forall₂.length_eq Hindices,
      List.length_drop, hargs]
    omega
  exact ⟨translatedLevels, translatedParams, translatedIndices,
    hlevels, rfl, Hparams, Hindices, hparamsLength, hindicesLength, Hfull⟩

end AppStack

namespace TrExpr

/-- Exact abstract view exposed when executable WHNF returns a concrete
forall.  The domain and body are strict translations; the whole abstract
forall remains definitionally equal to the pre-WHNF abstract type. -/
structure ForallView
    (env : VEnv) (Us : List Name) (Delta : VLCtx)
    (domain body : Expr) (abstractType : VExpr) where
  abstractDomain : VExpr
  abstractBody : VExpr
  domainType : env.IsType Us.length Delta.toCtx abstractDomain
  bodyType : env.IsType Us.length
    (abstractDomain :: Delta.toCtx) abstractBody
  domainTranslation : TrExprS env Us Delta domain abstractDomain
  bodyTranslation : TrExprS env Us
    ((none, .vlam abstractDomain) :: Delta) body abstractBody
  wholeDefEq : env.IsDefEqU Us.length Delta.toCtx
    (.forallE abstractDomain abstractBody) abstractType

/-- Invert a non-strict translation at an executable forall WHNF result.
No abstract shape premise is needed: strict translation fixes the outer
constructor and retains both typed components. -/
theorem forallView
    (H : TrExpr env Us Delta
      (.forallE binderName domain body binderInfo) abstractType) :
    Nonempty (ForallView env Us Delta domain body abstractType) := by
  rcases H with ⟨strictType, Hstrict, Hdefeq⟩
  cases Hstrict with
  | forallE HdomainType HbodyType Hdomain Hbody =>
      exact ⟨{
        abstractDomain := _
        abstractBody := _
        domainType := HdomainType
        bodyType := HbodyType
        domainTranslation := Hdomain
        bodyTranslation := Hbody
        wholeDefEq := Hdefeq }⟩

/-- Decompose a WHNF major type whose concrete head is an inductive
constant, while retaining the definitional equality supplied by `TrExpr`.

`whnf.WF` deliberately returns a non-strict translation because reduction
may change the concrete syntax.  Projection inference nevertheless needs
the exact abstract application spine selected by that syntax.  This theorem
isolates the join: the strict witness supplies the translated levels,
parameters, and indices, and its final `IsDefEqU` relates that exact
application to the original inferred abstract type. -/
theorem constantApplicationSplit
    (henv : VEnv.WF env) (hDelta : VLCtx.WF env Us.length Delta)
    (H : TrExpr env Us Delta
      ((Expr.const name levels).mkAppList args) abstractType)
    (hargs : args.length = numParams + numIndices) :
    ∃ translatedLevels translatedParams translatedIndices,
      levels.mapM (VLevel.ofLevel Us) = some translatedLevels ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.take numParams) translatedParams ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.drop numParams) translatedIndices ∧
      translatedParams.length = numParams ∧
      translatedIndices.length = numIndices ∧
      env.IsDefEqU Us.length Delta.toCtx
        (VExpr.mkApps (VExpr.const name translatedLevels)
          (translatedParams ++ translatedIndices))
        abstractType := by
  rcases H with ⟨strictType, Hstrict, Hdefeq⟩
  rcases AppStack.build Hstrict with ⟨abstractHead, Hstack⟩
  rcases Hstack.constantApplicationSplit hargs with
    ⟨translatedLevels, translatedParams, translatedIndices,
      _hlevels, rfl, Hparams, Hindices, hparamsLength,
      hindicesLength, Hfull⟩
  have Hjoin : env.IsDefEqU Us.length Delta.toCtx
      (VExpr.mkApps (VExpr.const name translatedLevels)
        (translatedParams ++ translatedIndices)) strictType :=
    Hfull.uniq henv (.refl henv hDelta) Hstrict
  exact ⟨translatedLevels, translatedParams, translatedIndices,
    _hlevels, Hparams, Hindices, hparamsLength, hindicesLength,
    Hjoin.trans henv hDelta.toCtx Hdefeq⟩

/-- Lookup-indexed form of `constantApplicationSplit`.  Matching the strict
head translation against one exact installed constant additionally recovers
the executable universe-arity check. -/
theorem constantApplicationSplitAt
    (henv : VEnv.WF env) (hDelta : VLCtx.WF env Us.length Delta)
    (H : TrExpr env Us Delta
      ((Expr.const name levels).mkAppList args) abstractType)
    (hlookup : env.constants name = some constant)
    (hargs : args.length = numParams + numIndices) :
    ∃ translatedLevels translatedParams translatedIndices,
      levels.mapM (VLevel.ofLevel Us) = some translatedLevels ∧
      levels.length = constant.uvars ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.take numParams) translatedParams ∧
      List.Forall₂ (TrExprS env Us Delta)
        (args.drop numParams) translatedIndices ∧
      translatedParams.length = numParams ∧
      translatedIndices.length = numIndices ∧
      env.IsDefEqU Us.length Delta.toCtx
        (VExpr.mkApps (VExpr.const name translatedLevels)
          (translatedParams ++ translatedIndices))
        abstractType := by
  have hlevelArity : levels.length = constant.uvars := by
    rcases H with ⟨strictType, Hstrict, _Hdefeq⟩
    rcases AppStack.build Hstrict with ⟨abstractHead, Hstack⟩
    have Hhead := Hstack.tr
    cases Hhead with
    | const habstract _ hlength =>
        rw [hlookup] at habstract
        cases Option.some.inj habstract
        exact hlength
  rcases H.constantApplicationSplit henv hDelta hargs with
    ⟨translatedLevels, translatedParams, translatedIndices,
      hlevels, Hparams, Hindices, hparamsLength, hindicesLength, Hdefeq⟩
  exact ⟨translatedLevels, translatedParams, translatedIndices,
    hlevels, hlevelArity, Hparams, Hindices, hparamsLength,
    hindicesLength, Hdefeq⟩

end TrExpr

namespace VerifyInductive.ProjectionNameReady.InferenceMetadata

/-- Exact production `numFields` selects a literal suffix of the translated
constructor telescope.  The complete abstract domains come from strict
translation of the concrete constructor type; no suffix WHNF or projection
compatibility premise is involved. -/
theorem constructorFieldDomains
    (H : InferenceMetadata safety constants env name index) :
    ∃ parameterDomains fieldDomains residual,
      H.sourceConstructor.type = VExpr.wrapForalls
        (parameterDomains ++ fieldDomains) residual ∧
      fieldDomains.length = H.constructor.alignment.info.numFields := by
  let concreteType := H.constructor.alignment.info.type
  let arity := AddInductive.constructorArity concreteType
  have Htranslation : TrExprS env
      H.constructor.alignment.info.levelParams [] concreteType
      H.sourceConstructor.type :=
    H.sourceConstructorTranslation.2.2
  rcases Htranslation.constructorArityPrefix (count := arity)
      (Nat.le_refl arity) with
    ⟨domains, residual, hdomainsLength, htarget⟩
  let parameterDomains := domains.take H.family.decl.nparams
  let fieldDomains := domains.drop H.family.decl.nparams
  have hsplit : domains = parameterDomains ++ fieldDomains := by
    exact (List.take_append_drop H.family.decl.nparams domains).symm
  have hfields : fieldDomains.length =
      H.constructor.alignment.info.numFields := by
    calc
      fieldDomains.length = domains.length - H.family.decl.nparams := by
        simp [fieldDomains]
      _ = arity - H.family.decl.nparams := by rw [hdomainsLength]
      _ = H.constructor.alignment.info.numFields :=
        H.constructor.alignment.numFields.symm
  exact ⟨parameterDomains, fieldDomains, residual,
    by simpa only [hsplit] using htarget, hfields⟩

/-- Exact abstract major-type spine recovered from the executable
`whnf`/`withApp` branch.  Its lengths are already normalized to the installed
declaration for universes and common parameters; indices remain indexed by
the production field until `ProductionFamilyAlignment.numIndices` is
threaded from header production. -/
structure MajorSpine
    (H : InferenceMetadata safety constants env name index)
    (Us : List Name) (Delta : VLCtx) (concreteArgs : List Expr)
    (major : VExpr) where
  familyLevels : List VLevel
  params : List VExpr
  indices : List VExpr
  familyLevels_wf : ∀ level ∈ familyLevels, level.WF Us.length
  familyLevels_length : familyLevels.length = H.family.decl.uvars
  params_length : params.length = H.family.decl.nparams
  indices_length : indices.length = H.familyInfo.numIndices
  majorType : env.HasType Us.length Delta.toCtx major
    (VExpr.mkApps (.const name familyLevels) (params ++ indices))
  paramsTranslation : List.Forall₂ (TrExprS env Us Delta)
    (concreteArgs.take H.familyInfo.numParams) params
  indicesTranslation : List.Forall₂ (TrExprS env Us Delta)
    (concreteArgs.drop H.familyInfo.numParams) indices

/-- Complete the syntax shell once the verified constructor-field loop has
produced the result universe, motive, and exact field telescope. -/
def MajorSpine.expansion
    (S : MajorSpine H Us Delta concreteArgs major)
    (resultLevel : VLevel) (motive : VExpr)
    (fieldDomains : List VExpr) (hindex : index < fieldDomains.length) :
    CanonicalProjectionExpansion where
  structName := H.sourceOwner.name
  familyLevels := S.familyLevels
  resultLevel := resultLevel
  params := S.params
  indices := S.indices
  motive := motive
  major := major
  fieldDomains := fieldDomains
  index := index
  index_lt := hindex

/-- The successful major-type WHNF trace constructs its exact abstract
spine.  Universe and parameter arities are discharged from ordinary
constant translation plus production alignment, rather than accepted as
projection-specific evidence. -/
theorem majorSpine
    (H : InferenceMetadata safety constants env name index)
    (henv : VEnv.WF env) (hDelta : VLCtx.WF env Us.length Delta)
    (Htype : TrExpr env Us Delta
      ((Expr.const name concreteLevels).mkAppList concreteArgs) abstractType)
    (Hmajor : env.HasType Us.length Delta.toCtx major abstractType)
    (hargs : concreteArgs.length =
      H.familyInfo.numParams + H.familyInfo.numIndices) :
    Nonempty (MajorSpine H Us Delta concreteArgs major) := by
  rcases Htype.constantApplicationSplitAt henv hDelta H.sourceOwnerLookup
      hargs with
    ⟨familyLevels, params, indices, hlevels, hlevelArity,
      Hparams, Hindices, hparamsLength, hindicesLength, HtypeDefeq⟩
  have hfamilyLevelsLength : familyLevels.length = H.family.decl.uvars := by
    calc
      familyLevels.length = concreteLevels.length :=
        (Lean4Lean.List.Forall₂.length_eq
          (List.mapM_eq_some.1 hlevels)).symm
      _ = H.sourceOwner.uvars := hlevelArity
      _ = H.familyInfo.levelParams.length :=
        H.sourceOwnerTranslation.2.1.symm
      _ = H.family.decl.uvars := H.family.alignment.levelParams
  have hparamsLength' : params.length = H.family.decl.nparams :=
    hparamsLength.trans H.family.alignment.numParams
  have hmajorType : env.HasType Us.length Delta.toCtx major
      (VExpr.mkApps (.const name familyLevels) (params ++ indices)) :=
    Hmajor.defeqU_r henv hDelta.toCtx HtypeDefeq.symm
  exact ⟨{
    familyLevels := familyLevels
    params := params
    indices := indices
    familyLevels_wf := VLevel.WF.of_mapM_ofLevel hlevels
    familyLevels_length := hfamilyLevelsLength
    params_length := hparamsLength'
    indices_length := hindicesLength
    majorType := hmajorType
    paramsTranslation := Hparams
    indicesTranslation := Hindices }⟩

/-- Assemble the installed-origin half of a canonical projection from exact
resolved metadata.  The only additional inputs are the syntactic universe
and argument-spine lengths of the candidate expansion; all declaration,
owner, constructor, recursor, and eliminator identities are derived from the
successful executable lookup trace. -/
def installedOrigin
    (H : InferenceMetadata safety constants env name index)
    (P : CanonicalProjectionExpansion)
    (hstruct : P.structName = name)
    (hfamilyLevels : P.familyLevels.length = H.family.decl.uvars)
    (hfamilyLevelsWF : ∀ level ∈ P.familyLevels, level.WF U)
    (hresultLevelWF : P.resultLevel.WF U)
    (hparams : P.params.length = H.family.decl.nparams)
    (hindices : P.indices.length = H.sourceOwner.numIndices) :
    CanonicalProjectionExpansion.InstalledOrigin env U P where
  decl := H.family.decl
  owner := H.sourceOwner
  ctor := H.sourceConstructor
  recursor := H.family.recursor
  eliminator := H.eliminator
  installed := H.family.installed
  owner_mem := H.sourceOwner_mem
  owner_name := H.sourceOwner_name.trans hstruct.symm
  owner_single := H.sourceOwnerSingle
  recursor_name := by simpa [hstruct] using H.family.recursorName
  recursor_lookup := by simpa [hstruct] using H.family.recursorLookup
  eliminator_lookup := by simpa [hstruct] using H.eliminatorAbstractLookup
  recursor_shape := by
    simpa [H.sourceOwner_eq] using H.family.recursorShape
  familyLevels_length := hfamilyLevels
  familyLevels_wf := hfamilyLevelsWF
  resultLevel_wf := hresultLevelWF
  params_length := hparams
  indices_length := hindices

/-- The major-spine trace supplies the entire installed typing certificate
for its canonical syntax shell.  Its index count now comes from exact
production-family alignment; the remaining arguments are exactly the outputs
of the constructor-field loop, not compatibility evidence. -/
def MajorSpine.installedTyping
    {safety : DefinitionSafety} {constants : ConstMap} {env : VEnv}
    {name : Name} {index : Nat}
    {H : InferenceMetadata safety constants env name index}
    {Us : List Name} {Delta : VLCtx} {concreteArgs : List Expr}
    {major : VExpr}
    (S : MajorSpine H Us Delta concreteArgs major)
    (resultLevel : VLevel) (hresultLevel : resultLevel.WF Us.length)
    (motive : VExpr) (fieldDomains : List VExpr)
    (hindex : index < fieldDomains.length) :
    CanonicalProjectionExpansion.InstalledTyping env Us.length Delta.toCtx
      (S.expansion resultLevel motive fieldDomains hindex) where
  toInstalledOrigin := {
    decl := H.family.decl
    owner := H.sourceOwner
    ctor := H.sourceConstructor
    recursor := H.family.recursor
    eliminator := H.eliminator
    installed := H.family.installed
    owner_mem := H.sourceOwner_mem
    owner_name := rfl
    owner_single := H.sourceOwnerSingle
    recursor_name := by
      simpa [MajorSpine.expansion, H.sourceOwner_name] using
        H.family.recursorName
    recursor_lookup := by
      simpa [MajorSpine.expansion, H.sourceOwner_name] using
        H.family.recursorLookup
    eliminator_lookup := by
      simpa [MajorSpine.expansion, H.sourceOwner_name] using
        H.eliminatorAbstractLookup
    recursor_shape := by
      simpa [H.sourceOwner_eq] using H.family.recursorShape
    familyLevels_length := S.familyLevels_length
    familyLevels_wf := S.familyLevels_wf
    resultLevel_wf := hresultLevel
    params_length := S.params_length
    indices_length := S.indices_length.trans (by
      simpa [H.sourceOwner_eq] using H.family.alignment.numIndices) }
  majorType := by
    change env.HasType Us.length Delta.toCtx major
      (VExpr.mkApps (.const H.sourceOwner.name S.familyLevels)
        (S.params ++ S.indices))
    rw [H.sourceOwner_name]
    exact S.majorType

end VerifyInductive.ProjectionNameReady.InferenceMetadata

end Lean4Lean
