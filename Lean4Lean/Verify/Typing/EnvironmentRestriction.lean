import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

open Lean

namespace VEnv

/-- The constants on which a particular typing/definitional-equality
derivation depends.  This is proof-relevant on purpose: merely knowing that
the endpoints avoid a name cannot exclude a transitivity detour through that
constant. -/
inductive IsDefEq.UsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {ctx lhs rhs type}, env.IsDefEq uvars ctx lhs rhs type → Prop where
  | elimDF {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size}
      (Hlookup : env.eliminators block schema)
      (Htype : schema.genericType owner = some type)
      (Hclosed : type.Closed)
      (Hperm : schema.Permission uvars owner levels target)
      (Hright : ∀ level ∈ target' :: levels', level.WF uvars)
      (Heq : List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels'))
      (Htyping : env.IsDefEq uvars ctx (type.instL (target :: levels))
        (type.instL (target :: levels)) (.sort typeLevel)) :
      UsesOnly changed Htyping →
      UsesOnly changed (.elimDF Hlookup Htype Hclosed Hperm Hright Heq Htyping)
  | elimIota {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size}
      (Hlookup : env.eliminators block schema)
      (Hgen : schema.genericEquations block owner = some rules)
      (Hmem : df ∈ rules)
      (Hclosed : InductiveSignature.CaseSchema.RuleClosed df)
      (Hperm : schema.Permission uvars owner levels target)
      (Hleft : env.IsDefEq uvars ctx (df.lhs.instL (target :: levels))
        (df.lhs.instL (target :: levels)) (df.type.instL (target :: levels)))
      (Hright : env.IsDefEq uvars ctx (df.rhs.instL (target :: levels))
        (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels))) :
      UsesOnly changed Hleft → UsesOnly changed Hright →
      UsesOnly changed (.elimIota Hlookup Hgen Hmem Hclosed Hperm Hleft Hright)
  | bvar (H : Lookup ctx i type) : UsesOnly changed (.bvar H)
  | symm : UsesOnly changed H → UsesOnly changed (.symm H)
  | trans : UsesOnly changed H₁ → UsesOnly changed H₂ →
      UsesOnly changed (.trans H₁ H₂)
  | sortDF (Hleft : left.WF uvars) (Hright : right.WF uvars)
      (Heq : left ≈ right) : UsesOnly changed (.sortDF Hleft Hright Heq)
  | constDF
      (name : Name) (ci : VConstant)
      (levels levels' : List VLevel)
      (Hlookup : env.constants name = some ci)
      (Hleft : ∀ (level : VLevel), level ∈ levels → level.WF uvars)
      (Hright : ∀ (level : VLevel), level ∈ levels' → level.WF uvars)
      (Hlength : levels.length = ci.uvars)
      (Heq : List.Forall₂ (· ≈ ·) levels levels')
      (Hname : ¬ changed name) :
      UsesOnly changed (.constDF Hlookup Hleft Hright Hlength Heq)
  | appDF : UsesOnly changed Hfn → UsesOnly changed Harg →
      UsesOnly changed (.appDF Hfn Harg)
  | projDF
      (typeName : Name) (info : VProjectionInfo)
      (levels : List VLevel) (params indexArgs : List VExpr)
      (index : Nat) (sourceMajor fieldType : VExpr)
      (Gamma : List VExpr) (fieldLevel : VLevel)
      (major major' : VExpr)
      (Hinfo : env.projections typeName info)
      (Hlevels : ∀ level ∈ levels, level.WF uvars)
      (Huvars : levels.length = info.uvars)
      (Hparams : params.length = info.nparams)
      (Hindices : indexArgs.length = info.nindices)
      (HfieldType : info.fieldType typeName levels params index sourceMajor =
        some fieldType)
      (Hfield : env.IsDefEq uvars Gamma fieldType fieldType (.sort fieldLevel))
      (Hmajor : env.IsDefEq uvars Gamma sourceMajor major
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)))
      (Hmajor' : env.IsDefEq uvars Gamma sourceMajor major'
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)))
      (Hclosed : info.ctorType.Closed)
      (Hguard : (info.resultLevel.inst levels).IsNeverZero ∨
        fieldLevel ≈ .zero) :
      UsesOnly changed Hfield → UsesOnly changed Hmajor →
      UsesOnly changed Hmajor' →
      UsesOnly changed (.projDF Hinfo Hlevels Huvars Hparams Hindices
        HfieldType Hfield Hmajor Hmajor' Hclosed Hguard)
  | lamDF : UsesOnly changed Htype → UsesOnly changed Hbody →
      UsesOnly changed (.lamDF Htype Hbody)
  | forallEDF : UsesOnly changed Htype → UsesOnly changed Hbody →
      UsesOnly changed (.forallEDF Htype Hbody)
  | defeqDF : UsesOnly changed Htype → UsesOnly changed Hterm →
      UsesOnly changed (.defeqDF Htype Hterm)
  | beta : UsesOnly changed Hbody → UsesOnly changed Harg →
      UsesOnly changed (.beta Hbody Harg)
  | eta : UsesOnly changed H → UsesOnly changed (.eta H)
  | proofIrrel : UsesOnly changed Hprop → UsesOnly changed Hleft →
      UsesOnly changed Hright →
      UsesOnly changed (.proofIrrel Hprop Hleft Hright)
  | extra
      (df : VDefEq) (levels : List VLevel)
      (Hdf : env.defeqs df)
      (Hlevels : ∀ (level : VLevel), level ∈ levels → level.WF uvars)
      (Hlength : levels.length = df.uvars) :
      UsesOnly changed (.extra Hdf Hlevels Hlength)
  | projIota
      (Hinfo : env.projections typeName info)
      (Hproj : env.IsDefEq uvars Gamma
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args))
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args))
        fieldType)
      (Hindex : args[info.nparams + index]? = some field)
      (Hfield : env.IsDefEq uvars Gamma field field fieldType) :
      UsesOnly changed Hproj → UsesOnly changed Hfield →
      UsesOnly changed (.projIota Hinfo Hproj Hindex Hfield)
  | structEta
      (Hinfo : env.projections typeName info)
      (Hparams : params.length = info.nparams)
      (Hindices : info.nindices = 0)
      (He : env.IsDefEq uvars Gamma e e (VExpr.mkApps (.const typeName levels) params))
      (Hctor : env.IsDefEq uvars Gamma
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e))
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e))
        (VExpr.mkApps (.const typeName levels) params)) :
      UsesOnly changed He → UsesOnly changed Hctor →
      UsesOnly changed (.structEta Hinfo Hparams Hindices He Hctor)
  | unitLike
      (Hinfo : env.projections typeName info)
      (Hparams : params.length = info.nparams)
      (Hindices : info.nindices = 0)
      (HnumFields : info.numFields = 0)
      (He : env.IsDefEq uvars Gamma e e (VExpr.mkApps (.const typeName levels) params))
      (He' : env.IsDefEq uvars Gamma e' e' (VExpr.mkApps (.const typeName levels) params)) :
      UsesOnly changed He → UsesOnly changed He' →
      UsesOnly changed (.unitLike Hinfo Hparams Hindices HnumFields He He')

/-- If every installed constant is outside `changed`, every derivation in
the environment carries a canonical restriction witness. -/
theorem IsDefEq.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsDefEq uvars ctx lhs rhs type)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  induction H with
  | elimDF hlookup htype hclosed hperm hright heq htyping ih =>
    exact .elimDF hlookup htype hclosed hperm hright heq htyping ih
  | elimIota hlookup hgen hmem hclosed hperm hleft hright ihLeft ihRight =>
    exact .elimIota hlookup hgen hmem hclosed hperm hleft hright ihLeft ihRight
  | bvar Hlookup => exact .bvar Hlookup
  | symm H IH => exact .symm IH
  | trans H₁ H₂ IH₁ IH₂ => exact .trans IH₁ IH₂
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | constDF Hlookup Hleft Hright Hlength Heq =>
    exact .constDF _ _ _ _ Hlookup Hleft Hright Hlength Heq
      (Hconstants Hlookup)
  | appDF Hfn Harg IHfn IHarg => exact .appDF IHfn IHarg
  | @projDF typeName info levels params index sourceMajor fieldType Gamma
      fieldLevel major indexArgs major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard IHfield IHmajor IHmajor' =>
    exact .projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard IHfield IHmajor IHmajor'
  | lamDF Htype Hbody IHtype IHbody => exact .lamDF IHtype IHbody
  | forallEDF Htype Hbody IHtype IHbody => exact .forallEDF IHtype IHbody
  | defeqDF Htype Hterm IHtype IHterm => exact .defeqDF IHtype IHterm
  | beta Hbody Harg IHbody IHarg => exact .beta IHbody IHarg
  | eta H IH => exact .eta IH
  | proofIrrel Hprop Hleft Hright IHprop IHleft IHright =>
    exact .proofIrrel IHprop IHleft IHright
  | extra Hdf Hlevels Hlength => exact .extra _ _ Hdf Hlevels Hlength
  | projIota Hinfo Hproj Hindex Hfield IHproj IHfield =>
    exact .projIota Hinfo Hproj Hindex Hfield IHproj IHfield
  | structEta Hinfo Hparams Hindices He Hctor IHe IHctor =>
    exact .structEta Hinfo Hparams Hindices He Hctor IHe IHctor
  | unitLike Hinfo Hparams Hindices HnumFields He He' IHe IHe' =>
    exact .unitLike Hinfo Hparams Hindices HnumFields He He' IHe IHe'

/-- Environment monotonicity preserves the exact constant-dependency
certificate carried by a typing derivation.  This is stronger than
reconstructing `UsesOnly` in the larger environment: the latter may already
contain newly installed constants which the original derivation never
consulted. -/
theorem IsDefEq.UsesOnly.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : env.IsDefEq uvars ctx lhs rhs type}
    (HU : H.UsesOnly changed) :
    (H.mono henv).UsesOnly changed := by
  induction HU with
  | elimDF hlookup htype hclosed hperm hright heq htyping _ ih =>
    exact .elimDF (henv.eliminators hlookup) htype hclosed hperm hright heq
      (htyping.mono henv) ih
  | elimIota hlookup hgen hmem hclosed hperm hleft hright _ _ ihLeft ihRight =>
    exact .elimIota (henv.eliminators hlookup) hgen hmem hclosed hperm
      (hleft.mono henv) (hright.mono henv) ihLeft ihRight
  | bvar Hlookup => exact .bvar Hlookup
  | symm _ IH => exact .symm IH
  | trans _ _ IH₁ IH₂ => exact .trans IH₁ IH₂
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | constDF name ci levels levels' Hlookup Hleft Hright Hlength Heq Hname =>
    exact .constDF name ci levels levels' (henv.constants Hlookup)
      Hleft Hright Hlength Heq Hname
  | projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard _ _ _ IHfield IHmajor IHmajor' =>
    exact .projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      (henv.projections Hinfo) Hlevels Huvars Hparams Hindices HfieldType
      (Hfield.mono henv) (Hmajor.mono henv) (Hmajor'.mono henv)
      Hclosed Hguard IHfield IHmajor IHmajor'
  | appDF _ _ IHfn IHarg => exact .appDF IHfn IHarg
  | lamDF _ _ IHtype IHbody => exact .lamDF IHtype IHbody
  | forallEDF _ _ IHtype IHbody => exact .forallEDF IHtype IHbody
  | defeqDF _ _ IHtype IHterm => exact .defeqDF IHtype IHterm
  | beta _ _ IHbody IHarg => exact .beta IHbody IHarg
  | eta _ IH => exact .eta IH
  | proofIrrel _ _ _ IHprop IHleft IHright =>
    exact .proofIrrel IHprop IHleft IHright
  | extra df levels Hdf Hlevels Hlength =>
    exact .extra df levels (henv.defeqs Hdf) Hlevels Hlength
  | projIota Hinfo Hproj Hindex Hfield _ _ IHproj IHfield =>
    exact .projIota (henv.projections Hinfo) (Hproj.mono henv) Hindex (Hfield.mono henv)
      IHproj IHfield
  | structEta Hinfo Hparams Hindices He Hctor _ _ IHe IHctor =>
    exact .structEta (henv.projections Hinfo) Hparams Hindices (He.mono henv) (Hctor.mono henv)
      IHe IHctor
  | unitLike Hinfo Hparams Hindices HnumFields He He' _ _ IHe IHe' =>
    exact .unitLike (henv.projections Hinfo) Hparams Hindices HnumFields (He.mono henv)
      (He'.mono henv) IHe IHe'

/-- A typehood witness avoids `changed` when its retained typing derivation
does. -/
def IsType.UsesOnly {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {type : VExpr} (changed : Name → Prop)
    (_H : env.IsType uvars ctx type) : Prop :=
  ∃ level, ∃ Htype : env.HasType uvars ctx type (.sort level),
    Htype.UsesOnly changed

theorem IsType.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsType uvars ctx type)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  rcases H with ⟨level, Htype⟩
  exact ⟨level, Htype, Htype.usesOnly_of_constants Hconstants⟩

/-- Typehood restriction evidence survives ordinary environment extension
with the original derivation's dependency set. -/
theorem IsType.UsesOnly.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : env.IsType uvars ctx type}
    (HU : H.UsesOnly changed) :
    (H.mono henv).UsesOnly changed := by
  rcases HU with ⟨level, Htype, Huses⟩
  exact ⟨level, Htype.mono henv, Huses.mono henv⟩

/-- Static environment dependencies of the side condition used by literal
translation. -/
def ContainsLits.UsesOnly (changed : Name → Prop) : Literal → Prop
  | .natVal _ => ¬ changed ``Nat
  | .strVal _ => ¬ changed ``Char.ofNat ∧ ¬ changed ``String.ofList

theorem ContainsLits.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop} {literal : Literal}
    (H : env.ContainsLits literal)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    ContainsLits.UsesOnly changed literal := by
  cases literal with
  | natVal value =>
    rcases H with ⟨ci, Hlookup⟩
    exact Hconstants Hlookup
  | strVal value =>
    rcases H with ⟨⟨charCi, Hchar⟩, stringCi, Hstring⟩
    exact ⟨Hconstants Hchar, Hconstants Hstring⟩

end VEnv

/-- A finite environment anchor for one verified projection.  Restriction
replay does not need every constant of the ambient source environment: it only
needs an earlier environment in which the same projection derivation was
already valid and whose constants all avoid `changed`.

The explicit anchor keeps the evidence stable when the translation is
subsequently weakened to a larger environment. -/
structure TrProj.RestrictionSupport
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    {structName : Name} {index : Nat} {major projected : VExpr}
    (changed : Name → Prop)
    (H : TrProj (env := env) (U := U) Gamma structName index major projected) where
  anchor : VEnv
  anchor_le : anchor ≤ env
  projection : TrProj (env := anchor) (U := U) Gamma
    structName index major projected
  constants : ∀ {name ci}, anchor.constants name = some ci →
    ¬ changed name

def TrProj.RestrictionSupport.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : TrProj (env := env) (U := U) Gamma
      structName index major projected}
    (S : H.RestrictionSupport changed) :
    (H.mono henv).RestrictionSupport changed where
  anchor := S.anchor
  anchor_le := S.anchor_le.trans henv
  projection := S.projection
  constants := S.constants

/-- The semantic premises and constant translations used by one concrete
expression translation derivation. -/
inductive TrExprS.UsesOnly {env : VEnv} {levelParams : List Name}
    (changed : Name → Prop) :
    ∀ {ctx source target}, TrExprS env levelParams ctx source target → Prop where
  | bvar (ctx : VLCtx) (index : Nat) (target type : VExpr)
      (Hlookup : ctx.find? (.inl index) = some (target, type)) :
      UsesOnly changed (.bvar Hlookup)
  | fvar (ctx : VLCtx) (fvar : FVarId) (target type : VExpr)
      (Hlookup : ctx.find? (.inr fvar) = some (target, type)) :
      UsesOnly changed (.fvar Hlookup)
  | sort (level : Level) (targetLevel : VLevel)
      (Hlevel : VLevel.ofLevel levelParams level = some targetLevel) :
      UsesOnly changed (.sort Hlevel)
  | const
      (name : Name) (ci : VConstant) (levels : List Level)
      (targets : List VLevel)
      (Hlookup : env.constants name = some ci)
      (Hlevels : levels.mapM (VLevel.ofLevel levelParams) = some targets)
      (Hlength : levels.length = ci.uvars)
      (Hname : ¬ changed name) :
      UsesOnly changed (.const Hlookup Hlevels Hlength)
  | app
      (HfnTypeUses : HfnType.UsesOnly changed)
      (HargTypeUses : HargType.UsesOnly changed)
      (HfnUses : UsesOnly changed Hfn)
      (HargUses : UsesOnly changed Harg) :
      UsesOnly changed (.app HfnType HargType Hfn Harg)
  | lam
      (HtypeUses : Htype.UsesOnly changed)
      (HdomainUses : UsesOnly changed Hdomain)
      (HbodyUses : UsesOnly changed Hbody) :
      UsesOnly changed (.lam Htype Hdomain Hbody)
  | forallE
      (HdomainTypeUses : HdomainType.UsesOnly changed)
      (HbodyTypeUses : HbodyType.UsesOnly changed)
      (HdomainUses : UsesOnly changed Hdomain)
      (HbodyUses : UsesOnly changed Hbody) :
      UsesOnly changed (.forallE HdomainType HbodyType Hdomain Hbody)
  | letE
      (HvalueTypeUses : HvalueType.UsesOnly changed)
      (HtypeUses : UsesOnly changed Htype)
      (HvalueUses : UsesOnly changed Hvalue)
      (HbodyUses : UsesOnly changed Hbody) :
      UsesOnly changed (.letE HvalueType Htype Hvalue Hbody)
  | lit
      (Hcontains : env.ContainsLits literal)
      (Hliteral : VEnv.ContainsLits.UsesOnly changed literal)
      (HconstructorUses : UsesOnly changed Hconstructor) :
      UsesOnly changed (.lit Hcontains Hconstructor)
  | mdata (Huses : UsesOnly changed H) :
      UsesOnly changed (.mdata H)
  | proj (ctx : VLCtx) (source : Expr) (target : VExpr)
      (structName : Name) (index : Nat) (projected : VExpr)
      (H : TrExprS env levelParams ctx source target)
      (Hproj : TrProj ctx.toCtx structName index target projected)
      (Huses : UsesOnly changed H)
      (HprojUses : Hproj.RestrictionSupport changed) :
      UsesOnly changed (.proj H Hproj)

theorem TrExprS.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : TrExprS env levelParams ctx source target)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  induction H with
  | bvar Hlookup => exact .bvar _ _ _ _ Hlookup
  | fvar Hlookup => exact .fvar _ _ _ _ Hlookup
  | sort Hlevel => exact .sort _ _ Hlevel
  | const Hlookup Hlevels Hlength =>
    exact .const _ _ _ _ Hlookup Hlevels Hlength (Hconstants Hlookup)
  | app HfnType HargType Hfn Harg IHfn IHarg =>
    exact .app
      (HfnType.usesOnly_of_constants Hconstants)
      (HargType.usesOnly_of_constants Hconstants) IHfn IHarg
  | lam Htype Hdomain Hbody IHdomain IHbody =>
    exact .lam (Htype.usesOnly_of_constants Hconstants) IHdomain IHbody
  | forallE HdomainType HbodyType Hdomain Hbody IHdomain IHbody =>
    exact .forallE
      (HdomainType.usesOnly_of_constants Hconstants)
      (HbodyType.usesOnly_of_constants Hconstants) IHdomain IHbody
  | letE HvalueType Htype Hvalue Hbody IHtype IHvalue IHbody =>
    exact .letE (HvalueType.usesOnly_of_constants Hconstants)
      IHtype IHvalue IHbody
  | lit Hcontains Hconstructor IH =>
    exact .lit Hcontains (Hcontains.usesOnly_of_constants Hconstants) IH
  | mdata H IH => exact .mdata IH
  | proj H Hproj IH =>
    exact .proj _ _ _ _ _ _ H Hproj IH {
      anchor := env
      anchor_le := VEnv.LE.rfl
      projection := Hproj
      constants := Hconstants }

/-- A translated expression retains its proof-relevant dependency
certificate when its derivation is weakened to a larger environment. -/
theorem TrExprS.UsesOnly.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : TrExprS env levelParams ctx source target}
    (HU : H.UsesOnly changed) :
    (H.mono henv).UsesOnly changed := by
  induction HU with
  | bvar ctx index target type Hlookup =>
    exact .bvar ctx index target type Hlookup
  | fvar ctx fvar target type Hlookup =>
    exact .fvar ctx fvar target type Hlookup
  | sort level targetLevel Hlevel => exact .sort level targetLevel Hlevel
  | const name ci levels targets Hlookup Hlevels Hlength Hname =>
    exact .const name ci levels targets (henv.constants Hlookup)
      Hlevels Hlength Hname
  | app HfnTypeUses HargTypeUses HfnUses HargUses IHfn IHarg =>
    exact .app (HfnTypeUses.mono henv) (HargTypeUses.mono henv)
      IHfn IHarg
  | lam HtypeUses HdomainUses HbodyUses IHdomain IHbody =>
    exact .lam (HtypeUses.mono henv) IHdomain IHbody
  | forallE HdomainTypeUses HbodyTypeUses HdomainUses HbodyUses
      IHdomain IHbody =>
    exact .forallE (HdomainTypeUses.mono henv)
      (HbodyTypeUses.mono henv) IHdomain IHbody
  | letE HvalueTypeUses HtypeUses HvalueUses HbodyUses
      IHtype IHvalue IHbody =>
    exact .letE (HvalueTypeUses.mono henv) IHtype IHvalue IHbody
  | lit Hcontains Hliteral HconstructorUses IH =>
    exact .lit (Hcontains.mono henv) Hliteral IH
  | mdata Huses IH => exact .mdata IH
  | proj ctx source target structName index projected H Hproj Huses
      HprojUses IH =>
    exact .proj ctx source target structName index projected
      (H.mono henv) (Hproj.mono henv) IH (HprojUses.mono henv)

end Lean4Lean
