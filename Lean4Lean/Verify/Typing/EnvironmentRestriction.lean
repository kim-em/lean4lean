import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

open Lean

namespace VEnv

/-- `src` is included in `dst` away from the constants selected by
`changed`.  Definitional equality rules are retained globally: the
derivation-scoped `UsesOnly` predicate below records precisely which
constant lookups must be transported. -/
structure LEExcept (changed : Name → Prop) (src dst : VEnv) : Prop where
  constants : ∀ {name ci}, src.constants name = some ci → ¬ changed name →
    dst.constants name = some ci
  defeqs : ∀ {df}, src.defeqs df → dst.defeqs df
  projections : ∀ {name info}, src.projections name info →
    dst.projections name info

theorem LE.toLEExcept (H : src ≤ dst) (changed : Name → Prop) :
    LEExcept changed src dst where
  constants h _ := H.constants h
  defeqs := H.defeqs
  projections := H.projections

theorem LEExcept.rfl (env : VEnv) (changed : Name → Prop) :
    LEExcept changed env env where
  constants h _ := h
  defeqs := id
  projections := id

theorem LEExcept.trans
    (Hab : LEExcept changed a b) (Hbc : LEExcept changed b c) :
    LEExcept changed a c where
  constants h hn := Hbc.constants (Hab.constants h hn) hn
  defeqs h := Hbc.defeqs (Hab.defeqs h)
  projections h := Hbc.projections (Hab.projections h)

/-- The constants on which a particular typing/definitional-equality
derivation depends.  This is proof-relevant on purpose: merely knowing that
the endpoints avoid a name cannot exclude a transitivity detour through that
constant. -/
inductive IsDefEq.UsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {ctx lhs rhs type}, env.IsDefEq uvars ctx lhs rhs type → Prop where
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

theorem IsDefEq.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.IsDefEq uvars ctx lhs rhs type)
    (HU : H.UsesOnly changed) :
    dst.IsDefEq uvars ctx lhs rhs type := by
  induction HU with
  | bvar Hlookup => exact .bvar Hlookup
  | symm _ IH => exact .symm IH
  | trans _ _ IH₁ IH₂ => exact .trans IH₁ IH₂
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | constDF name ci levels levels' Hlookup Hleft Hright Hlength Heq Hname =>
    exact .constDF (E.constants Hlookup Hname) Hleft Hright Hlength Heq
  | appDF _ _ IHf IHa => exact .appDF IHf IHa
  | projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      _ _ _ Hclosed Hguard _ _ _ IHfield IHmajor IHmajor' =>
    exact .projDF (E.projections Hinfo) Hlevels Huvars Hparams Hindices
      HfieldType IHfield IHmajor IHmajor' Hclosed Hguard
  | lamDF _ _ IHtype IHbody => exact .lamDF IHtype IHbody
  | forallEDF _ _ IHtype IHbody => exact .forallEDF IHtype IHbody
  | defeqDF _ _ IHtype IHterm => exact .defeqDF IHtype IHterm
  | beta _ _ IHbody IHarg => exact .beta IHbody IHarg
  | eta _ IH => exact .eta IH
  | proofIrrel _ _ _ IHprop IHleft IHright =>
    exact .proofIrrel IHprop IHleft IHright
  | extra df levels Hdf Hlevels Hlength =>
    exact .extra (E.defeqs Hdf) Hlevels Hlength

/-- If every installed constant is outside `changed`, every derivation in
the environment carries a canonical restriction witness. -/
theorem IsDefEq.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsDefEq uvars ctx lhs rhs type)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  induction H with
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

theorem HasType.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.HasType uvars ctx term type)
    (HU : H.UsesOnly changed) :
    dst.HasType uvars ctx term type :=
  IsDefEq.rebaseExcept E H HU

/-- Dependency evidence for an untyped definitional-equality witness. -/
def IsDefEqU.UsesOnly {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {left right : VExpr} (changed : Name → Prop)
    (_H : env.IsDefEqU uvars ctx left right) : Prop :=
  ∃ type, ∃ Hdefeq : env.IsDefEq uvars ctx left right type,
    Hdefeq.UsesOnly changed

theorem IsDefEqU.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.IsDefEqU uvars ctx left right)
    (HU : H.UsesOnly changed) :
    dst.IsDefEqU uvars ctx left right := by
  rcases HU with ⟨type, Hdefeq, Huses⟩
  exact ⟨type, Hdefeq.rebaseExcept E Huses⟩

theorem IsDefEqU.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsDefEqU uvars ctx left right)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  rcases H with ⟨type, Hdefeq⟩
  exact ⟨type, Hdefeq, Hdefeq.usesOnly_of_constants Hconstants⟩

/-- A typehood witness avoids `changed` when its retained typing derivation
does. -/
def IsType.UsesOnly {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {type : VExpr} (changed : Name → Prop)
    (_H : env.IsType uvars ctx type) : Prop :=
  ∃ level, ∃ Htype : env.HasType uvars ctx type (.sort level),
    Htype.UsesOnly changed

theorem IsType.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.IsType uvars ctx type)
    (HU : H.UsesOnly changed) :
    dst.IsType uvars ctx type := by
  rcases HU with ⟨level, Htype, Huses⟩
  exact ⟨level, Htype.rebaseExcept E Huses⟩

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

/-- Pointwise dependency evidence for a context conversion. -/
inductive IsDefEqCtx.UsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {base left right}, env.IsDefEqCtx uvars base left right → Prop where
  | zero : UsesOnly changed (.zero : env.IsDefEqCtx uvars base base base)
  | succ : UsesOnly changed Hctx → Htype.UsesOnly changed →
      UsesOnly changed (.succ Hctx Htype)

theorem IsDefEqCtx.UsesOnly.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : env.IsDefEqCtx uvars base left right}
    (HU : H.UsesOnly changed) :
    (H.mono henv).UsesOnly changed := by
  induction HU with
  | zero => exact .zero
  | succ _ _ IH => exact .succ IH (IsDefEq.UsesOnly.mono henv ‹_›)

theorem IsDefEqCtx.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.IsDefEqCtx uvars base left right)
    (HU : H.UsesOnly changed) :
    dst.IsDefEqCtx uvars base left right := by
  induction HU with
  | zero => exact .zero
  | succ HctxUses HtypeUses IH =>
    exact .succ IH (IsDefEq.rebaseExcept E _ HtypeUses)

theorem IsDefEqCtx.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsDefEqCtx uvars base left right)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  induction H with
  | zero => exact .zero
  | succ Hctx Htype IH =>
    exact .succ IH (Htype.usesOnly_of_constants Hconstants)

/-- Static environment dependencies of the side condition used by literal
translation. -/
def ContainsLits.UsesOnly (changed : Name → Prop) : Literal → Prop
  | .natVal _ => ¬ changed ``Nat
  | .strVal _ => ¬ changed ``Char.ofNat ∧ ¬ changed ``String.ofList

theorem ContainsLits.rebaseExcept
    (E : LEExcept changed src dst)
    (H : src.ContainsLits lit)
    (HU : ContainsLits.UsesOnly changed lit) :
    dst.ContainsLits lit := by
  cases lit with
  | natVal n =>
    rcases H with ⟨ci, Hci⟩
    exact ⟨ci, E.constants Hci HU⟩
  | strVal s =>
    rcases H with ⟨⟨charCi, Hchar⟩, stringCi, Hstring⟩
    exact ⟨⟨charCi, E.constants Hchar HU.1⟩,
      stringCi, E.constants Hstring HU.2⟩

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

/-- Restriction evidence for semantic local-declaration equality. -/
inductive VLocalDecl.IsDefEq.UsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {ctx left right}, VLocalDecl.IsDefEq env uvars ctx left right → Prop where
  | vlam : Htype.UsesOnly changed → UsesOnly changed (.vlam Htype)
  | vlet : Hvalue.UsesOnly changed → Htype.UsesOnly changed →
      UsesOnly changed (.vlet Hvalue Htype)

theorem VLocalDecl.IsDefEq.rebaseExcept
    (E : VEnv.LEExcept changed src dst)
    (H : VLocalDecl.IsDefEq src uvars ctx left right)
    (HU : H.UsesOnly changed) :
    VLocalDecl.IsDefEq dst uvars ctx left right := by
  induction HU with
  | vlam Huses => exact .vlam (VEnv.IsDefEq.rebaseExcept E _ Huses)
  | vlet HvalueUses HtypeUses =>
    exact .vlet (VEnv.IsDefEq.rebaseExcept E _ HvalueUses)
      (VEnv.IsDefEq.rebaseExcept E _ HtypeUses)

theorem VLocalDecl.IsDefEq.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : VLocalDecl.IsDefEq env uvars ctx left right)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  cases H with
  | vlam Htype => exact .vlam (Htype.usesOnly_of_constants Hconstants)
  | vlet Hvalue Htype =>
    exact VLocalDecl.IsDefEq.UsesOnly.vlet
      (Hvalue.usesOnly_of_constants Hconstants)
      (Htype.usesOnly_of_constants Hconstants)

/-- Pointwise restriction evidence for semantic local-context equality. -/
inductive VLCtx.IsDefEq.UsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {left right}, VLCtx.IsDefEq env uvars left right → Prop where
  | nil : UsesOnly changed (.nil : VLCtx.IsDefEq env uvars [] [])
  | cons (left right : VLCtx) (ofv : Option (FVarId × List FVarId))
      (leftDecl rightDecl : VLocalDecl)
      (Hctx : VLCtx.IsDefEq env uvars left right)
      (Hfresh : ∀ fv deps, ofv = some (fv, deps) →
      fv ∉ left.fvars ∧ deps ⊆ left.fvars) :
      (Hdecl : VLocalDecl.IsDefEq env uvars left.toCtx leftDecl rightDecl) →
      UsesOnly changed Hctx → Hdecl.UsesOnly changed →
      UsesOnly changed (.cons Hctx Hfresh Hdecl)

theorem VLCtx.IsDefEq.rebaseExcept
    (E : VEnv.LEExcept changed src dst)
    (H : VLCtx.IsDefEq src uvars left right)
    (HU : H.UsesOnly changed) :
    VLCtx.IsDefEq dst uvars left right := by
  induction HU with
  | nil => exact .nil
  | cons left right ofv leftDecl rightDecl Hctx Hfresh Hdecl
      HctxUses HdeclUses IH =>
    exact .cons IH Hfresh (VLocalDecl.IsDefEq.rebaseExcept E _ HdeclUses)

theorem VLCtx.IsDefEq.usesOnly_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : VLCtx.IsDefEq env uvars left right)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.UsesOnly changed := by
  induction H with
  | nil => exact .nil
  | cons Hctx Hfresh Hdecl IH =>
    exact .cons _ _ _ _ _ Hctx Hfresh Hdecl IH
      (Hdecl.usesOnly_of_constants Hconstants)

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

theorem TrProj.RestrictionSupport.rebaseExcept
    (E : VEnv.LEExcept changed src dst)
    {H : TrProj (env := src) (U := U) Gamma
      structName index major projected}
    (S : H.RestrictionSupport changed) :
    TrProj (env := dst) (U := U) Gamma
      structName index major projected := by
  apply S.projection.mono
  constructor
  · intro name ci hlookup
    exact E.constants (S.anchor_le.constants hlookup) (S.constants hlookup)
  · intro df hdf
    exact E.defeqs (S.anchor_le.defeqs hdf)
  · intro name info hlookup
    exact E.projections (S.anchor_le.projections hlookup)

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

theorem TrExprS.rebaseExcept
    (E : VEnv.LEExcept changed src dst)
    (H : TrExprS src levelParams ctx source target)
    (HU : H.UsesOnly changed) :
    TrExprS dst levelParams ctx source target := by
  induction HU with
  | bvar ctx index target type Hlookup => exact .bvar Hlookup
  | fvar ctx fvar target type Hlookup => exact .fvar Hlookup
  | sort level targetLevel Hlevel => exact .sort Hlevel
  | const name ci levels targets Hlookup Hlevels Hlength Hname =>
    exact .const (E.constants Hlookup Hname) Hlevels Hlength
  | app HfnTypeUses HargTypeUses HfnUses HargUses IHfn IHarg =>
    exact .app
      (VEnv.IsDefEq.rebaseExcept E _ HfnTypeUses)
      (VEnv.IsDefEq.rebaseExcept E _ HargTypeUses)
      IHfn IHarg
  | lam HtypeUses HdomainUses HbodyUses IHdomain IHbody =>
    exact .lam (VEnv.IsType.rebaseExcept E _ HtypeUses)
      IHdomain IHbody
  | forallE HdomainTypeUses HbodyTypeUses HdomainUses HbodyUses IHdomain IHbody =>
    exact .forallE
      (VEnv.IsType.rebaseExcept E _ HdomainTypeUses)
      (VEnv.IsType.rebaseExcept E _ HbodyTypeUses)
      IHdomain IHbody
  | letE HvalueTypeUses HtypeUses HvalueUses HbodyUses IHtype IHvalue IHbody =>
    exact .letE
      (VEnv.IsDefEq.rebaseExcept E _ HvalueTypeUses)
      IHtype IHvalue IHbody
  | lit Hcontains Hliteral HconstructorUses IH =>
    exact .lit (VEnv.ContainsLits.rebaseExcept E Hcontains Hliteral) IH
  | mdata Huses IH => exact .mdata IH
  | proj ctx source target structName index projected H Hproj Huses
      HprojUses IH =>
    exact .proj IH (HprojUses.rebaseExcept E)

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
