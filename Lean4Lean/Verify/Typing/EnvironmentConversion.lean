import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean

namespace VEnv

/-- A semantic environment inclusion.  A source constant may be represented
by a different declaration in the target environment, but its universe arity
is unchanged and its declared type is definitionally equal there.  This is
the appropriate relation for transporting derivations across nested
lowering/restoration, where an inductive header keeps its name but changes
its (definitionally equal) translated type. -/
structure DefEqLE (source target : VEnv) : Prop where
  constants : ∀ {name sourceConst},
    source.constants name = some sourceConst →
    ∃ targetConst,
      target.constants name = some targetConst ∧
      sourceConst.uvars = targetConst.uvars ∧
      target.IsDefEqU sourceConst.uvars [] sourceConst.type targetConst.type
  defeqs : ∀ {rule}, source.defeqs rule → target.defeqs rule

/-- A semantic environment inclusion restricted to the constants used by a
particular derivation.  Constants selected by `changed` may be absent from
the target; every other source lookup is represented there by a declaration
of the same universe arity and a definitionally equal type.

This is the semantic counterpart of `LEExcept`.  It is needed when nested
restoration changes the types of the original family headers while removing
generated auxiliary headers altogether. -/
structure DefEqLEExcept (changed : Name → Prop)
    (source target : VEnv) : Prop where
  constants : ∀ {name sourceConst},
    source.constants name = some sourceConst → ¬ changed name →
    ∃ targetConst,
      target.constants name = some targetConst ∧
      sourceConst.uvars = targetConst.uvars ∧
      target.IsDefEqU sourceConst.uvars [] sourceConst.type targetConst.type
  defeqs : ∀ {rule}, source.defeqs rule → target.defeqs rule

theorem DefEqLE.toDefEqLEExcept
    (E : DefEqLE source target) (changed : Name → Prop) :
    DefEqLEExcept changed source target where
  constants hlookup _ := E.constants hlookup
  defeqs := E.defeqs

/-- Transport a typed definitional equality through a semantic environment
inclusion.  The local context is unchanged; its target-environment
well-formedness is precisely what permits conversion at constants whose
declared types changed definitionally. -/
theorem IsDefEq.rebaseDefEqLE
    (E : DefEqLE source target)
    (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsDefEq uvars ctx left right type) :
    target.IsDefEq uvars ctx left right type := by
  induction H with
  | bvar Hlookup => exact .bvar Hlookup
  | symm _ ih => exact .symm (ih hctx)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hctx) (ih₂ hctx)
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | @constDF name sourceConst levels levels' currentCtx Hlookup Hleft Hright
      Hlength Heq =>
    rcases E.constants Hlookup with
      ⟨targetConst, HtargetLookup, Huvars, Htypes⟩
    have Hnew : target.IsDefEq uvars currentCtx (.const name levels)
        (.const name levels') (targetConst.type.instL levels) :=
      .constDF HtargetLookup Hleft Hright (Hlength.trans Huvars) Heq
    have Htypes' : target.IsDefEqU uvars currentCtx
        (sourceConst.type.instL levels) (targetConst.type.instL levels) := by
      have Hinst := Htypes.instL Hleft
      change ∃ type, target.IsDefEq uvars currentCtx
        (sourceConst.type.instL levels) (targetConst.type.instL levels) type
      rcases Hinst with ⟨type, Htype⟩
      exact ⟨type, by simpa using Htype.weak0 htarget.ordered⟩
    exact Htypes'.symm.defeqDF htarget hctx Hnew
  | appDF _ _ ihFn ihArg => exact .appDF (ihFn hctx) (ihArg hctx)
  | lamDF _ _ ihDomain ihBody =>
    have ihDomain' := ihDomain hctx
    have hdomain : target.IsType uvars _ _ :=
      ⟨_, ihDomain'.hasType.1⟩
    exact .lamDF ihDomain' (ihBody ⟨hctx, hdomain⟩)
  | forallEDF _ _ ihDomain ihBody =>
    have ihDomain' := ihDomain hctx
    have hdomain : target.IsType uvars _ _ :=
      ⟨_, ihDomain'.hasType.1⟩
    exact .forallEDF ihDomain' (ihBody ⟨hctx, hdomain⟩)
  | defeqDF _ _ ihType ihTerm =>
    exact .defeqDF (ihType hctx) (ihTerm hctx)
  | beta _ _ ihBody ihArg =>
    have ihArg' := ihArg hctx
    have hdomain : target.IsType uvars _ _ :=
      ihArg'.isType htarget hctx
    exact .beta (ihBody ⟨hctx, hdomain⟩) ihArg'
  | eta _ ih => exact .eta (ih hctx)
  | proofIrrel _ _ _ ihProp ihLeft ihRight =>
    exact .proofIrrel (ihProp hctx) (ihLeft hctx) (ihRight hctx)
  | extra Hrule Hlevels Hlength =>
    exact .extra (E.defeqs Hrule) Hlevels Hlength

/-- Transport one dependency-certified derivation through a semantic
environment inclusion which may omit exactly the selected constants. -/
theorem IsDefEq.rebaseDefEqLEExcept
    (E : DefEqLEExcept changed source target)
    (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsDefEq uvars ctx left right type)
    (HU : H.UsesOnly changed) :
    target.IsDefEq uvars ctx left right type := by
  induction HU with
  | bvar Hlookup => exact .bvar Hlookup
  | symm _ ih => exact .symm (ih hctx)
  | trans _ _ ihLeft ihRight => exact .trans (ihLeft hctx) (ihRight hctx)
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | @constDF currentCtx name sourceConst levels levels' Hlookup Hleft Hright Hlength
      Heq Hname =>
    rcases E.constants Hlookup Hname with
      ⟨targetConst, HtargetLookup, Huvars, Htypes⟩
    have Hnew : target.IsDefEq uvars currentCtx (.const name levels)
        (.const name levels') (targetConst.type.instL levels) :=
      .constDF HtargetLookup Hleft Hright (Hlength.trans Huvars) Heq
    have Htypes' : target.IsDefEqU uvars currentCtx
        (sourceConst.type.instL levels) (targetConst.type.instL levels) := by
      have Hinst := Htypes.instL Hleft
      rcases Hinst with ⟨type, Htype⟩
      exact ⟨type, by simpa using Htype.weak0 htarget.ordered⟩
    exact Htypes'.symm.defeqDF htarget hctx Hnew
  | appDF _ _ ihFn ihArg => exact .appDF (ihFn hctx) (ihArg hctx)
  | lamDF _ _ ihDomain ihBody =>
    have ihDomain' := ihDomain hctx
    have hdomain : target.IsType uvars _ _ :=
      ⟨_, ihDomain'.hasType.1⟩
    exact .lamDF ihDomain' (ihBody ⟨hctx, hdomain⟩)
  | forallEDF _ _ ihDomain ihBody =>
    have ihDomain' := ihDomain hctx
    have hdomain : target.IsType uvars _ _ :=
      ⟨_, ihDomain'.hasType.1⟩
    exact .forallEDF ihDomain' (ihBody ⟨hctx, hdomain⟩)
  | defeqDF _ _ ihType ihTerm =>
    exact .defeqDF (ihType hctx) (ihTerm hctx)
  | beta _ _ ihBody ihArg =>
    have ihArg' := ihArg hctx
    have hdomain : target.IsType uvars _ _ :=
      ihArg'.isType htarget hctx
    exact .beta (ihBody ⟨hctx, hdomain⟩) ihArg'
  | eta _ ih => exact .eta (ih hctx)
  | proofIrrel _ _ _ ihProp ihLeft ihRight =>
    exact .proofIrrel (ihProp hctx) (ihLeft hctx) (ihRight hctx)
  | extra df levels Hrule Hlevels Hlength =>
    exact .extra (E.defeqs Hrule) Hlevels Hlength

theorem HasType.rebaseDefEqLE
    (E : DefEqLE source target) (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.HasType uvars ctx term type) :
    target.HasType uvars ctx term type :=
  VEnv.IsDefEq.rebaseDefEqLE E htarget hctx H

theorem IsType.rebaseDefEqLE
    (E : DefEqLE source target) (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsType uvars ctx type) :
    target.IsType uvars ctx type :=
  H.imp fun _ Htype => VEnv.IsDefEq.rebaseDefEqLE E htarget hctx Htype

theorem IsDefEqU.rebaseDefEqLE
    (E : DefEqLE source target) (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsDefEqU uvars ctx left right) :
    target.IsDefEqU uvars ctx left right :=
  H.imp fun _ Hdefeq => VEnv.IsDefEq.rebaseDefEqLE E htarget hctx Hdefeq

theorem IsDefEqU.rebaseDefEqLEExcept
    (E : DefEqLEExcept changed source target) (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsDefEqU uvars ctx left right)
    (HU : H.UsesOnly changed) :
    target.IsDefEqU uvars ctx left right := by
  rcases HU with ⟨type, Hdefeq, Huses⟩
  exact ⟨type, Hdefeq.rebaseDefEqLEExcept E htarget hctx Huses⟩

theorem IsType.rebaseDefEqLEExcept
    (E : DefEqLEExcept changed source target) (htarget : target.WF)
    (hctx : OnCtx ctx (target.IsType uvars))
    (H : source.IsType uvars ctx type)
    (HU : H.UsesOnly changed) :
    target.IsType uvars ctx type := by
  rcases HU with ⟨level, Htype, Huses⟩
  exact ⟨level, Htype.rebaseDefEqLEExcept E htarget hctx Huses⟩

theorem IsDefEqCtx.rebaseDefEqLEExcept
    (E : DefEqLEExcept changed source target) (htarget : target.WF)
    (H : source.IsDefEqCtx uvars base left right)
    (HU : H.UsesOnly changed)
    (hbase : OnCtx base (target.IsType uvars)) :
    target.IsDefEqCtx uvars base left right := by
  induction HU with
  | zero => exact .zero
  | @succ _ _ _ _ _ Hctx Htype HctxUses HtypeUses ih =>
    have Hctx' := ih
    have hleft : OnCtx _ (target.IsType uvars) := Hctx'.isType' hbase
    exact .succ Hctx'
      (Htype.rebaseDefEqLEExcept E htarget hleft HtypeUses)

theorem ContainsLits.rebaseDefEqLE
    (E : DefEqLE source target)
    (H : source.ContainsLits literal) : target.ContainsLits literal := by
  cases literal with
  | natVal value =>
    rcases H with ⟨sourceConstant, Hsource⟩
    rcases E.constants Hsource with ⟨constant, Hlookup, _, _⟩
    exact ⟨constant, Hlookup⟩
  | strVal value =>
    rcases H.1 with ⟨sourceChar, HsourceChar⟩
    rcases H.2 with ⟨sourceString, HsourceString⟩
    rcases E.constants HsourceChar with ⟨charConstant, Hchar, _, _⟩
    rcases E.constants HsourceString with
      ⟨stringConstant, Hstring, _, _⟩
    exact ⟨⟨charConstant, Hchar⟩, ⟨stringConstant, Hstring⟩⟩

theorem ContainsLits.rebaseDefEqLEExcept
    (E : DefEqLEExcept changed source target)
    (H : source.ContainsLits literal)
    (HU : ContainsLits.UsesOnly changed literal) :
    target.ContainsLits literal := by
  cases literal with
  | natVal value =>
    rcases H with ⟨sourceConstant, Hsource⟩
    rcases E.constants Hsource HU with ⟨constant, Hlookup, _, _⟩
    exact ⟨constant, Hlookup⟩
  | strVal value =>
    rcases H.1 with ⟨sourceChar, HsourceChar⟩
    rcases H.2 with ⟨sourceString, HsourceString⟩
    rcases E.constants HsourceChar HU.1 with ⟨charConstant, Hchar, _, _⟩
    rcases E.constants HsourceString HU.2 with
      ⟨stringConstant, Hstring, _, _⟩
    exact ⟨⟨charConstant, Hchar⟩, ⟨stringConstant, Hstring⟩⟩

end VEnv

/-- Structural expression translation is stable under semantic environment
inclusion.  Constant targets are unchanged because translation records only
the name and instantiated universe levels; `DefEqLE` supplies the target
lookup and equality of universe arities. -/
theorem TrExprS.rebaseDefEqLE
    (E : VEnv.DefEqLE source target)
    (htarget : target.WF)
    (hctx : VLCtx.WF target levelParams.length ctx)
    (H : TrExprS source levelParams ctx expression translated) :
    TrExprS target levelParams ctx expression translated := by
  induction H with
  | bvar Hlookup => exact .bvar Hlookup
  | fvar Hlookup => exact .fvar Hlookup
  | sort Hlevel => exact .sort Hlevel
  | const Hlookup Hlevels Hlength =>
    rcases E.constants Hlookup with
      ⟨targetConst, HtargetLookup, Huvars, _⟩
    exact .const HtargetLookup Hlevels (Hlength.trans Huvars)
  | app HfnType HargType Hfn Harg ihFn ihArg =>
    exact .app
      (HfnType.rebaseDefEqLE E htarget hctx.toCtx)
      (HargType.rebaseDefEqLE E htarget hctx.toCtx)
      (ihFn hctx) (ihArg hctx)
  | lam Htype Hdomain Hbody ihDomain ihBody =>
    have Htype' := Htype.rebaseDefEqLE E htarget hctx.toCtx
    exact .lam Htype' (ihDomain hctx)
      (ihBody ⟨hctx, by simp, Htype'⟩)
  | forallE HdomainType HbodyType Hdomain Hbody ihDomain ihBody =>
    have HdomainType' :=
      HdomainType.rebaseDefEqLE E htarget hctx.toCtx
    have HbodyType' := HbodyType.rebaseDefEqLE E htarget
      (And.intro hctx.toCtx HdomainType')
    exact .forallE HdomainType' HbodyType' (ihDomain hctx)
      (ihBody ⟨hctx, by simp, HdomainType'⟩)
  | letE HvalueType Htype Hvalue Hbody ihType ihValue ihBody =>
    have HvalueType' :=
      HvalueType.rebaseDefEqLE E htarget hctx.toCtx
    exact .letE HvalueType' (ihType hctx) (ihValue hctx)
      (ihBody ⟨hctx, by simp, HvalueType'⟩)
  | lit Hcontains Hconstructor ih =>
    exact .lit (Hcontains.rebaseDefEqLE E) (ih hctx)
  | mdata H ih => exact .mdata (ih hctx)
  | proj H Hproj ih => exact .proj (ih hctx) Hproj

/-- Dependency-certified expression translation through a semantic
environment inclusion which may omit selected constants. -/
theorem TrExprS.rebaseDefEqLEExcept
    (E : VEnv.DefEqLEExcept changed source target)
    (htarget : target.WF)
    (hctx : VLCtx.WF target levelParams.length ctx)
    (H : TrExprS source levelParams ctx expression translated)
    (HU : H.UsesOnly changed) :
    TrExprS target levelParams ctx expression translated := by
  induction HU with
  | bvar ctx index translated type Hlookup => exact .bvar Hlookup
  | fvar ctx fvar translated type Hlookup => exact .fvar Hlookup
  | sort level targetLevel Hlevel => exact .sort Hlevel
  | const name sourceConst levels targets Hlookup Hlevels Hlength Hname =>
    rcases E.constants Hlookup Hname with
      ⟨targetConst, HtargetLookup, Huvars, _⟩
    exact .const HtargetLookup Hlevels (Hlength.trans Huvars)
  | app HfnTypeUses HargTypeUses HfnUses HargUses ihFn ihArg =>
    exact .app
      (VEnv.IsDefEq.rebaseDefEqLEExcept E htarget hctx.toCtx _ HfnTypeUses)
      (VEnv.IsDefEq.rebaseDefEqLEExcept E htarget hctx.toCtx _ HargTypeUses)
      (ihFn hctx) (ihArg hctx)
  | lam HtypeUses HdomainUses HbodyUses ihDomain ihBody =>
    have Htype' := VEnv.IsType.rebaseDefEqLEExcept E htarget hctx.toCtx _
      HtypeUses
    exact .lam Htype' (ihDomain hctx)
      (ihBody ⟨hctx, by simp, Htype'⟩)
  | forallE HdomainTypeUses HbodyTypeUses HdomainUses HbodyUses
      ihDomain ihBody =>
    have HdomainType' := VEnv.IsType.rebaseDefEqLEExcept E htarget
      hctx.toCtx _ HdomainTypeUses
    have HbodyType' := VEnv.IsType.rebaseDefEqLEExcept E htarget
      (And.intro hctx.toCtx HdomainType') _ HbodyTypeUses
    exact .forallE HdomainType' HbodyType' (ihDomain hctx)
      (ihBody ⟨hctx, by simp, HdomainType'⟩)
  | letE HvalueTypeUses HtypeUses HvalueUses HbodyUses ihType ihValue ihBody =>
    have HvalueType' := VEnv.IsDefEq.rebaseDefEqLEExcept E htarget
      hctx.toCtx _ HvalueTypeUses
    exact .letE HvalueType' (ihType hctx) (ihValue hctx)
      (ihBody ⟨hctx, by simp, HvalueType'⟩)
  | lit Hcontains Hliteral HconstructorUses ih =>
    exact .lit (VEnv.ContainsLits.rebaseDefEqLEExcept E Hcontains Hliteral)
      (ih hctx)
  | mdata Huses ih => exact .mdata (ih hctx)
  | proj ctx expression translated structName index projected H Hproj Huses ih =>
    exact .proj (ih hctx) Hproj

end Lean4Lean
