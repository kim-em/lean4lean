import Lean4Lean.Verify.Inductive.Constructor.Replay

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace mkRecInfos.loopCtorArgs.loop

/-- Typed second-pass refinement of the genuine constructor-field suffix.
Unlike `recursiveDomains`, this theorem remains applicable after mutual
major/motive frames have rebased the semantic universe list. -/
theorem recursiveDomainsRecursor {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    {decl : VInductDecl} {depth : Nat} {typeTarget : VExpr}
    {recLparams : List Name}
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (R : RecursorContextWF c recLparams)
    {fields : List (RecursorRecursiveDomainAt
      R.venv decl recLparams.length)}
    {args : List VExpr}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hparams : stats.params.size ≤ i)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htype : TrExprS R.venv recLparams R.mlctx.vlctx t typeTarget)
    (hfields : RecursorFieldSelectionsAt R.venv decl recLparams.length
      bu u fields)
    (hargs : List.Forall₂
      (TrExprS R.venv recLparams R.mlctx.vlctx) u.toList args)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {t' : Expr} {typeTarget' : VExpr} {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomainAt
        Rcurrent.venv decl recLparams.length)} {args' : List VExpr},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        t' typeTarget' →
      RecursorFieldSelectionsAt Rcurrent.venv decl recLparams.length
        bu' u' fields' →
      List.Forall₂
        (TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' current).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
      t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u depth typeTarget fields args with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      have hparam : stats.params[i]? = none := by
        apply Array.getElem?_eq_none
        omega
      rw [hparam]
      have htypeTr := htype.trExpr R.checking.tr.wf R.mlctx_wf.tr.wf
      rcases TrExpr.forallE_source htypeTr with
        ⟨sourceDom, sourceBody, hdom, hbody, hdomType, _, _⟩
      rcases hconsume c recLparams R hdom hdomType with
        ⟨consumedDom, Hdom⟩
      rcases Hdom.body R hbody with
        ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
      refine withLocalDecl.recursorWF (name := name) (bi := bi) (Q := Q)
        R Hdom.consumed Hdom.isType ?_
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotationsVerified bi }
      let R' : RecursorContextWF c' recLparams :=
        R.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
      have Hstats' := Hstats.withFVar R'.checking.tr.wf
        R'.mlctx_wf.tr.wf
      have hctx' : checkPositivityStep.VLCtx.NoIndConsts
          (decl.types.map (·.name)) R'.mlctx.vlctx := by
        apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
        rfl
      let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have hdomWeak : TrExprS R'.venv recLparams R'.mlctx.vlctx dom
          (sourceDom.liftN 1 0) := by
        apply Hdom.source.weakFV R.checking.tr.wf.ordered W
        exact R'.mlctx_wf.tr.wf
      have hargsWeak : List.Forall₂
          (TrExprS R'.venv recLparams R'.mlctx.vlctx) u.toList
          (args.map fun arg => arg.liftN 1 0) := by
        apply checkPositivityStep.forall₂_map_right hargs
        intro source arg harg
        exact harg.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
      have harg : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        exact TrExprS.fvar (A := consumedDom.lift) (by
          change VLCtx.find? ((some (⟨c.ngen.curr⟩,
            dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type])
      have hopened := R.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbodyConsumed
      have Hclass := isRecArg.refinesRecursor R' Hstats' hconsume
        hlit hctx'
        (hdomWeak.trExpr R'.checking.tr.wf R'.mlctx_wf.tr.wf)
      refine Hclass.bind fun selected hselected => ?_
      cases selected with
      | none =>
        exact ih R' Hstats' (by omega) hlit hctx' hopened
          (.nonrecursive hfields) hargsWeak
      | some target =>
        rcases hselected target rfl with ⟨howner, hrecursive⟩
        let cert : RecursorRecursiveDomainAt
            R'.venv decl recLparams.length := {
          fieldIndex := bu.size
          ownerIdx := target
          owner_lt := howner
          ctx := R'.mlctx.vlctx.toCtx
          depth := depth + 1
          domain := sourceDom.liftN 1 0
          recursive := hrecursive }
        have hargs' : List.Forall₂
            (TrExprS R'.venv recLparams R'.mlctx.vlctx)
            (u.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((args.map fun arg => arg.liftN 1 0) ++ [.bvar 0]) := by
          simpa using checkPositivityStep.forall₂_append
            hargsWeak (.cons harg .nil)
        exact ih R' Hstats' (by omega) hlit hctx' hopened
          (.recursive hfields (cert := cert) rfl) hargs'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      exact Hk R htype hfields hargs

end mkRecInfos.loopCtorArgs.loop

/-- Public recursor-universe constructor-field refinement, composing the
already certified common-parameter prefix with the genuine-field traversal. -/
theorem mkRecInfos.loopCtorArgs.recursiveDomainsRecursor {alpha : Type}
    (stats : AddInductive.InductiveStats) (t tail : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    {decl : VInductDecl} {depth : Nat} {tailTarget : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : RecursorParamPrefix stats 0 t tail)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {t' : Expr} {typeTarget' : VExpr} {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomainAt
        Rcurrent.venv decl recLparams.length)} {args' : List VExpr},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        t' typeTarget' →
      RecursorFieldSelectionsAt Rcurrent.venv decl recLparams.length
        bu' u' fields' →
      List.Forall₂
        (TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' current).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  let inputContext := c
  unfold AddInductive.mkRecInfos.loopCtorArgs
  have hread : ((read : AddInductive.M AddInductive.Context)
      inputContext).WF (fun c' => c' = inputContext) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  have Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size #[] #[] fuel inputContext).WF Q := by
    intro fuel
    exact mkRecInfos.loopCtorArgs.loop.recursiveDomainsRecursor stats k R
      Hstats (Nat.le_refl _) hconsume hlit hctx htail .nil .nil Hk
  exact mkRecInfos.loopCtorArgs.loop.followsParamPrefix stats k hprefix Htail
    inputContext.fuel.inductiveFuel

/-- A domain already checked under the inductive declaration universes can be
used unchanged as concrete syntax under the recursor universes.  Its abstract
target is shifted only in the fresh large-elimination case. -/
theorem ContextWF.ConsumedDomain.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    {dom : Expr} {sourceTarget consumedTarget : VExpr}
    (Hdom : Hc.ConsumedDomain dom sourceTarget consumedTarget)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    ∃ sourceTarget' consumedTarget',
      R.ConsumedDomain dom sourceTarget' consumedTarget' := by
  dsimp only
  cases elimLevel with
  | zero =>
    change ∃ sourceTarget' consumedTarget',
      (Hc.toRecursorContextWF).ConsumedDomain
        dom sourceTarget' consumedTarget'
    exact ⟨sourceTarget, consumedTarget, {
      source := Hdom.source
      consumed := Hdom.consumed
      isType := Hdom.isType
      source_defeq := Hdom.source_defeq }⟩
  | param name =>
    change ∃ sourceTarget' consumedTarget',
      (Hc.prependRecursorLevelParam Helim).ConsumedDomain
        dom sourceTarget' consumedTarget'
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (name :: c.lparams).length := by
      simpa [shift] using VLevel.prependShift_wf (n := c.lparams.length)
    refine ⟨sourceTarget.instL shift, consumedTarget.instL shift, {
      source := ?_
      consumed := ?_
      isType := ?_
      source_defeq := ?_ }⟩
    · simpa only [ContextWF.prependRecursorLevelParam,
        TypeChecker.MLCtx.prependLevelParam_vlctx, shift] using
        Hdom.source.prependLevelParam
          Hc.checking.tr.wf Hc.mlctx_wf.tr.wf Helim
    · simpa only [ContextWF.prependRecursorLevelParam,
        TypeChecker.MLCtx.prependLevelParam_vlctx, shift] using
        Hdom.consumed.prependLevelParam
          Hc.checking.tr.wf Hc.mlctx_wf.tr.wf Helim
    · rcases Hdom.isType with ⟨level, htype⟩
      exact ⟨level.inst shift, by
        simpa only [ContextWF.prependRecursorLevelParam,
          TypeChecker.MLCtx.prependLevelParam_vlctx, VLCtx.instL_toCtx,
          List.length_cons, VExpr.instL, shift] using
          htype.instL hshift⟩
    · rcases Hdom.source_defeq with ⟨level, heq⟩
      exact ⟨level.inst shift, by
        simpa only [ContextWF.prependRecursorLevelParam,
          TypeChecker.MLCtx.prependLevelParam_vlctx, VLCtx.instL_toCtx,
          List.length_cons, VExpr.instL, shift] using
          heq.instL hshift⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Semantic certificate for the two locals installed after one family's
indices have been replayed.  The starting context is already interpreted
under the recursor universe list, so the same certificate applies to every
member of a mutual block, including those reached after earlier frames. -/
structure RecursorMotiveFrameWF
    {c : AddInductive.Context} {recLparams : List Name}
    (Rindices : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (familyIdx : Nat)
    (indices : Array Expr) (elimLevel : Level) where
  familyTarget : VExpr
  familyTr :
    TrExprS Rindices.venv recLparams Rindices.mlctx.vlctx
      (mkAppN stats.indConsts[familyIdx]! stats.params) familyTarget
  familyIndexTargets : List VExpr
  familyIndicesTr : List.Forall₂
    (TrExprS Rindices.venv recLparams Rindices.mlctx.vlctx)
    indices.toList familyIndexTargets
  majorSourceTarget : VExpr
  majorSourceEq : majorSourceTarget =
    VExpr.mkApps familyTarget familyIndexTargets
  majorTarget : VExpr
  majorSourceDefEq :
    Rindices.venv.IsDefEqU recLparams.length Rindices.mlctx.vlctx.toCtx
      majorSourceTarget majorTarget
  majorTr :
    let majorTy :=
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
    TrExprS Rindices.venv
      recLparams
      Rindices.mlctx.vlctx majorTy majorTarget
  majorType :
    Rindices.venv.IsType
      recLparams.length
      Rindices.mlctx.vlctx.toCtx majorTarget
  indexDomains : List VExpr
  indexDomains_length : indexDomains.length = indices.size
  indexDomains_eq : indexDomains =
    (Rindices.mlctx.vlctx.toCtx.take indices.size).reverse
  resultLevel : VLevel
  resultLevelWF : resultLevel.WF recLparams.length
  motiveTarget : VExpr
  motiveTarget_eq :
    motiveTarget =
      ((VExpr.wrapForalls indexDomains
        (.forallE majorTarget (.sort resultLevel))).liftN
          indices.size 0).liftN 1 0
  /-- Exact generated motive telescope before it is weakened back through
  the freshly opened indices and major.  Retaining this checked form makes
  the production motive comparable with the independently replayed
  canonical telescope in their common outer context. -/
  motiveClosed :
    let majorTy :=
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      majorTr majorType
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    ∃ hsize : indices.size ≤ Rindices.mlctx.length,
      ∃ closedTarget,
        TrExprS Rindices.venv recLparams
          (Rindices.mlctx.dropN indices.size hsize).vlctx
          motiveTy.consumeTypeAnnotationsVerified closedTarget ∧
        Rindices.venv.IsType recLparams.length
          (Rindices.mlctx.dropN indices.size hsize).vlctx.toCtx closedTarget ∧
        closedTarget = VExpr.wrapForalls indexDomains
          (.forallE majorTarget (.sort resultLevel))
  motiveTr :
    let majorTy :=
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      majorTr majorType
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    TrExprS Rmajor.venv
      recLparams
      Rmajor.mlctx.vlctx motiveTy.consumeTypeAnnotationsVerified motiveTarget
  motiveType :
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      majorTr majorType
    Rmajor.venv.IsType
      recLparams.length
      Rmajor.mlctx.vlctx.toCtx motiveTarget
  motiveSourceEq :
    let majorTy :=
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    motiveTy.consumeTypeAnnotationsVerified = motiveTy

/-- The independent canonical family/motive telescope attached to one
completed executable frame.  Its motive type is still compared with the
annotation-consumed production target in a separate step; this package
records the exact declarative telescope and types its family endpoint. -/
structure RecursorMotiveCanonicalFrameWF
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (familyIdx : Nat)
    (indices : Array Expr) (elimLevel : Level)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    Type where
  familyType : VExpr
  motiveType : VExpr
  familyTyping : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    Hframe.familyTarget familyType
  telescope : RecursorMotiveTelescope Hframe.resultLevel indices.size
    Hframe.familyTarget familyType motiveType

/-- `Expr.inferImplicit` changes only concrete binder annotations, which are
erased by the abstract expression translation.  In particular the abstract
recursor type proved before this production post-processing step remains the
translation of the type installed in the environment. -/
theorem TrExprS.inferImplicit
    (H : TrExprS env Us Δ e e') (numParams : Nat) (considerRange : Bool) :
    TrExprS env Us Δ (e.inferImplicit numParams considerRange) e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        simp only [Expr.inferImplicit]
        exact .forallE hdomType hbodyType hdom
          (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- Conversely, the annotation-only `inferImplicit` pass can be erased from
the concrete side of a translation derivation. -/
theorem TrExprS.of_inferImplicit
    (H : TrExprS env Us Δ (e.inferImplicit numParams considerRange) e') :
    TrExprS env Us Δ e e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        exact .forallE hdomType hbodyType hdom (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- A concrete expression consists of exactly `arity` leading forall binders
and the indicated residual body.  This deliberately forgets binder domains:
`RecursorShape` records them existentially but constrains their cardinality. -/
inductive Expr.ForallTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : ForallTelescope body 0 body
  | cons : ForallTelescope body arity result →
      ForallTelescope (.forallE name dom body bi) (arity + 1) result

theorem Expr.ForallTelescope.trans
    (Houter : Expr.ForallTelescope outer outerArity middle)
    (Hinner : Expr.ForallTelescope middle innerArity result) :
    Expr.ForallTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.ForallTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

/-- Structural translation of a concrete forall telescope exposes exactly
the same number of abstract forall domains.  Binder types may translate to
different expressions, so they are returned existentially in source order. -/
theorem Expr.ForallTelescope.translatedTakeForalls
    (Htelescope : Expr.ForallTelescope input arity residual)
    (Htranslation : TrExprS env Us Δ input output) :
    ∃ domains translatedResidual,
      output.takeForalls arity = some (domains, translatedResidual) ∧
      domains.length = arity := by
  induction Htelescope generalizing Δ output with
  | nil => exact ⟨[], output, rfl, rfl⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Htranslation with
    | forallE hdomType hbodyType hdom hbody =>
      rename_i ty' body'
      rcases ih hbody with ⟨domains, translatedResidual, htake, hlength⟩
      exact ⟨ty' :: domains, translatedResidual, by
        simp [VExpr.takeForalls, htake], by simp [hlength]⟩

/-- Abstracting one retained free variable preserves telescope arity; the
residual body is abstracted below all telescope binders. -/
theorem Expr.ForallTelescope.abstract1
    (H : Expr.ForallTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Simultaneous abstraction is the iterated form of `abstract1` and likewise
preserves the exact leading telescope. -/
theorem Expr.ForallTelescope.abstractList
    (H : Expr.ForallTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Instantiating below a forall telescope preserves its arity and performs
the same instantiation below all retained binders in the residual. -/
theorem Expr.ForallTelescope.instantiate1'
    (H : Expr.ForallTelescope outer arity result)
    (arg : Expr) (k : Nat := 0) :
    Expr.ForallTelescope (outer.instantiate1' arg k) arity
      (result.instantiate1' arg (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.instantiate1']
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Inserting loose bound variables below a forall telescope preserves its
arity; the insertion cutoff advances once beneath each retained binder. -/
theorem Expr.ForallTelescope.liftLooseBVars'
    (H : Expr.ForallTelescope outer arity result)
    (k amount : Nat) :
    Expr.ForallTelescope (outer.liftLooseBVars' k amount) arity
      (result.liftLooseBVars' (k + arity) amount) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.liftLooseBVars']
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.ForallTelescope.isForall_of_pos
    (H : Expr.ForallTelescope outer arity residual) (hpos : 0 < arity) :
    outer.isForall = true := by
  cases H with
  | nil => simp at hpos
  | cons => rfl

/-- For a fixed source and exact arity, the residual of a forall telescope
is unique.  Maximality is needed only when comparing different arities. -/
theorem Expr.ForallTelescope.residual_eq
    (Hleft : Expr.ForallTelescope source arity leftResidual)
    (Hright : Expr.ForallTelescope source arity rightResidual) :
    leftResidual = rightResidual := by
  induction Hleft with
  | nil => cases Hright; rfl
  | cons Htail ih =>
    cases Hright with
    | cons HrightTail => exact ih HrightTail

/-- A maximal forall decomposition is unique.  This is deliberately stated
with a non-forall condition on both residuals: without maximality, the same
source admits every shorter prefix as another `ForallTelescope`. -/
theorem Expr.ForallTelescope.eq_of_residual_not_forall
    (Hleft : Expr.ForallTelescope source leftArity leftResidual)
    (Hright : Expr.ForallTelescope source rightArity rightResidual)
    (hleft : leftResidual.isForall = false)
    (hright : rightResidual.isForall = false) :
    leftArity = rightArity ∧ leftResidual = rightResidual := by
  induction Hleft generalizing rightArity rightResidual with
  | nil =>
    cases Hright with
    | nil => exact ⟨rfl, rfl⟩
    | cons Htail => simp [Expr.isForall] at hleft
  | @cons body leftArity leftResidual name dom bi Hleft ih =>
    cases Hright with
    | nil => simp [Expr.isForall] at hright
    | cons Hright =>
      rcases ih Hright hleft hright with ⟨harity, hresidual⟩
      exact ⟨by omega, hresidual⟩

/-- Substitution by a free variable cannot manufacture a leading forall.
This reflection lemma is the converse shape fact needed to recover the
original source telescope from lowering's successively opened one. -/
theorem Expr.ForallTelescope.reflect_instantiate1'_fvar
    (H : Expr.ForallTelescope
      (e.instantiate1' (.fvar fv) k) arity residual) :
    ∃ sourceResidual, Expr.ForallTelescope e arity sourceResidual := by
  induction arity generalizing e residual k with
  | zero => exact ⟨e, .nil _⟩
  | succ arity ih =>
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.instantiate1'] at H
      cases H with
      | cons Htail =>
        rcases ih Htail with ⟨sourceResidual, Hsource⟩
        exact ⟨sourceResidual, .cons Hsource⟩
    | bvar i =>
      by_cases hlt : i < k
      · simp only [Expr.instantiate1', hlt, ↓reduceIte] at H
        exact Bool.noConfusion (H.isForall_of_pos (by omega))
      · by_cases heq : i = k
        · subst i
          simp only [Expr.instantiate1', Nat.lt_irrefl, ↓reduceIte] at H
          rw [Expr.liftLooseBVars_eq_self
            (by simp [Expr.looseBVarRange'])] at H
          exact Bool.noConfusion (H.isForall_of_pos (by omega))
        · simp only [Expr.instantiate1', hlt, heq, ↓reduceIte] at H
          exact Bool.noConfusion (H.isForall_of_pos (by omega))
    | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      simp only [Expr.instantiate1'] at H
      have hfor := H.isForall_of_pos (by omega)
      exact Bool.noConfusion hfor

theorem Expr.abstractList_fvar_of_not_mem
    (hmem : fv ∉ fvs) :
    (Expr.fvar fv).abstractList fvs k = .fvar fv := by
  induction fvs generalizing k with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mem_cons, not_or] at hmem
    have hne : head ≠ fv := Ne.symm hmem.1
    simp [Expr.abstractList, Expr.abstract1, hne, ih hmem.2]

@[simp] theorem Expr.abstractList_const
    (name : Name) (levels : List Level) (fvs : List FVarId) (k : Nat) :
    (Expr.const name levels).abstractList fvs k = .const name levels := by
  induction fvs with
  | nil => rfl
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

theorem Expr.abstractList_bvar_ge (fvs : List FVarId) (k n : Nat) :
    (Expr.bvar (k + n)).abstractList fvs k =
      .bvar (k + n + fvs.length) := by
  induction fvs generalizing n with
  | nil => simp
  | cons head tail ih =>
    simp only [Expr.abstractList]
    rw [show (Expr.bvar (k + n)).abstract1 head k = .bvar (k + n + 1) by
      simp [Expr.abstract1]]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

theorem Expr.abstractList_bvar_lt (fvs : List FVarId)
    (h : n < k) :
    (Expr.bvar n).abstractList fvs k = .bvar n := by
  induction fvs with
  | nil => simp
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, h, ih]

@[simp] theorem Expr.abstractList_app :
    (Expr.app fn arg).abstractList fvs k =
      .app (fn.abstractList fvs k) (arg.abstractList fvs k) := by
  induction fvs generalizing fn arg with
  | nil => simp
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

@[simp] theorem Expr.abstractList_lam :
    (Expr.lam name dom body bi).abstractList fvars k =
      .lam name (dom.abstractList fvars k)
        (body.abstractList fvars (k + 1)) bi := by
  induction fvars generalizing dom body k with
  | nil => simp
  | cons fv fvars ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

@[simp] theorem Expr.abstractList_forallE :
    (Expr.forallE name dom body bi).abstractList fvars k =
      .forallE name (dom.abstractList fvars k)
        (body.abstractList fvars (k + 1)) bi := by
  induction fvars generalizing dom body k with
  | nil => simp
  | cons fv fvars ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

@[simp] theorem Expr.abstractList_letE :
    (Expr.letE name ty value body nondep).abstractList fvars k =
      .letE name (ty.abstractList fvars k)
        (value.abstractList fvars k)
        (body.abstractList fvars (k + 1)) nondep := by
  induction fvars generalizing ty value body k with
  | nil => simp
  | cons fv fvars ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

@[simp] theorem Expr.abstractList_mdata :
    (Expr.mdata md body).abstractList fvars k =
      .mdata md (body.abstractList fvars k) := by
  induction fvars generalizing body k with
  | nil => simp
  | cons fv fvars ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

@[simp] theorem Expr.abstractList_proj :
    (Expr.proj name idx body).abstractList fvars k =
      .proj name idx (body.abstractList fvars k) := by
  induction fvars generalizing body k with
  | nil => simp
  | cons fv fvars ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

theorem Expr.abstractList_mkAppN :
    (mkAppN fn args).abstractList fvs k =
      mkAppN (fn.abstractList fvs k)
        (args.map fun arg => arg.abstractList fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

theorem Expr.liftLooseBVars'_mkAppN :
    (mkAppN fn args).liftLooseBVars' start amount =
      mkAppN (fn.liftLooseBVars' start amount)
        (args.map fun arg => arg.liftLooseBVars' start amount) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Expr.liftLooseBVars']

theorem Expr.mkAppRange_to_end
    (fn : Expr) (args : Array Expr) (start : Nat)
    (hstart : start ≤ args.size) :
    mkAppRange fn start args.size args =
      Expr.mkAppList fn (args.toList.drop start) := by
  apply Expr.mkAppRange_eq
      (l₁ := args.toList.take start) (l₂ := args.toList.drop start)
      (l₃ := [])
  · simp
  · simp [List.length_take, Nat.min_eq_left hstart]
  · simp

theorem Expr.mkAppRange_from_zero
    (fn : Expr) (args : Array Expr) (stop : Nat)
    (hstop : stop ≤ args.size) :
    mkAppRange fn 0 stop args =
      Expr.mkAppList fn (args.toList.take stop) := by
  apply Expr.mkAppRange_eq
      (l₁ := []) (l₂ := args.toList.take stop)
      (l₃ := args.toList.drop stop)
  · simp
  · rfl
  · simp [List.length_take, Nat.min_eq_left hstop]

theorem Expr.getAppFn_mkAppList (fn : Expr) (args : List Expr) :
    (Expr.mkAppList fn args).getAppFn = fn.getAppFn := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.mkAppList]
    simpa [Expr.getAppFn] using ih (.app fn arg)

theorem Expr.getAppArgsList_mkAppList (fn : Expr) (args : List Expr) :
    (Expr.mkAppList fn args).getAppArgsList =
      fn.getAppArgsList ++ args := by
  induction args generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [Expr.mkAppList]
    rw [ih]
    simp [Expr.getAppArgsList_app, List.append_assoc]

theorem Expr.getAppFn_mkAppList_const
    (name : Name) (levels : List Level) (args : List Expr) :
    (Expr.mkAppList (.const name levels) args).getAppFn =
      .const name levels := by
  simpa [Expr.getAppFn] using
    Expr.getAppFn_mkAppList (.const name levels) args

theorem Expr.getAppArgsList_mkAppList_const
    (name : Name) (levels : List Level) (args : List Expr) :
    (Expr.mkAppList (.const name levels) args).getAppArgsList = args := by
  rw [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_const]
  simp

theorem Expr.abstractList_fvar_getElem
    (hnd : fvs.Nodup) (i : Nat) (hi : i < fvs.length) :
    (Expr.fvar fvs[i]).abstractList fvs k =
      .bvar (k + (fvs.length - 1 - i)) := by
  induction fvs generalizing i k with
  | nil => simp at hi
  | cons head tail ih =>
    simp only [List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Expr.abstractList]
      rw [show (Expr.fvar head).abstract1 head k = .bvar k by
        simp [Expr.abstract1]]
      simpa using Expr.abstractList_bvar_ge tail k 0
    | succ i =>
      have hiTail : i < tail.length := by simpa using hi
      have hne : tail[i] ≠ head := by
        intro heq
        apply hnd.1
        simpa [heq] using List.getElem_mem hiTail
      simp only [List.getElem_cons_succ, Expr.abstractList]
      rw [show (Expr.fvar tail[i]).abstract1 head k = .fvar tail[i] by
        simp [Expr.abstract1, Ne.symm hne]]
      rw [ih hnd.2 i hiTail (k := k)]
      congr 1
      simp only [List.length_cons]
      omega

/-- Abstraction at an inner cutoff preserves every already-valid outer bound
variable and adds one new valid slot. -/
theorem Closed.abstract1_at
    (H : Closed e (depth + outer)) :
    Closed (Expr.abstract1 fv e depth) (depth + outer + 1) := by
  induction e generalizing depth outer <;>
    simp_all [Closed, Expr.abstract1, Nat.add_assoc]
  case bvar i =>
    split <;> omega
  case fvar =>
    split <;> simp [Closed]
  case lam body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  case forallE body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  case letE body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody

/-- List abstraction at an inner cutoff preserves an existing outer de
Bruijn prefix and extends it by exactly the number of selected variables. -/
theorem Closed.abstractList_at
    (H : Closed e (depth + outer)) :
    Closed (e.abstractList fvars depth)
      (depth + outer + fvars.length) := by
  induction fvars generalizing e outer with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList, List.length_cons]
    have Hhead := Closed.abstract1_at (fv := fv) H
    have Htail := ih (outer := outer + 1) Hhead
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Htail

/-- Abstracting free variables below `extra` freshly introduced binders is
the same operation as abstracting at the original depth and weakening the
result.  Closedness rules out pre-existing loose variables at the insertion
cut, so the two de Bruijn presentations agree exactly. -/
theorem Expr.abstractList_add_eq_liftLooseBVars
    (Hclosed : Closed e depth) (Hnodup : fvars.Nodup) :
    e.abstractList fvars (depth + extra) =
      (e.abstractList fvars depth).liftLooseBVars' depth extra := by
  induction e generalizing depth extra with
  | bvar i =>
    simp only [Closed] at Hclosed
    rw [Expr.abstractList_bvar_lt fvars (by omega),
      Expr.abstractList_bvar_lt fvars Hclosed]
    simp [Expr.liftLooseBVars', Hclosed]
  | fvar fv =>
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    rcases Hclosed with ⟨Hfn, Harg⟩
    simp [Expr.liftLooseBVars', ihFn Hfn, ihArg Harg]
  | lam name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_lam, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | forallE name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_forallE, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    simp only [Expr.abstractList_letE, Expr.liftLooseBVars']
    rw [ihTy Hty, ihValue Hvalue]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed

/-- Weakening below an abstraction cutoff commutes with closing free
variables, provided the abstraction is moved past the inserted binders. -/
theorem Expr.liftLooseBVars'_abstractList_add
    (e : Expr) (fvars : List FVarId) (start cutoff amount : Nat)
    (Hcutoff : start ≤ cutoff) (Hnodup : fvars.Nodup) :
    (e.liftLooseBVars' start amount).abstractList fvars (cutoff + amount) =
      (e.abstractList fvars cutoff).liftLooseBVars' start amount := by
  induction e generalizing start cutoff amount with
  | bvar i =>
    by_cases hstart : i < start
    · rw [show (Expr.bvar i).liftLooseBVars' start amount = .bvar i by
          simp [Expr.liftLooseBVars', hstart],
        Expr.abstractList_bvar_lt fvars (by omega),
        Expr.abstractList_bvar_lt fvars (by omega)]
      simp [Expr.liftLooseBVars', hstart]
    · by_cases hcut : i < cutoff
      · rw [show (Expr.bvar i).liftLooseBVars' start amount =
              .bvar (i + amount) by
            simp [Expr.liftLooseBVars', hstart],
          Expr.abstractList_bvar_lt fvars (by omega),
          Expr.abstractList_bvar_lt fvars hcut]
        simp [Expr.liftLooseBVars', hstart]
      · obtain ⟨n, rfl⟩ : ∃ n, i = cutoff + n :=
          ⟨i - cutoff, by omega⟩
        have hge : ¬ cutoff + n < start := by omega
        have hgeAbstract :
            ¬ cutoff + n + fvars.length < start := by omega
        rw [show (Expr.bvar (cutoff + n)).liftLooseBVars' start amount =
              .bvar ((cutoff + amount) + n) by
            simp [Expr.liftLooseBVars', hge]; omega,
          Expr.abstractList_bvar_ge,
          Expr.abstractList_bvar_ge]
        simp [Expr.liftLooseBVars', hgeAbstract]
        omega
  | fvar fv =>
    simp only [Expr.liftLooseBVars']
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      congr 1
      omega
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    simp [Expr.liftLooseBVars', ihFn start cutoff amount Hcutoff,
      ihArg start cutoff amount Hcutoff]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_lam]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_forallE]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_letE]
    rw [ihTy start cutoff amount Hcutoff,
      ihValue start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff

/-- If closing a list of free variables yields a term scoped by exactly the
new de Bruijn prefix, the original term had no loose variables at the
abstraction cut. -/
theorem Expr.closed_of_abstractList
    (Hclosed : Closed (e.abstractList fvars depth)
      (depth + fvars.length)) :
    Closed e depth := by
  induction e generalizing depth with
  | bvar i =>
    by_cases hi : i < depth
    · exact hi
    · have heq : i = depth + (i - depth) := by omega
      rw [heq, Expr.abstractList_bvar_ge] at Hclosed
      simpa only [Closed] using (show i < depth from by
        simp only [Closed] at Hclosed
        omega)
  | fvar => trivial
  | sort => trivial
  | const => trivial
  | mvar id =>
    have heq : (Expr.mvar id).abstractList fvars depth =
        .mvar id := by
      clear Hclosed
      induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
    rw [heq] at Hclosed
    exact Hclosed
  | lit => trivial
  | app fn arg ihFn ihArg =>
    rw [Expr.abstractList_app] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hfn, Harg⟩
    exact ⟨ihFn Hfn, ihArg Harg⟩
  | lam name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_lam] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | forallE name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_forallE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rw [Expr.abstractList_letE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    refine ⟨ihTy Hty, ihValue Hvalue, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | mdata md body ih =>
    rw [Expr.abstractList_mdata] at Hclosed
    simpa only [Closed] using ih Hclosed
  | proj name idx body ih =>
    rw [Expr.abstractList_proj] at Hclosed
    simpa only [Closed] using ih Hclosed

theorem Expr.abstractList_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractList fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i (by simpa using hiLeft)

/-- Closing a selected free variable and reopening with an equally sized
free-variable array returns the reopening variable at the same position. -/
theorem Expr.abstract_instantiateRev_fvar_getElem
    (fvars restoreFvars : List FVarId)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (i : Nat) (hi : i < fvars.length) :
    ((Expr.fvar fvars[i]).abstract
        (fvars.map Expr.fvar).toArray).instantiateRev
        (restoreFvars.map Expr.fvar).toArray =
      .fvar restoreFvars[i] := by
  rw [Expr.abstract_eq, Expr.abstractList_fvar_getElem hnd i hi,
    Expr.instantiateRev_eq, Expr.instantiate_eq]
  simp only [Array.toList_reverse]
  rw [Expr.instantiateList_reverse]
  rw [← hsize]
  exact Expr.instantiateRevList_bvar_fvars_getElem restoreFvars i 0
    (by omega)

/-- Close an expression over one free-variable parameter array and reopen it
with another. -/
def Expr.reopenParams (e : Expr) (params restoreAs : Array Expr) : Expr :=
  (e.abstract params).instantiateRev restoreAs

/-- Transparent list model of parameter reopening at an arbitrary de Bruijn
depth. -/
def Expr.reopenFVarsAt (e : Expr) (fvars restoreFvars : List FVarId)
    (k : Nat := 0) : Expr :=
  (e.abstractList fvars k).instantiateRevList
    (restoreFvars.map Expr.fvar) k

theorem _root_.Lean4Lean.FVarsIn.abstractList_eq_self
    (H : e.FVarsIn fun fv => fv ∉ fvars) (Hclosed : Closed e k) :
    e.abstractList fvars k = e := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    simp only [List.mem_cons, not_or] at H
    simp only [Expr.abstractList]
    rw [(H.mono fun other hother => hother.1).abstract_eq_self Hclosed]
    exact ih (H.mono fun other hother => hother.2)

theorem Expr.reopenFVarsAt_eq_self
    (Hfvars : e.FVarsIn fun fv => fv ∉ fvars)
    (Hclosed : Closed e k) (Hrange : e.looseBVarRange' ≤ k) :
    Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  unfold Expr.reopenFVarsAt
  rw [Hfvars.abstractList_eq_self Hclosed]
  exact Expr.instantiateRevList'_eq_self Hrange

theorem Expr.reopenFVarsAt_eq_self_of_abstract
    (Habstract : ∀ k, e.abstractList fvars k = e)
    (Hrange : e.looseBVarRange' = 0) (k : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  unfold Expr.reopenFVarsAt
  rw [Habstract]
  exact Expr.instantiateRevList'_eq_self (by omega)

theorem Expr.abstractList_eq_self_of_abstract1
    (e : Expr) (H : ∀ fv k, e.abstract1 fv k = e)
    (fvars : List FVarId) (k : Nat) :
    e.abstractList fvars k = e := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih => simp [Expr.abstractList, H, ih]

theorem Expr.reopenFVarsAt_of_abstract1_eq_self
    (H : ∀ fv depth, e.abstract1 fv depth = e)
    (Hrange : e.looseBVarRange' = 0) (fvars restoreFvars : List FVarId)
    (k : Nat) : Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  apply Expr.reopenFVarsAt_eq_self_of_abstract
    (fun depth => Expr.abstractList_eq_self_of_abstract1 e H fvars depth)
    Hrange

theorem Expr.reopenFVarsAt_bvar
    (hsize : restoreFvars.length = fvars.length) (i k : Nat) :
    Expr.reopenFVarsAt (.bvar i) fvars restoreFvars k = .bvar i := by
  unfold Expr.reopenFVarsAt
  by_cases hi : i < k
  · rw [Expr.abstractList_bvar_lt fvars hi]
    exact Expr.instantiateRevList_bvar_fvars_lt restoreFvars i k hi
  · obtain ⟨n, rfl⟩ : ∃ n, i = k + n := by
      exact ⟨i - k, by omega⟩
    rw [Expr.abstractList_bvar_ge]
    rw [← hsize]
    exact Expr.instantiateRevList_bvar_fvars_ge restoreFvars k n

theorem Expr.reopenFVarsAt_selected
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (i : Nat) (hi : i < fvars.length) (k : Nat) :
    Expr.reopenFVarsAt (.fvar fvars[i]) fvars restoreFvars k =
      .fvar restoreFvars[i] := by
  unfold Expr.reopenFVarsAt
  rw [Expr.abstractList_fvar_getElem hnd i hi]
  rw [← hsize]
  exact Expr.instantiateRevList_bvar_fvars_getElem restoreFvars i k
    (by omega)

theorem Expr.reopenFVarsAt_fvar_exists
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (fv : FVarId) (k : Nat) :
    ∃ restored, Expr.reopenFVarsAt (.fvar fv) fvars restoreFvars k =
      .fvar restored := by
  by_cases hfv : fv ∈ fvars
  · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
    exact ⟨restoreFvars[i], Expr.reopenFVarsAt_selected hnd hsize i hi k⟩
  · refine ⟨fv, Expr.reopenFVarsAt_eq_self_of_abstract
      (fun depth => Expr.abstractList_fvar_of_not_mem hfv)
      (by simp [Expr.looseBVarRange']) k⟩

/-- Close-and-reopen free-variable renaming is independent of the de Bruijn
depth at which the surrounding syntax traversal encounters the expression. -/
theorem Expr.reopenFVarsAt_depth_independent
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k₁ k₂ : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k₁ =
      Expr.reopenFVarsAt e fvars restoreFvars k₂ := by
  induction e generalizing k₁ k₂ with
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize,
      Expr.reopenFVarsAt_bvar hsize]
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi,
        Expr.reopenFVarsAt_selected hnd hsize i hi]
    · have habstract : ∀ k, (Expr.fvar fv).abstractList fvars k = .fvar fv := by
        intro k
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₁,
        Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₂]
  | mvar id =>
    have habstract : ∀ k, (Expr.mvar id).abstractList fvars k = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.mvar id) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | sort u =>
    have habstract : ∀ k, (Expr.sort u).abstractList fvars k = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.sort u) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | const name levels =>
    have habstract : ∀ k, (Expr.const name levels).abstractList fvars k =
        .const name levels := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.const name levels) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | lit literal =>
    have habstract : ∀ k, (Expr.lit literal).abstractList fvars k =
        .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.lit literal) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app]
    change Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₁)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₁) =
      Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₂)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₂)
    rw [ihFn k₁ k₂, ihArg k₁ k₂]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam]
    change Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE]
    change Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE]
    change Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₁)
        (Expr.reopenFVarsAt value fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) nondep =
      Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₂)
        (Expr.reopenFVarsAt value fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) nondep
    rw [ihTy k₁ k₂, ihValue k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | mdata md body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata]
    change Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]
  | proj name idx body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj]
    change Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]

/-- Reopening replaces free variables only by free variables, so it cannot
manufacture a constant node. -/
theorem Expr.reopenFVarsAt_eq_const
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k : Nat)
    (H : Expr.reopenFVarsAt e fvars restoreFvars k = .const name levels) :
    e = .const name levels := by
  induction e generalizing k with
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize] at H
    cases H
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi] at H
      cases H
    · have habstract : ∀ depth,
          (Expr.fvar fv).abstractList fvars depth = .fvar fv := by
        intro depth
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange'])] at H
      cases H
  | mvar id =>
    have habstract : ∀ depth,
        (Expr.mvar id).abstractList fvars depth = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1 (.mvar id)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    cases H
  | sort u =>
    have habstract : ∀ depth,
        (Expr.sort u).abstractList fvars depth = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1 (.sort u)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    cases H
  | const sourceName sourceLevels =>
    have habstract : ∀ depth,
        (Expr.const sourceName sourceLevels).abstractList fvars depth =
          .const sourceName sourceLevels := by
      exact Expr.abstractList_eq_self_of_abstract1 (.const sourceName sourceLevels)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lit literal =>
    have habstract : ∀ depth,
        (Expr.lit literal).abstractList fvars depth = .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1 (.lit literal)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    cases H
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app] at H
    cases H
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam] at H
    cases H
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE] at H
    cases H
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE] at H
    cases H
  | mdata md body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata] at H
    cases H
  | proj typeName idx body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj] at H
    cases H

/-- Constant application heads are likewise reflected by free-variable
reopening. -/
theorem Expr.getAppFn_reopenFVarsAt_eq_const
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k : Nat)
    (H : (Expr.reopenFVarsAt e fvars restoreFvars k).getAppFn =
      .const name levels) :
    e.getAppFn = .const name levels := by
  induction e generalizing k with
  | app fn arg ihFn ihArg =>
    apply ihFn
    simpa [Expr.reopenFVarsAt, Expr.getAppFn] using H
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize] at H
    exact H
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi] at H
      cases H
    · have habstract : ∀ depth,
          (Expr.fvar fv).abstractList fvars depth = .fvar fv := by
        intro depth
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange'])] at H
      exact H
  | mvar id =>
    have habstract : ∀ depth,
        (Expr.mvar id).abstractList fvars depth = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1 (.mvar id)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | sort u =>
    have habstract : ∀ depth,
        (Expr.sort u).abstractList fvars depth = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1 (.sort u)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | const sourceName sourceLevels =>
    have habstract : ∀ depth,
        (Expr.const sourceName sourceLevels).abstractList fvars depth =
          .const sourceName sourceLevels := by
      exact Expr.abstractList_eq_self_of_abstract1 (.const sourceName sourceLevels)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lit literal =>
    have habstract : ∀ depth,
        (Expr.lit literal).abstractList fvars depth = .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1 (.lit literal)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lam name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | forallE name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | mdata md body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | proj typeName idx body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H

/-- The implementation's array operation is the depth-zero instance of the
transparent free-variable reopening model. -/
theorem Expr.reopenParams_eq_reopenFVarsAt
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray) :
    Expr.reopenParams e params restoreAs =
      Expr.reopenFVarsAt e fvars restoreFvars 0 := by
  subst params
  subst restoreAs
  simp [Expr.reopenParams, Expr.reopenFVarsAt, Expr.abstract_eq,
    Expr.instantiateRev_eq, Expr.instantiate_eq, Array.toList_reverse,
    Expr.instantiateList_reverse]

/-- Reopening at the depth of a syntax traversal agrees with the operational
depth-zero parameter reopening. -/
theorem Expr.reopenFVarsAt_eq_reopenParams
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (e : Expr) (k : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k =
      Expr.reopenParams e params restoreAs := by
  rw [Expr.reopenFVarsAt_depth_independent hnd hsize e k 0]
  exact (Expr.reopenParams_eq_reopenFVarsAt hparams hrestore).symm

theorem Expr.reopenParams_app
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray) :
    Expr.reopenParams (.app fn arg) params restoreAs =
      .app (Expr.reopenParams fn params restoreAs)
        (Expr.reopenParams arg params restoreAs) := by
  subst params
  simp [Expr.reopenParams, Expr.abstract_eq, Expr.instantiateRev_eq,
    Expr.instantiate_eq, Array.toList_reverse]

theorem Expr.reopenParams_const
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray) :
    Expr.reopenParams (.const name levels) params restoreAs =
      .const name levels := by
  subst params
  simp only [Expr.reopenParams, Expr.abstract_eq,
    Expr.instantiateRev_eq, Expr.instantiate_eq]
  have habstract : (Expr.const name levels).abstractList fvars =
      .const name levels := by
    induction fvars <;> simp [Expr.abstractList, Expr.abstract1, *]
  rw [habstract]
  apply Expr.instantiateList'_eq_self
  exact Nat.le_refl 0

theorem Expr.reopenParams_mkAppList
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray) :
    Expr.reopenParams (Expr.mkAppList fn args) params restoreAs =
      Expr.mkAppList (Expr.reopenParams fn params restoreAs)
        (args.map fun arg => Expr.reopenParams arg params restoreAs) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.mkAppList, List.map_cons]
    rw [ih, Expr.reopenParams_app fvars hparams]

theorem Expr.reopenParams_of_getAppFn_const
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hhead : input.getAppFn = .const name levels) :
    Expr.reopenParams input params restoreAs =
      Expr.mkAppList (.const name levels)
        (input.getAppArgsList.map fun arg =>
          Expr.reopenParams arg params restoreAs) := by
  calc
    Expr.reopenParams input params restoreAs =
        Expr.reopenParams
          (Expr.mkAppList input.getAppFn input.getAppArgsList)
          params restoreAs :=
      congrArg (fun e => Expr.reopenParams e params restoreAs)
        (Expr.mkAppList_getAppArgsList input).symm
    _ = Expr.mkAppList
          (Expr.reopenParams input.getAppFn params restoreAs)
          (input.getAppArgsList.map fun arg =>
            Expr.reopenParams arg params restoreAs) :=
      Expr.reopenParams_mkAppList fvars hparams
    _ = _ := by
      rw [hhead, Expr.reopenParams_const fvars hparams]

theorem Expr.abstractList_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractList binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractList_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

/-- Closing one free variable does not change the head of an application
spine, except for closing that head itself. -/
theorem Expr.getAppFn_abstract1 (e : Expr) (fv : FVarId) (k : Nat := 0) :
    (e.abstract1 fv k).getAppFn = e.getAppFn.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simpa [Expr.abstract1, Expr.getAppFn] using ihFn k
  | bvar i => simp [Expr.abstract1, Expr.getAppFn]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppFn, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppFn]

/-- Closing free variables does not change the head of an application spine,
except for closing that head itself. -/
theorem Expr.getAppFn_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppFn =
      e.getAppFn.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    exact congrArg (fun head => head.abstractList fvars k)
      (Expr.getAppFn_abstract1 e fv k)

/-- Closing one free variable acts pointwise on the arguments of an
application spine and preserves their order. -/
theorem Expr.getAppArgsList_abstract1 (e : Expr) (fv : FVarId)
    (k : Nat := 0) :
    (e.abstract1 fv k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simp only [Expr.abstract1, Expr.getAppArgsList_app, ihFn,
      List.map_append, List.map_cons, List.map_nil]
  | bvar i => simp [Expr.abstract1, Expr.getAppArgsList]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppArgsList, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppArgsList]

/-- Closing free variables acts pointwise on the arguments of an application
spine and preserves their order. -/
theorem Expr.getAppArgsList_abstractList (e : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => simp
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    calc
      ((e.abstract1 fv k).abstractList fvars k).getAppArgsList =
          (e.abstract1 fv k).getAppArgsList.map
            (fun arg => arg.abstractList fvars k) := ih _
      _ = (e.getAppArgsList.map fun arg => arg.abstract1 fv k).map
            (fun arg => arg.abstractList fvars k) :=
        congrArg (fun args => args.map
          (fun arg => arg.abstractList fvars k))
          (Expr.getAppArgsList_abstract1 e fv k)
      _ = e.getAppArgsList.map fun arg =>
          (arg.abstract1 fv k).abstractList fvars k := by
        simp only [List.map_map]
        apply congrArg (fun f => List.map f e.getAppArgsList)
        funext arg
        rfl

/-- Array form of `getAppArgsList_abstractList`. -/
theorem Expr.getAppArgs_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgs =
      e.getAppArgs.map fun arg => arg.abstractList fvars k := by
  apply Array.toList_inj.mp
  simp only [Expr.getAppArgs_toList, Expr.getAppArgsList_abstractList,
    Array.toList_map]

/-- Closing free variables acts pointwise on the index suffix returned by
`getIIndices`; the classifier component is irrelevant to this projection. -/
theorem checkPositivityStep.getIIndices.snd_abstractList
    (stats : AddInductive.InductiveStats) (type : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    (AddInductive.getIIndices stats (type.abstractList fvars k)).2 =
      (AddInductive.getIIndices stats type).2.map
        (fun index => index.abstractList fvars k) := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map]
  have suffixToList (e : Expr) :
      (AddInductive.getIIndices stats e).2.toList =
        e.getAppArgs.toList.drop stats.params.size := by
    simp only [AddInductive.getIIndices]
    let suffix := e.getAppArgs.toSubarray stats.params.size
    calc
      (Std.Slice.toArray suffix).toList = suffix.toList := by
        exact (congrArg Array.toList
          (Subarray.toArray_eq_sliceToArray (s := suffix)).symm).trans
            Subarray.toList_toArray
      _ = e.getAppArgs.toList.drop stats.params.size := by
        rw [List.drop_eq_drop_min]
        simp only [suffix, Subarray.toList_eq, Array.array_toSubarray,
          Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
          Array.toList_extract, List.extract_eq_take_drop,
          Array.length_toList]
        apply List.take_of_length_le
        simp
  rw [suffixToList, suffixToList]
  simp [Expr.getAppArgs_toList, Expr.getAppArgsList_abstractList]

/-- The concrete inductive-occurrence scan observes only constants, so
closing a free variable cannot affect its result. -/
theorem checkPositivityStep.hasIndOcc_abstract1
    (indConsts : Array Expr) (e : Expr) (fv : FVarId) (k : Nat := 0) :
    AddInductive.hasIndOcc indConsts (e.abstract1 fv k) =
      AddInductive.hasIndOcc indConsts e := by
  rw [checkPositivityStep.hasIndOcc_eq_findAny,
    checkPositivityStep.hasIndOcc_eq_findAny]
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1, Expr.findAny]
  | fvar other =>
    by_cases h : fv == other
    · simp [Expr.abstract1, Expr.findAny, h]
    · simp [Expr.abstract1, Expr.findAny, h]
  | mvar | sort | const | lit => simp [Expr.abstract1, Expr.findAny]
  | app fn arg ihFn ihArg =>
    simp [Expr.abstract1, Expr.findAny, ihFn, ihArg]
  | lam name dom body bi ihDom ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihDom, ihBody]
  | forallE name dom body bi ihDom ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihDom, ihBody]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihTy, ihValue, ihBody]
  | mdata md body ih => simp [Expr.abstract1, Expr.findAny, ih]
  | proj name idx body ih => simp [Expr.abstract1, Expr.findAny, ih]

/-- Simultaneously closing any list of free variables preserves the concrete
inductive-occurrence scan. -/
theorem checkPositivityStep.hasIndOcc_abstractList
    (indConsts : Array Expr) (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    AddInductive.hasIndOcc indConsts (e.abstractList fvars k) =
      AddInductive.hasIndOcc indConsts e := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    exact checkPositivityStep.hasIndOcc_abstract1 indConsts e fv k

/-- Closing a free variable cannot manufacture a constant. -/
theorem Expr.abstract1_eq_const
    {e : Expr} {fv : FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstract1 fv k = .const name levels) :
    e = .const name levels := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true <;> simp [Expr.abstract1, h] at H
  | mvar | sort | lit => simp [Expr.abstract1] at H
  | const => simpa [Expr.abstract1] using H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Iterated closing likewise reflects constant syntax. -/
theorem Expr.abstractList_eq_const
    {e : Expr} {fvars : List FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstractList fvars k = .const name levels) :
    e = .const name levels := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [Expr.abstractList] at H
    exact Expr.abstract1_eq_const (ih H)

/-- If the target variable is not the one being closed, a resulting free
variable was already that exact free variable in the source. -/
theorem Expr.abstract1_eq_fvar_of_ne
    {e : Expr} {target fv : FVarId} {k : Nat}
    (hne : target ≠ fv)
    (H : e.abstract1 fv k = .fvar target) :
    e = .fvar target := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true
    · simp [Expr.abstract1, h] at H
    · simp only [Expr.abstract1, h, ↓reduceIte] at H
      cases H
      rfl
  | mvar | sort | const | lit => simp [Expr.abstract1] at H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Reflection of a free variable through a list abstraction disjoint from
that variable. -/
theorem Expr.abstractList_eq_fvar_of_not_mem
    {e : Expr} {target : FVarId} {fvars : List FVarId} {k : Nat}
    (hnot : target ∉ fvars)
    (H : e.abstractList fvars k = .fvar target) :
    e = .fvar target := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [List.mem_cons, not_or] at hnot
    simp only [Expr.abstractList] at H
    have Hinter : e.abstract1 fv k = .fvar target := ih hnot.2 H
    exact Expr.abstract1_eq_fvar_of_ne (target := target) (fv := fv)
      hnot.1 Hinter

/-- A valid concrete inductive application remains valid after closing a
set of fresh field variables.  The disjointness premise says precisely that
the cached common parameters belong to the older root context. -/
theorem checkPositivityStep.isValidIndAppIdx.abstractList
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (paramFvars binders : List FVarId)
    (hparams : stats.params = (paramFvars.map Expr.fvar).toArray)
    (hdisjoint : ∀ fv, fv ∈ paramFvars → fv ∉ binders)
    (k : Nat := 0) :
    AddInductive.isValidIndAppIdx stats
      (type.abstractList binders k) i = true := by
  have hconstGet : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalid hconst
  have habstractHead : (type.abstractList binders k).getAppFn =
      .const name levels := by
    rw [Expr.getAppFn_abstractList type binders k, hhead]
    induction binders <;> simp_all [Expr.abstractList, Expr.abstract1]
  have hheadClosed :
      ((type.abstractList binders k).getAppFn == stats.indConsts[i]!) =
        true := by
    simpa only [habstractHead, hconstGet] using
      (beq_self_eq_true (Expr.const name levels))
  have harityClosed : (type.abstractList binders k).getAppArgs.size =
      stats.params.size + stats.nindices[i]! := by
    rw [Expr.getAppArgs_abstractList type binders k, Array.size_map]
    exact checkPositivityStep.isValidIndAppIdx.arity hvalid
  have hparamsClosed : ∀ j
      (hj : j < stats.params.size),
      stats.params[j] =
        (type.abstractList binders k).getAppArgs[j]'(by omega) := by
    intro j hj
    have hsize : stats.params.size = paramFvars.length := by
      rw [hparams]
      simp
    have hjFvars : j < paramFvars.length := by omega
    have hjSource : j < type.getAppArgs.size := by
      have := checkPositivityStep.isValidIndAppIdx.arity hvalid
      omega
    have hjClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      omega
    have hparamAt : stats.params[j] = .fvar paramFvars[j] := by
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hparams
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjFvars] using hget
    have hargEqv := checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hparamAt] at hargEqv
    have harg : type.getAppArgs[j]'hjSource = .fvar paramFvars[j] :=
      Expr.eqv_fvar_eq hargEqv
    have habstractArg :
        (type.abstractList binders k).getAppArgs[j]'hjClosed =
          .fvar paramFvars[j] := by
      have hargs := Expr.getAppArgs_abstractList type binders k
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
      have habstract :
          (type.getAppArgs[j]'hjSource).abstractList binders k =
            .fvar paramFvars[j] := by
        rw [harg]
        exact Expr.abstractList_fvar_of_not_mem
          (hdisjoint paramFvars[j] (List.getElem_mem hjFvars))
      simpa [Array.getElem!_eq_getD, Array.getD, hjClosed, hjSource,
        habstract] using hget
    exact hparamAt.trans habstractArg.symm
  have hindicesClosed : ∀ j
      (hlower : stats.params.size ≤ j)
      (hupper : j < (type.abstractList binders k).getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts
        (type.abstractList binders k).getAppArgs[j] = false := by
    intro j hlower hupper
    have hupperSource : j < type.getAppArgs.size := by
      simpa only [Expr.getAppArgs_abstractList type binders k,
        Array.size_map] using hupper
    have hsource :=
      checkPositivityStep.isValidIndAppIdx.indexNoOccurrence hvalid
        hlower hupperSource
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have hargEq :
        (type.abstractList binders k).getAppArgs[j]'hupper =
          (type.getAppArgs[j]'hupperSource).abstractList binders k := by
      simpa [Array.getElem!_eq_getD, Array.getD, hupper,
        hupperSource] using hget
    calc
      AddInductive.hasIndOcc stats.indConsts
          (type.abstractList binders k).getAppArgs[j] =
          AddInductive.hasIndOcc stats.indConsts
            ((type.getAppArgs[j]'hupperSource).abstractList binders k) :=
        congrArg (AddInductive.hasIndOcc stats.indConsts) hargEq
      _ = AddInductive.hasIndOcc stats.indConsts
          type.getAppArgs[j] :=
        checkPositivityStep.hasIndOcc_abstractList stats.indConsts
          type.getAppArgs[j] binders k
      _ = false := hsource
  exact checkPositivityStep.isValidIndAppIdx.intro hheadClosed harityClosed
    hparamsClosed hindicesClosed

/-- Conversely, closing fresh field variables cannot turn an invalid
application into a valid one.  Together with `abstractList`, this is the
alpha-invariance bridge used between constructor checking and recursor
generation. -/
theorem checkPositivityStep.isValidIndAppIdx.of_abstractList
    (paramFvars binders : List FVarId) (k : Nat := 0)
    (hvalid : AddInductive.isValidIndAppIdx stats
      (type.abstractList binders k) i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFvars.map Expr.fvar).toArray)
    (hdisjoint : ∀ fv, fv ∈ paramFvars → fv ∉ binders) :
    AddInductive.isValidIndAppIdx stats type i = true := by
  have hconstGet : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  have habstractHead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalid hconst
  have habstractSourceHead :
      type.getAppFn.abstractList binders k = .const name levels := by
    rw [← Expr.getAppFn_abstractList type binders k]
    exact habstractHead
  have hsourceHead : type.getAppFn = .const name levels :=
    Expr.abstractList_eq_const habstractSourceHead
  have hheadSource : (type.getAppFn == stats.indConsts[i]!) = true := by
    simpa only [hsourceHead, hconstGet] using
      (beq_self_eq_true (Expr.const name levels))
  have haritySource : type.getAppArgs.size =
      stats.params.size + stats.nindices[i]! := by
    have hclosed := checkPositivityStep.isValidIndAppIdx.arity hvalid
    simpa only [Expr.getAppArgs_abstractList type binders k,
      Array.size_map] using hclosed
  have hparamsSource : ∀ j (hj : j < stats.params.size),
      stats.params[j] = type.getAppArgs[j]'(by omega) := by
    intro j hj
    have hsize : stats.params.size = paramFvars.length := by
      rw [hparams]
      simp
    have hjFvars : j < paramFvars.length := by omega
    have hjSource : j < type.getAppArgs.size := by omega
    have hjClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      have := checkPositivityStep.isValidIndAppIdx.arity hvalid
      omega
    have hparamAt : stats.params[j] = .fvar paramFvars[j] := by
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hparams
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjFvars] using hget
    have hclosedEqv :=
      checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hparamAt] at hclosedEqv
    have hclosedArg :
        (type.abstractList binders k).getAppArgs[j]'hjClosed =
          .fvar paramFvars[j] := Expr.eqv_fvar_eq hclosedEqv
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have habstractArg :
        (type.getAppArgs[j]'hjSource).abstractList binders k =
          .fvar paramFvars[j] := by
      have hpointwise :
          (type.abstractList binders k).getAppArgs[j]'hjClosed =
            (type.getAppArgs[j]'hjSource).abstractList binders k := by
        simpa [Array.getElem!_eq_getD, Array.getD, hjClosed,
          hjSource] using hget
      exact hpointwise.symm.trans hclosedArg
    have hsourceArg : type.getAppArgs[j]'hjSource =
        .fvar paramFvars[j] :=
      Expr.abstractList_eq_fvar_of_not_mem
        (hdisjoint paramFvars[j] (List.getElem_mem hjFvars)) habstractArg
    exact hparamAt.trans hsourceArg.symm
  have hindicesSource : ∀ j (hlower : stats.params.size ≤ j)
      (hupper : j < type.getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
    intro j hlower hupper
    have hupperClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      simpa only [Expr.getAppArgs_abstractList type binders k,
        Array.size_map] using hupper
    have hclosed :=
      checkPositivityStep.isValidIndAppIdx.indexNoOccurrence hvalid
        hlower hupperClosed
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have hargEq :
        (type.abstractList binders k).getAppArgs[j]'hupperClosed =
          (type.getAppArgs[j]'hupper).abstractList binders k := by
      simpa [Array.getElem!_eq_getD, Array.getD, hupperClosed,
        hupper] using hget
    calc
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] =
          AddInductive.hasIndOcc stats.indConsts
            ((type.getAppArgs[j]'hupper).abstractList binders k) :=
        (checkPositivityStep.hasIndOcc_abstractList stats.indConsts
          type.getAppArgs[j] binders k).symm
      _ = AddInductive.hasIndOcc stats.indConsts
          (type.abstractList binders k).getAppArgs[j] :=
        congrArg (AddInductive.hasIndOcc stats.indConsts) hargEq.symm
      _ = false := hclosed
  exact checkPositivityStep.isValidIndAppIdx.intro hheadSource haritySource
    hparamsSource hindicesSource

/-- Opening one more telescope binder and then closing the complete ordered
field list recovers the body obtained by stripping that binder from the
already-closed telescope. -/
theorem Expr.instantiate1_fvar_abstractList_append
    {fv : FVarId} {fvars : List FVarId} {body : Expr}
    (hfv : fv ∉ fvars)
    (hbody : body.FVarsIn (fun other => other ≠ fv)) :
    (body.instantiate1 (.fvar fv)).abstractList (fvars ++ [fv]) =
      body.abstractList fvars 1 := by
  rw [Expr.abstractList_append]
  simp only [Expr.abstractList]
  rw [Expr.abstract1_abstractList hfv]
  rw [Expr.instantiate1_eq, hbody.abstract_instantiate1]

/-- Closing free variables changes leaves but never the outer expression
constructor, so in particular it cannot create or remove a leading forall. -/
@[simp] theorem Expr.abstractList_isForall
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).isForall = e.isForall := by
  induction fvars generalizing e k with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    cases e <;> simp only [Expr.abstract1, Expr.isForall]
    case fvar fvarId =>
      by_cases h : (fv == fvarId) = true
      · rw [if_pos h]
      · rw [if_neg h]

/-- Canonical alpha-normalization trace for a constructor-field traversal.
`current` is the opened residual seen by production, while `residual` is the
same point of the original telescope with all opened fields closed back to
de Bruijn variables. -/
structure ConstructorFieldOpening
    (source current : Expr) (fields : Array Expr) : Type where
  fvars : List FVarId
  expressions : fields = (fvars.map Expr.fvar).toArray
  nodup : fvars.Nodup
  residual : Expr
  telescope : Expr.ForallTelescope source fields.size residual
  closed : current.abstractList fvars = residual

def ConstructorFieldOpening.empty (source : Expr) :
    ConstructorFieldOpening source source #[] where
  fvars := []
  expressions := rfl
  nodup := .nil
  residual := source
  telescope := .nil source
  closed := rfl

/-- Extend the canonical opening trace by the fresh field chosen by
`withLocalDecl`. -/
def ConstructorFieldOpening.push
    (H : ConstructorFieldOpening source
      (.forallE name dom body bi) fields)
    (hfv : fv ∉ H.fvars)
    (hbody : body.FVarsIn (fun other => other ≠ fv)) :
    ConstructorFieldOpening source
      (body.instantiate1 (.fvar fv))
      (fields.push (.fvar fv)) := by
  have hsize : fields.size = H.fvars.length := by
    have := congrArg Array.size H.expressions
    simpa using this
  let nextResidual := body.abstractList H.fvars 1
  have Hinner : Expr.ForallTelescope H.residual 1 nextResidual := by
    rw [← H.closed]
    simp only [Expr.abstractList_forallE]
    exact .cons (.nil nextResidual)
  refine {
    fvars := H.fvars ++ [fv]
    expressions := ?_
    nodup := ?_
    residual := nextResidual
    telescope := ?_
    closed := ?_ }
  · simp [H.expressions]
  · apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro other hother selected hselected
    simp only [List.mem_singleton] at hselected
    subst selected
    exact fun heq => hfv (heq ▸ hother)
  · have Htel := H.telescope.trans Hinner
    simpa [hsize] using Htel
  · exact Expr.instantiate1_fvar_abstractList_append hfv hbody

theorem Expr.abstractList_indexBVars
    (binders : List FVarId) (n k : Nat) (hk : n < k) :
    ((List.ofFn fun i : Fin n =>
        Expr.bvar (1 + (n - 1 - i))).toArray.map
      fun e => e.abstractList binders k) =
    (List.ofFn fun i : Fin n =>
      Expr.bvar (1 + (n - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < n := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_ofFn]
    apply Expr.abstractList_bvar_lt
    omega

/-- Translation erases names and binder annotations but preserves the exact
number of leading forall binders. -/
theorem TrExprS.forallTelescope_shape
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' := by
  induction Htel generalizing Δ e' with
  | nil => exact ⟨[], e', rfl, rfl⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq⟩
      exact ⟨ty' :: domains, result', by simp [hlength], by
        simp [VExpr.wrapForalls, heq]⟩

def abstractForallContext (domains : List VExpr) (Δ : VLCtx) : VLCtx :=
  (domains.reverse.map fun type => (none, .vlam type)) ++ Δ

@[simp] theorem VLCtx.instL_append
    (left right : VLCtx) (levels : List VLevel) :
    (left ++ right).instL levels =
      left.instL levels ++ right.instL levels := by
  induction left with
  | nil => rfl
  | cons entry left ih =>
    rcases entry with ⟨ofv, decl⟩
    simp [VLCtx.instL, ih]

@[simp] theorem VLCtx.instL_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (levels : List VLevel) :
    (abstractForallContext domains Δ).instL levels =
      abstractForallContext (domains.map (VExpr.instL levels))
        (Δ.instL levels) := by
  have hmap : ∀ types : List VExpr,
      VLCtx.instL
          (types.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) levels =
      types.map fun type =>
        ((none, .vlam (type.instL levels)) :
          Option (FVarId × List FVarId) × VLocalDecl) := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih =>
      simp [VLCtx.instL, VLocalDecl.instL, ih]
  unfold abstractForallContext
  rw [VLCtx.instL_append]
  rw [← List.map_reverse]
  rw [hmap domains.reverse]
  simp [List.map_reverse, List.map_map, Function.comp_def]

/-- Remove the outermost declaration of an anonymous forall context while
instantiating every dependent declaration nested beneath it.  The witness is
the context-side counterpart of `VExpr.inst_wrapForalls`; its bound-variable
cutoff is exactly the number of still-inner domains. -/
theorem VLCtx.InstN.abstractForallContext_outer
    (domains : List VExpr) (domain arg : VExpr) (Δ : VLCtx) :
    VLCtx.InstN Δ arg domain domains.length domains.length
      (abstractForallContext (domain :: domains) Δ)
      (abstractForallContext
        (VExpr.instForallDomains domains arg 0) Δ) := by
  have go : ∀ reversed : List VExpr,
      VLCtx.InstN Δ arg domain reversed.length reversed.length
        (abstractForallContext (domain :: reversed.reverse) Δ)
        (abstractForallContext
          (VExpr.instForallDomains reversed.reverse arg 0) Δ) := by
    intro reversed
    induction reversed with
    | nil =>
        simpa [abstractForallContext, VExpr.instForallDomains] using
          (VLCtx.InstN.zero (Δ₀ := Δ) (e₀ := arg) (A₀ := domain))
    | cons inner reversed ih =>
      have W := VLCtx.InstN.succ
        (d := VLocalDecl.vlam inner) ih
      simpa [abstractForallContext, VExpr.instForallDomains_append,
          VExpr.instForallDomains, VLocalDecl.depth, VLocalDecl.inst,
          Nat.add_assoc] using W
  simpa using go domains.reverse

/-- Consume a translated source residual and its target residual in lockstep
with independently translated, closed arguments.  `liftClosedDomains` is the
invariant making every later dependent domain return to the same shape after
the outer argument is substituted. -/
theorem TrExprS.instantiateLiftClosedDomains
    (henv : env.Ordered)
    (Hresidual : TrExprS env Us
      (abstractForallContext (VExpr.liftClosedDomains types 0) Δ)
      source target)
    (Hargs : List.Forall₂ (TrExprS env Us Δ) sourceArgs targetArgs)
    (Htypes : List.Forall₂
      (env.HasType Us.length Δ.toCtx) targetArgs types) :
    TrExprS env Us Δ
      (Expr.instantiateForallBody source sourceArgs)
      (VExpr.applyForallType
        (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) target)
        targetArgs) := by
  induction Hargs generalizing types source target with
  | nil =>
      cases Htypes
      simpa [Expr.instantiateForallBody, VExpr.applyForallType,
        VExpr.liftClosedDomains, VExpr.wrapForalls,
        abstractForallContext] using Hresidual
  | @cons sourceArg targetArg sourceArgs targetArgs Harg Hargs ih =>
      cases Htypes with
      | @cons _ domain _ types Htarget Htypes =>
        have hlength : sourceArgs.length = types.length :=
          (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs).trans
            (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes)
        let innerDomains := VExpr.liftClosedDomains types 1
        have W := VLCtx.InstN.abstractForallContext_outer innerDomains
          domain targetArg Δ
        have Hresidual' : TrExprS env Us
            (abstractForallContext (domain :: innerDomains) Δ)
            source target := by
          simpa [innerDomains, VExpr.liftClosedDomains] using Hresidual
        have Hstep := Harg.instN henv Htarget W Hresidual'
        have Hstep' : TrExprS env Us
            (abstractForallContext
              (VExpr.liftClosedDomains types 0) Δ)
            (source.instantiate1' sourceArg sourceArgs.length)
            (target.inst targetArg types.length) := by
          simpa [innerDomains,
            VExpr.instForallDomains_liftClosedDomains_succ,
            hlength] using Hstep
        have Htail := ih Hstep' Htypes
        have htarget :
            VExpr.applyForallType
                (VExpr.wrapForalls
                  (VExpr.liftClosedDomains (domain :: types) 0) target)
                (targetArg :: targetArgs) =
              VExpr.applyForallType
                (VExpr.wrapForalls
                  (VExpr.liftClosedDomains types 0)
                  (target.inst targetArg types.length)) targetArgs := by
          change VExpr.applyForallType
              ((VExpr.wrapForalls
                (VExpr.liftClosedDomains types 1) target).inst targetArg 0)
              targetArgs = _
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add, VExpr.liftClosedDomains_length]
          rw [VExpr.instForallDomains_liftClosedDomains_succ]
        simp only [Expr.instantiateForallBody]
        rw [htarget]
        exact Htail

/-- Consuming a source forall residual that was weakened beneath exactly the
supplied argument block restores the original residual, independently of the
arguments.  This is the source-side normalization used after applying all
generated recursive-result arguments to a minor. -/
@[simp] theorem Expr.instantiateForallBody_liftLooseBVars
    (body : Expr) (args : List Expr) :
    Expr.instantiateForallBody
        (body.liftLooseBVars' 0 args.length) args = body := by
  induction args generalizing body with
  | nil => simp [Expr.instantiateForallBody]
  | cons arg args ih =>
      simp only [Expr.instantiateForallBody, List.length_cons]
      have hstep := Expr.instantiate1'_liftLooseBVars
        (e := body) (a := arg) (s := 0) (d := args.length)
      simp only [Nat.zero_add] at hstep
      rw [hstep]
      simpa using ih (body := body)

@[simp] theorem abstractForallContext_toCtx
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).toCtx =
      domains.reverse ++ Δ.toCtx := by
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  unfold abstractForallContext
  rw [VLCtx.toCtx_append, htoCtx domains.reverse]

theorem _root_.Lean4Lean.OnCtx.drop (H : OnCtx Γ P) (n : Nat) :
    OnCtx (Γ.drop n) P := by
  induction n generalizing Γ with
  | zero => exact H
  | succ n ih =>
    cases Γ with
    | nil => exact H
    | cons head tail => exact ih H.1

@[simp] theorem abstractForallContext_fvars
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).fvars = Δ.fvars := by
  rw [abstractForallContext, VLCtx.fvars_append]
  have hnone : VLCtx.fvars
      (domains.reverse.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = [] := by
    let types := domains.reverse
    change VLCtx.fvars
      (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = []
    induction types with
    | nil => rfl
    | cons type types ih =>
      simp only [List.map_cons, VLCtx.fvars_cons_none, ih]
  rw [hnone, List.nil_append]

@[simp] theorem VLCtx.toCtx_map_anonymousLams (types : List VExpr) :
    VLCtx.toCtx (types.map fun type =>
      ((none, .vlam type) :
        Option (FVarId × List FVarId) × VLocalDecl)) = types := by
  induction types with
  | nil => rfl
  | cons type types ih => simp [VLCtx.toCtx, ih]

@[simp] theorem abstractForallContext_bvars
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).bvars =
      domains.length + Δ.bvars := by
  simp only [abstractForallContext, VLCtx.bvars_append]
  have hmap : ∀ types : List VExpr,
      VLCtx.bvars (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types.length := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.bvars, ih]
  rw [hmap]
  simp

/-- Extend a converted outer context by the same well-formed dependent inner
prefix on both sides. -/
theorem VEnv.IsDefEqCtx.extendSamePrefix
    (H : VEnv.IsDefEqCtx env U [] left right)
    (Hctx : OnCtx (types ++ left) (env.IsType U)) :
    VEnv.IsDefEqCtx env U [] (types ++ left) (types ++ right) := by
  induction types with
  | nil => simpa using H
  | cons type types ih =>
    rcases Hctx with ⟨Htail, level, Htype⟩
    exact .succ (ih Htail) Htype

/-- A conversion between ordinary typing contexts induces a conversion
between their completely anonymous verifier contexts. -/
theorem VLCtx.IsDefEq.ofDefEqCtxAnonymous
    (H : VEnv.IsDefEqCtx env U [] left right) :
    VLCtx.IsDefEq env U
      (left.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl))
      (right.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) := by
  induction H with
  | zero => exact .nil
  | succ H Htype ih =>
    exact .cons ih (by simp) (.vlam (by simpa using Htype))

/-- Context-conversion wrapper in outermost-to-innermost domain order. -/
theorem abstractForallContext.isDefEq
    (H : VEnv.IsDefEqCtx env U [] left.reverse right.reverse) :
    VLCtx.IsDefEq env U
      (abstractForallContext left [])
      (abstractForallContext right []) := by
  simpa [abstractForallContext] using
    VLCtx.IsDefEq.ofDefEqCtxAnonymous H

/-- Translation uniqueness over two independently assembled anonymous
dependent contexts, stated directly in the plain-context conversion form
produced by telescope replay. -/
theorem TrExprS.uniqAbstractForallContext
    {domainsLeft domainsRight : List VExpr}
    (Hleft : TrExprS env Us (abstractForallContext domainsLeft []) source
      leftTarget)
    (Hright : TrExprS env Us (abstractForallContext domainsRight []) source
      rightTarget)
    (henv : VEnv.WF env)
    (Hctx : VEnv.IsDefEqCtx env Us.length [] domainsLeft.reverse
      domainsRight.reverse) :
    env.IsDefEqU Us.length domainsLeft.reverse leftTarget rightTarget := by
  have Hvlctx := abstractForallContext.isDefEq Hctx
  have Huniq := Hleft.uniq henv Hvlctx Hright
  simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Huniq

/-- Anonymous lambda contexts of equal length have the same lookup shape.
This is the structural premise needed to recover the exact target of a
syntax-directed translation after context conversion. -/
theorem TrExprS.IsUniqueCtx.anonymousLams
    {left right : List VExpr}
    (hlen : left.length = right.length) :
    TrExprS.IsUniqueCtx
      (left.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl))
      (right.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) := by
  induction left generalizing right with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    exact .base
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      exact .cons (ih (Nat.succ.inj hlen)) .vlam

/-- Outermost-to-innermost anonymous forall contexts retain unique lookup
shape whenever their telescope lengths agree. -/
theorem abstractForallContext.isUniqueCtx
    {left right : List VExpr}
    (hlen : left.length = right.length) :
    TrExprS.IsUniqueCtx
      (abstractForallContext left [])
      (abstractForallContext right []) := by
  simpa [abstractForallContext] using
    (TrExprS.IsUniqueCtx.anonymousLams
      (left := left.reverse) (right := right.reverse) (by simp [hlen]))

/-- Remove a free-variable-only context prefix when the translated source
uses only variables from the retained suffix.  The target is intentionally
existential: deleting locals changes de Bruijn positions, and syntax-directed
translation computes the uniquely rebased target in the smaller scope. -/
theorem TrExprS.dropFVarPrefix
    (henv : env.WF)
    (hscope : (added ++ suffix).WF env Us.length)
    (hnoBV : (added ++ suffix).NoBV)
    (H : TrExprS env Us (added ++ suffix) source target)
    (hfvars : FVarsIn (· ∈ suffix.fvars) source) :
    ∃ target', TrExprS env Us suffix source target' := by
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added suffix hnoBV
  let W := VLCtx.FVLift.to_append suffix hadded
  have hclosed : Closed source := hnoBV ▸ H.closed
  exact H.weakFV_inv henv W (.refl henv hscope) hclosed hfvars

/-- Locate the first retained free-variable declaration below an anonymous
forall prefix and replace it by the corresponding bound-variable declaration.
The source and target contexts have definitionally identical typing lists;
only the source-variable lookup changes. -/
theorem abstractForallContext.abstractHead
    (domains : List VExpr) (tail : VLCtx) (fv : FVarId)
    (deps : List FVarId) (type : VExpr) :
    VLCtx.Abstract tail fv (.vlam type) domains.length domains.length
      (abstractForallContext domains
        ((some (fv, deps), .vlam type) :: tail))
      (abstractForallContext (type :: domains) tail) := by
  have go : ∀ pre : List VExpr,
      VLCtx.Abstract tail fv (.vlam type) pre.length pre.length
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          (some (fv, deps), .vlam type) :: tail)
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          (none, .vlam type) :: tail) := by
    intro pre
    induction pre with
    | nil => exact .zero
    | cons domain pre ih =>
      simpa [VLocalDecl.depth, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using VLCtx.Abstract.succ
          (d := .vlam domain) ih
  simpa [abstractForallContext, List.reverse_cons, List.map_append,
    List.append_assoc] using go domains.reverse

/-- Abstract a reverse-ordered prefix of free-variable lambda declarations
while retaining an arbitrary older context tail.  The closed declarations
become anonymous domains outside the already present `domains`; the tail is
left untouched. -/
theorem TrExprS.abstractFVarLambdaPrefix
    (Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvsRev scopePrefix)
    (hnodup : fvsRev.Nodup)
    (Htr : TrExprS env Us
      (abstractForallContext domains (scopePrefix ++ tail)) e e') :
    TrExprS env Us
      (abstractForallContext
        ((VLCtx.toCtx scopePrefix).reverse ++ domains) tail)
      (e.abstractList fvsRev.reverse domains.length) e' := by
  induction Hdecls generalizing domains e with
  | nil => simpa [VLCtx.toCtx] using Htr
  | @cons fv entry fvsRev scopePrefix hentry Hrest ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    have hnodup' := List.nodup_cons.mp hnodup
    have W := abstractForallContext.abstractHead
      domains (scopePrefix ++ tail) fv deps type
    have Hhead := Htr.abstract W
    have hfv : fv ∉ fvsRev.reverse := by
      simpa using hnodup'.1
    have Htail := ih hnodup'.2 Hhead
    have hsource :
        (e.abstract1 fv domains.length).abstractList fvsRev.reverse
            (type :: domains).length =
          e.abstractList (fv :: fvsRev).reverse domains.length := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := e) (a := fv) (as := fvsRev.reverse)
        (k := domains.length) hfv).symm
    rw [hsource] at Htail
    simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using Htail

/-- Close the complete source front retained by a narrow runtime scope.  The
executable target is unchanged; the concrete source is abstracted over the
front's free variables in oldest-first order, and the resulting anonymous
telescope sits directly above the identified base scope. -/
theorem checkInductiveTypes.loopType.NarrowRuntimeScope.abstractFront
    (H : checkInductiveTypes.loopType.NarrowRuntimeScope
      env Us scope runtime)
    (henv : env.WF)
    (hbase : scope.drop H.frontSourceDomains.length = baseScope)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext H.frontSourceDomains baseScope)
      (source.abstractList
        (VLCtx.fvars (scope.take H.frontSourceDomains.length)).reverse)
      target := by
  let scopePrefix := scope.take H.frontSourceDomains.length
  let tail := scope.drop H.frontSourceDomains.length
  have hscope : scopePrefix ++ tail = scope := by
    simpa [scopePrefix, tail] using
      (List.take_append_drop H.frontSourceDomains.length scope).symm
  have Htr' : TrExprS env Us
      (abstractForallContext [] (scopePrefix ++ tail)) source target := by
    simpa [abstractForallContext, hscope] using Htr
  have hnodup : (VLCtx.fvars scopePrefix).Nodup := by
    exact (VLCtx.fvars_take_sublist scope
      H.frontSourceDomains.length).nodup (H.scopeWF henv).fvars_nodup
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    (domains := []) H.front.sourceDeclarations hnodup Htr'
  simpa [scopePrefix, tail, H.front.sourceTakenContext, hbase] using
    Habstract

/-- The names in a retained front are exactly the free-variable prefix of
the full narrow scope; after the front, only the identified base remains. -/
theorem checkInductiveTypes.loopType.NarrowRuntimeScope.frontFVars
    (H : checkInductiveTypes.loopType.NarrowRuntimeScope
      env Us scope runtime)
    (hbase : scope.drop H.frontSourceDomains.length = baseScope) :
    scope.fvars =
      VLCtx.fvars (scope.take H.frontSourceDomains.length) ++
        VLCtx.fvars baseScope := by
  calc
    scope.fvars = VLCtx.fvars
        (scope.take H.frontSourceDomains.length ++
          scope.drop H.frontSourceDomains.length) := by
      rw [List.take_append_drop]
    _ = VLCtx.fvars (scope.take H.frontSourceDomains.length) ++
        VLCtx.fvars (scope.drop H.frontSourceDomains.length) := by
      rw [VLCtx.fvars_append]
    _ = _ := by rw [hbase]

/-- Closing the retained source front preserves the ordinary typing context
of the narrow scope, so its anonymous telescope is well formed whenever the
original named scope is. -/
theorem checkInductiveTypes.loopType.NarrowRuntimeScope.abstractFrontWF
    (H : checkInductiveTypes.loopType.NarrowRuntimeScope
      env Us scope runtime)
    (henv : env.WF)
    (hbase : scope.drop H.frontSourceDomains.length = baseScope) :
    OnCtx (abstractForallContext H.frontSourceDomains baseScope).toCtx
      (env.IsType Us.length) := by
  have HscopeWF := (H.scopeWF henv).toCtx
  have hcontext :
      (abstractForallContext H.frontSourceDomains baseScope).toCtx =
        scope.toCtx := by
    rw [H.front.sourceContext, hbase]
    simp
  rw [hcontext]
  exact HscopeWF

/-- Abstract a reverse-ordered suffix of free-variable lambda declarations
under an existing anonymous prefix.  The declaration order is newest first,
so successive abstractions occur at increasing cutoffs; the resulting source
is the ordinary simultaneous abstraction in oldest-first binder order. -/
theorem TrExprS.abstractFVarLambdaSuffix
    (Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvsRev scope)
    (hnodup : fvsRev.Nodup)
    (Htr : TrExprS env Us (abstractForallContext domains scope) e e') :
    TrExprS env Us
      (abstractForallContext ((VLCtx.toCtx scope).reverse ++ domains) [])
      (e.abstractList fvsRev.reverse domains.length) e' := by
  induction Hdecls generalizing domains e with
  | nil => simpa [VLCtx.toCtx] using Htr
  | @cons fv entry fvsRev scope hentry Htail ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    have hnodup' := List.nodup_cons.mp hnodup
    have W := abstractForallContext.abstractHead
      domains scope fv deps type
    have Hhead := Htr.abstract W
    have hfv : fv ∉ fvsRev.reverse := by
      simpa using hnodup'.1
    have Hrest := ih hnodup'.2 Hhead
    have hsource :
        (e.abstract1 fv domains.length).abstractList fvsRev.reverse
            (type :: domains).length =
          e.abstractList (fv :: fvsRev).reverse domains.length := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := e) (a := fv) (as := fvsRev.reverse)
        (k := domains.length) hfv).symm
    rw [hsource] at Hrest
    simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using Hrest

/-- Close every retained declaration in a non-contiguous free-variable
scope.  Exact binder order is recorded by `scope.fvars`, so the resulting
anonymous telescope abstracts the source in oldest-first order without
assuming that the selected declarations formed a runtime prefix. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.abstractAll
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList scope.fvars.reverse) target := by
  have Htr' : TrExprS env Us
      (abstractForallContext [] scope) source target := by
    simpa [abstractForallContext] using Htr
  have hnodup : scope.fvars.Nodup :=
    (H.scopeWF henv).fvars_nodup
  simpa using TrExprS.abstractFVarLambdaSuffix
    H.declarations hnodup Htr'

/-- Closing an exact free-variable scope preserves its typing context. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.abstractAllWF
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF) :
    OnCtx (abstractForallContext scope.toCtx.reverse []).toCtx
      (env.IsType Us.length) := by
  have Hscope := (H.scopeWF henv).toCtx
  simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hscope

private theorem forall₂_takeBoth
    {R : α → β → Prop} (H : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction n generalizing xs ys with
  | zero => exact .nil
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons h Htail => exact .cons h (ih Htail)

private theorem namedLambdaDeclarations_fvars
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) xs ys) :
    VLCtx.fvars ys = xs := by
  induction H with
  | nil => rfl
  | @cons fv entry fvs entries hentry _ ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    change List.filterMap
      (fun x => Option.map (fun x => x.fst) x.fst) entries = fvs at ih
    simpa [VLCtx.fvars] using ih

/-- Close an initial segment of a non-contiguous selected scope while
retaining its exact older suffix.  Non-contiguity concerns the executable
runtime only; inside the selected scope, call locals and constructor fields
form an ordinary named prefix above the cached parameters. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.abstractPrefix
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF) (n : Nat)
    (hbase : scope.drop n = baseScope)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext (VLCtx.toCtx (scope.take n)).reverse baseScope)
      (source.abstractList (scope.fvars.take n).reverse) target := by
  let scopePrefix := scope.take n
  let tail := scope.drop n
  have hscope : scopePrefix ++ tail = scope := by
    simpa [scopePrefix, tail] using (List.take_append_drop n scope).symm
  have Hprefix := forall₂_takeBoth H.declarations n
  have hprefixFVars : VLCtx.fvars scopePrefix = scope.fvars.take n := by
    exact namedLambdaDeclarations_fvars Hprefix
  have Htr' : TrExprS env Us
      (abstractForallContext [] (scopePrefix ++ tail)) source target := by
    simpa [abstractForallContext, hscope] using Htr
  have hnodup : (scope.fvars.take n).Nodup :=
    (H.scopeWF henv).fvars_nodup.sublist (List.take_sublist n scope.fvars)
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    (domains := []) Hprefix hnodup Htr'
  simpa [scopePrefix, tail, hprefixFVars, hbase] using Habstract

/-- Abstracting an outer binder list after an already abstracted inner list
at the inner-list cutoff is equivalent to their ordinary outer-to-inner
simultaneous abstraction. -/
theorem Expr.abstractList_after_inner
    {e : Expr} {outer inner : List FVarId} {k : Nat}
    (hnodup : (outer ++ inner).Nodup) :
    (e.abstractList inner k).abstractList outer (k + inner.length) =
      e.abstractList (outer ++ inner) k := by
  induction outer generalizing e with
  | nil => simp
  | cons fv outer ih =>
    have hnodup' := List.nodup_cons.mp hnodup
    have hfvInner : fv ∉ inner := by
      exact fun h => hnodup'.1 (List.mem_append_right outer h)
    have htail : (outer ++ inner).Nodup := by
      simpa [List.cons_append] using hnodup'.2
    have hfvInnerNodup : (fv :: inner).Nodup :=
      List.nodup_cons.mpr ⟨hfvInner, (List.nodup_append.mp htail).2.1⟩
    simp only [List.cons_append, Expr.abstractList]
    rw [Expr.abstract1_abstractList'
      (e := e) (a := fv) (as := inner) (k := k)
      hfvInnerNodup]
    exact ih htail

/-- If abstraction has no unexpected free variables, the original expression
can only additionally mention the variable that was abstracted. -/
theorem FVarsIn.of_abstract1
    {e : Expr} {fv : FVarId} {k : Nat} {P : FVarId → Prop}
    (H : (e.abstract1 fv k).FVarsIn P) :
    e.FVarsIn fun other => other = fv ∨ P other := by
  induction e generalizing k with
  | bvar i => trivial
  | fvar other =>
    by_cases h : other = fv
    · simp [h, FVarsIn]
    · simpa [FVarsIn, Expr.abstract1, h, Ne.symm h] using H
  | sort level => simpa [FVarsIn, Expr.abstract1] using H
  | const name levels => simpa [FVarsIn, Expr.abstract1] using H
  | mvar id => simpa [FVarsIn, Expr.abstract1] using H
  | lit literal => trivial
  | app fn arg ihFn ihArg =>
    exact ⟨ihFn H.1, ihArg H.2⟩
  | lam name type body bi ihType ihBody =>
    exact ⟨ihType H.1, ihBody H.2⟩
  | forallE name type body bi ihType ihBody =>
    exact ⟨ihType H.1, ihBody H.2⟩
  | letE name type value body bi ihType ihValue ihBody =>
    exact ⟨ihType H.1, ihValue H.2.1, ihBody H.2.2⟩
  | mdata data body ih => exact ih H
  | proj name index body ih => exact ih H

/-- List form of `FVarsIn.of_abstract1`. -/
theorem FVarsIn.of_abstractList
    {e : Expr} {fvars : List FVarId} {k : Nat} {P : FVarId → Prop}
    (H : (e.abstractList fvars k).FVarsIn P) :
    e.FVarsIn fun fv => fv ∈ fvars ∨ P fv := by
  induction fvars generalizing e with
  | nil => simpa using H
  | cons fv fvars ih =>
    have Htail := ih H
    have Hhead := FVarsIn.of_abstract1 Htail
    exact Hhead.mono fun other h => by
      rcases h with h | h
      · simp [h]
      · rcases h with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

@[simp] theorem abstractForallContext_append
    (outer inner : List VExpr) (Δ : VLCtx) :
    abstractForallContext inner (abstractForallContext outer Δ) =
      abstractForallContext (outer ++ inner) Δ := by
  simp [abstractForallContext, List.reverse_append, List.map_append,
    List.append_assoc]

/-- Abstracting a lambda telescope only prepends bound variables, so it
preserves absence of a selected set of constants in context values. -/
theorem VLCtx.NoIndConsts.abstractForallContext
    (H : VLCtx.NoIndConsts names Δ) :
    VLCtx.NoIndConsts names (abstractForallContext domains Δ) := by
  unfold Lean4Lean.VerifyInductive.abstractForallContext
  have go : ∀ (entries : List VExpr) {v : Nat ⊕ FVarId}
      {mapped type : VExpr},
      (VLCtx.find? ((entries.map fun type =>
        ((none, VLocalDecl.vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) v =
        some (mapped, type)) →
      mapped.containsAnyConst names = false := by
    intro entries
    induction entries with
    | nil =>
      intro v mapped type hfind
      exact H hfind
    | cons type entries ih =>
      intro v mapped result hfind
      have hprefix : VLCtx.NoIndConsts names
          ((entries.map fun type =>
            ((none, VLocalDecl.vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) := by
        intro v mapped result hfind
        exact ih hfind
      have hcons : VLCtx.NoIndConsts names
          ((none, VLocalDecl.vlam type) ::
            (entries.map fun type =>
              ((none, VLocalDecl.vlam type) :
                Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) :=
        VLCtx.NoIndConsts.cons
          (ofv := none) (d := VLocalDecl.vlam type) hprefix (by rfl)
      exact hcons (by simpa only [List.map_cons, List.cons_append] using hfind)
  intro v mapped type hfind
  exact go domains.reverse hfind

/-- Prepending the abstract lambda domains is the canonical bound-variable
lift of the retained outer context. -/
theorem abstractForallContext.bvLift
    (domains : List VExpr) (Δ : VLCtx) :
    VLCtx.BVLift Δ (abstractForallContext domains Δ)
      domains.length 0 domains.length 0 := by
  have hprefix : ∀ (pref : List VExpr),
      VLCtx.BVLift Δ
        ((pref.map fun type => (none, .vlam type)) ++ Δ)
        pref.length 0 pref.length 0 := by
    intro pref
    induction pref with
    | nil => exact .refl
    | cons type pref ih =>
      simpa [VLocalDecl.depth, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        VLCtx.BVLift.skip (.vlam type) ih
  simpa [abstractForallContext] using hprefix domains.reverse

/-- Insert a block between an outer telescope and an existing inner prefix.
The dependent inner domains are lifted exactly as `Ctx.LiftN` requires, while
the source and target binder counts expose the cutoff used on residuals. -/
theorem abstractForallContext.bvInsertBeforeInner
    (outer inserted inner : List VExpr) :
    let liftedInner :=
      (liftContextPrefix inserted.length inner.reverse).reverse
    VLCtx.BVLift
      (abstractForallContext (outer ++ inner) [])
      (abstractForallContext (outer ++ inserted ++ liftedInner) [])
      inserted.length inner.length inserted.length inner.length := by
  let outerCtx := abstractForallContext outer []
  have go : ∀ pre : List VExpr,
      VLCtx.BVLift
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++ outerCtx)
        (((liftContextPrefix inserted.length pre).map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          abstractForallContext inserted outerCtx)
        inserted.length pre.length inserted.length pre.length := by
    intro pre
    induction pre with
    | nil =>
      simpa [liftContextPrefix, liftContextPrefixAt, outerCtx] using
        abstractForallContext.bvLift inserted outerCtx
    | cons domain pre ih =>
      simpa [liftContextPrefix, liftContextPrefixAt, VLocalDecl.depth,
        VLocalDecl.liftN,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        VLCtx.BVLift.cons (.vlam domain) ih
  simpa [abstractForallContext, outerCtx, List.reverse_append,
    List.map_append, List.append_assoc] using go inner.reverse

/-- Translation-level form of `bvInsertBeforeInner`: insert a telescope
between already closed outer and inner binders, lifting both residuals at
the inner-binder cutoff. -/
theorem TrExprS.insertBeforeInner
    (henv : env.Ordered)
    (Htr : TrExprS env Us
      (abstractForallContext (outer ++ inner) []) source target)
    (inserted : List VExpr) :
    let liftedInner :=
      (liftContextPrefix inserted.length inner.reverse).reverse
    TrExprS env Us
      (abstractForallContext (outer ++ inserted ++ liftedInner) [])
      (source.liftLooseBVars' inner.length inserted.length)
      (target.liftN inserted.length inner.length) := by
  let W := abstractForallContext.bvInsertBeforeInner outer inserted inner
  simpa using Htr.weakBV henv W

/-- Strengthened telescope inversion retaining the exact abstract context in
which the concrete residual is translated. -/
theorem TrExprS.forallTelescope_shape_with_context
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' ∧
      TrExprS env Us (abstractForallContext domains Δ) result result' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl, by simpa [abstractForallContext] using Htr⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq, hresult⟩
      refine ⟨ty' :: domains, result', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapForalls, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresult

/-- Typed telescope inversion additionally retains typehood of the residual
in the exact abstract context generated by the translated domains. -/
theorem TrExprS.forallTelescope_typed_shape_with_context
    (henv : env.WF)
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e')
    (Htype : env.IsType Us.length Δ.toCtx e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' ∧
      TrExprS env Us (abstractForallContext domains Δ) result result' ∧
      env.IsType Us.length
        (abstractForallContext domains Δ).toCtx result' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl, by
      simpa [abstractForallContext] using Htr, by
      simpa [abstractForallContext] using Htype⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ Hbody
      have HbodyType := (Htype.forallE_inv henv.ordered).2
      rcases ih Hbody HbodyType with
        ⟨domains, result', hlength, heq, Hresult, HresultType⟩
      refine ⟨ty' :: domains, result', by simp [hlength], ?_, ?_, ?_⟩
      · simp [VExpr.wrapForalls, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using Hresult
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using HresultType

/-- A nonempty translated concrete forall telescope is an abstract type.
The translation constructor already carries exactly the two typing premises
needed for abstract forall formation. -/
theorem TrExprS.isType_of_forallTelescope
    (Htel : Expr.ForallTelescope e arity result)
    (hpositive : 0 < arity)
    (Htr : TrExprS env Us Δ e e') :
    env.IsType Us.length Δ.toCtx e' := by
  cases Htel with
  | nil => omega
  | cons _ =>
    cases Htr with
    | forallE hdomType hbodyType _ _ =>
      exact VEnv.IsType.forallE hdomType hbodyType

/-- Compositional semantic certificate for a concrete forall telescope.
Unlike a bare whole-expression translation, this exposes the translation and
typehood obligation at every binder and at the final residual. -/
inductive Expr.ForallTelescopeTypeTranslation
    (env : VEnv) (Us : List Name) : VLCtx → Expr → Nat → VExpr → Prop
  | nil (Htr : TrExprS env Us Δ body body')
      (Htype : env.IsType Us.length Δ.toCtx body') :
      Expr.ForallTelescopeTypeTranslation env Us Δ body 0 body'
  | cons
      (Hdom : TrExprS env Us Δ dom dom')
      (HdomType : env.IsType Us.length Δ.toCtx dom')
      (Hbody : Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam dom') :: Δ) body n body') :
      Expr.ForallTelescopeTypeTranslation env Us Δ
        (.forallE name dom body bi) (n + 1) (.forallE dom' body')

theorem Expr.ForallTelescopeTypeTranslation.isType
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    env.IsType Us.length Δ.toCtx e' := by
  induction H with
  | nil _ Htype => exact Htype
  | cons _ HdomType _ ih => exact .forallE HdomType ih

theorem Expr.ForallTelescopeTypeTranslation.translation
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    TrExprS env Us Δ e e' := by
  induction H with
  | nil Htr _ => exact Htr
  | cons Hdom HdomType Hbody ih =>
    exact .forallE HdomType Hbody.isType Hdom ih

theorem Expr.ForallTelescopeTypeTranslation.mono
    (henv : env ≤ env')
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source arity target) :
    Expr.ForallTelescopeTypeTranslation env' Us Δ source arity target := by
  induction H with
  | nil Htr Htype => exact .nil (Htr.mono henv) (Htype.mono henv)
  | cons Hdom HdomType Hbody ih =>
    exact .cons (Hdom.mono henv) (HdomType.mono henv) ih

/-- Prepend a fresh concrete universe parameter to every judgment retained by
a translated forall telescope.  The concrete telescope is unchanged; the
semantic context and target are instantiated by the standard one-place
universe shift. -/
theorem Expr.ForallTelescopeTypeTranslation.prependLevelParam
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source arity target)
    (henv : env.WF) (hΔ : Δ.WF env Us.length) (hfresh : fresh ∉ Us) :
    Expr.ForallTelescopeTypeTranslation env (fresh :: Us)
      (Δ.instL (VLevel.prependShift Us.length)) source arity
      (target.instL (VLevel.prependShift Us.length)) := by
  let shift := VLevel.prependShift Us.length
  have hshift : ∀ level ∈ shift,
      level.WF (fresh :: Us).length := by
    simpa [shift] using VLevel.prependShift_wf (n := Us.length)
  induction H with
  | nil Htr Htype =>
    exact .nil (Htr.prependLevelParam henv hΔ hfresh) (by
      simpa [shift, VLCtx.instL_toCtx] using Htype.instL hshift)
  | cons Hdom HdomType Hbody ih =>
    exact .cons
      (Hdom.prependLevelParam henv hΔ hfresh)
      (by simpa [shift, VLCtx.instL_toCtx] using HdomType.instL hshift)
      (by
        simpa [shift, VLCtx.instL, VLocalDecl.instL] using
          ih ⟨hΔ, nofun, HdomType⟩)

theorem Expr.ForallTelescopeTypeTranslation.telescope
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    ∃ residual, Expr.ForallTelescope e n residual := by
  induction H with
  | nil => exact ⟨_, .nil _⟩
  | cons _ _ _ ih =>
    rcases ih with ⟨residual, Htel⟩
    exact ⟨residual, .cons Htel⟩

/-- Expose the abstract domains and residual carried by a binder-by-binder
translation.  The residual is typed in precisely the context obtained by
opening those domains, so callers can apply a term to the canonical binder
variables without reconstructing any domain syntax. -/
theorem Expr.ForallTelescopeTypeTranslation.toWrapForalls
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target) :
    ∃ domains sourceResidual targetResidual,
      domains.length = n ∧
      Expr.ForallTelescope source n sourceResidual ∧
      target = VExpr.wrapForalls domains targetResidual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        sourceResidual targetResidual ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx
        targetResidual := by
  induction H with
  | nil Htr Htype =>
    exact ⟨[], _, _, rfl, .nil _, rfl, by
      simpa [abstractForallContext] using Htr, by
      simpa [abstractForallContext] using Htype⟩
  | @cons Δ dom domTarget body n bodyTarget name bi
      Hdom HdomType Hbody ih =>
    rcases ih with
      ⟨domains, sourceResidual, targetResidual, hlength, Htelescope,
        htarget, Hresidual, HresidualType⟩
    refine ⟨domTarget :: domains, sourceResidual, targetResidual,
      by simp [hlength], .cons Htelescope, ?_, ?_, ?_⟩
    · simp [VExpr.wrapForalls, htarget]
    · simpa [abstractForallContext, List.map_append,
        List.append_assoc] using Hresidual
    · simpa [abstractForallContext, List.map_append,
        List.append_assoc] using HresidualType

/-- Split an exactly sized typed telescope after `prefixArity` binders,
retaining both the translated prefix domains and the binder-by-binder typed
suffix in their canonical abstract context. -/
theorem Expr.ForallTelescopeTypeTranslation.dropPrefix
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source
      (prefixArity + suffixArity) target) :
    ∃ prefixDomains suffixSource suffixTarget,
      prefixDomains.length = prefixArity ∧
      Expr.ForallTelescope source prefixArity suffixSource ∧
      target = VExpr.wrapForalls prefixDomains suffixTarget ∧
      Expr.ForallTelescopeTypeTranslation env Us
        (abstractForallContext prefixDomains Δ)
        suffixSource suffixArity suffixTarget := by
  induction prefixArity generalizing Δ source target with
  | zero =>
    exact ⟨[], source, target, rfl, .nil source, by rfl, by
      simpa [abstractForallContext] using H⟩
  | succ prefixArity ih =>
    rw [show (prefixArity + 1) + suffixArity =
      (prefixArity + suffixArity) + 1 by omega] at H
    cases H with
    | @cons Δ dom domTarget body arity bodyTarget name bi
        Hdom HdomType Hbody =>
      rcases ih Hbody with
        ⟨domains, suffixSource, suffixTarget, hlength, Hsource,
          htarget, Hsuffix⟩
      refine ⟨domTarget :: domains, suffixSource, suffixTarget,
        by simp [hlength], .cons Hsource, ?_, ?_⟩
      · simp [VExpr.wrapForalls, htarget]
      · simpa [abstractForallContext, List.map_append,
          List.append_assoc] using Hsuffix

/-- The domain at one exact position of a concrete forall telescope.  This
small source-only relation avoids carrying an arbitrary residual body when a
semantic proof needs to identify which local declaration production closed
at a generated-recursors slot. -/
inductive Expr.ForallBinderAt : Expr → Nat → Expr → Prop
  | here : Expr.ForallBinderAt (.forallE name domain body bi) 0 domain
  | there : Expr.ForallBinderAt body i domain →
      Expr.ForallBinderAt (.forallE name outerDomain body bi) (i + 1) domain

/-- Selecting any forall binder proves that consuming a possible annotation
at the top level leaves the enclosing expression unchanged. -/
theorem Expr.ForallBinderAt.consumeTypeAnnotationsVerified_eq_self
    (H : Expr.ForallBinderAt source i domain) :
    source.consumeTypeAnnotationsVerified = source := by
  cases H with
  | here => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
  | there _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

theorem Expr.ForallBinderAt.unique
    (H₁ : Expr.ForallBinderAt source i domain₁)
    (H₂ : Expr.ForallBinderAt source i domain₂) : domain₁ = domain₂ := by
  induction H₁ with
  | @here name domain body bi =>
      cases H₂
      rfl
  | there _ ih =>
      cases H₂ with
      | there H₂ => exact ih H₂

/-- A selected forall domain inherits every free-variable restriction of
the enclosing telescope. -/
theorem Expr.ForallBinderAt.domainFVarsIn
    (H : Expr.ForallBinderAt source i domain)
    (Hsource : source.FVarsIn P) : domain.FVarsIn P := by
  induction H with
  | here => exact Hsource.1
  | there _ ih => exact ih Hsource.2

/-- Abstraction of a free variable through a forall prefix reaches the
selected domain below exactly the number of preceding binders. -/
theorem Expr.ForallBinderAt.abstract1
    (H : Expr.ForallBinderAt source i domain) (fv : FVarId) (k : Nat := 0) :
    Expr.ForallBinderAt (source.abstract1 fv k) i
      (domain.abstract1 fv (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.abstract1] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.abstract1 fv (k + 1))
          (bi := bi) (domain := domain.abstract1 fv k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.abstract1 fv k)
        (bi := bi) Htail
      simpa [Expr.abstract1, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.abstractList
    (H : Expr.ForallBinderAt source i domain)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.ForallBinderAt (source.abstractList fvars k) i
      (domain.abstractList fvars (k + i)) := by
  induction fvars generalizing source domain with
  | nil => simpa using H
  | cons fv fvars ih =>
      simpa only [Expr.abstractList] using
        ih (H.abstract1 fv k)

/-- Prepending a concrete forall telescope shifts the position of a selected
binder by exactly the prefix arity. -/
theorem Expr.ForallTelescope.prependBinderAt
    (Hprefix : Expr.ForallTelescope outer prefixArity middle)
    (Hbinder : Expr.ForallBinderAt middle i domain) :
    Expr.ForallBinderAt outer (prefixArity + i) domain := by
  induction Hprefix with
  | nil => simpa using Hbinder
  | @cons body arity result name outerDomain bi Hprefix ih =>
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain) (bi := bi) (ih Hbinder)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- `inferImplicit` changes binder annotations but preserves every concrete
forall domain at its original position. -/
theorem Expr.ForallBinderAt.inferImplicit
    (H : Expr.ForallBinderAt source i domain)
    (max : Nat) (inferBinderTypes : Bool) :
    Expr.ForallBinderAt (source.inferImplicit max inferBinderTypes) i domain := by
  induction H generalizing max with
  | @here name domain body bi =>
      cases max with
      | zero => simpa [Expr.inferImplicit] using
          (Expr.ForallBinderAt.here (name := name) (body := body)
            (bi := bi) (domain := domain))
      | succ max =>
          simpa [Expr.inferImplicit] using
            (Expr.ForallBinderAt.here (name := name)
              (body := body.inferImplicit max inferBinderTypes)
              (bi := if bi.isExplicit &&
                (body.inferImplicit max inferBinderTypes).hasLooseBVarInExplicitDomain
                  0 inferBinderTypes then .implicit else bi)
              (domain := domain))
  | @there body i domain name outerDomain bi H ih =>
      cases max with
      | zero => simpa [Expr.inferImplicit] using
          (Expr.ForallBinderAt.there (name := name)
            (outerDomain := outerDomain) (bi := bi) H)
      | succ max =>
          have Htail := ih max
          simpa [Expr.inferImplicit] using
            (Expr.ForallBinderAt.there (name := name)
              (outerDomain := outerDomain)
              (bi := if bi.isExplicit &&
                (body.inferImplicit max inferBinderTypes).hasLooseBVarInExplicitDomain
                  0 inferBinderTypes then .implicit else bi)
              Htail)

/-- A prefix decomposition followed by one explicit forall identifies the
domain at that prefix position. -/
theorem Expr.ForallTelescope.binderAt
    (H : Expr.ForallTelescope source i suffix)
    (hsuffix : suffix = .forallE name domain body bi) :
    Expr.ForallBinderAt source i domain := by
  induction H with
  | nil =>
      rw [hsuffix]
      exact .here
  | cons _ ih =>
      exact .there (ih hsuffix)

/-- Select one binder from a typed translated telescope.  The returned
source domain is translated and typed in the exact abstract context formed
by the preceding target domains; the remaining body keeps its full
binder-by-binder certificate. -/
theorem Expr.ForallTelescopeTypeTranslation.binderAt
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target)
    (i : Nat) (hi : i < n) :
    ∃ prefixDomains suffixSource name sourceDomain sourceBody bi
        domainTarget bodyTarget,
      prefixDomains.length = i ∧
      Expr.ForallTelescope source i suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      target = VExpr.wrapForalls prefixDomains
        (.forallE domainTarget bodyTarget) ∧
      TrExprS env Us (abstractForallContext prefixDomains Δ)
        sourceDomain domainTarget ∧
      env.IsType Us.length
        (abstractForallContext prefixDomains Δ).toCtx domainTarget ∧
      Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam domainTarget) ::
          abstractForallContext prefixDomains Δ)
        sourceBody (n - i - 1) bodyTarget := by
  have hn : n = i + (n - i) := by omega
  rw [hn] at H
  rcases H.dropPrefix with
    ⟨prefixDomains, suffixSource, suffixTarget, hprefixLength,
      Hsource, htarget, Hsuffix⟩
  have hsuffixArity : n - i = (n - i - 1) + 1 := by omega
  rw [hsuffixArity] at Hsuffix
  cases Hsuffix with
  | @cons _ sourceDomain domainTarget sourceBody arity bodyTarget name bi
      Hdomain HdomainType Hbody =>
    exact ⟨prefixDomains, _, name, sourceDomain, sourceBody, bi,
      domainTarget, bodyTarget, hprefixLength, Hsource, rfl, htarget,
      Hdomain, HdomainType, Hbody⟩

/-- Select a binder when the complete abstract target telescope is already
known.  This identifies the selected target domain itself, rather than only
returning an existential domain from structural inversion. -/
theorem Expr.ForallTelescopeTypeTranslation.binderAt_target
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target)
    (domains : List VExpr) (result : VExpr)
    (htarget : target = VExpr.wrapForalls domains result)
    (hlength : domains.length = n)
    (i : Nat) (hi : i < n) :
    ∃ suffixSource name sourceDomain sourceBody bi bodyTarget,
      Expr.ForallTelescope source i suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext (domains.take i) Δ)
        sourceDomain domains[i] ∧
      env.IsType Us.length
        (abstractForallContext (domains.take i) Δ).toCtx domains[i] ∧
      Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam domains[i]) ::
          abstractForallContext (domains.take i) Δ)
        sourceBody (n - i - 1) bodyTarget := by
  rcases H.binderAt i hi with
    ⟨prefixDomains, suffixSource, name, sourceDomain, sourceBody, bi,
      domainTarget, bodyTarget, hprefixLength, Hsource, hsource,
      htarget', Hdomain, HdomainType, Hbody⟩
  have hidomains : i < domains.length := by omega
  have hsplit : domains = domains.take i ++ domains[i] ::
      domains.drop (i + 1) := by
    calc
      domains = domains.take (i + 1) ++ domains.drop (i + 1) :=
        (List.take_append_drop (i + 1) domains).symm
      _ = (domains.take i ++ [domains[i]]) ++ domains.drop (i + 1) := by
        rw [List.take_append_getElem hidomains]
      _ = domains.take i ++ domains[i] :: domains.drop (i + 1) := by
        simp [List.append_assoc]
  have hprefix : prefixDomains = domains.take i := by
    apply VExpr.wrapForalls_prefix_domains_eq hprefixLength
      (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidomains)])
    calc
      VExpr.wrapForalls prefixDomains (.forallE domainTarget bodyTarget) =
          target := htarget'.symm
      _ = VExpr.wrapForalls domains result := htarget
      _ = VExpr.wrapForalls
          (domains.take i ++ domains[i] :: domains.drop (i + 1)) result := by
        rw [← hsplit]
  subst prefixDomains
  have hsuffix : .forallE domainTarget bodyTarget =
      VExpr.wrapForalls (domains[i] :: domains.drop (i + 1)) result := by
    apply VExpr.wrapForalls_left_cancel (domains.take i)
    calc
      VExpr.wrapForalls (domains.take i) (.forallE domainTarget bodyTarget) =
          target := htarget'.symm
      _ = VExpr.wrapForalls domains result := htarget
      _ = VExpr.wrapForalls
          (domains.take i ++ domains[i] :: domains.drop (i + 1)) result := by
        rw [← hsplit]
      _ = VExpr.wrapForalls (domains.take i)
          (VExpr.wrapForalls (domains[i] :: domains.drop (i + 1)) result) := by
        exact VExpr.wrapForalls_append _ _ _
  simp only [VExpr.wrapForalls] at hsuffix
  injection hsuffix with hdomainTarget _hbodyTarget
  subst domainTarget
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType, Hbody⟩

/-- Two translated forall telescopes have definitionally equal abstract
prefix contexts whenever their concrete binder domains agree pointwise.
The bodies and the remaining telescope arities may differ; dependency is
handled by extending the context conversion one translated binder at a
time. -/
theorem Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtx
    (Henv : env.WF)
    (H₁ : Expr.ForallTelescopeTypeTranslation env Us []
      source₁ arity₁ target₁)
    (H₂ : Expr.ForallTelescopeTypeTranslation env Us []
      source₂ arity₂ target₂)
    (domains₁ domains₂ : List VExpr) (result₁ result₂ : VExpr)
    (htarget₁ : target₁ = VExpr.wrapForalls domains₁ result₁)
    (htarget₂ : target₂ = VExpr.wrapForalls domains₂ result₂)
    (hlength₁ : domains₁.length = arity₁)
    (hlength₂ : domains₂.length = arity₂)
    (prefixLen : Nat) (hprefix₁ : prefixLen ≤ arity₁)
    (hprefix₂ : prefixLen ≤ arity₂)
    (Hdomains : ∀ i (hiprefix : i < prefixLen)
      (hi₁ : i < arity₁) (hi₂ : i < arity₂)
      {domain₁ domain₂ : Expr},
      Expr.ForallBinderAt source₁ i domain₁ →
      Expr.ForallBinderAt source₂ i domain₂ →
      domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      (domains₁.take prefixLen).reverse
      (domains₂.take prefixLen).reverse := by
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have habstractToCtx : ∀ types : List VExpr,
      (abstractForallContext types []).toCtx = types.reverse := by
    intro types
    simpa [abstractForallContext, ← List.map_reverse] using
      htoCtx types.reverse
  induction prefixLen with
  | zero => exact .zero
  | succ prefixLen ih =>
    have hi₁ : prefixLen < arity₁ := by omega
    have hi₂ : prefixLen < arity₂ := by omega
    have hdom₁ : prefixLen < domains₁.length := by omega
    have hdom₂ : prefixLen < domains₂.length := by omega
    have Hprior := ih (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by omega) hi₁ hi₂ Hbinder₁ Hbinder₂)
    rcases H₁.binderAt_target domains₁ result₁ htarget₁ hlength₁
        prefixLen hi₁ with
      ⟨suffix₁, name₁, sourceDomain₁, sourceBody₁, bi₁, bodyTarget₁,
        Hsource₁, hsuffix₁, Hdomain₁, _HdomainType₁, _Hbody₁⟩
    rcases H₂.binderAt_target domains₂ result₂ htarget₂ hlength₂
        prefixLen hi₂ with
      ⟨suffix₂, name₂, sourceDomain₂, sourceBody₂, bi₂, bodyTarget₂,
        Hsource₂, hsuffix₂, Hdomain₂, _HdomainType₂, _Hbody₂⟩
    have hsourceDomain : sourceDomain₁ = sourceDomain₂ :=
      Hdomains prefixLen (Nat.lt_succ_self _) hi₁ hi₂
        (Hsource₁.binderAt hsuffix₁) (Hsource₂.binderAt hsuffix₂)
    rw [← hsourceDomain] at Hdomain₂
    have Hvlctx := abstractForallContext.isDefEq Hprior
    have HdomainU := Hdomain₁.uniq Henv Hvlctx Hdomain₂
    rcases _HdomainType₁ with ⟨level, HdomainType₁⟩
    have HdomainU' : env.IsDefEqU Us.length
        (domains₁.take prefixLen).reverse
        domains₁[prefixLen] domains₂[prefixLen] := by
      rw [habstractToCtx] at HdomainU
      exact HdomainU
    have HdomainType₁' : env.HasType Us.length
        (domains₁.take prefixLen).reverse domains₁[prefixLen]
        (.sort level) := by
      rw [habstractToCtx] at HdomainType₁
      exact HdomainType₁
    have Hdomain' := HdomainU'.of_l Henv Hprior.isType HdomainType₁'
    have Hnext : VEnv.IsDefEqCtx env Us.length []
        (domains₁[prefixLen] :: (domains₁.take prefixLen).reverse)
        (domains₂[prefixLen] :: (domains₂.take prefixLen).reverse) :=
      .succ Hprior Hdomain'
    have htake₁ : domains₁.take (prefixLen + 1) =
        domains₁.take prefixLen ++ [domains₁[prefixLen]] := by
      exact (List.take_append_getElem hdom₁).symm
    have htake₂ : domains₂.take (prefixLen + 1) =
        domains₂.take prefixLen ++ [domains₂[prefixLen]] := by
      exact (List.take_append_getElem hdom₂).symm
    rw [htake₁, htake₂]
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append] using Hnext

/-- Base-context form of `commonPrefixDefEqCtx`.  The two translations may
start over independently produced anonymous telescopes, provided those base
telescopes are already definitionally equal.  Each selected binder extends
that conversion, so dependency in all later domains is preserved. -/
theorem Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
    (Henv : env.WF)
    (Hbase : VEnv.IsDefEqCtx env Us.length []
      base₁.reverse base₂.reverse)
    (H₁ : Expr.ForallTelescopeTypeTranslation env Us
      (abstractForallContext base₁ []) source₁ arity₁ target₁)
    (H₂ : Expr.ForallTelescopeTypeTranslation env Us
      (abstractForallContext base₂ []) source₂ arity₂ target₂)
    (domains₁ domains₂ : List VExpr) (result₁ result₂ : VExpr)
    (htarget₁ : target₁ = VExpr.wrapForalls domains₁ result₁)
    (htarget₂ : target₂ = VExpr.wrapForalls domains₂ result₂)
    (hlength₁ : domains₁.length = arity₁)
    (hlength₂ : domains₂.length = arity₂)
    (prefixLen : Nat) (hprefix₁ : prefixLen ≤ arity₁)
    (hprefix₂ : prefixLen ≤ arity₂)
    (Hdomains : ∀ i (hiprefix : i < prefixLen)
      (hi₁ : i < arity₁) (hi₂ : i < arity₂)
      {domain₁ domain₂ : Expr},
      Expr.ForallBinderAt source₁ i domain₁ →
      Expr.ForallBinderAt source₂ i domain₂ →
      domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      ((domains₁.take prefixLen).reverse ++ base₁.reverse)
      ((domains₂.take prefixLen).reverse ++ base₂.reverse) := by
  have habstractToCtx : ∀ (base types : List VExpr),
      (abstractForallContext types
        (abstractForallContext base [])).toCtx =
        types.reverse ++ base.reverse := by
    intro base types
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  induction prefixLen with
  | zero => simpa using Hbase
  | succ prefixLen ih =>
    have hi₁ : prefixLen < arity₁ := by omega
    have hi₂ : prefixLen < arity₂ := by omega
    have hdom₁ : prefixLen < domains₁.length := by omega
    have hdom₂ : prefixLen < domains₂.length := by omega
    have Hprior := ih (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by omega) hi₁ hi₂ Hbinder₁ Hbinder₂)
    rcases H₁.binderAt_target domains₁ result₁ htarget₁ hlength₁
        prefixLen hi₁ with
      ⟨suffix₁, name₁, sourceDomain₁, sourceBody₁, bi₁, bodyTarget₁,
        Hsource₁, hsuffix₁, Hdomain₁, HdomainType₁, _Hbody₁⟩
    rcases H₂.binderAt_target domains₂ result₂ htarget₂ hlength₂
        prefixLen hi₂ with
      ⟨suffix₂, name₂, sourceDomain₂, sourceBody₂, bi₂, bodyTarget₂,
        Hsource₂, hsuffix₂, Hdomain₂, _HdomainType₂, _Hbody₂⟩
    have hsourceDomain : sourceDomain₁ = sourceDomain₂ :=
      Hdomains prefixLen (Nat.lt_succ_self _) hi₁ hi₂
        (Hsource₁.binderAt hsuffix₁) (Hsource₂.binderAt hsuffix₂)
    rw [← hsourceDomain] at Hdomain₂
    have Hvlctx : VLCtx.IsDefEq env Us.length
        (abstractForallContext (domains₁.take prefixLen)
          (abstractForallContext base₁ []))
        (abstractForallContext (domains₂.take prefixLen)
          (abstractForallContext base₂ [])) := by
      have Hanonymous := abstractForallContext.isDefEq
        (left := base₁ ++ domains₁.take prefixLen)
        (right := base₂ ++ domains₂.take prefixLen) (by
          simpa [List.reverse_append, List.append_assoc] using Hprior)
      simpa [abstractForallContext, List.reverse_append,
        List.map_append, List.append_assoc] using Hanonymous
    have HdomainU := Hdomain₁.uniq Henv Hvlctx Hdomain₂
    rcases HdomainType₁ with ⟨level, HdomainType₁⟩
    have HdomainU' : env.IsDefEqU Us.length
        ((domains₁.take prefixLen).reverse ++ base₁.reverse)
        domains₁[prefixLen] domains₂[prefixLen] := by
      rw [habstractToCtx] at HdomainU
      exact HdomainU
    have HdomainType₁' : env.HasType Us.length
        ((domains₁.take prefixLen).reverse ++ base₁.reverse)
        domains₁[prefixLen] (.sort level) := by
      rw [habstractToCtx] at HdomainType₁
      exact HdomainType₁
    have Hdomain' := HdomainU'.of_l Henv Hprior.isType HdomainType₁'
    have Hnext : VEnv.IsDefEqCtx env Us.length []
        (domains₁[prefixLen] ::
          (domains₁.take prefixLen).reverse ++ base₁.reverse)
        (domains₂[prefixLen] ::
          (domains₂.take prefixLen).reverse ++ base₂.reverse) :=
      .succ Hprior Hdomain'
    have htake₁ : domains₁.take (prefixLen + 1) =
        domains₁.take prefixLen ++ [domains₁[prefixLen]] := by
      exact (List.take_append_getElem hdom₁).symm
    have htake₂ : domains₂.take (prefixLen + 1) =
        domains₂.take prefixLen ++ [domains₂[prefixLen]] := by
      exact (List.take_append_getElem hdom₂).symm
    rw [htake₁, htake₂]
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc] using Hnext

/-- A translated telescope known to be a type decomposes canonically into
the binder-by-binder certificate. This establishes that the new interface
loses no information while exposing exactly where restoration must act. -/
theorem Expr.ForallTelescopeTypeTranslation.ofTrExprS
    (Htel : Expr.ForallTelescope e n residual)
    (Htr : TrExprS env Us Δ e e')
    (Htype : env.IsType Us.length Δ.toCtx e') :
    Expr.ForallTelescopeTypeTranslation env Us Δ e n e' := by
  induction Htel generalizing Δ e' with
  | nil => exact .nil Htr Htype
  | cons Htail ih =>
    cases Htr with
    | forallE HdomType HbodyType Hdom Hbody =>
      exact .cons Hdom HdomType (ih Hbody HbodyType)

/-- The source closure retained by non-contiguous narrowing has exactly one
forall per selected free variable, and its residual is ordinary simultaneous
abstraction in oldest-first order. -/
theorem checkInductiveTypes.loopType.FVarNarrowSources.closeSource_telescope
    (H : checkInductiveTypes.loopType.FVarNarrowSources env Us scope)
    (hnodup : scope.fvars.Nodup) (body : Expr) :
    Expr.ForallTelescope (H.closeSource body) scope.length
      (body.abstractList scope.fvars.reverse) := by
  induction H generalizing body with
  | nil => exact .nil body
  | @cons scope domainTarget fv deps tail name binderInfo domain Hdomain ih =>
    change (fv :: scope.fvars).Nodup at hnodup
    have hnodupParts := List.nodup_cons.mp hnodup
    let innerBody := body.abstract1 fv
    have Houter := ih hnodupParts.2
      (.forallE name domain innerBody binderInfo)
    have Houter' : Expr.ForallTelescope
        (tail.closeSource (.forallE name domain innerBody binderInfo))
        scope.length
        (.forallE name (domain.abstractList scope.fvars.reverse)
          (innerBody.abstractList scope.fvars.reverse 1) binderInfo) := by
      simpa [innerBody] using Houter
    have Hinner : Expr.ForallTelescope
        (.forallE name (domain.abstractList scope.fvars.reverse)
          (innerBody.abstractList scope.fvars.reverse 1) binderInfo)
        1 (innerBody.abstractList scope.fvars.reverse 1) := by
      simpa using Expr.ForallTelescope.cons
        (Expr.ForallTelescope.nil
          (innerBody.abstractList scope.fvars.reverse 1))
    have Hcombined := Houter'.trans Hinner
    have hfv : fv ∉ scope.fvars.reverse := by
      simpa using hnodupParts.1
    have hresidual :
        (body.abstract1 fv).abstractList scope.fvars.reverse 1 =
          body.abstractList (fv :: scope.fvars).reverse := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := body) (a := fv) (as := scope.fvars.reverse)
        (k := 0) hfv).symm
    rw [hresidual] at Hcombined
    simpa [FVarNarrowSources.closeSource] using Hcombined

/-- Translate a source body while closing every retained named declaration.
The target is the ordinary anonymous forall telescope over the narrowed
semantic domains, in oldest-first order. -/
theorem checkInductiveTypes.loopType.FVarNarrowSources.closeTranslation
    (H : checkInductiveTypes.loopType.FVarNarrowSources env Us scope)
    (henv : env.WF) (Hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    TrExprS env Us [] (H.closeSource body)
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  induction H generalizing body target with
  | nil =>
    change TrExprS env Us [] body target
    exact Hbody
  | @cons scope domainTarget fv deps tail name binderInfo domain Hdomain ih =>
    have HtailWF : scope.WF env Us.length := Hscope.1
    have HdomainType : env.IsType Us.length scope.toCtx domainTarget := by
      exact Hscope.2.2
    have W := abstractForallContext.abstractHead
      ([] : List VExpr) scope fv deps domainTarget
    have HbodyAbstract : TrExprS env Us
        ((none, .vlam domainTarget) :: scope)
        (body.abstract1 fv) target := by
      simpa [abstractForallContext] using Hbody.abstract W
    have Hforall : TrExprS env Us scope
        (.forallE name domain (body.abstract1 fv) binderInfo)
        (.forallE domainTarget target) :=
      .forallE HdomainType HbodyType Hdomain HbodyAbstract
    have HforallType : env.IsType Us.length scope.toCtx
        (.forallE domainTarget target) :=
      VEnv.IsType.forallE HdomainType HbodyType
    have Hclosed := ih HtailWF Hforall HforallType
    simpa [FVarNarrowSources.closeSource, VLCtx.toCtx,
      List.reverse_cons, VExpr.wrapForalls] using Hclosed

/-- Typed telescope form of `closeTranslation` when the exact semantic
source provenance is retained directly, without an ambient narrowing
wrapper. -/
theorem checkInductiveTypes.loopType.FVarNarrowSources.closeTypedTelescope
    (H : checkInductiveTypes.loopType.FVarNarrowSources env Us scope)
    (henv : env.WF) (Hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  have Htranslation := H.closeTranslation henv Hscope Hbody HbodyType
  have Htelescope := H.closeSource_telescope Hscope.fvars_nodup body
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
    apply VEnv.IsType.wrapForalls
    · simpa using Hscope.toCtx
    · simpa using HbodyType
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope Htranslation HtargetType

/-- Typed telescope form of `closeTranslation` for an arbitrary body.  This
is the reusable boundary between a named, non-contiguously narrowed scope and
the completely closed source declaration used by an independent
specification: the body may itself be a dependent telescope. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.closeTypedTelescope
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sources.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  exact H.sources.closeTypedTelescope henv (H.scopeWF henv)
    Hbody HbodyType

/-- Close the retained source declarations around a trivial sort.  This is
an independent translation of the complete narrowed prefix, rather than a
translation of only a later expression under that prefix. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.closedSortTranslation
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF) :
    TrExprS env Us []
      (H.sources.closeSource (.sort (.zero : Level)))
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) ∧
    env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
  have HscopeWF := H.scopeWF henv
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hsort : TrExprS env Us scope (.sort (.zero : Level))
      (.sort (.zero : VLevel)) := .sort hzero
  have HsortType : env.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  have Hclosed := H.sources.closeTranslation henv HscopeWF
    Hsort HsortType
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    apply VEnv.IsType.wrapForalls
    · simpa using HscopeWF.toCtx
    · simpa using HsortType
  exact ⟨Hclosed, HtargetType⟩

/-- Binder-by-binder form of `closedSortTranslation`.  The retained concrete
source expression and narrowed abstract target constitute a complete typed
forall telescope, not merely a whole-expression translation. -/
theorem checkInductiveTypes.loopType.FVarNarrowScope.closedSortTelescope
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sources.closeSource (.sort (.zero : Level))) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
  rcases H.closedSortTranslation henv with ⟨Htranslation, Htype⟩
  have Htelescope := H.sources.closeSource_telescope
    (H.scopeWF henv).fvars_nodup (.sort (.zero : Level))
  have Htelescope' : Expr.ForallTelescope
      (H.sources.closeSource (.sort (.zero : Level))) scope.length
      (.sort (.zero : Level)) := by
    have hsort : ∀ fvars : List FVarId,
        (Expr.sort (.zero : Level)).abstractList fvars =
          .sort (.zero : Level) := by
      intro fvars
      induction fvars with
      | nil => rfl
      | cons fv fvars ih =>
        simp only [Expr.abstractList]
        rw [show (Expr.sort (.zero : Level)).abstract1 fv =
          .sort (.zero : Level) by rfl]
        exact ih
    rw [hsort] at Htelescope
    exact Htelescope
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope' Htranslation Htype

theorem List.exists_append_five_of_length_eq
    (xs : List α) (a b c d e : Nat)
    (h : xs.length = a + b + c + d + e) :
    ∃ as bs cs ds es,
      xs = as ++ bs ++ cs ++ ds ++ es ∧
      as.length = a ∧ bs.length = b ∧ cs.length = c ∧
      ds.length = d ∧ es.length = e := by
  let as := xs.take a
  let restA := xs.drop a
  let bs := restA.take b
  let restB := restA.drop b
  let cs := restB.take c
  let restC := restB.drop c
  let ds := restC.take d
  let es := restC.drop d
  refine ⟨as, bs, cs, ds, es, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [as, bs, cs, ds, es, restA, restB, restC]
    symm
    simp only [List.append_assoc]
    rw [List.take_append_drop d, List.take_append_drop c,
      List.take_append_drop b, List.take_append_drop a]
  all_goals simp [as, bs, cs, ds, es, restA, restB, restC, h] <;> omega

private theorem vlamPrefix_find_bvar
    (pref : List VExpr) (Δ : VLCtx) (i : Nat) (hi : i < pref.length) :
    ∃ type, VLCtx.find? ((pref.map fun type =>
      ((none, VLocalDecl.vlam type) :
        Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ)
      (Sum.inl i) = some (VExpr.bvar i, type) := by
  induction pref generalizing i with
  | nil => simp at hi
  | cons type pref ih =>
    cases i with
    | zero =>
      refine ⟨type.lift, ?_⟩
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
    | succ i =>
      have hi' : i < pref.length := by simpa using hi
      rcases ih i hi' with ⟨found, hfind⟩
      refine ⟨found.lift, ?_⟩
      simp only [List.map_cons, List.cons_append, VLCtx.find?, VLCtx.next]
      rw [hfind]
      simp [VLocalDecl.depth, VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm]

theorem abstractForallContext.find?_bvar
    (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    ∃ type, VLCtx.find? (abstractForallContext domains Δ) (.inl i) =
      some (.bvar i, type) := by
  apply vlamPrefix_find_bvar domains.reverse Δ i
  simpa using hi

/-- Every in-range source de Bruijn variable translates to the identically
numbered abstract variable in a canonical forall context. -/
theorem TrExprS.bvar_of_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    TrExprS env Us (abstractForallContext domains Δ)
      (.bvar i) (.bvar i) := by
  rcases abstractForallContext.find?_bvar domains Δ i hi with
    ⟨type, hfind⟩
  exact .bvar hfind

/-- Pointwise form of `bvar_of_abstractForallContext` for an arbitrary
in-range application spine. -/
theorem TrExprS.bvars_of_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (indices : List Nat)
    (hindices : ∀ index ∈ indices, index < domains.length) :
    List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
      (indices.map Expr.bvar) (indices.map VExpr.bvar) := by
  induction indices with
  | nil => exact .nil
  | cons index indices ih =>
    apply List.Forall₂.cons
    · exact TrExprS.bvar_of_abstractForallContext domains Δ index
        (hindices index (by simp))
    · exact ih fun other hother => hindices other (by simp [hother])

/-- Canonically ordered binder variables translate pointwise in any larger
abstract forall context. -/
theorem TrExprS.canonicalBvars_of_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (n : Nat)
    (hn : n ≤ domains.length) :
    List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
      (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i))
      (List.ofFn fun i : Fin n => VExpr.bvar (n - 1 - i)) := by
  apply List.forall₂_of_getElem (by simp)
  intro i hsource htarget
  have hi : i < n := by simpa using hsource
  simp only [List.getElem_ofFn]
  apply TrExprS.bvar_of_abstractForallContext
  omega

theorem TrExprS.bvar_eq_of_abstractForallContext
    (H : TrExprS env Us (abstractForallContext domains Δ) (.bvar i) out)
    (hi : i < domains.length) : out = .bvar i := by
  cases H with
  | bvar hfind =>
    rcases abstractForallContext.find?_bvar domains Δ i hi with
      ⟨type, hcanonical⟩
    rw [hcanonical] at hfind
    exact (congrArg Prod.fst (Option.some.inj hfind)).symm

theorem TrExprS.foldl_bvars_eq
    (domains : List VExpr) (Δ : VLCtx)
    (args : List Nat) (hargs : ∀ i ∈ args, i < domains.length)
    (base : Expr) (vbase : VExpr)
    (hbase : ∀ out, TrExprS env Us (abstractForallContext domains Δ)
      base out → out = vbase)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (args.foldl (fun fn i => .app fn (.bvar i)) base) out) :
    out = args.foldl (fun fn i => .app fn (.bvar i)) vbase := by
  induction args generalizing base vbase with
  | nil => exact hbase out H
  | cons i args ih =>
    apply ih (fun j hj => hargs j (by simp [hj]))
      (.app base (.bvar i)) (.app vbase (.bvar i))
    · intro result Hresult
      cases Hresult with
      | app _ _ hfn harg =>
        rw [hbase _ hfn,
          TrExprS.bvar_eq_of_abstractForallContext harg
            (hargs i (by simp))]
    · exact H

/-- Binding a list of ordinary local declarations creates one concrete forall
per selected declaration and leaves precisely the simultaneous abstraction of
the selected free variables as its residual body. -/
theorem LocalContext.mkBindingList_forallTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (LocalContext.mkBindingList false lctx fvs body)
      fvs.length (body.abstractList fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.ForallTelescope
        (LocalContext.mkBindingList.go false lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingList.go]
      have htail := ih
        (LocalContext.mkBindingList1 false lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.ForallTelescope
          (LocalContext.mkBindingList1 false lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1, hfind]
        exact Expr.ForallTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractList fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- The production `LocalContext.mkForall` interface specialized to an
explicit list of free variables known to denote ordinary declarations. -/
theorem LocalContext.mkForall_fvars_forallTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (lctx.mkForall (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_forallTelescope hdecl

/-- A concrete expression consists of exactly `arity` leading lambda binders
and the indicated residual body. -/
inductive Expr.LambdaTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : LambdaTelescope body 0 body
  | cons : LambdaTelescope body arity result →
      LambdaTelescope (.lam name dom body bi) (arity + 1) result

/-- Two expressions have the same concrete leading lambda binders, while
their residual bodies may differ.  Generated recursive calls and the
eta-expanded fields used as their major premises are related in exactly this
way: production closes both over one shared local-context selection. -/
inductive Expr.SameLambdaPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameLambdaPrefix 0 left right
  | cons : Expr.SameLambdaPrefix n left right →
      Expr.SameLambdaPrefix (n + 1)
        (.lam name dom left bi) (.lam name dom right bi)

/-- A concrete forall telescope and lambda telescope use the same literal
binder prefix.  This is the source-syntax bridge used when a checked local
forall supplies the binder-domain translations for the eta-expanded lambda
over the same selected local declarations. -/
inductive Expr.SameForallLambdaPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameForallLambdaPrefix 0 forallBody lambdaBody
  | cons : Expr.SameForallLambdaPrefix n forallBody lambdaBody →
      Expr.SameForallLambdaPrefix (n + 1)
        (.forallE name dom forallBody bi) (.lam name dom lambdaBody bi)

theorem Expr.SameForallLambdaPrefix.abstract1
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody)
    (fv : FVarId) (k : Nat := 0) :
    Expr.SameForallLambdaPrefix n
      (forallBody.abstract1 fv k) (lambdaBody.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameForallLambdaPrefix.abstractList
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameForallLambdaPrefix n
      (forallBody.abstractList fvars k) (lambdaBody.abstractList fvars k) := by
  induction fvars generalizing forallBody lambdaBody k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Reuse the checked domain translations of a forall telescope to
translate a lambda telescope with the same literal source binder prefix.
Only the lambda residual is supplied independently. -/
theorem Expr.SameForallLambdaPrefix.translateLambda
    (Hsame : Expr.SameForallLambdaPrefix n forallSource lambdaSource)
    (HforallTelescope : Expr.ForallTelescope
      forallSource n forallResidual)
    (HlambdaTelescope : Expr.LambdaTelescope
      lambdaSource n lambdaResidual)
    (hdomains : domains.length = n)
    (Hforall : TrExprS env Us Delta forallSource
      (VExpr.wrapForalls domains forallTarget))
    (HlambdaResidual : TrExprS env Us
      (abstractForallContext domains Delta) lambdaResidual lambdaTarget) :
    TrExprS env Us Delta lambdaSource
      (VExpr.wrapLams domains lambdaTarget) := by
  induction Hsame generalizing domains Delta forallResidual lambdaResidual
      forallTarget lambdaTarget with
  | nil =>
    cases HforallTelescope
    cases HlambdaTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using HlambdaResidual
  | @cons n forallBody lambdaBody name dom bi Hsame ih =>
    cases HforallTelescope with
    | cons HforallTail =>
      cases HlambdaTelescope with
      | cons HlambdaTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Hforall with
          | forallE HdomainType _ HdomainTr HforallBody =>
            apply TrExprS.lam HdomainType HdomainTr
            have htail : domains.length = n := by simpa using hdomains
            simpa [VExpr.wrapLams, abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HforallTail HlambdaTail htail HforallBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HlambdaResidual)

theorem Expr.SameLambdaPrefix.symm
    (H : Expr.SameLambdaPrefix n left right) :
    Expr.SameLambdaPrefix n right left := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem Expr.SameLambdaPrefix.abstract1
    (H : Expr.SameLambdaPrefix n left right) (fv : FVarId) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.abstract1 fv k) (right.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameLambdaPrefix.abstractList
    (H : Expr.SameLambdaPrefix n left right)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.abstractList fvars k) (right.abstractList fvars k) := by
  induction fvars generalizing left right k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Substituting the same outer placeholder into two expressions preserves
their literal common lambda prefix.  Binder domains are transformed
identically; only the unrestricted residuals may differ. -/
theorem Expr.SameLambdaPrefix.instantiate1'
    (H : Expr.SameLambdaPrefix n left right)
    (value : Expr) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.instantiate1' value k) (right.instantiate1' value k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
      simp only [Expr.instantiate1']
      exact .cons (ih (k + 1))

/-- Outermost specialization of `Expr.SameLambdaPrefix.instantiate1'`. -/
theorem Expr.SameLambdaPrefix.instantiate1
    (H : Expr.SameLambdaPrefix n left right) (value : Expr) :
    Expr.SameLambdaPrefix n
      (left.instantiate1 value) (right.instantiate1 value) := by
  simpa [Expr.instantiate1_eq] using H.instantiate1' value 0

/-- Reuse the binder-domain part of one lambda translation with a different
residual body.  The two source telescopes share their concrete prefix, so the
template derivation supplies the exact translated domains and their type
proofs; only the independently translated residual is replaced. -/
theorem Expr.SameLambdaPrefix.replaceTranslatedResidual
    (Hsame : Expr.SameLambdaPrefix n template replacement)
    (HtemplateTelescope : Expr.LambdaTelescope template n templateResidual)
    (HreplacementTelescope :
      Expr.LambdaTelescope replacement n replacementResidual)
    (hdomains : domains.length = n)
    (Htemplate :
      TrExprS env Us Delta template (VExpr.wrapLams domains templateTarget))
    (HreplacementResidual :
      TrExprS env Us (abstractForallContext domains Delta)
        replacementResidual replacementTarget) :
    TrExprS env Us Delta replacement
      (VExpr.wrapLams domains replacementTarget) := by
  induction Hsame generalizing domains Delta templateResidual
      replacementResidual templateTarget replacementTarget with
  | nil =>
    cases HtemplateTelescope
    cases HreplacementTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using HreplacementResidual
  | @cons n left right name dom bi Hsame ih =>
    cases HtemplateTelescope with
    | cons HtemplateTail =>
      cases HreplacementTelescope with
      | cons HreplacementTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Htemplate with
          | lam HdomainType HdomainTr HtemplateBody =>
            have htail : domains.length = n := by simpa using hdomains
            apply TrExprS.lam HdomainType HdomainTr
            change TrExprS env Us ((none, .vlam domain) :: Delta) right
              (VExpr.wrapLams domains replacementTarget)
            simpa [abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HtemplateTail HreplacementTail htail HtemplateBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidual)

/-- Closing two bodies over the same list of ordinary local declarations
creates the same concrete lambda prefix. -/
theorem LocalContext.sameLambdaPrefix_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (left right : Expr) :
    Expr.SameLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 true lctx [] fv
            (result.abstract1 fv)) left)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 true lctx [] fv
            (result.abstract1 fv)) right) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1, hfind]
    exact Expr.SameLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstract1 fv)

/-- Closing one residual with foralls and another with lambdas over the same
ordinary declarations creates one literal cross-kind binder prefix. -/
theorem LocalContext.sameForallLambdaPrefix_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 false lctx [] fv
            (result.abstract1 fv)) forallBody)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 true lctx [] fv
            (result.abstract1 fv)) lambdaBody) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1, hfind]
    exact Expr.SameForallLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstract1 fv)

theorem Expr.LambdaTelescope.trans
    (Houter : Expr.LambdaTelescope outer outerArity middle)
    (Hinner : Expr.LambdaTelescope middle innerArity result) :
    Expr.LambdaTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.LambdaTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

/-- A concrete lambda expression and arity determine its telescope residual. -/
theorem Expr.LambdaTelescope.result_eq
    (Hleft : Expr.LambdaTelescope outer arity left)
    (Hright : Expr.LambdaTelescope outer arity right) : left = right := by
  induction Hleft generalizing right with
  | nil => cases Hright; rfl
  | cons Hleft ih =>
      cases Hright with
      | cons Hright => exact ih Hright

/-- Instantiating an outer loose variable preserves a concrete lambda
telescope.  In the residual the substitution depth is shifted past every
leading binder, exactly as it is when a closed recursive-call template is
instantiated with its final recursor prefix. -/
theorem Expr.LambdaTelescope.instantiate1'
    (H : Expr.LambdaTelescope outer arity result)
    (value : Expr) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.instantiate1' value k) arity
      (result.instantiate1' value (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
      simp only [Expr.instantiate1']
      apply Expr.LambdaTelescope.cons
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Specialization of `Expr.LambdaTelescope.instantiate1'` at the outermost
substitution depth. -/
theorem Expr.LambdaTelescope.instantiate1
    (H : Expr.LambdaTelescope outer arity result) (value : Expr) :
    Expr.LambdaTelescope (outer.instantiate1 value) arity
      (result.instantiate1' value arity) := by
  simpa [Expr.instantiate1_eq] using H.instantiate1' value 0

/-- Abstracting one free variable below a closed loose-variable boundary can
introduce at most the newly bound variable at that boundary. -/
theorem Expr.abstract1_looseBVarRange_le
    {e : Expr} {fv : FVarId} {k : Nat}
    : (e.abstract1 fv k).looseBVarRange' ≤
        max k e.looseBVarRange' + 1 := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1, Lean.Expr.looseBVarRange']; split <;> omega
  | fvar other =>
      simp only [Expr.abstract1]
      split <;> simp [Lean.Expr.looseBVarRange']
  | mvar | sort | const | lit => simp [Expr.abstract1, Lean.Expr.looseBVarRange']
  | app fn arg ihFn ihArg =>
      simp only [Expr.abstract1, Lean.Expr.looseBVarRange', Nat.max_le]
      constructor
      · exact Nat.le_trans (ihFn (k := k)) (by omega)
      · exact Nat.le_trans (ihArg (k := k)) (by omega)
  | mdata data body ih | proj _ _ body ih =>
      simpa [Expr.abstract1, Lean.Expr.looseBVarRange'] using ih (k := k)
  | lam name domain body bi ihDomain ihBody
  | forallE name domain body bi ihDomain ihBody =>
      simp only [Expr.abstract1, Lean.Expr.looseBVarRange', Nat.max_le]
      constructor
      · exact Nat.le_trans (ihDomain (k := k)) (by omega)
      · have Hbody := ihBody (k := k + 1)
        omega
  | letE name type value body nondep ihType ihValue ihBody =>
      simp only [Expr.abstract1, Lean.Expr.looseBVarRange', Nat.max_le]
      constructor
      · constructor
        · exact Nat.le_trans (ihType (k := k)) (by omega)
        · exact Nat.le_trans (ihValue (k := k)) (by omega)
      · have Hbody := ihBody (k := k + 1)
        omega

/-- Simultaneous free-variable abstraction raises a closed loose-variable
boundary by exactly the number of introduced binders. -/
theorem Expr.abstractList_looseBVarRange_le
    {e : Expr} {fvs : List FVarId} {k : Nat}
    : (e.abstractList fvs k).looseBVarRange' ≤
        max k e.looseBVarRange' + fvs.length := by
  induction fvs generalizing e k with
  | nil => exact Nat.le_max_right _ _
  | cons fv fvs ih =>
      simp only [Expr.abstractList, List.length_cons]
      have Hhead := Expr.abstract1_looseBVarRange_le
        (e := e) (fv := fv) (k := k)
      have Htail := ih (e := e.abstract1 fv k) (k := k)
      omega

/-- Application spines preserve a common loose-variable bound. -/
theorem Expr.mkAppN_looseBVarRange_le
    (Hfn : fn.looseBVarRange' ≤ k)
  (Hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ k) :
    (mkAppN fn args).looseBVarRange' ≤ k := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  have Hlist : ∀ arg ∈ args.toList, arg.looseBVarRange' ≤ k := by
    intro arg harg
    exact Hargs arg (Array.mem_toList_iff.mp harg)
  generalize args.toList = list at Hlist
  induction list generalizing fn with
  | nil => exact Hfn
  | cons arg rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · simpa [Lean.Expr.looseBVarRange', Nat.max_le] using
          And.intro Hfn (Hlist arg (by simp))
      · intro other hother
        exact Hlist other (by simp [hother])

@[simp] theorem Expr.instantiate1'_mkAppN :
    (mkAppN fn args).instantiate1' value k =
      mkAppN (fn.instantiate1' value k)
        (args.map fun arg => arg.instantiate1' value k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  rw [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg rest ih =>
      simp only [List.foldl_cons, List.map_cons, Expr.instantiate1']
      exact ih (fn := fn.app arg)

@[simp] theorem Expr.getAppFn_liftLooseBVars'
    {e : Expr} {start amount : Nat} :
    (e.liftLooseBVars' start amount).getAppFn =
      e.getAppFn.liftLooseBVars' start amount := by
  induction e generalizing start with
  | app fn arg ih => simpa [Expr.getAppFn, Expr.liftLooseBVars'] using ih
  | _ => rfl

theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_eq_self
    (H : Expr.ForallTelescope outer arity body)
    (hbody : body.consumeTypeAnnotationsVerified = body) :
    outer.consumeTypeAnnotationsVerified = outer := by
  cases H with
  | nil => exact hbody
  | cons H =>
    apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_eq_self_of_pos
    (H : Expr.ForallTelescope outer arity body) (hpos : 0 < arity) :
    outer.consumeTypeAnnotationsVerified = outer := by
  cases H with
  | nil => simp at hpos
  | cons _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

/-- Removing a possible top-level binder annotation preserves the number of
leading forall binders.  In the zero-binder case the residual may itself be
the annotation payload, so it is retained existentially. -/
theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_arity
    (H : Expr.ForallTelescope outer arity body) :
    ∃ residual, Expr.ForallTelescope outer.consumeTypeAnnotationsVerified
      arity residual := by
  cases H with
  | nil => exact ⟨_, .nil _⟩
  | @cons body arity result name dom bi Htail =>
      have houter :
          (Expr.forallE name dom body bi).consumeTypeAnnotationsVerified =
            Expr.forallE name dom body bi := by
        apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
      exact ⟨_, houter ▸ Expr.ForallTelescope.cons Htail⟩

theorem Expr.LambdaTelescope.abstract1
    (H : Expr.LambdaTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.LambdaTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.LambdaTelescope.abstractList
    (H : Expr.LambdaTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- A lambda telescope whose binder domains avoid a selected set of
constants.  The residual body is intentionally unrestricted: generated
recursive calls contain the newly installed recursor in that position. -/
inductive Expr.AvoidingLambdaTelescope (names : List Name) :
    Expr → Nat → Expr → Prop
  | nil (body : Expr) : AvoidingLambdaTelescope names body 0 body
  | cons : dom.AvoidsConsts names →
      AvoidingLambdaTelescope names body arity result →
      AvoidingLambdaTelescope names (.lam name dom body bi) (arity + 1)
        result

theorem Expr.AvoidingLambdaTelescope.toLambdaTelescope
    (H : Expr.AvoidingLambdaTelescope names outer arity result) :
    Expr.LambdaTelescope outer arity result := by
  induction H with
  | nil => exact .nil _
  | cons _ _ ih => exact .cons ih

/-- Avoidance is a property of the shared binder domains, not of the
unrestricted residual.  It therefore transports across an exact common
lambda prefix once the replacement telescope identifies its residual. -/
theorem Expr.SameLambdaPrefix.avoidingLambdaTelescope
    (Hsame : Expr.SameLambdaPrefix arity template replacement)
    (Htemplate : Expr.AvoidingLambdaTelescope names template arity
      templateResidual)
    (Hreplacement : Expr.LambdaTelescope replacement arity
      replacementResidual) :
    Expr.AvoidingLambdaTelescope names replacement arity
      replacementResidual := by
  induction Hsame generalizing templateResidual replacementResidual with
  | nil =>
      cases Htemplate
      cases Hreplacement
      exact .nil _
  | cons Hsame ih =>
      cases Htemplate with
      | cons hdomain HtemplateTail =>
        cases Hreplacement with
        | cons HreplacementTail =>
          exact .cons hdomain (ih HtemplateTail HreplacementTail)

theorem Expr.AvoidingLambdaTelescope.trans
    (Houter : Expr.AvoidingLambdaTelescope names outer outerArity middle)
    (Hinner : Expr.AvoidingLambdaTelescope names middle innerArity result) :
    Expr.AvoidingLambdaTelescope names outer (outerArity + innerArity)
      result := by
  induction Houter with
  | nil => simpa using Hinner
  | cons hdom Houter ih =>
    simpa [Nat.add_assoc, Nat.add_comm innerArity 1] using
      Expr.AvoidingLambdaTelescope.cons hdom (ih Hinner)

theorem Expr.AvoidingLambdaTelescope.abstract1
    (H : Expr.AvoidingLambdaTelescope names outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.AvoidingLambdaTelescope names (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons hdom H ih =>
    simp only [Expr.abstract1]
    apply Expr.AvoidingLambdaTelescope.cons (hdom.abstract1 fv k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.AvoidingLambdaTelescope.abstractList
    (H : Expr.AvoidingLambdaTelescope names outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.AvoidingLambdaTelescope names (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Translation of a lambda telescope retains its arity and exposes the
residual translation beneath precisely the corresponding abstract binders. -/
theorem TrExprS.lambdaTelescope_shape_with_context
    (Htel : Expr.LambdaTelescope e arity residual)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Δ)
        residual residual' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr⟩
  | @cons body arity residual name dom bi Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with
        ⟨domains, residual', hlength, heq, hresidual⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual

/-- Exact-target telescope inversion.  When the translated target is already
presented with the right number of lambdas, syntax-directedness exposes the
residual under precisely those domains, without introducing existentially
chosen replacements. -/
theorem TrExprS.lambdaTelescope_exact_residual
    (Htel : Expr.LambdaTelescope e arity residual)
    (hdomains : domains.length = arity)
    (Htr : TrExprS env Us Δ e (VExpr.wrapLams domains target)) :
    TrExprS env Us (abstractForallContext domains Δ) residual target := by
  induction Htel generalizing domains Δ with
  | nil =>
    have : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using Htr
  | @cons body arity residual name dom bi Htel ih =>
    cases domains with
    | nil => simp at hdomains
    | cons domain domains =>
      cases Htr with
      | @lam domain' body' =>
        rename_i _ _ _ hbody
        have htail : domains.length = arity := by simpa using hdomains
        simpa [abstractForallContext, List.map_append, List.append_assoc]
          using ih htail hbody

/-- The target domains exposed by a translated lambda telescope form a
well-formed extension of the starting verification context. -/
theorem TrExprS.lambdaTelescope_contextWF
    (Htel : Expr.LambdaTelescope e arity residual)
    (hdomains : domains.length = arity)
    (Htr : TrExprS env Us Δ e (VExpr.wrapLams domains target))
    (hDelta : Δ.WF env Us.length) :
    (abstractForallContext domains Δ).WF env Us.length := by
  induction Htel generalizing domains Δ with
  | nil =>
      have : domains = [] := List.eq_nil_of_length_eq_zero hdomains
      subst domains
      simpa [abstractForallContext] using hDelta
  | @cons body arity residual name dom bi Htel ih =>
      cases domains with
      | nil => simp at hdomains
      | cons domain domains =>
        cases Htr with
        | lam HdomainType _ HbodyTr =>
          have htail : domains.length = arity := by simpa using hdomains
          have hnext : VLCtx.WF env Us.length
              ((none, VLocalDecl.vlam domain) :: Δ) :=
            ⟨hDelta, by simp, HdomainType⟩
          simpa [abstractForallContext, List.reverse_cons,
            List.map_append, List.append_assoc] using
              ih htail HbodyTr hnext

/-- Post-installation telescope inversion driven by source-syntax absence.
Only binder domains are shown recursor-free; the residual is allowed to
contain the newly installed recursor constants. -/
theorem TrExprS.avoidingLambdaTelescope_shape_with_context
    (Htel : Expr.AvoidingLambdaTelescope names e arity residual)
    (hctx : VLCtx.NoIndConsts names Delta)
    (Htr : TrExprS env Us Delta e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Delta)
        residual residual' ∧
      ∀ dom ∈ domains, dom.SourceConstFree names := by
  have hctxSupport : checkPositivityStep.VLCtx.SourceConstFree names Delta :=
    checkPositivityStep.VLCtx.SourceConstFree.ofNoIndConsts
      (names := names) (Δ := Delta) hctx
  clear hctx
  induction Htel generalizing Delta e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr, by simp⟩
  | @cons dom body arity residual name bi hdom Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ hdomTr hbody
      have hdomFree :=
        checkPositivityStep.TrExprS.noConstsOfSourceAvoids
          hdom hctxSupport hdomTr
      have hctx' : checkPositivityStep.VLCtx.SourceConstFree names
          ((none, VLocalDecl.vlam dom') :: Delta) :=
        checkPositivityStep.VLCtx.SourceConstFree.cons
          (d := .vlam dom') (ofv := none) hctxSupport (.bvar 0)
      rcases ih hbody hctx' with
        ⟨domains, residual', hlength, heq, hresidual, hfree⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual
      · intro current hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact hdomFree
        · exact hfree current hmem

/-- Freshness-aware lambda-telescope inversion. Each translated binder domain
is retained as recursor-free at the point where the translation constructor
exposes it; the residual remains translated in the exact abstract context. -/
theorem TrExprS.lambdaTelescope_shape_with_context_noFresh
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (Htel : Expr.LambdaTelescope e arity residual)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Δ)
        residual residual' ∧
      ∀ dom ∈ domains, dom.SourceConstFree names := by
  have hctxSupport : checkPositivityStep.VLCtx.SourceConstFree names Δ :=
    checkPositivityStep.VLCtx.SourceConstFree.ofNoIndConsts
      (names := names) (Δ := Δ) hctx
  clear hctx
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr, by simp⟩
  | @cons body arity residual name dom bi Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ hdom hbody
      have hdomFree := checkPositivityStep.TrExprS.noFreshConsts
        hfresh hctxSupport hdom
      have hctx' : checkPositivityStep.VLCtx.SourceConstFree names
          ((none, VLocalDecl.vlam dom') :: Δ) :=
        checkPositivityStep.VLCtx.SourceConstFree.cons
          (d := .vlam dom') (ofv := none) hctxSupport (.bvar 0)
      rcases ih hbody hctx' with
        ⟨domains, residual', hlength, heq, hresidual, hfree⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual
      · intro current hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact hdomFree
        · exact hfree current hmem

/-- Binding ordinary local declarations with `mkLambda` creates one concrete
lambda per selected declaration and leaves simultaneous abstraction of those
free variables as the residual body. -/
theorem LocalContext.mkBindingList_lambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (LocalContext.mkBindingList true lctx fvs body)
      fvs.length (body.abstractList fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.LambdaTelescope
        (LocalContext.mkBindingList.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingList.go]
      have htail := ih
        (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.LambdaTelescope
          (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1, hfind]
        exact Expr.LambdaTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractList fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- The production `LocalContext.mkLambda` interface specialized to an
explicit array of ordinary local free variables. -/
theorem LocalContext.mkLambda_fvars_lambdaTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_lambdaTelescope hdecl

/-- Binder-aware counterpart retaining source-level absence for every
selected local declaration type. -/
theorem LocalContext.mkBindingList_avoidingLambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (havoid : ∀ fv index name type bi kind,
      fv ∈ fvs →
      lctx.find? fv = some (.cdecl index fv name type bi kind) →
      type.AvoidsConsts namesToAvoid) :
    Expr.AvoidingLambdaTelescope namesToAvoid
      (LocalContext.mkBindingList true lctx fvs body)
      fvs.length (body.abstractList fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      xs ⊆ fvs →
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.AvoidingLambdaTelescope namesToAvoid
        (LocalContext.mkBindingList.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _ _
      exact .nil _
    | cons fv xs ih =>
      intro current hsubset hxs
      rw [LocalContext.mkBindingList.go]
      have htail := ih
        (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
        (fun x hx => hsubset (by simp [hx]))
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.AvoidingLambdaTelescope namesToAvoid
          (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1, hfind]
        apply Expr.AvoidingLambdaTelescope.cons
        · exact (havoid fv index name type bi kind
            (hsubset (by simp)) hfind).abstractList xs.reverse
        · exact .nil _
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractList fvs) (by simp)
      (fun fv hfv => hdecl fv (by simpa using hfv))

theorem LocalContext.mkLambda_fvars_avoidingLambdaTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (havoid : ∀ fv index name type bi kind,
      fv ∈ fvs →
      lctx.find? fv = some (.cdecl index fv name type bi kind) →
      type.AvoidsConsts namesToAvoid) :
    Expr.AvoidingLambdaTelescope namesToAvoid
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_avoidingLambdaTelescope hdecl havoid

theorem LocalContext.mkBindingList_append_four
    (hdecl : ∀ fv ∈ ((as ++ bs) ++ cs) ++ ds,
      ∃ decl, lctx.find? fv = some decl)
    (hnodup : (((as ++ bs) ++ cs) ++ ds).Nodup) :
    LocalContext.mkBindingList isLambda lctx
        (((as ++ bs) ++ cs) ++ ds) body =
      LocalContext.mkBindingList isLambda lctx as
        (LocalContext.mkBindingList isLambda lctx bs
          (LocalContext.mkBindingList isLambda lctx cs
            (LocalContext.mkBindingList isLambda lctx ds body))) := by
  have habcd := List.nodup_append.mp hnodup
  have habc := List.nodup_append.mp habcd.1
  have hab := List.nodup_append.mp habc.1
  have hasDecl : ∀ fv ∈ as, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hbsDecl : ∀ fv ∈ bs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hcsDecl : ∀ fv ∈ cs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hdsDecl : ∀ fv ∈ ds, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  rw [LocalContext.mkBindingList_eq_fold hdecl hnodup,
    LocalContext.mkBindingList_eq_fold hasDecl hab.1,
    LocalContext.mkBindingList_eq_fold hbsDecl hab.2.1,
    LocalContext.mkBindingList_eq_fold hcsDecl habc.2.1,
    LocalContext.mkBindingList_eq_fold hdsDecl habcd.2.1]
  simp only [List.foldr_append]

/-- A selected executable array consists solely of ordinary free-variable
declarations in the retained local context. -/
structure LocalForallSelection (lctx : LocalContext) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  declarations : ∀ fv ∈ fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

/-- `LocalContext.mkLambda` uses one literal binder prefix for any two
residual bodies when it closes the same duplicate-free local selection. -/
theorem LocalForallSelection.sameLambdaPrefix
    (H : LocalForallSelection lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameLambdaPrefix xs.size
      (lctx.mkLambda xs left) (lctx.mkLambda xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkLambda, LocalContext.mkLambda,
    LocalContext.mkBinding_eq, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold hfind hnodup,
    LocalContext.mkBindingList_eq_fold hfind hnodup]
  simpa using LocalContext.sameLambdaPrefix_fold hdecl left right

/-- `mkForall` and `mkLambda` close two residuals with the same literal
ordinary-declaration prefix when they use the same duplicate-free local
selection. -/
theorem LocalForallSelection.sameForallLambdaPrefix
    (H : LocalForallSelection lctx xs)
    (hnodup : H.fvars.Nodup) (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix xs.size
      (lctx.mkForall xs forallBody) (lctx.mkLambda xs lambdaBody) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkLambda,
    LocalContext.mkBinding_eq, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold hfind hnodup,
    LocalContext.mkBindingList_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallLambdaPrefix_fold hdecl
    forallBody lambdaBody

/-- Operational form of a local selection, convenient to preserve while the
reader context is extended by generated binders. -/
structure BoundFVarArray (c : AddInductive.Context) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  members : ∀ fv ∈ fvars, fv ∈ c.lctx.fvars

def recursorFVarId : Expr → FVarId
  | .fvar fv => fv
  | _ => default

def ExprArrayFVarIds (xs : Array Expr) : List FVarId :=
  xs.toList.map recursorFVarId

theorem cachedParameterDecls_fvars
    {decls : VLCtx}
    (H : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl params decls) :
    ∃ fvars : List FVarId,
      params = fvars.map Expr.fvar ∧ decls.fvars = fvars := by
  induction H with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons param entry params decls Hhead _ ih =>
    rcases Hhead with ⟨fv, deps, type, rfl, rfl⟩
    rcases ih with ⟨fvars, hparams, hdecls⟩
    exact ⟨fv :: fvars, by simp [hparams], by simp [hdecls]⟩

/-- The declaration order of the retained parameter suffix is the reverse of
the executable parameter array's free-variable order. -/
theorem RecursorParameterContextSuffix.parameterDecls_fvars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    H.parameterDecls.fvars = (ExprArrayFVarIds stats.params).reverse := by
  rcases cachedParameterDecls_fvars H.cached with
    ⟨fvars, hparams, hdecls⟩
  rw [hdecls]
  have hids := congrArg (List.map recursorFVarId) hparams
  simpa [ExprArrayFVarIds, List.map_reverse, Function.comp_def,
    recursorFVarId] using hids.symm

/-- Close the independently cached parameter suffix outside an existing
anonymous inner telescope.  The source parameter order is supplied by the
same bound array used by recursor generation, while the target domains come
from the cache established during header checking. -/
theorem RecursorParameterContextSuffix.abstractParameters
    {c root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (Hparams : BoundFVarArray root stats.params)
    (hnodup : Hparams.fvars.Nodup)
    (Htr : TrExprS env Us
      (abstractForallContext domains H.parameterDecls) source target) :
    TrExprS env Us
      (abstractForallContext
        (H.parameterDecls.toCtx.reverse ++ domains) [])
      (source.abstractList Hparams.fvars domains.length) target := by
  have hparamExprs : stats.params.toList.reverse =
      Hparams.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList Hparams.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have Hcached : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl
      (Hparams.fvars.reverse.map Expr.fvar) H.parameterDecls := by
    have Hbase := H.cached
    rw [hparamExprs] at Hbase
    exact Hbase
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      Hparams.fvars.reverse H.parameterDecls := by
    rw [List.forall₂_map_left_iff] at Hcached
    exact Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have Hclosed := TrExprS.abstractFVarLambdaSuffix
    (domains := domains) Hdecls
      (List.nodup_reverse.mpr hnodup) Htr
  simp only [List.reverse_reverse] at Hclosed
  simpa using Hclosed

/-- The cached parameter identifiers form a dependency-closed subset of the
whole recursor context.  Generated motives and minors are newer ambient
declarations, so excluding them cannot hide a dependency of a parameter. -/
theorem RecursorParameterContextSuffix.parameterFVarsUp
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    IsFVarUpSet (fun fv => fv ∈ ExprArrayFVarIds stats.params)
      R.mlctx.vlctx := by
  have hwf : VLCtx.WF R.venv recLparams.length
      (H.ambientDecls ++ H.parameterDecls) := by
    rw [← H.context]
    exact R.mlctx_wf.tr.wf
  have hcached := IsFVarUpSet.suffixFVars H.parameterDecls
    H.ambientDecls hwf
  have hcongr : ∀ fv ∈
      (H.ambientDecls ++ H.parameterDecls).fvars,
      fv ∈ H.parameterDecls.fvars ↔
        fv ∈ ExprArrayFVarIds stats.params := by
    intro fv _
    rw [H.parameterDecls_fvars]
    simp
  have hconverted :=
    (IsFVarUpSet.congr hwf.fvwf hcongr).mp hcached
  simpa [H.context] using hconverted

/-- Typed form of `closedSortTranslation`.  Besides translating the cached
parameter telescope, it retains the abstract typehood needed to open those
domains as the base context of a later dependent telescope transport. -/
theorem RecursorParameterContextSuffix.closedSortTyped
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    let parameterMLCtx := R.mlctx.dropN depth H.depth_le
    TrExprS R.venv recLparams []
        (R.mlctx.lctx.mkForall stats.params
          (.sort (.zero : Level)))
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) ∧
      R.venv.IsType recLparams.length []
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) := by
  let parameterMLCtx := R.mlctx.dropN depth H.depth_le
  have hparameterWF : parameterMLCtx.WF R.venv recLparams := by
    simpa [parameterMLCtx] using R.mlctx_wf.dropN depth H.depth_le
  have hparameterOnly : MLCtxOnlyLams parameterMLCtx := by
    simpa [parameterMLCtx] using R.onlyLams.dropN depth H.depth_le
  have hparameterCtx : parameterMLCtx.vlctx = H.parameterDecls := by
    simpa [parameterMLCtx] using H.dropAmbient_vlctx
  have hparams : stats.params.toList.reverse =
      (parameterMLCtx.fvarRevList parameterMLCtx.length
        (Nat.le_refl _)).map Expr.fvar := by
    rcases cachedParameterDecls_fvars H.cached with
      ⟨fvars, hsource, hscope⟩
    rw [TypeChecker.MLCtx.fvarRevList_all, hparameterCtx, hscope]
    exact hsource
  have hparamsArray : stats.params =
      (parameterMLCtx.vlctx.fvars.reverse.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    rw [TypeChecker.MLCtx.fvarRevList_all] at hparams
    have hforward := congrArg List.reverse hparams
    simpa [List.map_reverse] using hforward
  have hlocalSource : R.mlctx.lctx.mkForall stats.params
        (.sort (.zero : Level)) =
      parameterMLCtx.lctx.mkForall stats.params
        (.sort (.zero : Level)) := by
    rw [hparamsArray, LocalContext.mkForall, LocalContext.mkForall,
      LocalContext.mkBinding_eq, LocalContext.mkBinding_eq]
    apply LocalContext.mkBindingList_congr
    intro fv hfv
    apply R.onlyLams.dropN_find?_eq R.mlctx_wf depth H.depth_le
    exact List.mem_reverse.mp hfv
  have hsource : parameterMLCtx.lctx.mkForall stats.params
        (.sort (.zero : Level)) =
      parameterMLCtx.mkForall parameterMLCtx.length (Nat.le_refl _)
        (.sort (.zero : Level)) :=
    hparameterWF.mkForall_eq parameterMLCtx.length (Nat.le_refl _) hparams
  have hzero : VLevel.ofLevel recLparams (.zero : Level) =
      some (.zero : VLevel) := rfl
  have hsort : TrExprS R.venv recLparams parameterMLCtx.vlctx
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have hsortType : R.venv.IsType recLparams.length
      parameterMLCtx.vlctx.toCtx (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  have hclosed := hparameterWF.mkForall_trS R.checking.tr.wf
    hsort hsortType parameterMLCtx.length (Nat.le_refl _)
  have hdomains := hparameterOnly.forallDomains_eq_take_reverse
    parameterMLCtx.length (Nat.le_refl _)
  have hparameterLength : parameterMLCtx.length =
      H.parameterDecls.length := by
    rw [← TypeChecker.MLCtx.vlctx_length, hparameterCtx]
  have htake : H.parameterDecls.toCtx.take parameterMLCtx.length =
      H.parameterDecls.toCtx := by
    have htoCtxLength : H.parameterDecls.toCtx.length =
        H.parameterDecls.length :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        H.cached
    apply List.take_of_length_le
    rw [htoCtxLength, ← hparameterLength]
    exact Nat.le_refl _
  rw [TypeChecker.MLCtx.dropN_all, ← hsource] at hclosed
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, hdomains] at hclosed
  rw [hparameterCtx, htake] at hclosed
  rw [hlocalSource]
  exact hclosed

/-- A deliberately trivial body can be closed over the exact cached
parameter declarations.  This supplies an independently translated source
telescope whose prefix can be compared with any production telescope built
from the same parameter selection. -/
theorem RecursorParameterContextSuffix.closedSortTranslation
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    let parameterMLCtx := R.mlctx.dropN depth H.depth_le
    TrExprS R.venv recLparams []
      (R.mlctx.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) :=
  H.closedSortTyped.1

/-- The exact cached-parameter suffix reconstructed by header checking is
the bound, duplicate-free parameter array consumed by `mkRecInfos`. -/
def checkInductiveTypes.loopType.ParameterContextSuffix.paramsBound
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc stats depth) :
    BoundFVarArray c stats.params := by
  refine {
    fvars := ExprArrayFVarIds stats.params
    expressions := ?_
    members := ?_ }
  · rw [← Array.toList_inj]
    rcases cachedParameterDecls_fvars H.cached with
      ⟨reversedFVars, hparamsRev, hscopeFVars⟩
    have hreverse := congrArg List.reverse hparamsRev
    have hparams : stats.params.toList =
        reversedFVars.reverse.map Expr.fvar := by
      simpa [List.map_reverse] using hreverse
    change stats.params.toList =
      (ExprArrayFVarIds stats.params).map Expr.fvar
    rw [ExprArrayFVarIds, hparams]
    simp [recursorFVarId, Function.comp_def]
  · intro fv hfv
    rcases cachedParameterDecls_fvars H.cached with
      ⟨reversedFVars, hparamsRev, hscopeFVars⟩
    have hreverse := congrArg List.reverse hparamsRev
    have hparams : stats.params.toList =
        reversedFVars.reverse.map Expr.fvar := by
      simpa [List.map_reverse] using hreverse
    have hparameter : fv ∈ H.parameterDecls.fvars := by
      rw [hscopeFVars]
      change fv ∈ ExprArrayFVarIds stats.params at hfv
      rw [ExprArrayFVarIds, hparams] at hfv
      simpa [recursorFVarId, Function.comp_def] using hfv
    have hfull : fv ∈ Hc.mlctx.vlctx.fvars := by
      rw [H.context, VLCtx.fvars_append]
      exact List.mem_append_right _ hparameter
    rw [← Hc.mlctx_wf.tr.fvars_eq, Hc.lctx_eq] at hfull
    exact hfull

theorem checkInductiveTypes.loopType.ParameterContextSuffix.paramsBound_nodup
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc stats depth) :
    (H.paramsBound (c := c)).fvars.Nodup := by
  change (ExprArrayFVarIds stats.params).Nodup
  rcases cachedParameterDecls_fvars H.cached with
    ⟨reversedFVars, hparamsRev, hscopeFVars⟩
  have hreverse := congrArg List.reverse hparamsRev
  have hparams : stats.params.toList =
      reversedFVars.reverse.map Expr.fvar := by
    simpa [List.map_reverse] using hreverse
  have hfull := Hc.mlctx_wf.fvars_nodup
  rw [H.context, VLCtx.fvars_append] at hfull
  have hparameter : H.parameterDecls.fvars.Nodup :=
    (List.nodup_append.mp hfull).2.1
  rw [hscopeFVars] at hparameter
  rw [ExprArrayFVarIds, hparams]
  simpa [recursorFVarId, Function.comp_def] using
    (List.nodup_reverse.2 hparameter)

structure BindingContextLE (c c' : AddInductive.Context) : Prop where
  fvars : c.lctx.fvars ⊆ c'.lctx.fvars
  declarations : ∀ fv ∈ c.lctx.fvars,
    c'.lctx.find? fv = c.lctx.find? fv
  env_eq : c'.env = c.env
  lparams_eq : c'.lparams = c.lparams
  safety_eq : c'.safety = c.safety
  allowPrimitive_eq : c'.allowPrimitive = c.allowPrimitive
  fuel_eq : c'.fuel = c.fuel

instance : CoeFun (BindingContextLE c c') fun _ =>
    ∀ ⦃fv⦄, fv ∈ c.lctx.fvars → fv ∈ c'.lctx.fvars where
  coe H := H.fvars

theorem BindingContextLE.refl (c : AddInductive.Context) :
    BindingContextLE c c :=
  ⟨fun _ => id, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BindingContextLE.trans
    (H₁ : BindingContextLE c₁ c₂) (H₂ : BindingContextLE c₂ c₃) :
    BindingContextLE c₁ c₃ :=
  ⟨fun _ h => H₂ (H₁ h),
    fun fv hfv => (H₂.declarations fv (H₁ hfv)).trans
      (H₁.declarations fv hfv),
    H₂.env_eq.trans H₁.env_eq,
    H₂.lparams_eq.trans H₁.lparams_eq,
    H₂.safety_eq.trans H₁.safety_eq,
    H₂.allowPrimitive_eq.trans H₁.allowPrimitive_eq,
    H₂.fuel_eq.trans H₁.fuel_eq⟩

/-- `BindingContextLE` records the executable fields that affect local
binder identity and lookup.  The embedded typechecker's active universe
parameter list is tracked separately by `RecursorContextWF`, so changing it
on either endpoint preserves this relation definitionally. -/
theorem BindingContextLE.rebaseTypeCheckerLParams
    (H : BindingContextLE c c')
    (lparams lparams' : Option (List Name)) :
    BindingContextLE
      { c with typeCheckerLParams := lparams }
      { c' with typeCheckerLParams := lparams' } :=
  ⟨H.fvars, H.declarations, H.env_eq, H.lparams_eq, H.safety_eq,
    H.allowPrimitive_eq, H.fuel_eq⟩


end VerifyInductive
end Lean4Lean
