import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Expr.Abstraction
import Lean4Lean.Verify.Typing.Telescope

/-! # Translation lemmas

Lemmas about the translation relations `TrExprS` and `TrExpr`: uniqueness, forall telescopes and
their domains, application spines, universe substitution and alignment across convertible
contexts.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-- Translations are preserved by the executable's non-reducing level substitution
(`instantiateLevelParamsCore' false`), provided it agrees with the abstract instantiation
`ls` on every level of the source. Because the substitution does not simplify, the other
universe expressions of the term are kept as they are. -/
theorem TrExprS.substLevelParamsCore
    (hΔ : VLCtx.WF env ps.length Δ)
    (hls : ∀ level ∈ ls, level.WF Us.length)
    (hlevels : ∀ u u', VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F false) = some (u'.inst ls))
    (H : TrExprS env ps Δ e e') :
    TrExprS env Us (Δ.instL ls) (Expr.instantiateLevelParamsCore' false F e)
      (e'.instL ls) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (hlevels _ _ hlevel)
  | @const _ _ sourceLevels targetLevels info hlookup hlevel harity =>
    apply TrExprS.const hlookup ?_ (by simpa using harity)
    have Hmap := List.mapM_eq_some.mp hlevel
    apply List.mapM_eq_some.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun u u' hu => hlevels u u' hu) Hmap
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hls)
      (VLCtx.instL_toCtx _ ▸ harg.instL hls) (ihFn hΔ) (ihArg hΔ)
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hls)
      (ihTy hΔ) (ihVal hΔ) (ihBody ⟨hΔ, nofun, hval⟩)
  | lit hlit _ ih =>
    exact .lit hlit (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ hproj ih =>
    exact .proj (ih hΔ) (VLCtx.instL_toCtx _ ▸ hproj.instL hls)

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Invert the syntax-directed part of a translated forall while retaining the
definitional equality introduced by normalization.  Header and constructor
loops use this after `whnf`: the kernel expression is syntactically a
forall, but its abstract translation need only be definitionally equal to one. -/
theorem TrExpr.forallE_source
    (H : TrExpr env Us Δ (.forallE name dom body bi) type') :
    ∃ dom' body',
      TrExprS env Us Δ dom dom' ∧
      TrExprS env Us ((none, .vlam dom') :: Δ) body body' ∧
      env.IsType Us.length Δ.toCtx dom' ∧
      env.IsType Us.length (dom' :: Δ.toCtx) body' ∧
      env.IsDefEqU Us.length Δ.toCtx (.forallE dom' body') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | forallE HdomType HbodyType Hdom Hbody =>
    exact ⟨_, _, Hdom, Hbody, HdomType, HbodyType, Hdefeq⟩

/-- Invert a kernel sort after normalization, retaining both its universe
translation and its definitional equality to the abstract source tail. -/
theorem TrExpr.sort_source
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEqU Us.length Δ.toCtx (.sort level') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | sort Hlevel => exact ⟨_, Hlevel, Hdefeq⟩

/-- A translated kernel sort pins the type of the abstract conversion to
the successor sort, not merely to an existentially hidden type. -/
theorem TrExpr.sort_result
    (henv : VEnv.WF env) (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEq Us.length Δ.toCtx type' (.sort level')
        (.sort (.succ level')) := by
  rcases TrExpr.sort_source H with ⟨level', hlevel, typeEq⟩
  exact ⟨level', hlevel, typeEq.symm.of_r henv hctx
    (.sort (.of_ofLevel hlevel))⟩

/-- Aggregates the final `ensureSort` translation with the independently
recorded parameter/index telescope into the public `TypeShape` judgment. -/
theorem TrExpr.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : Δ.toCtx = indices.reverse ++ ownParams.reverse)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars, hctxEq] using hresult⟩

/-- Context-conversion form of `typeShape`.  This is the form needed by the
executable telescope because annotation consumption changes binder domains
definitionally, while preserving the same de Bruijn context shape. -/
theorem TrExpr.typeShapeOfDefEqCtx
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx env Us.length []
      (indices.reverse ++ ownParams.reverse) Δ.toCtx)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hresult' := hresult.defeqDFC henv.ordered (hctxEq.symm henv.orderedStrong)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hresult'⟩

section ScopeAlignment
variable {env : VEnv} {Us : List Name} {scope chk : VLCtx}

/-- A checker-context result whose input is aligned with a scope transfers
back to that scope, retargeted at the scope translation of the input. -/
theorem _root_.Lean4Lean.TrExpr.alignBack (henv : env.WF)
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hin : TrExprS env Us scope input nt)
    (hin₀ : TrExprS env Us chk input t₀)
    (hres : TrExpr env Us chk result t₀) :
    TrExpr env Us scope result nt := by
  rcases hres with ⟨r₀, hr₀, hr₀eq⟩
  have hsym := h.symm henv.orderedStrong
  obtain ⟨r, hr⟩ := hr₀.defeqDFC henv hsym
  have hu := hr₀.uniq henv hsym hr
  have hctx := h.defeqCtx.symm henv.orderedStrong
  have hu' := hu.defeqDFC henv.ordered hctx
  have heq' := hr₀eq.defeqDFC henv.ordered hctx
  have hinU := hin.uniq henv h hin₀
  exact ⟨r, hr, (hu'.symm.trans henv h.wf.toCtx heq').trans henv h.wf.toCtx
    hinU.symm⟩

/-- A scope translation transfers to an aligned checker context. -/
theorem _root_.Lean4Lean.TrExprS.alignTo (henv : env.WF)
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hs : TrExprS env Us scope e a) :
    ∃ b, TrExprS env Us chk e b ∧ env.IsDefEqU Us.length scope.toCtx a b := by
  obtain ⟨b, hb⟩ := hs.defeqDFC henv h
  exact ⟨b, hb, hs.uniq henv h hb⟩

end ScopeAlignment

/-- Inverse of `TrExprS.abstract`: a bound variable standing for an abstracted
free variable may be instantiated back with that free variable. -/
theorem _root_.Lean4Lean.TrExprS.instantiateFVar {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (hfresh : v₀ ∉ Δ₀.fvars)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ₁ (e.instantiate1' (.fvar v₀) dk) e' := by
  induction H generalizing dk k Δ₁ with
  | @bvar _ _ _ i h1 =>
    have h := W.find? (v := .inl i) (by nofun)
    simp only at h
    rw [h] at h1
    simp only [Expr.instantiate1']
    by_cases hi : i < dk
    · rw [if_pos hi] at h1 ⊢
      exact .bvar h1
    · rw [if_neg hi] at h1 ⊢
      by_cases hd : i = dk
      · rw [if_pos hd] at h1 ⊢
        simpa [Expr.liftLooseBVars'] using (TrExprS.fvar h1 : TrExprS env Us Δ₁ _ _)
      · rw [if_neg hd] at h1 ⊢
        exact .bvar h1
  | @fvar _ _ _ fv h1 =>
    have hne : fv ≠ v₀ := by
      intro heq
      apply hfresh
      have hmem := VLCtx.find?_eq_some.1 ⟨_, h1⟩
      rw [W.fvars_eq.2, heq] at hmem
      exact hmem
    have h := W.find? (v := .inr fv) (by simpa using hne)
    simp only at h
    rw [h] at h1
    simp only [Expr.instantiate1']
    exact .fvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W.succ)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 W.succ)
  | lit h1 _ ih =>
    have := ih W
    rw [Expr.instantiate1'_eq_self Closed.toConstructor.looseBVarRange_le] at this
    simp only [Expr.instantiate1']
    exact .lit h1 this
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (W.toCtx ▸ h2)

/-- Pointwise syntax-directed translation uniqueness, lifted to an aligned
list of source expressions. -/
theorem TrExprS.forall₂_unique
    (Hctx : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H₁ : List.Forall₂ (TrExprS env Us Δ₁) sources targets₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ₂) sources targets₂) :
    targets₁ = targets₂ := by
  induction H₁ generalizing targets₂ with
  | nil => cases H₂; rfl
  | cons Hhead _ ih =>
    let .cons Hhead₂ Htail₂ := H₂
    rw [Hhead.uniqueCtx Hctx Hhead₂, ih Htail₂]

/-- The translation of a constant-headed application is not a binder. -/
theorem TrExprS.forallArity_eq_zero_of_const_head {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} {name : Name} {levels : List Level}
    (H : TrExprS env Us Δ e e') (hhead : e.getAppFn = .const name levels) :
    e'.forallArity = 0 := by
  cases e with
  | const => cases H; rfl
  | app => cases H; rfl
  | _ => simp [Expr.getAppFn] at hhead

/-- Translation preserves the binder count of a pure forall spine. -/
theorem TrExprS.forallArity_of_spine {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} {k : Nat}
    (Hspine : Expr.ForallSpine e k) (H : TrExprS env Us Δ e e') : e'.forallArity = k := by
  induction Hspine generalizing Δ e' with
  | codomain hhead => exact TrExprS.forallArity_eq_zero_of_const_head H hhead
  | step _ ih =>
    cases H with
    | forallE _ _ _ hbody => simp [VExpr.forallArity, ih hbody]

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
attribute [local simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj

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

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Opening two closed terms at different de Bruijn depths commutes, with
the outer depth decreasing by one once the inner binder is instantiated. -/
theorem Expr.instantiate1'_instantiate1'_closed
    (e outer inner : Expr) (j d : Nat)
    (houter : outer.Closed 0) (hinner : inner.Closed 0) :
    (e.instantiate1' outer (j + d + 1)).instantiate1' inner j =
      (e.instantiate1' inner j).instantiate1' outer (j + d) := by
  induction e generalizing j with
  | bvar i =>
    simp only [Expr.instantiate1']
    repeat' first | split
    all_goals try simp only [Expr.instantiate1']
    all_goals repeat' first | split
    all_goals try rw [Expr.liftLooseBVars_eq_self
      houter.looseBVarRange_le]
    all_goals try rw [Expr.liftLooseBVars_eq_self
      hinner.looseBVarRange_le]
    all_goals try rfl
    all_goals try exact Expr.instantiate1'_eq_self (by
      simpa using houter)
    all_goals try exact (Expr.instantiate1'_eq_self (by
      simpa using hinner)).symm
    all_goals try { exfalso; omega }
    · have hclosed := hinner.looseBVarRange_le
      symm
      exact Expr.instantiate1'_eq_self
        (Nat.le_trans hclosed (Nat.zero_le (j + d)))
    · have hclosed := houter.looseBVarRange_le
      rw [Expr.liftLooseBVars_eq_self hclosed]
      exact Expr.instantiate1'_eq_self
        (Nat.le_trans hclosed (Nat.zero_le j))
  | fvar | mvar | sort | const | lit => rfl
  | app fn arg ihFn ihArg =>
    simp only [Expr.instantiate1']
    rw [ihFn, ihArg]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1']
    rw [ihDom]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1']
    rw [ihDom]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.instantiate1']
    rw [ihTy, ihValue]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | mdata md body ihBody =>
    simp only [Expr.instantiate1']
    rw [ihBody]
  | proj name idx body ihBody =>
    simp only [Expr.instantiate1']
    rw [ihBody]

/-- Opening one closed outer argument below a reverse simultaneous block of
closed inner arguments commutes with opening that block. -/
theorem Expr.instantiateRevList_instantiate1'_closed
    (e arg : Expr) (args : List Expr) (k d : Nat := 0)
    (harg : arg.Closed 0)
    (hargs : ∀ item ∈ args, item.Closed 0) :
    (e.instantiate1' arg (k + args.length + d)).instantiateRevList args k =
      (e.instantiateRevList args k).instantiate1' arg (k + d) := by
  induction args generalizing d with
  | nil => simp
  | cons head tail ih =>
    simp only [List.length_cons, Expr.instantiateRevList]
    rw [show k + (tail.length + 1) + d =
      k + tail.length + (d + 1) by omega]
    rw [ih (d + 1) (by
      intro item hitem
      exact hargs item (by simp [hitem]))]
    exact Expr.instantiate1'_instantiate1'_closed _ _ _ k d harg
      (hargs head (by simp))

/-- For closed arguments, the source-side instantiation of a forall body used along a
translated forall telescope is Lean's reverse simultaneous instantiation
`instantiateRevList`. -/
theorem Expr.instantiateForallBody_eq_instantiateRevList
    (body : Expr) (args : List Expr)
    (hargs : ∀ arg ∈ args, arg.Closed 0) :
    Expr.instantiateForallBody body args =
      body.instantiateRevList args := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.instantiateForallBody, Expr.instantiateRevList]
    have htail : ∀ item ∈ args, item.Closed 0 := by
      intro item hitem
      exact hargs item (by simp [hitem])
    calc
      Expr.instantiateForallBody
          (body.instantiate1' arg args.length) args =
        (body.instantiate1' arg args.length).instantiateRevList args :=
          ih _ htail
      _ = (body.instantiateRevList args).instantiate1' arg := by
        simpa using Expr.instantiateRevList_instantiate1'_closed
          body arg args 0 0 (hargs arg (by simp)) htail

/-- Substitute one translated argument, typed at the first domain, into a forall
telescope translation. The result is rebuilt from the instantiated whole type, so the
source and abstract residuals stay at the same binder depth. -/
theorem Expr.ForallTelescopeTypeTranslation.inst
    (henv : env.OrderedStrong)
    (HargType : env.HasType Us.length Δ.toCtx argTarget domainTarget)
    (Harg : TrExprS env Us Δ arg argTarget)
    (H : Expr.ForallTelescopeTypeTranslation env Us
      ((none, .vlam domainTarget) :: Δ) source arity target) :
    Expr.ForallTelescopeTypeTranslation env Us Δ
      (source.instantiate1' arg) arity (target.inst argTarget) := by
  rcases H.telescope with ⟨residual, Htelescope⟩
  have Htelescope' := Htelescope.instantiate1' arg 0
  have Htranslation := H.translation.inst henv HargType Harg
  have Htype := H.isType.instN henv .zero HargType
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope' Htranslation Htype

/-- Apply a function of the translated type to translated dependent arguments,
instantiating the source and abstract forall telescopes in lockstep. The instantiated
source residual translates to the abstract residual type, and the abstract application
has that type. -/
theorem Expr.ForallTelescopeTypeTranslation.applyTranslatedArguments
    (henv : env.WF)
    (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ sourceType
      sourceArgs.length targetType)
    (Htelescope : Expr.ForallTelescope sourceType sourceArgs.length
      sourceResidual)
    (Hfn : env.HasType Us.length Δ.toCtx fnTarget targetType)
    (Hargs : List.Forall₂ (TrExprS env Us Δ) sourceArgs targetArgs)
    (Happs : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps fnTarget targetArgs)) :
    TrExprS env Us Δ
        (Expr.instantiateForallBody sourceResidual sourceArgs)
        (VExpr.applyForallType targetType targetArgs) ∧
      env.HasType Us.length Δ.toCtx
        (VExpr.mkApps fnTarget targetArgs)
        (VExpr.applyForallType targetType targetArgs) := by
  induction Hargs generalizing sourceType targetType fnTarget sourceResidual with
  | nil =>
    cases H with
    | nil Htranslation _Htype =>
      cases Htelescope
      simpa [Expr.instantiateForallBody, VExpr.applyForallType,
        VExpr.mkApps] using And.intro Htranslation Hfn
  | @cons sourceArg targetArg sourceArgs targetArgs Harg Hargs ih =>
    cases H with
    | @cons _ domainSource domainTarget bodySource arity bodyTarget name bi
        Hdomain HdomainType Hbody =>
      cases Htelescope with
      | cons Htail =>
        have HargType := VEnv.HasType.mkApps_head henv hctx Hfn Happs
        have Hbody' := Hbody.inst henv.orderedStrong HargType Harg
        have Htail' := Htail.instantiate1' sourceArg 0
        have Hfn' : env.HasType Us.length Δ.toCtx
            (.app fnTarget targetArg) (bodyTarget.inst targetArg) :=
          Hfn.app HargType
        have Happs' : VExpr.WF env Us.length Δ.toCtx
            (VExpr.mkApps (.app fnTarget targetArg) targetArgs) := by
          simpa [VExpr.mkApps] using Happs
        have Hresult := ih Hbody' Htail' Hfn' Happs'
        simpa [Expr.instantiateForallBody, VExpr.applyForallType,
          VExpr.mkApps] using Hresult

end VerifyInductive

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The domain of binder `i` of a telescope translating to `wrapForalls domains result`
translates to `domains[i]` over the context extended by the first `i` domains. -/
theorem Expr.ForallBinderAt.translation
    (Hb : Expr.ForallBinderAt source i domain)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (hi : i < domains.length) :
    TrExprS env Us (abstractForallContext (domains.take i) Δ) domain domains[i] := by
  induction Hb generalizing Δ domains result with
  | here =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ Hdom _ => simpa [abstractForallContext] using Hdom
  | @there body i domain name outerDomain bi Hb ih =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ _ Hbody =>
        have ht := ih Hbody (by simpa using hi)
        simpa [abstractForallContext, List.map_append, List.append_assoc] using ht

theorem TrExprS.const_bvarSpine_eq
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some vlevels)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i))) target)
    (hn : n ≤ domains.length) :
    target = VExpr.mkApps (.const name vlevels) (bvarSpine n) := by
  let args := List.ofFn fun i : Fin n => n - 1 - i
  have hargs : ∀ i ∈ args, i < domains.length := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    have := j.isLt
    omega
  have hsource : Expr.mkAppList (.const name levels)
      (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.foldl (fun fn i => .app fn (.bvar i)) (.const name levels) := by
    rw [show (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.map Expr.bvar by simp [args, List.map_ofFn, Function.comp_def]]
    simp [Expr.mkAppList_eq_foldl, List.foldl_map]
  rw [hsource] at Htr
  have heq := TrExprS.foldl_bvars_eq domains Δ args hargs (.const name levels)
    (.const name vlevels) (fun out Hconst => by
      cases Hconst with
      | const _ hlevels _ =>
        rw [Hlevels] at hlevels
        cases Option.some.inj hlevels
        rfl) Htr
  have htargets : bvarSpine n = args.map VExpr.bvar := by
    simp [bvarSpine_eq_ofFn, args, List.map_ofFn, Function.comp_def]
  simpa [VExpr.mkApps, htargets, List.foldl_map] using heq

/-- A translation of a telescope to `wrapForalls domains result` restricts to a translation of
its first `n` domains (`Expr.forallDomainsOnly`) to `wrapForalls domains Prop`, which is a type. -/
theorem TrExprS.forallDomainsOnly
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result)) :
    TrExprS env Us Δ (Expr.forallDomainsOnly n source)
        (VExpr.wrapForalls domains (.sort .zero)) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains (.sort .zero)) := by
  induction Htel generalizing domains Δ result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    exact ⟨.sort rfl, ⟨_, .sort trivial⟩⟩
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons domain domains =>
      cases Htr with
      | forallE HdomType _ Hdom Hbody =>
        obtain ⟨Hbody', HbodyType⟩ := ih (by simpa using hlen) Hbody
        exact ⟨.forallE HdomType HbodyType Hdom Hbody', .forallE HdomType HbodyType⟩

theorem TrExprS.forallPrefixContextEq
    (henv : env.WF) (Htel : Expr.ForallTelescope source n residual)
    (hlen₁ : domains₁.length = n) (hlen₂ : domains₂.length = n)
    (Htr₁ : TrExprS env Us Δ₁ source (VExpr.wrapForalls domains₁ result₁))
    (Htr₂ : TrExprS env Us Δ₂ source (VExpr.wrapForalls domains₂ result₂))
    (Hctx : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) :
    VLCtx.IsDefEq env Us.length (abstractForallContext domains₁ Δ₁)
      (abstractForallContext domains₂ Δ₂) := by
  induction Htel generalizing Δ₁ Δ₂ domains₁ domains₂ result₁ result₂ with
  | nil =>
    have hnil₁ := List.eq_nil_of_length_eq_zero hlen₁
    have hnil₂ := List.eq_nil_of_length_eq_zero hlen₂
    subst domains₁ domains₂
    simpa [abstractForallContext] using Hctx
  | cons Htel ih =>
    cases domains₁ with
    | nil => simp at hlen₁
    | cons dom₁ domains₁ =>
      cases domains₂ with
      | nil => simp at hlen₂
      | cons dom₂ domains₂ =>
        cases Htr₁ with
        | forallE HdomType₁ _ Hdom₁ Hbody₁ =>
          cases Htr₂ with
          | forallE _ _ Hdom₂ Hbody₂ =>
            have Heq := Hdom₁.uniq henv Hctx Hdom₂
            have Hnext : VLCtx.IsDefEq env Us.length
                ((none, .vlam dom₁) :: Δ₁) ((none, .vlam dom₂) :: Δ₂) :=
              .cons Hctx nofun (.vlam (Heq.of_l henv Hctx.wf.toCtx HdomType₁.choose_spec))
            simpa [abstractForallContext, List.map_append, List.append_assoc] using
              ih (by simpa using hlen₁) (by simpa using hlen₂) Hbody₁ Hbody₂ Hnext

theorem TrExprS.forallTelescope_residual_typed
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (Htype : env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result)) :
    TrExprS env Us (abstractForallContext domains Δ) residual result ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx result := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Htr Htype
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htr with
      | forallE _ HbodyType _ Hbody =>
        simpa [abstractForallContext, List.map_append, List.append_assoc] using
          ih (by simpa using hlen) Hbody HbodyType

/-- If the first `n` domains of `source` (closed with `Prop`, `Expr.forallDomainsOnly`)
translate to `domains`, and the residual after them translates to a type `result` in the
context extended by `domains`, then `source` translates to `wrapForalls domains result`, which
is a type. -/
theorem TrExprS.rebuildForallPrefix
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htemplate : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls domains (.sort .zero)))
    (Hres : TrExprS env Us (abstractForallContext domains Δ) residual result)
    (HresType : env.IsType Us.length (abstractForallContext domains Δ).toCtx result) :
    TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Hres HresType
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htemplate with
      | forallE HdomType _ Hdom Hbody =>
        obtain ⟨Hbody', HbodyType⟩ := ih (by simpa using hlen) Hbody
          (by simpa [abstractForallContext, List.map_append, List.append_assoc] using Hres)
          (by simpa [abstractForallContext, List.map_append, List.append_assoc] using HresType)
        exact ⟨.forallE HdomType HbodyType Hdom Hbody', .forallE HdomType HbodyType⟩

theorem TrExprS.of_forallBinderTranslations
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Hdomains : ∀ i (hi : i < domains.length) sourceDomain,
      Expr.ForallBinderAt source i sourceDomain →
      TrExprS env Us (abstractForallContext (domains.take i) Δ) sourceDomain domains[i] ∧
      env.IsType Us.length (abstractForallContext (domains.take i) Δ).toCtx domains[i])
    (Hres : TrExprS env Us (abstractForallContext domains Δ) residual result)
    (HresType : env.IsType Us.length (abstractForallContext domains Δ).toCtx result) :
    TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Hres HresType
  | @cons body arity residual name sourceDom bi Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      have Hdom := Hdomains 0 (by simp) sourceDom .here
      simp only [List.take_zero, abstractForallContext, List.reverse_nil, List.map_nil,
        List.nil_append, List.getElem_cons_zero] at Hdom
      have Htail : ∀ i (hi : i < domains.length) sourceDomain,
          Expr.ForallBinderAt body i sourceDomain →
          TrExprS env Us (abstractForallContext (domains.take i) ((none, .vlam dom) :: Δ))
            sourceDomain domains[i] ∧
          env.IsType Us.length
            (abstractForallContext (domains.take i) ((none, .vlam dom) :: Δ)).toCtx domains[i] := by
        intro i hi sourceDomain Hb
        have Hd := Hdomains (i+1) (by simpa using hi) sourceDomain (.there Hb)
        simp only [List.getElem_cons_succ] at Hd
        simpa [abstractForallContext, List.take_succ_cons, List.map_append, List.append_assoc] using Hd
      obtain ⟨Hbody, HbodyType⟩ := ih (by simpa using hlen) Htail
        (by simpa [abstractForallContext, List.map_append, List.append_assoc] using Hres)
        (by simpa [abstractForallContext, List.map_append, List.append_assoc] using HresType)
      exact ⟨.forallE Hdom.2 HbodyType Hdom.1 Hbody, .forallE Hdom.2 HbodyType⟩

/-- Given a translation of a telescope to a type `target` and a translation of its first `n`
domains to `domains`, the telescope also translates to `wrapForalls domains result` for some
`result` that translates the residual in the context extended by `domains`; both are types,
and `target` is definitionally equal to `wrapForalls domains result`. -/
theorem TrExprS.retargetForallPrefix
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (Htel : Expr.ForallTelescope source n residual)
    (hdomains : domains.length = n)
    (Hfull : TrExprS env Us Δ source target)
    (Htype : env.IsType Us.length Δ.toCtx target)
    (Htemplate : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls domains (.sort .zero))) :
    ∃ result,
      TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) ∧
      TrExprS env Us (abstractForallContext domains Δ) residual result ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx result ∧
      env.IsDefEqU Us.length Δ.toCtx target (VExpr.wrapForalls domains result) := by
  obtain ⟨oldDomains, oldResult, hlen, heq, _⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Hfull
  subst target
  have Hprefix := (TrExprS.forallDomainsOnly Htel hlen Hfull).1
  have Hcontexts := TrExprS.forallPrefixContextEq henv Htel.domainsOnly hlen hdomains
    Hprefix Htemplate (.refl henv hΔ)
  obtain ⟨Hres, HresType⟩ := TrExprS.forallTelescope_residual_typed Htel hlen Hfull Htype
  obtain ⟨result, HnewRes⟩ := Hres.defeqDFC henv Hcontexts
  have HresEq := Hres.uniq henv Hcontexts HnewRes
  have HnewType := (HresType.defeqU_l henv Hcontexts.wf.toCtx HresEq).defeqDFC
    henv.ordered Hcontexts.defeqCtx
  obtain ⟨Hnew, HnewFullType⟩ := TrExprS.rebuildForallPrefix Htel hdomains Htemplate HnewRes HnewType
  exact ⟨result, Hnew, HnewFullType, HnewRes, HnewType,
    Hfull.uniq henv (.refl henv hΔ) Hnew⟩

theorem TrExprS.forallTelescope_residual
    (Htel : Expr.ForallTelescope source n residual) (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result)) :
    TrExprS env Us (abstractForallContext domains Δ) residual result := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using Htr
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htr with
      | forallE _ _ _ Hbody =>
        simpa [abstractForallContext, List.map_append, List.append_assoc] using
          ih (by simpa using hlen) Hbody

theorem TrExprS.shiftedBvarSpine_eq
    (Hargs : List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
      (List.ofFn (fun i : Fin n => Expr.bvar (below + (n - 1 - i)))) targets)
    (hbound : n + below ≤ domains.length) :
    targets = InductiveSignature.vars n below := by
  apply List.ext_getElem
  · have h := Lean4Lean.List.Forall₂.length_eq Hargs
    simpa [InductiveSignature.vars] using h.symm
  · intro i hi hj
    have hin : i < n := by simpa [InductiveSignature.vars] using hj
    have h := List.forall₂_getElem Hargs i (by simpa using hin) hi
    simp only [List.getElem_ofFn] at h
    have heq := TrExprS.bvar_eq_of_abstractForallContext h (by omega)
    simpa [InductiveSignature.vars, List.getElem_reverse] using heq

end Lean4Lean.VerifyInductive

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

namespace VerifyInductive

/-- Two telescopes of abstract domains translating the same source domains,
each in the context of the earlier ones, coincide. -/
theorem TrExprS.telescope_unique {env : VEnv} {Us : List Name} (Δ : VLCtx) :
    ∀ (sources : List Lean.Expr) (L₁ L₂ : List VExpr),
      (h₁ : L₁.length = sources.length) → (h₂ : L₂.length = sources.length) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₁.take i) Δ)
        sources[i] (L₁[i]'(by omega))) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₂.take i) Δ)
        sources[i] (L₂[i]'(by omega))) →
      L₁ = L₂ := by
  intro sources L₁ L₂ h₁ h₂ H₁ H₂
  have key : ∀ n, n ≤ sources.length → L₁.take n = L₂.take n := by
    intro n
    induction n with
    | zero => intro; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hn' : n < sources.length := by omega
      have heq : L₁[n]'(by omega) = L₂[n]'(by omega) := by
        have a := H₁ n hn'
        have b := H₂ n hn'
        rw [hprev] at a
        exact a.unique b
      rw [List.take_add_one, List.take_add_one, hprev, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (h := by omega), heq]
  have := key sources.length (Nat.le_refl _)
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this

end VerifyInductive

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Translations of a telescope and of its unannotated form, in contexts that differ only in
binder types, have syntactically equal bodies once the same number of binders is opened,
provided removing annotations leaves the residual unchanged. -/
theorem TrExprS.unannotatedTelescope_body_eq {venv : VEnv} {Us : List Name}
    (Htel : Expr.ForallTelescope raw n residual) :
    Lean4Lean.Expr.consumeForallTypes annOk residual = residual →
    ∀ {Δ₁ Δ₂ : VLCtx} {As Cs : List VExpr} {B D : VExpr},
      TrExprS.IsUniqueCtx Δ₁ Δ₂ →
      TrExprS venv Us Δ₁ raw (VExpr.wrapForalls As B) →
      TrExprS venv Us Δ₂ (Lean4Lean.Expr.consumeForallTypes annOk raw) (VExpr.wrapForalls Cs D) →
      As.length = n → Cs.length = n → B = D := by
  induction Htel with
  | nil body =>
    intro hres Δ₁ Δ₂ As Cs B D hΔ H1 H2 hA hC
    cases As with
    | cons => simp at hA
    | nil =>
    cases Cs with
    | cons => simp at hC
    | nil =>
    rw [hres] at H2
    simpa [VExpr.wrapForalls] using TrExprS.uniqueCtx hΔ H1 H2
  | cons _ ih =>
    intro hres Δ₁ Δ₂ As Cs B D hΔ H1 H2 hA hC
    cases As with
    | nil => simp at hA
    | cons A As =>
    cases Cs with
    | nil => simp at hC
    | cons C Cs =>
    simp only [VExpr.wrapForalls, List.foldr_cons, Lean4Lean.Expr.consumeForallTypes] at H1 H2
    cases H1 with
    | forallE _ _ _ Hbody =>
    cases H2 with
    | forallE _ _ _ Hcbody =>
    exact ih hres (hΔ.cons .vlam) Hbody Hcbody (by simpa using hA) (by simpa using hC)

/-- Pointwise syntactic uniqueness of translation lists. -/
theorem TrExprS.forall₂_uniqueS {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {srcs : List Expr} {l₁ l₂ : List VExpr}
    (H₁ : List.Forall₂ (TrExprS env Us Δ) srcs l₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ) srcs l₂) : l₁ = l₂ := by
  induction H₁ generalizing l₂ with
  | nil => cases H₂; rfl
  | cons h₁ _ ih =>
    cases H₂ with
    | cons h₂ H₂ => rw [h₁.unique h₂, ih H₂]

/-- Telescope inversion recording each translated domain: the `i`-th
abstract domain is the translation of the `i`-th literal source domain in the
context extended by the earlier abstract domains. -/
theorem TrExprS.forallTelescope_domains
    (Htel : Expr.ForallTelescope source n residual)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (hlen : domains.length = n) :
    ∀ (i : Nat) (hi : i < domains.length),
      TrExprS env Us (abstractForallContext (domains.take i) Δ)
        (Expr.forallDomainList n source)[i]! (domains[i]'hi) := by
  induction Htel generalizing Δ domains with
  | nil =>
    intro i hi
    simp only [List.length_eq_zero_iff] at hlen
    subst hlen
    simp at hi
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons d ds =>
      simp only [VExpr.wrapForalls, List.foldr_cons] at Htr
      cases Htr with
      | forallE _ _ Hdom Hbody =>
        intro i hi
        cases i with
        | zero => simpa [Expr.forallDomainList, abstractForallContext] using Hdom
        | succ i =>
          have Hi := ih (domains := ds) Hbody (by simpa using hlen) i (by simpa using hi)
          simpa [Expr.forallDomainList, abstractForallContext, List.map_append,
            List.append_assoc] using Hi

/-- `TrExprS.substLevelParamsCore` without the (unused) context invariant. -/
theorem TrExprS.substLevelParamsCore_of_levels
    {env : VEnv} {ps Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    {ls : List VLevel} {F : Name → Level}
    (hls : ∀ level ∈ ls, level.WF Us.length)
    (hlevels : ∀ u u', VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F false) = some (u'.inst ls))
    (H : TrExprS env ps Δ e e') :
    TrExprS env Us (Δ.instL ls) (Expr.instantiateLevelParamsCore' false F e)
      (e'.instL ls) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (hlevels _ _ hlevel)
  | @const _ _ sourceLevels targetLevels info hlookup hlevel harity =>
    apply TrExprS.const hlookup ?_ (by simpa using harity)
    have Hmap := List.mapM_eq_some.mp hlevel
    apply List.mapM_eq_some.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun u u' hu => hlevels u u' hu) Hmap
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hls)
      (VLCtx.instL_toCtx _ ▸ harg.instL hls) ihFn ihArg
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hls) ihDom ihBody
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hls) ihDom ihBody
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hls) ihTy ihVal ihBody
  | lit hlit _ ih =>
    exact .lit hlit (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih)
  | mdata _ ih => exact .mdata ih
  | proj _ hproj ih =>
    exact .proj ih (VLCtx.instL_toCtx _ ▸ hproj.instL hls)

/-- `TrExprS.prependLevelParam` without the (unused) context invariant. -/
theorem TrExprS.prependLevelParam_of_fresh
    {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr} {fresh : Name}
    (hfresh : fresh ∉ Us) (H : TrExprS env Us Δ e e') :
    TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e
      (e'.instL (VLevel.prependShift Us.length)) := by
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (VLevel.ofLevel_fresh_cons hfresh hlevel)
  | const hlookup hlevels harity =>
    exact .const hlookup (VLevel.mapM_ofLevel_fresh_cons hfresh hlevels) harity
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hshift)
      (VLCtx.instL_toCtx _ ▸ harg.instL hshift) ihFn ihArg
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hshift) ihDom ihBody
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hshift)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hshift) ihDom ihBody
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hshift) ihTy ihVal ihBody
  | lit hlit _ ih => exact .lit hlit ih
  | mdata _ ih => exact .mdata ih
  | proj _ hproj ih =>
    exact .proj ih (VLCtx.instL_toCtx _ ▸ hproj.instL hshift)

end Lean4Lean.VerifyInductive

namespace Lean4Lean

namespace VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The executable arity counts every binder of a concrete forall telescope. -/
theorem Expr.ForallTelescope.constructorArity
    (H : Expr.ForallTelescope source n result) :
    AddInductive.constructorArity source = n + AddInductive.constructorArity result := by
  induction H with
  | nil => simp
  | cons _ ih => simp [AddInductive.constructorArity, ih]; omega

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The annotation-only `inferImplicit` pass can be erased from the concrete
side of a forall telescope translation. -/
theorem Expr.ForallTelescopeTypeTranslation.of_inferImplicit
    {env : VEnv} {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {n : Nat} {e' : VExpr} (numParams : Nat)
      (considerRange : Bool),
      Expr.ForallTelescopeTypeTranslation env Us Δ
        (e.inferImplicit numParams considerRange) n e' →
      Expr.ForallTelescopeTypeTranslation env Us Δ e n e'
  | Δ, e, n, e', 0, cr, H => by simpa [Expr.inferImplicit] using H
  | Δ, e, n, e', numParams + 1, cr, H => by
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.inferImplicit] at H
      cases H with
      | nil Htr Htype => exact .nil (TrExprS.of_inferImplicit (numParams := numParams + 1)
          (considerRange := cr) (by simpa [Expr.inferImplicit] using Htr)) Htype
      | cons Hdom HdomType Hbody =>
        exact .cons Hdom HdomType
          (Expr.ForallTelescopeTypeTranslation.of_inferImplicit numParams cr Hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- Instantiate an abstracted binder of a forall telescope translation with
its free variable. -/
theorem Expr.ForallTelescopeTypeTranslation.instantiateFVar
    {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} (hfresh : v₀ ∉ Δ₀.fvars) :
    ∀ {dk k : Nat} {Δ₁ Δ : VLCtx} {e : Expr} {n : Nat} {e' : VExpr},
      VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ →
      Expr.ForallTelescopeTypeTranslation env Us Δ e n e' →
      Expr.ForallTelescopeTypeTranslation env Us Δ₁
        (e.instantiate1' (.fvar v₀) dk) n e'
  | _, _, _, _, _, _, _, W, .nil Htr Htype =>
    .nil (TrExprS.instantiateFVar W hfresh Htr) (W.toCtx ▸ Htype)
  | _, _, _, _, _, _, _, W, .cons Hdom HdomType Hbody => by
    simp only [Expr.instantiate1']
    exact .cons (TrExprS.instantiateFVar W hfresh Hdom) (W.toCtx ▸ HdomType)
      (Expr.ForallTelescopeTypeTranslation.instantiateFVar hfresh W.succ Hbody)

/-- Apply a translated function to the free variables of a lambda prefix
opened above its context.  The application is translated and typed by the
canonical variables, and its type is the remaining telescope. -/
theorem TrExprS.mkAppList_fvarPrefix {env : VEnv} {Us : List Name}
    (henv : env.WF) {Δ₀ : VLCtx} {f : Expr} {bF : VExpr}
    (hf : TrExprS env Us Δ₀ f bF) :
    ∀ (pre : VLCtx) {rest : List VExpr} {body : VExpr},
      (pre ++ Δ₀).WF env Us.length →
      (∀ e ∈ pre, ∃ fv deps d, e = (some (fv, deps), .vlam d)) →
      env.HasType Us.length Δ₀.toCtx bF
        (VExpr.wrapForalls ((VLCtx.toCtx pre).reverse ++ rest) body) →
      TrExprS env Us (pre ++ Δ₀)
          (Expr.mkAppList f ((VLCtx.fvars pre).reverse.map Expr.fvar))
          (VExpr.mkApps (bF.liftN pre.length)
            (bvarSpine pre.length)) ∧
        env.HasType Us.length (pre ++ Δ₀).toCtx
          (VExpr.mkApps (bF.liftN pre.length)
            (bvarSpine pre.length))
          (VExpr.wrapForalls rest body)
  | [], rest, body, _, _, hty => by
    simpa [Expr.mkAppList, VExpr.mkApps, VLCtx.toCtx, VLCtx.fvars] using
      And.intro hf hty
  | e :: pre, rest, body, hwf, hlams, hty => by
    obtain ⟨fv, deps, d, rfl⟩ := hlams e (by simp)
    have hlams' : ∀ e ∈ pre, ∃ fv deps d, e = (some (fv, deps), .vlam d) :=
      fun e he => hlams e (by simp [he])
    have hty' : env.HasType Us.length Δ₀.toCtx bF
        (VExpr.wrapForalls ((VLCtx.toCtx pre).reverse ++ (d :: rest)) body) := by
      simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using hty
    obtain ⟨htr, htyped⟩ :=
      TrExprS.mkAppList_fvarPrefix henv hf pre hwf.1 hlams' hty'
    let W : VLCtx.FVLift (pre ++ Δ₀)
        ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)) 0 1 0 :=
      .skip_fvar _ _ .refl
    have htrW := htr.weakFV henv.orderedStrong W hwf
    have htyW := htyped.weakN henv.ordered W.toCtx
    have harg : TrExprS env Us ((some (fv, deps), .vlam d) :: (pre ++ Δ₀))
        (.fvar fv) (.bvar 0) := by
      apply TrExprS.fvar (A := d.liftN 1)
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift]
    have hargTy : env.HasType Us.length
        (VLCtx.toCtx ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)))
        (.bvar 0) (d.liftN 1) := by
      have hlookup : VLCtx.find?
          ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)) (.inr fv) =
          some (.bvar 0, d.liftN 1) := by
        simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
          VLocalDecl.value, VLocalDecl.type, VExpr.lift]
      exact hwf.find?_wf henv.orderedStrong hlookup
    have hfnTy : env.HasType Us.length
        (VLCtx.toCtx ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)))
        ((VExpr.mkApps (bF.liftN pre.length)
          (bvarSpine pre.length)).liftN 1)
        (.forallE (d.liftN 1) ((VExpr.wrapForalls rest body).liftN 1 1)) := by
      simpa [VExpr.wrapForalls, VExpr.liftN] using htyW
    have happ := TrExprS.app hfnTy hargTy htrW harg
    have happTy := VEnv.HasType.app hfnTy hargTy
    have hvars : VExpr.mkApps (bF.liftN (pre.length + 1))
        (bvarSpine (pre.length + 1)) =
        .app ((VExpr.mkApps (bF.liftN pre.length)
          (bvarSpine pre.length)).liftN 1) (.bvar 0) := by
      rw [bvarSpine_add pre.length 1, VExpr.mkApps_append,
        VExpr.liftN_mkApps]
      simp [bvarSpine, VExpr.mkApps, VExpr.liftN_liftN]
    refine ⟨?_, ?_⟩
    · simpa [Expr.mkAppList, List.reverse_cons, List.map_append,
        Expr.mkAppList_append, hvars] using happ
    · simpa [hvars, VExpr.inst_liftN_bvar] using happTy

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open VerifyInductive

theorem TrExprS.toSyn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : TrSyn Us Δ e e' := H.toTrSyn

/-- A typed translation of a source expression whose syntactic translation is
known has exactly that target. -/
theorem TrExprS.of_syn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e₁ e₂ : VExpr}
    (H : TrExprS env Us Δ e e₁) (S : TrSyn Us Δ e e₂) : TrExprS env Us Δ e e₂ :=
  H.toTrSyn.unique S ▸ H

/-- The source of a shape translation in the small context is closed at the
shape's local depth and mentions only the earlier fields and the parameters. -/
theorem TrExprS.shapeSourceFacts {env : VEnv} {Us : List Name}
    {sp sfT rbT : List VExpr} {e : Lean.Expr} {t : VExpr} {F P : List FVarId} {pos : Nat}
    (hpos : pos ≤ F.length) (hsp : sp.length = P.length) (hsfT : sfT.length = pos)
    (H : TrExprS env Us (abstractForallContext (sp ++ sfT ++ rbT) [])
      ((e.abstractList (F.take pos) rbT.length).abstractList P (pos + rbT.length)) t) :
    Closed e rbT.length ∧ e.FVarsIn fun fv => fv ∈ F.take pos ∨ fv ∈ P := by
  have hFpos : (F.take pos).length = pos := by simp [hpos]
  have hclosed : Closed ((e.abstractList (F.take pos) rbT.length).abstractList P
      (pos + rbT.length)) (pos + rbT.length + P.length) := by
    have := H.closed
    simp only [abstractForallContext_bvars, List.length_append] at this
    simpa [hsp, hsfT, VLCtx.bvars, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hc1 := Expr.closed_of_abstractList hclosed
  refine ⟨Expr.closed_of_abstractList (by rw [hFpos, Nat.add_comm]; exact hc1), ?_⟩
  have h := H.fvarsIn
  simp only [abstractForallContext_fvars] at h
  have h1 := VerifyInductive.FVarsIn.of_abstractList h
  exact VerifyInductive.FVarsIn.of_abstractList (h1.mono fun fv hfv => by
    rcases hfv with hfv | hfv
    · exact hfv
    · simp [VLCtx.fvars] at hfv)

end Lean4Lean
