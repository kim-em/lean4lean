import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Verification state for the outer inductive-construction monad. The local
context is represented by the same `MLCtx` used by the typechecker proof, while
the production reader retains the independently generated `_ind_fresh` names. -/
structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv

def initialContext (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context where
  env; lparams; safety; allowPrimitive; fuel

def ContextWF.initial {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig) :
    ContextWF (initialContext env lparams safety allowPrimitive fuel) where
  venv := ves.venv safety
  checking := (wf.tr (safety := safety)).toCheckingValid
    (wf.hasPrimitives (safety := safety)) wf.safePrimitives
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun

theorem ContextWF.current_not_mem (H : ContextWF c) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem ContextWF.kernel_reserves_current (H : ContextWF c) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

def ContextWF.withLocalDecl (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    ContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := ⟨H.mlctx_wf,
    H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩
  lctx_eq := by
    change H.mlctx.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi =
      c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    rw [H.lctx_eq]
  ngen_prefix := by
    change c.ngen.namePrefix = `_ind_fresh
    exact H.ngen_prefix
  indFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.indFresh _ hmem).mono NameGenerator.LE.next
  kernelFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact H.kernel_reserves_current
    · exact H.kernelFresh _ hmem

theorem withLocalDecl.WF {k : Expr → AddInductive.M α} (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  have _Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  exact Hk

/-- Invert the syntax-directed part of a translated forall while retaining the
definitional equality introduced by normalization.  Header and constructor
loops use this after `whnf`: the production expression is syntactically a
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

/-- Invert a production sort after normalization, retaining both its universe
translation and its definitional equality to the abstract source tail. -/
theorem TrExpr.sort_source
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEqU Us.length Δ.toCtx (.sort level') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | sort Hlevel => exact ⟨_, Hlevel, Hdefeq⟩

/-- Opening a source binder with the fresh free variable chosen by the
production checker leaves its abstract body unchanged: the extended `VLCtx`
maps that free variable back to the new outermost de Bruijn variable. -/
theorem ContextWF.instantiateFresh (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam ty') :: Hc.mlctx.vlctx) body body') :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body' := by
  dsimp only
  rw [Expr.instantiate1_eq]
  exact hbody.inst_fvar Hc.checking.tr.wf.ordered
    (Hc.withLocalDecl htr hty).mlctx_wf.tr.wf

/-- Instantiate a source binder with an existing translated argument whose
cached type is only definitionally equal to the binder domain. -/
theorem ContextWF.instantiateDefEq (Hc : ContextWF c)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (harg : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx arg arg')
    (hargType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      arg' argType')
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' argType') :
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 arg) (body'.inst arg') := by
  have hargType' := hargType.defeqU_r Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq.symm
  rw [Expr.instantiate1_eq]
  exact hbody.inst Hc.checking.tr.wf.ordered hargType' harg

/-- Semantic certificate for the production checker's removal of binder type
annotations.  The consumed syntax may translate to a different abstract term,
but it must remain a type definitionally equal to the source domain. -/
structure ContextWF.ConsumedDomain (Hc : ContextWF c)
    (dom : Expr) (source' consumed' : VExpr) : Prop where
  source : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source'
  consumed : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
    dom.consumeTypeAnnotations consumed'
  isType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, Hc.venv.IsDefEq c.lparams.length Hc.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

theorem Expr.consumeTypeAnnotations_eq_self {dom : Expr}
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false) :
    dom.consumeTypeAnnotations = dom := by
  simp [hopt, hauto, hout, hsemi]

/-- Domains without a leading type annotation need no semantic transport. -/
theorem ContextWF.ConsumedDomain.unchanged (Hc : ContextWF c)
    (heq : dom.consumeTypeAnnotations = dom)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' := by
  rcases hty with ⟨u, hty⟩
  exact {
    source := htr
    consumed := heq.symm ▸ htr
    isType := ⟨u, hty⟩
    source_defeq := ⟨u, hty⟩ }

theorem ContextWF.ConsumedDomain.unannotated (Hc : ContextWF c)
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' :=
  .unchanged Hc (Expr.consumeTypeAnnotations_eq_self hopt hauto hout hsemi) htr hty

/-- Transport the source body translation to the annotation-consumed binder
type.  This is the bridge needed before opening the binder with the production
free variable. -/
theorem ContextWF.ConsumedDomain.body
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom body : Expr} {source' consumed' body' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam source') :: Hc.mlctx.vlctx) body body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam consumed') :: Hc.mlctx.vlctx) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length
        (source' :: Hc.mlctx.vlctx.toCtx) body' body'' := by
  rcases H.source_defeq with ⟨_, hdom⟩
  have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
      ((none, .vlam source') :: Hc.mlctx.vlctx)
      ((none, .vlam consumed') :: Hc.mlctx.vlctx) :=
    VLCtx.IsDefEq.cons
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) nofun (.vlam hdom)
  rcases hbody.defeqDFC Hc.checking.tr.wf hctx with ⟨body'', hbody''⟩
  exact ⟨body'', hbody'', hbody.uniq Hc.checking.tr.wf hctx hbody''⟩

def ContextWF.typeChecker (H : ContextWF c) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC H.checking H.mlctx H.mlctx_wf c.fuel

@[simp] theorem ContextWF.typeChecker_lctx (H : ContextWF c) :
    H.typeChecker.lctx = c.lctx := by
  simp [ContextWF.typeChecker, TypeChecker.VContext.mkCheckingValidMLC, H.lctx_eq]

/-- Reuse a verified typechecker computation inside `AddInductive.M`. -/
theorem liftTypeChecker.WF {x : TypeChecker.M α} (Hc : ContextWF c)
    (Hx : TypeChecker.M.WF Hc.typeChecker {} x fun a _ => Q a) :
    ((monadLift x : AddInductive.M α) c).WF Q := by
  change (TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x).WF Q
  rw [← Hc.lctx_eq]
  exact TypeChecker.M.WF.runCheckingValidMLC Hc.kernelFresh Hx

theorem checkTypeInContext.WF (Hc : ContextWF c)
    (hfvars : e.FVarsIn (· ∈ Hc.mlctx.vlctx.fvars)) :
    ((monadLift (TypeChecker.checkType e) : AddInductive.M Expr) c).WF fun ty =>
      ∃ e' ty', TrTyping Hc.venv c.lparams Hc.mlctx.vlctx e ty e' ty' :=
  liftTypeChecker.WF Hc (TypeChecker.checkType.WF hfvars)

theorem whnfInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc (TypeChecker.whnf.WF he)

theorem ensureSortInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' ∧ ∃ u, e₁ = .sort u :=
  liftTypeChecker.WF Hc (TypeChecker.ensureSort.WF he)

theorem ensureTypeInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ e'', TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e'' ∧
        ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
          Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx e'' (.sort u') :=
  liftTypeChecker.WF Hc (TypeChecker.ensureType.WF he)

theorem isDefEqInContext.WF (Hc : ContextWF c)
    (he₁ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₁ e₁')
    (he₂ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₂ e₂') :
    ((monadLift (TypeChecker.isDefEq e₁ e₂) : AddInductive.M Bool) c).WF fun b =>
      b → Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx e₁' e₂' :=
  liftTypeChecker.WF Hc (TypeChecker.isDefEq.WF he₁ he₂)

theorem checkNoMVarNoFVar.closed
    (H : Kernel.Environment.checkNoMVarNoFVar env name e = .ok ()) :
    e.FVarsIn fun _ => False := by
  have hm : e.hasMVar = false := by
    cases hm : e.hasMVar
    · rfl
    · have he : Kernel.Environment.checkNoMVar env name e =
          .error (.declHasMVars env name e) := by
        unfold Kernel.Environment.checkNoMVar
        rw [hm]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, he] at H
      contradiction
  have hf : e.hasFVar = false := by
    have hmok : Kernel.Environment.checkNoMVar env name e = .ok () := by
      unfold Kernel.Environment.checkNoMVar
      rw [hm]
      rfl
    cases hf : e.hasFVar
    · rfl
    · have he : Kernel.Environment.checkNoFVar env name e =
          .error (.declHasFVars env name e) := by
        unfold Kernel.Environment.checkNoFVar
        rw [hf]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, hmok, he] at H
      contradiction
  apply Lean4Lean.fvarsIn_iff.mpr
  refine ⟨?_, Lean4Lean.fvarsIn_iff_hasMVar.mpr hm⟩
  · intro fv hmem
    rw [Lean4Lean.fvarsList_eq_nil.2 hf] at hmem
    contradiction

theorem checkClosedType.WF (Hc : ContextWF c) :
    (AddInductive.checkClosedType name type c).WF fun checkedType =>
      ∃ type' checkedType',
        TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
          type checkedType type' checkedType' := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel
      (TypeChecker.checkType type)).WF _
  have hno : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkTypeInContext.WF Hc (hclosed.mono fun _ h => False.elim h)

namespace checkInductiveTypes.loopType

/-- Fuel exhaustion cannot produce a successful result. -/
theorem zero.WF :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      0 k c).WF Q := by
  intro _ h
  simp [AddInductive.checkInductiveTypes.loopType] at h

/-- Base case of the header telescope traversal.  This theorem deliberately
states only the executable control-flow fact; the caller's continuation owns
the declarative result-sort and accumulated-telescope obligations. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i = nparams)
    (Hk : (k type stats nindices c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  subst i
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]

/-- A non-forall tail with the wrong number of common parameters is rejected,
so this branch is semantically vacuous. -/
theorem parameterMismatch.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i ≠ nparams) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Verification step for an index binder.  `hdom`/`hdomType` are stated for
the annotation-consumed domain actually installed in the production local
context; deriving them from the source domain is the separate
`consumeTypeAnnotations` compatibility obligation. -/
theorem index.WF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Source-facing index step: consume the domain certificate and transport the
source body automatically before invoking `index.WF`. -/
theorem index.sourceWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.WF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- Verification step for a common parameter of the first mutual header.  In
addition to the opened-body relation, the continuation sees the exact fresh
free variable appended to the executable parameter cache. -/
theorem firstParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_pos hempty]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun param => do
      let stats := { stats with params := stats.params.push param }
      let type := body.instantiate1 param
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Source-facing first-parameter step, including annotation-domain and body
transport. -/
theorem firstParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact firstParameter.WF Hc hi hempty Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- Verification step for a common parameter of a later mutual header.  The
executable checker reuses the cached free variable and requires the new domain
to be definitionally equal to its local type. -/
theorem laterParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized, TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec (hequal rfl) normalized hnormalized

/-- Source-facing later-parameter step.  The successful executable equality
check supplies exactly the conversion needed to instantiate the translated
source body with the cached parameter. -/
theorem laterParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized,
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec heq normalized hnormalized

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

private def updatedStats (stats : AddInductive.InductiveStats)
    (lctx : LocalContext) (resultLevel : Level) (setResult : Bool)
    (nindices : Nat) (indName : Name) : AddInductive.InductiveStats :=
  let stats := if setResult then
    { stats with
      lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
  else stats
  { stats with
    nindices := stats.nindices.push nindices
    indConsts := stats.indConsts.push (.const indName stats.levels) }

@[simp] theorem updatedStats_levels :
    (updatedStats stats lctx resultLevel setResult nindices indName).levels =
      stats.levels := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_nindices_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices.size =
      stats.nindices.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_indConsts_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts.size =
      stats.indConsts.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_params :
    (updatedStats stats lctx resultLevel setResult nindices indName).params =
      stats.params := by
  cases setResult <;> rfl

/-- Post-telescope continuation for the first mutual header. -/
theorem firstResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_pos hempty]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [updatedStats, Expr.sortLevel!] using Hrec resultSort hsorted

/-- Post-telescope continuation for later mutual headers.  A mismatched result
universe throws; a successful path records the checked equivalence before
updating the per-type arrays. -/
theorem laterResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_neg (by simp [hnonempty])]
  by_cases hequiv : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = true
  · have hequiv' : resultSort.isEquiv stats.resultLevel = true := by
      simpa [Expr.sortLevel!] using hequiv
    simpa [updatedStats, Expr.sortLevel!, hequiv, hequiv'] using
      Hrec resultSort hequiv' hsorted
  · have hfalse : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = false := by
      cases h : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel <;>
        simp_all
    have hnot : (!(Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel) = true := by
      simp [hfalse]
    rw [if_pos hnot]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Base case of the mutual-header loop.  The executable assertions become
explicit invariants at the proof boundary instead of being silently erased. -/
theorem result.WF
    (hidx : ¬ dIdx < indTypes.size)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = indTypes.size)
    (hconsts : stats.indConsts.size = indTypes.size)
    (hparams : stats.params.size = nparams)
    (Hk : (k stats c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_neg hidx]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [hlevels, hindices, hconsts, hparams] using Hk

/-- Verified prefix of one mutual-header iteration: closed source checking and
WHNF are connected to the abstract translation before control enters the
already verified telescope loop.  The continuation owns the result-sort,
statistics update, and recursive mutual iteration invariants. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ normalized, TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_pos hidx]
  change (AddInductive.checkClosedType indTypes[dIdx].name indTypes[dIdx].type c >>=
    fun _ => ((do
      let normalized ← TypeChecker.whnf indTypes[dIdx].type
      AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.WF Hc).bind fun checkedType hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    exact (whnfInContext.WF Hc hchecked.2.1).bind fun normalized hnormalized =>
      Hloop checkedType type' checkedType' hchecked normalized hnormalized

end checkInductiveTypes.loopInd

namespace checkConstructors.loopCtor

theorem zero.WF :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkConstructors.loopCtor] at h

/-- A constructor telescope ending in the checked target application returns
success; the separate application-refinement theorem will connect
`isValidIndAppIdx` to `VInductDecl.ValidIndAppAt`. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals exact Except.WF.pure hQ

/-- An invalid non-forall constructor target is rejected. -/
theorem invalidResult.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = false) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Common-parameter branch of a constructor telescope.  The cached parameter
type comparison is converted directly into abstract body instantiation. -/
theorem parameter.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = some param)
    (hget : (AddInductive.getType param c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx param param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 param) (body'.inst param') →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel c).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  change (AddInductive.getType param c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other
          s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel) : AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact Hrec heq hopened

/-- Safe constructor-field branch.  Successful field typing, the executable
universe bound, positivity, annotation transport, and fresh body opening are
all delivered to the recursive continuation. -/
theorem safeField.sourceWF
    {Pos : Prop}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF (fun _ => Pos))
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      Pos →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !false then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    refine Hpos.bind fun _ hpos => ?_
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound hpos body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Unsafe constructor-field branch: the same source typing, universe, and
annotation obligations apply, while positivity is intentionally skipped. -/
theorem unsafeField.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !true then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkConstructors.loopCtor

namespace checkPositivityStep

theorem noOccurrence.WF
    {type : Expr} {Q : Unit → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok ()).WF Q
  exact Except.WF.pure hQ

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

theorem invalidApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = none) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkPositivityStep

/-- Production-side installation of a list of kernel constants. This small
reference function is used only to state the staging invariant; the executable
inductive checker continues to build the same environments directly. -/
def addConstants : Environment → List ConstantInfo → Environment
  | env, [] => env
  | env, ci :: cis => addConstants (env.add ci) cis

/-- A certificate that a list of production constants and abstract constants
are installed in lockstep. Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.production
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    addConstants env (entries.map Prod.fst) = outEnv := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa [addConstants] using ih

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConsts (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConsts]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConsts, ← htr.2, hadd]
    exact ih

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConsts_le H.abstract

/-- Three-stage installation certificate matching the executable order:
mutual headers, constructors, then recursors. Reduction equations are not
included here because their validity depends on the independent iota schema. -/
structure StagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  typesAdded : AddConstants safety env venv types envTypes venvTypes
  ctorsAdded : AddConstants safety envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors outEnv outVEnv

theorem StagedBlock.valid
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid (H.ctorsAdded.valid (H.typesAdded.valid hvalid))

theorem StagedBlock.abstract_types
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    venv.addConsts (types.map Prod.snd) = some H.venvTypes :=
  H.typesAdded.abstract

theorem StagedBlock.abstract_ctors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvTypes.addConsts (ctors.map Prod.snd) = some H.venvCtors :=
  H.ctorsAdded.abstract

theorem StagedBlock.abstract_recursors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvCtors.addConsts (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- The first executable check on every source inductive header is an ordinary
type-checker run. At an empty local context its successful result already
provides both the source translation and the abstract typing derivation; later
stages must transport the same statement through the common-parameter local
context. -/
theorem checkType_closed.WF
    (hvalid : CheckingEnv.Valid safety env venv)
    (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType e)).WF
      fun ty => ∃ e' ty', TrTyping venv lparams [] e ty e' ty' := by
  have hfvars : e.FVarsIn fun fv => fv ∈ VLCtx.fvars ([] : VLCtx) :=
    hclosed.mono fun _ h => False.elim h
  exact TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := lparams) (fuel := fuel)
    (TypeChecker.checkType.WF hfvars)

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
