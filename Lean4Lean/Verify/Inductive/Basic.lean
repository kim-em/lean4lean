import Init.Data.Array.Lemmas
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

/-- A translated production sort pins the type of the abstract conversion to
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

/-- Semantic compatibility required of Lean's opaque annotation erasure.
It is kept as one named boundary condition until the translations of
`OptParam`, `AutoParam`, and output-parameter wrappers are verified directly. -/
def ConsumeTypeAnnotationsCompat : Prop :=
  ∀ (c : AddInductive.Context) (Hc : ContextWF c)
    {dom : Expr} {source' : VExpr},
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source' →
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx source' →
    ∃ consumed', Hc.ConsumedDomain dom source' consumed'

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

@[simp] theorem updatedStats_indConsts :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts =
      stats.indConsts.push (.const indName stats.levels) := by
  cases setResult <;> rfl

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

/-- The first mutual header records its result universe and simultaneously
assembles the independent `TypeShape` certificate before continuing with the
remaining headers. -/
theorem firstResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx =
      indices.reverse ++ ownParams.reverse)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      decl.TypeShape Hc.venv params target →
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
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  apply Hrec resultSort
  exact TrExpr.typeShape Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

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

theorem hasIndOcc_eq_findAny :
    AddInductive.hasIndOcc indConsts type =
      type.findAny (fun
        | .const name _ => indConsts.any fun I => I.constName! == name
        | _ => false) := by
  unfold AddInductive.hasIndOcc
  exact Expr.find?_isSome_eq_findAny _ _

def IndConstNames (indConsts : Array Expr) (names : List Name) : Prop :=
  ∀ name, (indConsts.any fun I => I.constName! == name) = names.contains name

/-- The concrete array accumulated by header checking has exactly the abstract
mutual-family names, in declaration order.  Keeping this stronger structural
fact separate makes the weaker search correspondence above reusable by both
positivity and recursive-target validation. -/
structure IndConstArray (levels : List Level) (indConsts : Array Expr)
    (names : List Name) : Prop where
  exact : indConsts = (names.map fun name => .const name levels).toArray
  names : IndConstNames indConsts names

/-- The portion of the mutable header statistics needed to interpret a
recursive application in the independent declaration.  In particular, the
common parameters are related by expression translation rather than merely by
array position. -/
structure ValidAppStatsWF (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

theorem forall₂_length_eq
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.mapM_some_length
    {xs : List α} {ys : List β} {f : α → Option β}
    (H : xs.mapM f = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp at H
    subst ys
    rfl
  | cons x xs ih =>
    cases hx : f x <;> simp [hx] at H
    rename_i y
    cases hxs : xs.mapM f <;> simp [hxs] at H
    rename_i ys'
    subst ys
    simp [ih hxs]

theorem forall₂_get?_eq_some
    {R : α → β → Prop} {as : List α} {bs : List β}
    {i : Nat} {a : α} {b : β}
    (H : List.Forall₂ R as bs)
    (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at ha hb
      subst a
      subst b
      exact h
    | succ i => exact ih (by simpa using ha) (by simpa using hb)

theorem ValidAppStatsWF.params_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.params.size = decl.nparams := by
  have := forall₂_length_eq H.params
  simpa [VInductDecl.paramVars] using this

theorem ValidAppStatsWF.types_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem ValidAppStatsWF.indConstAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem ValidAppStatsWF.nindicesAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem ValidAppStatsWF.paramAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env Us Δ stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlen := forall₂_length_eq H.params
      simpa using hlen ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    forall₂_get?_eq_some H.params hsource htarget⟩

theorem ValidAppStatsWF.paramFVarAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

theorem forall₂_map_right
    (H : List.Forall₂ R as bs)
    (hf : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S as (bs.map f) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

@[simp] theorem VInductDecl.paramVars_liftN
    {decl : VInductDecl} {depth : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN 1 e 0) =
      decl.paramVars (depth + 1) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  omega

theorem ValidAppStatsWF.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsWF
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  have W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 := by
    change VLCtx.FVLift Hc.mlctx.vlctx
      ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) 0 1 0
    exact .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    H.params fun h =>
      h.weakFV Hc'.checking.tr.wf W Hc'.mlctx_wf.tr.wf
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  change List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    stats.params.toList (decl.paramVars (depth + 1))
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

theorem IndConstArray.empty (levels : List Level) :
    IndConstArray levels #[] [] where
  exact := rfl
  names := by simp [IndConstNames, Array.any]

theorem IndConstArray.push
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names) (newName : Name) :
    IndConstArray levels (indConsts.push (.const newName levels))
      (names ++ [newName]) where
  exact := by rw [H.exact]; simp
  names := by
    intro name
    rw [Array.any_push, H.names name]
    change (names.contains name || (newName == name)) =
      (names ++ [newName]).contains name
    rw [List.contains_append]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.contains_cons,
      List.contains_nil, Bool.or_false]
    exact eq_comm

theorem IndConstArray.updatedStats
    {stats : AddInductive.InductiveStats} {names : List Name}
    {lctx : LocalContext} {resultLevel : Level} {setResult : Bool}
    {nindices : Nat} {indName : Name}
    (H : IndConstArray stats.levels stats.indConsts names) :
    IndConstArray
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).levels
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).indConsts
      (names ++ [indName]) := by
  simpa using H.push indName

def LiteralDisjoint (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal,
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

@[simp] theorem VExpr.containsAnyConst_liftN
    {e : VExpr} {n k : Nat} {names : List Name} :
    (e.liftN n k).containsAnyConst names = e.containsAnyConst names := by
  induction e generalizing k <;>
    simp [VExpr.liftN, VExpr.containsAnyConst, *]

theorem forall₂_append {R : α → β → Prop}
    (H₁ : List.Forall₂ R as₁ bs₁) (H₂ : List.Forall₂ R as₂ bs₂) :
    List.Forall₂ R (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

/-- Translation preserves a constant-headed application spine and the
left-to-right correspondence of all its arguments.  This is the syntax bridge
needed by both executable recursive-target checks. -/
theorem TrExprS.constAppSpine
    (H : TrExprS env Us Δ e e')
    (hhead : e.getAppFn = .const name levels) :
    ∃ levels' args',
      e'.getAppFnArgs = (.const name levels', args') ∧
      levels.mapM (VLevel.ofLevel Us) = some levels' ∧
      List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  induction e generalizing e' with
  | const _ _ =>
    cases H with
    | const _ hlevels _ =>
      cases hhead
      exact ⟨_, [], rfl, hlevels, .nil⟩
  | app fn arg ihFn _ =>
    cases H
    rename_i f' _ _ arg' _ _ hfn harg
    rcases ihFn hfn hhead with ⟨levels', args', hspine, hlevels, hargs⟩
    have hargs' := forall₂_append hargs (.cons harg .nil)
    refine ⟨levels', args' ++ [arg'], ?_, hlevels, ?_⟩
    · simp [hspine]
    · simpa only [Expr.getAppArgsList_app] using hargs'
  | bvar _ | fvar _ | sort _ | lit _ => cases hhead
  | mvar _ => cases H
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ _ => cases hhead

theorem TrExprS.eqv_fvar_target
    (H₁ : TrExprS env Us Δ (.fvar fv) e₁')
    (H₂ : TrExprS env Us Δ e₂ e₂')
    (heq : ((.fvar fv : Expr) == e₂) = true) : e₁' = e₂' := by
  cases e₂ <;> simp [(· == ·), Expr.eqv'] at heq
  have hfv : fv = _ := beq_iff_eq.mp heq
  subst_vars
  cases H₁ with
  | fvar h₁ =>
    cases H₂ with
    | fvar h₂ =>
      rw [h₁] at h₂
      cases h₂
      rfl

theorem isValidIndAppIdx.head
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    (type.getAppFn == stats.indConsts[i]!) = true := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.constHead
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels)) :
    type.getAppFn = .const name levels := by
  have hhead := isValidIndAppIdx.head hvalid
  have hget : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  rw [hget] at hhead
  exact Expr.eqv_const.mp hhead

theorem isValidIndAppIdx.arity
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    type.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.param
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hj : j < stats.params.size) :
    (stats.params[j] == type.getAppArgs[j]'(by
      have := isValidIndAppIdx.arity hvalid
      omega)) = true := by
  have hp :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    cases hparams :
        (stats.params == type.getAppArgs.extract 0 stats.params.size) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  rw [Array.beq_eq_decide] at hp
  split at hp
  · rename_i hsize
    simp only [decide_eq_true_eq] at hp
    have helem := hp j hj
    simpa only [Array.getElem_extract, Nat.zero_add] using helem
  · simp_all

theorem isValidIndAppIdx.indexNoOccurrence
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hlower : stats.params.size ≤ j) (hupper : j < type.getAppArgs.size) :
    AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
  have hall :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    have harity := isValidIndAppIdx.arity hvalid
    rw [harity]
    cases hclean :
        (type.getAppArgs.extract stats.params.size
          (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  have hk : j - stats.params.size <
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).size := by
    simp only [Array.size_extract]
    omega
  have hclean := Array.all_eq_true.mp hall (j - stats.params.size) hk
  simp only [Array.getElem_extract] at hclean
  have hj : stats.params.size + (j - stats.params.size) = j := by omega
  simp only [hj] at hclean
  cases hocc : AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] <;>
    simp_all

theorem isValidIndAppFrom?_some
    (h : AddInductive.isValidIndAppFrom? stats type start fuel = some i) :
    start ≤ i ∧ i < start + fuel ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  induction fuel generalizing start with
  | zero => simp [AddInductive.isValidIndAppFrom?] at h
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?] at h
    by_cases hvalid : AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hvalid] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hvalid⟩
    · have hfalse : AddInductive.isValidIndAppIdx stats type start = false := by
        cases hv : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hvalid hv)
      simp [hfalse] at h
      rcases ih h with ⟨hlower, hupper, hvalid⟩
      exact ⟨by omega, by omega, hvalid⟩

theorem isValidIndApp?_some
    (h : AddInductive.isValidIndApp? stats type = some i) :
    i < stats.indConsts.size ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  exact ⟨by simpa using (isValidIndAppFrom?_some h).2.1,
    (isValidIndAppFrom?_some h).2.2⟩

/-- A validated concrete parameter argument translates to the corresponding
abstract de Bruijn parameter.  The fvar-shape invariant is what upgrades
structural `Expr` equality to exact syntax translation here. -/
theorem ValidAppStatsWF.translatedParam
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlen := forall₂_length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlen, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := forall₂_get?_eq_some hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

def VLCtx.NoIndConsts (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.containsAnyConst names = false

theorem VLCtx.NoIndConsts.cons {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    VLCtx.NoIndConsts names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    simpa using H hfind

/-- Absence of a newly declared constant is preserved by syntax translation.
Literal expansion and projection translation are explicit side conditions:
literals introduce old primitive constants, while `TrProj` is still an
independent typing boundary in the existing model. -/
theorem TrExprS.noIndOcc
    (halign : IndConstNames indConsts names)
    (hlit : LiteralDisjoint indConsts)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e')
    (hno : AddInductive.hasIndOcc indConsts e = false) :
    e'.containsAnyConst names = false := by
  rw [hasIndOcc_eq_findAny] at hno
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | const _ _ _ =>
    simp only [Expr.findAny] at hno
    change names.contains _ = false
    rw [← halign]
    exact hno
  | app _ _ _ _ ihFn ihArg =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hfn, harg⟩
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx hfn, ihArg hctx harg⟩
  | lam _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨htyValue, hbody⟩
    rcases Bool.or_eq_false_iff.mp htyValue with ⟨hty, hvalue⟩
    have hvalue' := ihValue hctx hvalue
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none) hvalue') hbody
  | lit _ _ ih =>
    apply ih hctx
    rw [← hasIndOcc_eq_findAny]
    exact hlit _
  | mdata _ ih =>
    simpa only [Expr.findAny, Bool.false_or] using ih hctx hno
  | proj _ Hproj ih =>
    simp only [Expr.findAny, Bool.false_or] at hno
    exact hproj Hproj (ih hctx hno)

theorem ValidAppStatsWF.translatedIndexNoOccurrence
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].containsAnyConst (decl.types.map (·.name)) = false := by
  have hlen := forall₂_length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlen]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := forall₂_get?_eq_some hargs hsource htarget
  have hno := isValidIndAppIdx.indexNoOccurrence hvalid hlower hjArgs
  exact TrExprS.noIndOcc H.consts.names hlit hctx hproj harg hno

theorem isValidIndAppIdx.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (htarget : target = none ∨ target = some decl.types[typeIdx].name)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt target depth type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlen := List.mapM_some_length hlevels
    have hstats := H.levels
    omega
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := forall₂_length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalid hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, htarget,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalid hargs hlit hctx hproj
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

theorem isValidIndApp?.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt none depth type' := by
  rcases isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  exact isValidIndAppIdx.validIndAppAt H hi' htr hvalidIdx
    (Or.inl rfl) hlit hctx hproj

theorem noOccurrence.WF
    {type : Expr} {Q : Unit → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok ()).WF Q
  exact Except.WF.pure hQ

/-- The successful fast path of executable positivity establishes the
declarative nonrecursive case.  All non-syntactic correspondence assumptions
are named at the boundary: the accumulated mutual constants, local-variable
translation, literal expansion, and projection translation. -/
theorem noOccurrence.refines
    {decl : VInductDecl} {type' : VExpr} {depth : Nat} {ctx : List VExpr}
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htr : TrExprS env Us Δ type type')
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact noOccurrence.WF
    (Q := fun _ => decl.SyntacticallyPositive env ctx depth type')
    hocc (.nonrecursive <|
      checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit hctx hproj htr hocc)

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

/-- Once the application-spine refinement supplies `ValidIndAppAt`, the final
executable success branch is exactly the declarative recursive positivity
constructor. -/
theorem validApplication.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hrefines : decl.ValidIndAppAt none depth type') :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact validApplication.WF hocc hforall hvalid (.recursive hrefines)

theorem validApplication.sourceRefines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  apply validApplication.refines hocc hforall hvalid
  exact isValidIndApp?.validIndAppAt Hstats htr hvalid hlit hctx hproj

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

theorem negativeDomain.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_pos hdomOcc]
  change (Except.error _).WF Q
  exact Except.WF.throw

/-- Positive higher-order branch after WHNF.  Source-domain annotation
transport is shared with header and constructor telescopes. -/
theorem forallE.sourceWF
    (Hc : ContextWF c)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_neg (by simp [hdomOcc])]
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => recur (body.instantiate1 arg))
    Hc Hdom.consumed Hdom.isType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    Hdom.consumed Hdom.isType hbody''
  exact Hrec body'' hbodyEq hopened

/-- The successful higher-order branch refines the declarative `forallE`
positivity rule.  The recursive checker runs in the consumed-annotation local
context, while its certificate is deliberately stated for the original
source-domain/body translation used by the independent specification. -/
theorem forallE.refines
    {decl : VInductDecl} {depth : Nat}
    (Hc : ContextWF c)
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (huvars : c.lparams.length = decl.uvars)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
        (fun _ => decl.Positive Hc.venv
          (consumedDom' :: Hc.mlctx.vlctx.toCtx) (depth + 1) body'')) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx depth
        (.forallE sourceDom' sourceBody')) := by
  have hdomNo := checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit
    hctx hproj Hdom.source hdomOcc
  refine forallE.sourceWF (Q := fun _ => decl.SyntacticallyPositive Hc.venv
      Hc.mlctx.vlctx.toCtx depth (.forallE sourceDom' sourceBody'))
      (recur := recur) (ctor := ctor)
      (idx := idx) Hc hocc hdomOcc Hdom hbody ?_
  intro body'' hbodyEq hopened
  exact (Hrec body'' hbodyEq hopened).mono fun _ hpositive => by
    rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
    rcases hbodyEq with ⟨bodyType, hbodyEq⟩
    exact .forallE hdomNo
      (by simpa [huvars] using hdomEq)
      (by simpa [huvars] using hbodyEq) hpositive

end checkPositivityStep

namespace checkConstructors.loopCtor

/-- The terminal constructor target check now discharges the declarative
`CtorTailWF.result` rule, rather than returning an unconstrained success. -/
theorem result.refines
    {decl : VInductDecl} {depth : Nat} {result type' exprType : VExpr}
    {ctorCtx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hdefeq : env.IsDefEq decl.uvars ctorCtx result type' exprType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF env decl.types[targetIdx]
        ctorCtx depth result) := by
  exact checkConstructors.loopCtor.result.WF
    (Q := fun _ => decl.CtorTailWF env decl.types[targetIdx]
      ctorCtx depth result)
    hforall hvalid (.result
      (checkPositivityStep.isValidIndAppIdx.validIndAppAt
        Hstats hi htr hvalid (Or.inr rfl) hlit hctx hproj)
      hdefeq)

/-- Semantic wrapper for a safe constructor field.  The low-level traversal
supplies source typing and annotation transport; this theorem packages those
facts as the declarative `CtorTailWF.field` rule. -/
theorem safeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF
      (fun _ => decl.Positive Hc.venv ctorCtx depth sourceDom'))
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.Positive Hc.venv ctorCtx depth sourceDom' →
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
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine safeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (Pos := decl.Positive Hc.venv ctorCtx depth sourceDom')
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody Hpos ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    hpositive body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound hpositive body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inr hpositive)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

theorem unsafeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (hunsafe : decl.isUnsafe = true)
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
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
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine unsafeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inl hunsafe)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

/-- Starting after the common constructor parameters, the complete executable
constructor-tail traversal builds `CtorTailWF`.  The remaining level-order
premise is isolated explicitly until `Level.geq` is connected to `VLevel.LE`. -/
theorem tailRefines
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hpositivity : ∀ {c : AddInductive.Context} {depth posIdx : Nat}
      {type : Expr} {type' : VExpr} (Hc : ContextWF c),
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
        Hc.mlctx.vlctx stats decl depth →
      checkPositivityStep.VLCtx.NoIndConsts
        (decl.types.map (·.name)) Hc.mlctx.vlctx →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type' →
      (AddInductive.checkPositivity stats type ctor posIdx c).WF
        (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type'))
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  induction fuel generalizing c type type' depth i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htr with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        have hparamNext : stats.params[i + 1]? = none := by
          rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
          omega
        cases isUnsafe with
        | false =>
          have Hpos := hpositivity (posIdx := i) Hc Hstats hctx
            (hdom.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
          exact safeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            Hpos hbound fun _ _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
        | true =>
          exact unsafeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            (hunsafe rfl) hbound fun _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact invalidResult.WF hforall hvalid
      · rcases htr.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf with
          ⟨exprType, htype⟩
        subst target
        exact result.refines Hstats hi htr hforall hvalid hlit hctx hproj
          (by simpa [Hstats.uvars] using htype)

end checkConstructors.loopCtor

namespace checkPositivity.loop

theorem zero.WF :
    (AddInductive.checkPositivity.loop stats ctor idx type 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkPositivity.loop] at h

theorem succ.WF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.WF Hc htype).bind fun normalized hnormalized =>
    Hstep normalized hnormalized

/-- The complete recursive positivity traversal refines the independent
declarative judgment.  In particular, every recursive call under a higher-
order binder performs and records its own WHNF/definitional-equality step. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    refine succ.WF Hc hsource ?_
    intro normalized hnormalized
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx
              depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using hsourceExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit hctx hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        exact finish <| checkPositivityStep.forallE.refines Hc Hstats.consts
          hlit hctx hproj hocc' hdomOcc' Hdom Hstats.uvars hbody
          fun body'' hbodyEq hopened => by
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
              Hc Hdom.consumed Hdom.isType
            have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
              apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
              rfl
            exact ih Hc' Hstats' hctx'
              (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    ·
      cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit hctx hproj hocc' hforall hvalid

end checkPositivity.loop

theorem checkPositivity.WF
    (Hloop : (AddInductive.checkPositivity.loop stats ctor idx type
      c.fuel.inductiveFuel c).WF Q) :
    (AddInductive.checkPositivity stats type ctor idx c).WF Q := by
  unfold AddInductive.checkPositivity
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact Hloop

/-- Public positivity refinement, including the production fuel lookup. -/
theorem checkPositivity.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refines Hc Hstats hconsume hlit hctx hproj htype

/-- Constructor-tail refinement with the verified positivity traversal plugged
into every safe field. -/
theorem checkConstructors.loopCtor.tailRefinesFull
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  apply checkConstructors.loopCtor.tailRefines Hc Hstats hi htarget
    hparamAt hconsume hlit hctx hproj hunsafe hbound
  · intro c' depth' posIdx type' type'' Hc' Hstats' hctx' htype'
    exact checkPositivity.refines Hc' Hstats' hconsume hlit hctx' hproj htype'
  · exact htr

/-- Aggregation boundary for constructors: once the common-parameter prefix
has supplied its independent `takeForalls` and parameter-conversion facts, the
verified executable tail establishes the public `CtorShape` judgment. -/
theorem checkConstructors.loopCtor.ctorShapeRefines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ownParams.reverse)
    (htailEq : type' = tail)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesFull
    (ctor := ctor) (fuel := fuel) Hc Hstats hi
    htarget hparamAt hconsume hlit hctx hproj hunsafe hbound htr
  exact Htail.mono fun _ htail => by
    subst type'
    exact ⟨normalized, ownParams, tail, exprType, hctor, htake, hparams,
      hctxEq ▸ htail⟩

@[simp] theorem VInductDecl.recursorName_eq_mkRecName
    (decl : VInductDecl) (type : VInductiveType) :
    decl.recursorName type = Lean.mkRecName type.name := rfl

/-- The production choice of an extra eliminator universe has exactly the two
universe arities admitted by `RecursorShape`. -/
theorem AddInductive.getRecLevelParams_length :
    (AddInductive.getRecLevelParams elimLevel lparams).length = lparams.length ∨
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel with
  | param u => simp [AddInductive.getRecLevelParams]
  | _ => simp [AddInductive.getRecLevelParams]

theorem AddInductive.getRecLevelParams_length_of_param
    (h : elimLevel.isParam = true) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

theorem AddInductive.getRecLevelParams_length_of_not_param
    (h : elimLevel.isParam = false) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

/-- Abstract domains introduced by `MLCtx.mkForall'`, in outermost-to-
innermost order. Local lets are discharged by `mkForall'` and contribute no
domain. -/
def MLCtxForallDomains (c : TypeChecker.MLCtx) :
    (n : Nat) → n ≤ c.length → List VExpr
  | 0, _ => []
  | n + 1, h =>
    match c with
    | .vlam _ _ _ type' _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h) ++ [type']
    | .vlet _ _ _ _ _ _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h)

theorem TypeChecker.MLCtx.mkForall'_eq_wrapForalls
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkForall' n hn body = VExpr.wrapForalls (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkForall', MLCtxForallDomains,
      VExpr.wrapForalls]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      rw [ih, VExpr.wrapForalls_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

theorem MLCtxLamPrefix.forallDomains
    (H : MLCtxLamPrefix c n domains) :
    MLCtxForallDomains c n H.le = domains := by
  induction H with
  | nil => simp [MLCtxForallDomains]
  | cons H ih =>
    simp only [MLCtxForallDomains]
    change MLCtxForallDomains _ _ H.le ++ [_] = _
    rw [ih]

theorem MLCtxLamPrefix.mkForall'
    (H : MLCtxLamPrefix c n domains) (body : VExpr) :
    c.mkForall' n H.le body = VExpr.wrapForalls domains body := by
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, H.forallDomains]

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
