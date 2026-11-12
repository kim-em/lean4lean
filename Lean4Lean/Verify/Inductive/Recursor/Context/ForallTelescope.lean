import Lean4Lean.Verify.Expr.Abstraction
import Lean4Lean.Verify.LocalContext.Binding
import Lean4Lean.Verify.Typing.Translation
import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Typing.Telescope

/-! Inductive-checker adapters for forall and lambda telescopes.

Generic syntax comes from `Verify.Expr.Telescope`; anonymous-context translation,
residual typing and context conversion come from `Verify.Typing.Telescope`.
This module closes the header checking scopes (`SourceTelescope`, `ScopeEmbedding`,
`FrontScopeEmbedding`) and the recursor parameter suffix into those typed
certificates. It retains the phase-specific opening, positivity, local-context
array and binding-context lemmas used by the recursor construction. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

attribute [simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj

/-- An expression without free variables is unchanged by abstraction. -/
theorem FVarsIn.abstractN_eq_self {e : Expr} (h : FVarsIn (fun _ => False) e)
    (xs : List FVarId) (k : Nat) : e.abstractN xs k = e := by
  induction e generalizing k with
  | fvar v => exact absurd h id
  | bvar | const | sort | mvar | lit => rfl
  | mdata _ e ih | proj _ _ e ih => simp [Expr.abstractN, ih h]
  | app f a ihf iha => simp [Expr.abstractN, ihf h.1, iha h.2]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb => simp [Expr.abstractN, iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb => simp [Expr.abstractN, iht h.1, ihv h.2.1, ihb h.2.2]

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

theorem _root_.Lean4Lean.Closed.mkAppList_iff {fn : Expr} {args : List Expr}
    {k : Nat} :
    Closed (Expr.mkAppList fn args) k ↔
      Closed fn k ∧ ∀ a ∈ args, Closed a k := by
  induction args generalizing fn with
  | nil => simp [Expr.mkAppList]
  | cons a as ih =>
    simp only [Expr.mkAppList, ih, Closed, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩

theorem _root_.Lean4Lean.Closed.getAppArgsList_at {e : Expr} {k : Nat}
    (h : Closed e k) {a : Expr} (ha : a ∈ e.getAppArgsList) : Closed a k := by
  have h' : Closed (Expr.mkAppList e.getAppFn e.getAppArgsList) k := by
    rwa [Expr.mkAppList_getAppArgsList]
  exact (Closed.mkAppList_iff.mp h').2 a ha

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

/-- Conversely, closing fresh field variables cannot turn an invalid application into a
valid one. With `abstractList`, this shows that validity does not depend on the names of
the field variables, which differ between the constructor check and the recursor
construction. -/
theorem checkPositivityStep.isValidIndAppIdx.of_abstractList
    (paramFvars binders : List FVarId) (k : Nat := 0)
    (hvalid : AddInductive.isValidIndAppIdx stats
      (type.abstractList binders k) i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFvars.map Expr.fvar).toArray) :
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
      Expr.abstractList_eq_fvar habstractArg
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

/-- The opening of a constructor telescope by a field traversal. `current` is the opened
residual the executable sees, while `residual` is the same point of the source telescope
with all opened fields closed back to de Bruijn variables, which does not depend on the
names chosen for the fields. -/
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

/-- Extend the opening by the fresh field chosen by `withLocalDecl`. -/
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

/-- Close the front of a front scope embedding. The abstract target is unchanged; the
source is abstracted over the front's free variables in oldest-first order, and the
resulting anonymous telescope sits directly above the base scope. -/
theorem checkInductiveTypes.loopType.FrontScopeEmbedding.abstractFront
    (H : checkInductiveTypes.loopType.FrontScopeEmbedding
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
    simp [scopePrefix, tail]
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

/-- The free variables of a scope are those of its front followed by those of its
base. -/
theorem checkInductiveTypes.loopType.FrontScopeEmbedding.frontFVars
    (H : checkInductiveTypes.loopType.FrontScopeEmbedding
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

/-- Close every declaration of a (not necessarily contiguous) scope embedding. The binder
order is `scope.fvars`, so the resulting anonymous telescope abstracts the source in
oldest-first order without assuming that the declarations form a prefix of the executable
context. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.abstractAll
    (H : checkInductiveTypes.loopType.ScopeEmbedding
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

/-- The anonymous telescope obtained by closing a scope embedding is well formed. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.abstractAllWF
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    OnCtx (abstractForallContext scope.toCtx.reverse []).toCtx
      (env.IsType Us.length) := by
  have Hscope := (H.scopeWF henv).toCtx
  simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hscope

/-- Closing a body over a source telescope gives one forall per declaration of the scope,
with the simultaneous abstraction in oldest-first order as residual. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeSource_telescope
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (_hnodup : scope.fvars.Nodup) (body : Expr) :
    Expr.ForallTelescope (H.closeSource body) scope.length
      (body.abstractN scope.fvars.reverse) := by
  clear _hnodup
  induction H generalizing body with
  | nil =>
    have hfvars : (VLCtx.fvars ([] : VLCtx)) = [] := rfl
    simp only [SourceTelescope.closeSource, hfvars, List.reverse_nil,
      Expr.abstractN_nil, List.length_nil]
    exact .nil body
  | @cons scope domainTarget fv deps tail name binderInfo domain Hdomain ih =>
    let innerBody := body.abstractN [fv]
    have Houter := ih (.forallE name domain innerBody binderInfo)
    have Houter' : Expr.ForallTelescope
        (tail.closeSource (.forallE name domain innerBody binderInfo))
        scope.length
        (.forallE name (domain.abstractN scope.fvars.reverse)
          (innerBody.abstractN scope.fvars.reverse 1) binderInfo) := by
      simpa [innerBody, Expr.abstractN] using Houter
    have Hinner : Expr.ForallTelescope
        (.forallE name (domain.abstractN scope.fvars.reverse)
          (innerBody.abstractN scope.fvars.reverse 1) binderInfo)
        1 (innerBody.abstractN scope.fvars.reverse 1) := by
      simpa using Expr.ForallTelescope.cons
        (Expr.ForallTelescope.nil
          (innerBody.abstractN scope.fvars.reverse 1))
    have Hcombined := Houter'.trans Hinner
    have hresidual :
        (body.abstractN [fv]).abstractN scope.fvars.reverse 1 =
          body.abstractN (fv :: scope.fvars).reverse := by
      rw [List.reverse_cons, Expr.abstractN_append]
      rfl
    rw [hresidual] at Hcombined
    simpa [SourceTelescope.closeSource] using Hcombined

/-- Closing a translated type over a source telescope translates to the forall telescope
over the scope's abstract domains, in oldest-first order. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeTranslation
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (Hscope : scope.WF env Us.length)
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
    have hbodyClosed : Closed body := by
      have h := Hbody.closed
      simpa [VLCtx.bvars, tail.noBV] using h
    have h1 : body.abstractN [fv] = body.abstract1 fv :=
      Expr.abstractN_singleton hbodyClosed.looseBVarRange_le
    simpa [h1, SourceTelescope.closeSource, VLCtx.toCtx,
      List.reverse_cons, VExpr.wrapForalls] using Hclosed

/-- Binder-by-binder form of `closeTranslation`. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeTypedTelescope
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (Hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  have Htranslation := H.closeTranslation Hscope Hbody HbodyType
  have Htelescope := H.closeSource_telescope Hscope.fvars_nodup body
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
    apply VEnv.IsType.wrapForalls
    · simpa using Hscope.toCtx
    · simpa using HbodyType
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope Htranslation HtargetType

/-- Binder-by-binder form of `closeTranslation` for a scope embedding: closing a
translated type over the scope (which need not be contiguous) gives a closed typed
telescope. The body may itself be a dependent telescope. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closeTypedTelescope
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sourceTelescope.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  exact H.sourceTelescope.closeTypedTelescope (H.scopeWF henv)
    Hbody HbodyType

/-- Close the source declarations of a scope embedding around `Sort 0`. This is a
translation of the scope's telescope on its own, rather than of a later expression
under it. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closedSortTranslation
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    TrExprS env Us []
      (H.sourceTelescope.closeSource (.sort (.zero : Level)))
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
  have Hclosed := H.sourceTelescope.closeTranslation HscopeWF
    Hsort HsortType
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    apply VEnv.IsType.wrapForalls
    · simpa using HscopeWF.toCtx
    · simpa using HsortType
  exact ⟨Hclosed, HtargetType⟩

/-- Binder-by-binder form of `closedSortTranslation`. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closedSortTelescope
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sourceTelescope.closeSource (.sort (.zero : Level))) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
  rcases H.closedSortTranslation henv with ⟨Htranslation, Htype⟩
  have Htelescope := H.sourceTelescope.closeSource_telescope
    (H.scopeWF henv).fvars_nodup (.sort (.zero : Level))
  have Htelescope' : Expr.ForallTelescope
      (H.sourceTelescope.closeSource (.sort (.zero : Level))) scope.length
      (.sort (.zero : Level)) := by
    have hsort : ∀ fvars : List FVarId,
        (Expr.sort (.zero : Level)).abstractN fvars =
          .sort (.zero : Level) := fun _ => rfl
    rw [hsort] at Htelescope
    exact Htelescope
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope' Htranslation Htype

/-- A selected executable array consists solely of ordinary free-variable
declarations in the retained local context. -/
structure CDeclArray (lctx : LocalContext) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  declarations : ∀ fv ∈ fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

/-- `LocalContext.mkLambda` uses one literal binder prefix for any two
residual bodies when it closes the same duplicate-free local selection. -/
theorem CDeclArray.sameLambdaPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameLambdaPrefix xs.size
      (lctx.mkLambda xs left) (lctx.mkLambda xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkLambda, LocalContext.mkLambda,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameLambdaPrefixN_fold hdecl left right

/-- `mkForall` and `mkLambda` close two residuals with the same literal
ordinary-declaration prefix when they use the same duplicate-free local
selection. -/
theorem CDeclArray.sameForallLambdaPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix xs.size
      (lctx.mkForall xs forallBody) (lctx.mkLambda xs lambdaBody) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkLambda,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallLambdaPrefixN_fold hdecl
    forallBody lambdaBody

/-- An array of free variables, each a member of the local context of `c`. Membership is
preserved when the recursor construction adds binders. -/
structure FVarArrayIn (c : AddInductive.Context) (xs : Array Expr) where
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
theorem ParameterContextSuffix.parameterDecls_fvars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth) :
    H.parameterDecls.fvars = (ExprArrayFVarIds stats.params).reverse := by
  rcases cachedParameterDecls_fvars H.cached with
    ⟨fvars, hparams, hdecls⟩
  rw [hdecls]
  have hids := congrArg (List.map recursorFVarId) hparams
  simpa [ExprArrayFVarIds, List.map_reverse, Function.comp_def,
    recursorFVarId] using hids.symm

/-- Close the cached parameter suffix outside an anonymous inner telescope. The source
parameter order is that of the parameter array used by the recursor construction, and the
abstract domains are those cached by the header phase. -/
theorem ParameterContextSuffix.abstractParameters
    {c root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth)
    (Hparams : FVarArrayIn root stats.params)
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

/-- The cached parameters form a dependency-closed subset (an up-set) of the recursor
context: motives and minors are newer ambient declarations, so no parameter depends on
them. -/
theorem ParameterContextSuffix.parameterFVarsUp
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth) :
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

/-- Typed form of `closedSortTranslation`: the closed parameter telescope translates and
is a type, so its domains can be opened as the base context of a later telescope. -/
theorem ParameterContextSuffix.closedSortTyped
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth) :
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
    simpa [parameterMLCtx] using H.headerVLCtx
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
      LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN]
    apply LocalContext.mkBindingListN_congr
    intro fv hfv
    apply R.onlyLams.dropN_find?_eq R.mlctx_wf depth H.depth_le
    exact List.mem_reverse.mp hfv
  have hsource : parameterMLCtx.lctx.mkForall stats.params
        (.sort (.zero : Level)) =
      parameterMLCtx.mkForall parameterMLCtx.length (Nat.le_refl _)
        (.sort (.zero : Level)) :=
    hparameterWF.mkForall_eq parameterMLCtx.length (Nat.le_refl _) hparams trivial
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

/-- `Sort 0` closed over the cached parameter declarations translates. This gives a
translation of the parameter telescope on its own, whose prefix can be compared with any
executable telescope closed over the same parameters. -/
theorem ParameterContextSuffix.closedSortTranslation
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth) :
    TrExprS R.venv recLparams []
      (R.mlctx.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) :=
  H.closedSortTyped.1

/-- The parameter array `stats.params` used by `mkRecInfos` is an array of free variables
of the header context. -/
def ParameterContextSuffix.paramsBound
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc.toSemantics stats depth) :
    FVarArrayIn c stats.params := by
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

theorem ParameterContextSuffix.paramsBound_nodup
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc.toSemantics stats depth) :
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

/-- Changing only the checker context keeps the binding context. -/
theorem BindingContextLE.checkLCtx (c : AddInductive.Context) (l : LocalContext) :
    BindingContextLE { c with checkLCtx := l } c :=
  ⟨fun _ => id, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BindingContextLE.checkLCtx_rev (c : AddInductive.Context) (l : LocalContext) :
    BindingContextLE c { c with checkLCtx := l } :=
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

theorem MLCtxTopAgree.mkForall_eq {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (ha : n ≤ a.length) (hb : n ≤ b.length)
    (e : Expr) : a.mkForall n ha e = b.mkForall n hb e := by
  induction H generalizing e with
  | zero => simp
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.mkForall]
    exact ih _ _ _

theorem MLCtxTopAgree.forallTelescope {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ {W : Expr} {k : Nat} {rW : Expr}, Expr.ForallTelescope W k rW →
      ∃ r, Expr.ForallTelescope (b.mkForall n hb W) (n + k) r := by
  induction H with
  | zero => intro W k rW HW; exact ⟨rW, by simpa using HW⟩
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro W k rW HW
    simp only [TypeChecker.MLCtx.mkForall]
    have Habs := HW.abstract1 fv 0
    have Hcons : Expr.ForallTelescope
        (.forallE name ty (W.abstract1 fv) bi) (k + 1)
        (rW.abstract1 fv (0 + k)) := .cons Habs
    obtain ⟨r, Hr⟩ := ih (Nat.le_of_succ_le_succ hb) Hcons
    exact ⟨r, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hr⟩

theorem MLCtxTopAgree.binderAt_shift {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ {j : Nat} {d : Expr}, ∃ d', ∀ W : Expr, Expr.ForallBinderAt W j d →
      Expr.ForallBinderAt (b.mkForall n hb W) (n + j) d' := by
  induction H with
  | zero => intro j d; exact ⟨d, fun W h => by simpa using h⟩
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro j d
    obtain ⟨d', Hd'⟩ := ih (Nat.le_of_succ_le_succ hb)
      (j := j + 1) (d := d.abstract1 fv j)
    refine ⟨d', fun W HW => ?_⟩
    simp only [TypeChecker.MLCtx.mkForall]
    have Habs := HW.abstract1 fv 0
    have Hthere : Expr.ForallBinderAt
        (.forallE name ty (W.abstract1 fv) bi) (j + 1) (d.abstract1 fv j) := by
      simpa using Expr.ForallBinderAt.there (name := name)
        (outerDomain := ty) (bi := bi) Habs
    have := Hd' _ Hthere
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem MLCtxTopAgree.binderAt_indep {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ i < n, ∃ d, ∀ W : Expr, Expr.ForallBinderAt (b.mkForall n hb W) i d := by
  induction H with
  | zero => intro i hi; omega
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro i hi
    simp only [TypeChecker.MLCtx.mkForall]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨d, Hd⟩ := ih (Nat.le_of_succ_le_succ hb) i hi
      exact ⟨d, fun W => Hd _⟩
    · obtain ⟨d', Hd'⟩ := MLCtxTopAgree.binderAt_shift h
        (Nat.le_of_succ_le_succ hb) (j := 0) (d := ty)
      refine ⟨d', fun W => ?_⟩
      simpa using Hd' _ (Expr.ForallBinderAt.here (name := name)
        (domain := ty) (body := W.abstract1 fv) (bi := bi))

end VerifyInductive
end Lean4Lean
