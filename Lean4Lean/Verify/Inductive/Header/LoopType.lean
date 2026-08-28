import Lean4Lean.Verify.Inductive.Context

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopType

/-- Abstract images of the concrete parameter cache after `done` parameter
binders and `depth` subsequent index binders.  Its recursive presentation
matches the executable `Array.push` order exactly. -/
def cachedParamVars : Nat → Nat → List VExpr
  | 0, _ => []
  | done + 1, depth =>
    (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
      [.bvar depth]

@[simp] theorem cachedParamVars_zero : cachedParamVars 0 depth = [] := rfl

@[simp] theorem cachedParamVars_succ :
    cachedParamVars (done + 1) depth =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
        [.bvar depth] := rfl

@[simp] theorem cachedParamVars_length :
    (cachedParamVars done depth).length = done := by
  induction done with
  | zero => rfl
  | succ done ih => simp [cachedParamVars_succ, ih]

theorem cachedParamVars_getElem? :
    (cachedParamVars done depth)[i]? =
      if i < done then some (.bvar (depth + (done - 1 - i))) else none := by
  induction done generalizing depth i with
  | zero => simp
  | succ done ih =>
    simp only [cachedParamVars_succ]
    by_cases hprior : i < done
    · rw [List.getElem?_append_left (by simp [hprior])]
      rw [List.getElem?_map, ih]
      simp only [hprior, if_true, Option.map_some]
      simp [VExpr.liftN]
      congr 2
      omega
    · by_cases hcurrent : i < done + 1
      · have hieq : i = done := by omega
        subst i
        simp
      · have hout : done + 1 ≤ i := by omega
        rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
        simp [hcurrent]

@[simp] theorem cachedParamVars_depth_succ :
    cachedParamVars done (depth + 1) =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) := by
  induction done with
  | zero => rfl
  | succ done ih =>
    simp [cachedParamVars_succ, ih, List.map_map, VExpr.liftN,
      Function.comp_def]

theorem cachedParamVars_eq_paramVars (decl : VInductDecl) :
    cachedParamVars decl.nparams depth = decl.paramVars depth := by
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < decl.nparams
  · rw [VInductDecl.paramVars, List.getElem?_map]
    rw [List.getElem?_reverse (by simp [hi])]
    have hj : decl.nparams - 1 - i < decl.nparams := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by
      simp [VInductDecl.paramVars]
      omega)]
    simp [hi]

theorem cachedParamVars_zero_eq_recursorCanonicalVars (n : Nat) :
    cachedParamVars n 0 = recursorCanonicalVars n := by
  unfold recursorCanonicalVars
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < n
  · rw [List.getElem?_map, List.getElem?_reverse (by simp [hi])]
    have hj : n - 1 - i < n := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
    simp [hi]

/-- Local invariant for the first header's common-parameter branch. -/
structure ParameterCachePrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (done depth : Nat) : Prop where
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (cachedParamVars done depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- A concrete cached parameter and the free-variable declaration that owns
it in the retained verifier context. -/
def CachedParameterDecl (param : Expr)
    (entry : Option (FVarId × List FVarId) × VLocalDecl) : Prop :=
  ∃ fv deps type,
    param = .fvar fv ∧ entry = (some (fv, deps), .vlam type)

theorem VLCtx.toCtx_length_le (scope : VLCtx) :
    (VLCtx.toCtx scope).length ≤ scope.length := by
  induction scope with
  | nil => exact Nat.le_refl 0
  | cons entry scope ih =>
    rcases entry with ⟨ofv, decl⟩
    cases decl <;> simp [VLCtx.toCtx] <;> omega

/-- Cached parameter declarations are all lambda declarations, so conversion
to the abstract typing context drops no entries. -/
theorem CachedParameterDecl.forall₂_toCtx_length
    (H : List.Forall₂ CachedParameterDecl params scope) :
    (VLCtx.toCtx scope).length = scope.length := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨fv, deps, type, rfl, rfl⟩
    simp [VLCtx.toCtx, ih]

/-- Structural companion to `ParameterCachePrefix`.  Cached parameter local
declarations form an exact suffix of the retained context; every index added
after the parameter phase belongs to `ambientDecls`.  The reverse is
intentional:
the executable array stores parameters from oldest to newest, while local
declarations are pushed at the head.

This suffix decomposition is what lets later mutual headers discard ambient
indices and not-yet-used cached parameters before applying
`TrExprS.uninstantiateAfterWeakFV`. -/
structure ParameterContextSuffix (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : Hc.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂ CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  narrowParams : List.Forall₂
    (TrExprS Hc.venv c.lparams parameterDecls)
    stats.params.toList (cachedParamVars stats.params.size 0)

/-- Reindex a parameter cache across statistics updates that leave the
cached parameter array unchanged. -/
def ParameterCachePrefix.reindex
    (H : ParameterCachePrefix env Us Δ stats done depth)
    (hparams : stats'.params = stats.params) :
    ParameterCachePrefix env Us Δ stats' done depth where
  params := by rw [hparams]; exact H.params
  paramFVars := by rw [hparams]; exact H.paramFVars

/-- Reindex the exact cached suffix across a statistics update that changes
only per-header output fields. -/
def ParameterContextSuffix.reindex
    (H : ParameterContextSuffix Hc stats depth)
    (hparams : stats'.params = stats.params) :
    ParameterContextSuffix Hc stats' depth where
  ambientDecls := H.ambientDecls
  parameterDecls := H.parameterDecls
  context := H.context
  prefixLength := H.prefixLength
  cached := by rw [hparams]; exact H.cached
  narrowParams := by rw [hparams]; exact H.narrowParams

def _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts
    (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.containsAnyConst names = false

theorem _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : checkPositivityStep.VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    checkPositivityStep.VLCtx.NoIndConsts names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    simpa only [VExpr.containsAnyConst_liftN] using H hfind

abbrev _root_.Lean4Lean.VLCtx.NoIndConsts :=
  checkPositivityStep.VLCtx.NoIndConsts

theorem _root_.Lean4Lean.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    VLCtx.NoIndConsts names ((ofv, d) :: Δ) :=
  checkPositivityStep.VLCtx.NoIndConsts.cons H hvalue

/-- Every local introduced by the inductive machinery denotes its own bound
variable.  Consequently restoring a dropped suffix of such locals cannot
introduce an inductive constant into context lookup results. -/
theorem MLCtxOnlyLams.noIndConsts_of_dropN
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length)
    (hdrop : VLCtx.NoIndConsts names (m.dropN n hn).vlctx) :
    VLCtx.NoIndConsts names m.vlctx := by
  induction n generalizing m with
  | zero =>
    intro v mapped type hfind
    exact hdrop hfind
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      have Htail := H.tail_vlam
      have htail : VLCtx.NoIndConsts names tail.vlctx := by
        apply ih Htail (Nat.le_of_succ_le_succ hn)
        intro v mapped type hfind
        exact hdrop hfind
      change checkPositivityStep.VLCtx.NoIndConsts names
        ((some (fv, type.fvarsList), .vlam type') :: tail.vlctx)
      exact checkPositivityStep.VLCtx.NoIndConsts.cons htail rfl
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- A lambda-only translated local context can return only bound variables
from lookup, independently of the constants appearing in binder types. -/
theorem MLCtxOnlyLams.noIndConsts
    (H : MLCtxOnlyLams m) : VLCtx.NoIndConsts names m.vlctx := by
  induction m with
  | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
  | vlam fv name type type' bi tail ih =>
      exact VLCtx.NoIndConsts.cons (ih H.tail_vlam) rfl
  | vlet fv name type value type' value' tail ih =>
      exact H.vlet_false.elim

theorem ParameterContextSuffix.noIndConsts
    (H : ParameterContextSuffix Hc stats depth) (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ CachedParameterDecl params entries →
      checkPositivityStep.VLCtx.NoIndConsts names entries := by
    intro params entries hcached
    induction hcached with
    | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
    | @cons param entry params entries hentry _ ih =>
      rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
      exact checkPositivityStep.VLCtx.NoIndConsts.cons ih rfl
  intro v mapped type hfind
  exact go H.cached hfind

/-- A semantic header scope embedded in the larger executable local context.
`expanded` is the literal weakening of the narrow scope; it is kept separate
from `runtime` because annotation consumption can replace an installed binder
domain by a merely definitionally equal expression. -/
inductive FrontFVLift : List VExpr → List VExpr →
    VLCtx → VLCtx → Lift → Prop
  | zero (W : VLCtx.FVLift' scope expanded 0 shift 0) :
      FrontFVLift [] [] scope expanded shift
  | cons (fv deps indexType)
      (hdeps : deps ⊆ scope.fvars)
      (H : FrontFVLift sourceDomains expandedDomains
        scope expanded shift) :
      FrontFVLift (sourceDomains ++ [indexType])
        (expandedDomains ++ [indexType.lift' shift])
        ((some (fv, deps), .vlam indexType) :: scope)
        ((some (fv, deps), .vlam (indexType.lift' shift)) :: expanded)
        (shift.consN 1)

theorem FrontFVLift.sourcePrefix
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (scope.toCtx.take sourceDomains.length).reverse = sourceDomains := by
  induction H with
  | zero => rfl
  | cons fv deps indexType _ H ih =>
    simp [VLCtx.toCtx, ih, List.take_succ_cons, List.reverse_cons]

theorem FrontFVLift.expandedPrefix
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (expanded.toCtx.take expandedDomains.length).reverse =
      expandedDomains := by
  induction H with
  | zero => rfl
  | cons fv deps indexType _ H ih =>
    simp [VLCtx.toCtx, ih, List.take_succ_cons, List.reverse_cons]

theorem FrontFVLift.length_eq
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    sourceDomains.length = expandedDomains.length := by
  induction H with
  | zero => rfl
  | cons _ _ _ _ _ ih => simpa using congrArg Nat.succ ih

theorem FrontFVLift.sourceLengthLE
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    sourceDomains.length ≤ scope.toCtx.length := by
  induction H with
  | zero => simp
  | cons _ _ _ _ _ ih => simpa [VLCtx.toCtx] using Nat.succ_le_succ ih

theorem FrontFVLift.sourceLengthLEScope
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    sourceDomains.length ≤ scope.length := by
  induction H with
  | zero => simp
  | cons _ _ _ _ _ ih => simpa using Nat.succ_le_succ ih

theorem FrontFVLift.sourceBaseBVars
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    VLCtx.bvars (scope.drop sourceDomains.length) = VLCtx.bvars scope := by
  induction H with
  | zero => rfl
  | cons fv deps indexType hdeps H ih =>
    simpa [VLCtx.bvars] using ih

theorem FrontFVLift.expandedLengthLE
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    expandedDomains.length ≤ expanded.toCtx.length := by
  induction H with
  | zero => simp
  | cons _ _ _ _ _ ih => simpa [VLCtx.toCtx] using Nat.succ_le_succ ih

theorem FrontFVLift.sourceContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    VLCtx.toCtx scope =
      sourceDomains.reverse ++
        VLCtx.toCtx (scope.drop sourceDomains.length) := by
  induction H with
  | zero => simp
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    simpa [VLCtx.toCtx, List.reverse_append, List.append_assoc] using
      congrArg (indexType :: ·) ih

/-- The retained source front consists exactly of named lambda declarations.
This is the declaration-shape premise needed to turn those free variables
back into the anonymous binders of the canonical equation telescope. -/
theorem FrontFVLift.sourceDeclarations
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      (VLCtx.fvars (scope.take sourceDomains.length))
      (scope.take sourceDomains.length) := by
  induction H with
  | zero => exact .nil
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp only [List.length_append, List.length_singleton, Nat.add_one,
      List.take_succ_cons, VLCtx.fvars_cons_some]
    exact List.Forall₂.cons (by exact ⟨deps, indexType, rfl⟩) ih

/-- The expanded side of a retained front consists of the same named lambda
declarations, with each domain weakened by the accumulated embedding. -/
theorem FrontFVLift.expandedDeclarations
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      (VLCtx.fvars (expanded.take expandedDomains.length))
      (expanded.take expandedDomains.length) := by
  induction H with
  | zero => exact .nil
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp only [List.length_append, List.length_singleton, Nat.add_one,
      List.take_succ_cons, VLCtx.fvars_cons_some]
    exact List.Forall₂.cons
      (by exact ⟨deps, indexType.lift' shift, rfl⟩) ih

/-- `toCtx` sees every declaration in the retained source prefix because
`withIndex` adds lambdas only. -/
theorem FrontFVLift.sourceTakenContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (VLCtx.toCtx (scope.take sourceDomains.length)).reverse =
      sourceDomains := by
  induction H with
  | zero => rfl
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp [List.take_succ_cons, VLCtx.toCtx, ih, List.reverse_cons]

theorem FrontFVLift.expandedTakenContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (VLCtx.toCtx (expanded.take expandedDomains.length)).reverse =
      expandedDomains := by
  induction H with
  | zero => rfl
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp [List.take_succ_cons, VLCtx.toCtx, ih, List.reverse_cons]

/-- Taking a declaration prefix can only remove free-variable names. -/
theorem _root_.Lean4Lean.VLCtx.fvars_take_sublist
    (scope : VLCtx) (n : Nat) :
    (VLCtx.fvars (scope.take n)).Sublist scope.fvars := by
  induction n generalizing scope with
  | zero => simp
  | succ n ih =>
    cases scope with
    | nil => simp
    | cons entry scope =>
      rcases entry with ⟨ofv, decl⟩
      cases ofv with
      | none => simpa using ih scope
      | some fv =>
        change (fv.1 :: VLCtx.fvars (scope.take n)).Sublist
          (fv.1 :: VLCtx.fvars scope)
        exact List.cons_sublist_cons.mpr (ih scope)

theorem FrontFVLift.expandedContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    VLCtx.toCtx expanded =
      expandedDomains.reverse ++
        VLCtx.toCtx (expanded.drop expandedDomains.length) := by
  induction H with
  | zero => simp
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    simpa [VLCtx.toCtx, List.reverse_append, List.append_assoc] using
      congrArg (indexType.lift' shift :: ·) ih

/-- Recover the fixed free-variable weakening below a front accumulated by
`withIndex`.  Removing the leading source and expanded declarations exposes
the same base weakening from which the front was built. -/
theorem FrontFVLift.base
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    ∃ baseScope baseExpanded baseShift,
      scope.drop sourceDomains.length = baseScope ∧
      expanded.drop expandedDomains.length = baseExpanded ∧
      shift = baseShift.consN sourceDomains.length ∧
      VLCtx.FVLift' baseScope baseExpanded 0 baseShift 0 := by
  induction H with
  | zero W =>
    exact ⟨_, _, _, rfl, rfl, by simp, W⟩
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    rcases ih with
      ⟨baseScope, baseExpanded, baseShift, hsource, hexpanded,
        hshift, Hbase⟩
    refine ⟨baseScope, baseExpanded, baseShift, ?_, ?_, ?_, Hbase⟩
    · simpa using hsource
    · simpa using hexpanded
    · rw [hshift]
      simp [Lift.consN]

theorem _root_.Lean4Lean.VLCtx.IsDefEq.drop
    (H : VLCtx.IsDefEq env U left right) (n : Nat) :
    VLCtx.IsDefEq env U (left.drop n) (right.drop n) := by
  induction n generalizing left right with
  | zero => exact H
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons H _ _ => exact ih H

/-- A verifier-context conversion preserves the named-lambda shape of every
selected leading declaration.  Domain expressions may differ, but the free
variable identifier and dependency metadata are shared by `VLCtx.IsDefEq`.
-/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.leftLambdaDeclarations
    (H : VLCtx.IsDefEq env U left right)
    (Hright : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvars (right.take n)) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvars (left.take n) := by
  induction n generalizing left right fvars with
  | zero =>
    have hfvars : fvars = [] :=
      List.eq_nil_of_length_eq_zero
        (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hright)
    subst fvars
    exact .nil
  | succ n ih =>
    cases H with
    | nil =>
      have hfvars : fvars = [] :=
        List.eq_nil_of_length_eq_zero
          (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hright)
      subst fvars
      exact .nil
    | @cons leftTail rightTail ofv leftDecl rightDecl Hctx _ Hdecl =>
      cases fvars with
      | nil => cases Hright
      | cons fv fvars =>
        simp only [List.take_succ_cons] at Hright ⊢
        cases Hright with
        | cons hentry Htail =>
          rcases hentry with ⟨deps, type, hentry⟩
          cases hentry
          cases Hdecl with
          | vlam Htype =>
            exact .cons ⟨deps, _, rfl⟩ (ih Hctx Htail)

theorem _root_.Lean4Lean.VLCtx.IsDefEq.bvars
    (H : VLCtx.IsDefEq env U left right) :
    VLCtx.bvars left = VLCtx.bvars right :=
  match H with
  | .nil => rfl
  | .cons (ofv := none) H _ _ => congrArg Nat.succ H.bvars
  | .cons (ofv := some _) H _ _ => H.bvars

theorem Lift.closeReopen_cons (shift : Lift) (n : Nat) :
    Lift.comp (Lift.comp (Lift.skipN .refl n) shift) (.skip .refl) =
      Lift.comp (Lift.skipN .refl (n + 1)) (.cons shift) := by
  induction shift generalizing n with
  | refl => simp [Lift.skipN_skipN]
  | skip shift ih => simp [ih, Lift.skipN_skipN]
  | cons shift ih =>
    cases n with
    | zero => rfl
    | succ n => simp [ih, Lift.skipN_skipN, Nat.add_assoc]

theorem VExpr.liftN_lift'_liftN_one (body : VExpr)
    (shift : Lift) (n : Nat) :
    ((body.liftN n 0).lift' shift).liftN 1 0 =
      (body.liftN (n + 1) 0).lift' shift.cons := by
  simp only [← VExpr.lift'_consN_skipN, Lift.consN, Lift.skipN,
    ← VExpr.lift'_comp]
  rw [Lift.closeReopen_cons]
  rw [show n + 1 = Nat.succ n by omega]
  rfl

/-- Closing the leading declarations represented by a front-preserving
free-variable lift and then reopening them in the ambient context commutes
strictly with weakening. -/
theorem FrontFVLift.closeReopen
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift)
    (body : VExpr) :
    ((VExpr.wrapForalls sourceDomains body).liftN
        sourceDomains.length 0).lift' shift =
      (VExpr.wrapForalls expandedDomains (body.lift' shift)).liftN
        expandedDomains.length 0 := by
  induction H generalizing body with
  | zero => simp [VExpr.wrapForalls]
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    have h := congrArg (fun result => result.liftN 1 0)
      (ih (.forallE indexType body))
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls, VExpr.liftN,
      VExpr.liftN_liftN, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, VExpr.liftN_lift'_liftN_one] using h

/-- Closing the retained front turns the full front-preserving shift into
the base shift below that front.  This is the non-reopened naturality law
needed when inverse weakening returns the production motive to its canonical
parameter scope. -/
theorem FrontFVLift.closeAtBase
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift)
    (baseShift : Lift)
    (hshift : shift = baseShift.consN sourceDomains.length)
    (body : VExpr) :
    (VExpr.wrapForalls sourceDomains body).lift' baseShift =
      VExpr.wrapForalls expandedDomains (body.lift' shift) := by
  induction H generalizing body baseShift with
  | zero =>
    simpa [VExpr.wrapForalls] using (congrArg (body.lift' ·) hshift).symm
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    have hprevious : shift = baseShift.consN sourceDomains.length := by
      simpa [Lift.consN] using hshift
    have h := ih baseShift hprevious (.forallE indexType body)
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls,
      VExpr.lift', Lift.consN] using h

structure NarrowRuntimeScope (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  frontSourceDomains : List VExpr
  frontExpandedDomains : List VExpr
  front : FrontFVLift frontSourceDomains frontExpandedDomains
    scope expanded shift
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  noIndConsts : ∀ names,
    checkPositivityStep.VLCtx.NoIndConsts names scope

def NarrowRuntimeScope.mono {env env' : VEnv} (henv : env ≤ env')
    (H : NarrowRuntimeScope env Us scope runtime) :
    NarrowRuntimeScope env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  frontSourceDomains := H.frontSourceDomains
  frontExpandedDomains := H.frontExpandedDomains
  front := H.front
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts

/-- Retarget only the executable context of a narrow scope along an exact
context equality.  The semantic front is copied field-by-field so its data
projections remain definitionally unchanged, rather than being hidden below
a dependent cast. -/
def NarrowRuntimeScope.retargetRuntime
    (H : NarrowRuntimeScope env Us scope runtime)
    (h : runtime = runtime') :
    NarrowRuntimeScope env Us scope runtime' where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  frontSourceDomains := H.frontSourceDomains
  frontExpandedDomains := H.frontExpandedDomains
  front := H.front
  context := by cases h; exact H.context
  upset := by cases h; exact H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts

theorem NarrowRuntimeScope.scopeWF
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF) :
    scope.WF env Us.length :=
  H.lift.wf henv H.context.wf

/-- Restrict a translated concrete expression to its semantic header scope.
The source-side free-variable premise is the deliberate ownership boundary:
ambient declarations retained by the executable loop may not occur. -/
theorem NarrowRuntimeScope.restrict
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ e', TrExprS env Us scope e e' := by
  exact htr.weakFV'_inv henv H.lift
    (H.context.symm henv.ordered) hclosed hfvars

/-- Restriction together with the definitional equality obtained by
weakening the narrowed translation back into the executable context. -/
theorem NarrowRuntimeScope.restrictEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ narrow', TrExprS env Us scope e narrow' ∧
      env.IsDefEqU Us.length runtime.toCtx e'
        (narrow'.lift' H.shift) := by
  rcases H.restrict henv htr hclosed hfvars with ⟨narrow', hnarrow⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  exact ⟨narrow', hnarrow,
    htr.uniq henv (H.context.symm henv.ordered) hweak⟩

/-- The abstract target computed in the executable context is the weakening
of the independently translated narrow target. -/
theorem NarrowRuntimeScope.fullTargetEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

/-- Restrict a runtime expression translation whose target is already known
in the semantic scope.  This packages the inverse-weakening argument needed
after executable WHNF: restrict the normalized source translation, compare
both weakened targets in the runtime context, then cancel the weakening. -/
theorem NarrowRuntimeScope.restrictTrExpr
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope input narrowTarget)
    (hfullInput : TrExpr env Us runtime input fullTarget)
    (hfullResult : TrExpr env Us runtime result fullTarget)
    (hclosed : Closed result 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) result) :
    TrExpr env Us scope result narrowTarget := by
  rcases hfullResult with ⟨resultFull, hresultFull, hresultTarget⟩
  rcases H.restrictEq henv hresultFull hclosed hfvars with
    ⟨resultNarrow, hresultNarrow, hresultLift⟩
  have htargetLift := H.fullTargetEq henv hnarrow hfullInput
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (resultNarrow.lift' H.shift) (narrowTarget.lift' H.shift) :=
    (hresultLift.symm.trans henv hruntimeWF hresultTarget).trans
      henv hruntimeWF htargetLift.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      resultNarrow narrowTarget :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨resultNarrow, hresultNarrow, hnarrowEq⟩

/-- Transfer a runtime typing result for a translated concrete expression
back to its independently translated target in the narrow scope. -/
theorem NarrowRuntimeScope.hasTypeOfFull
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExprS env Us runtime e full')
    (htype : env.HasType Us.length runtime.toCtx full' (.sort u)) :
    env.HasType Us.length scope.toCtx narrow' (.sort u) := by
  have htarget := H.fullTargetEq henv hnarrow
    (hfull.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htarget.symm
  have hexpanded := hliftTyped.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

/-- Transfer a full-runtime typing judgment when both the term and its type
have independently reconstructed translations in the narrow scope.  This is
the dependent counterpart of `hasTypeOfFull`: inverse weakening is applied
only after both sides have been aligned with their full-runtime targets. -/
theorem NarrowRuntimeScope.hasTypeOfFullPair
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrowTerm : TrExprS env Us scope term termNarrow)
    (hnarrowType : TrExprS env Us scope type typeNarrow)
    (hfullTerm : TrExprS env Us runtime term termFull)
    (hfullType : TrExprS env Us runtime type typeFull)
    (htype : env.HasType Us.length runtime.toCtx termFull typeFull) :
    env.HasType Us.length scope.toCtx termNarrow typeNarrow := by
  have htermTarget := H.fullTargetEq henv hnarrowTerm
    (hfullTerm.trExpr henv (H.context.symm henv.ordered).wf)
  have htypeTarget := H.fullTargetEq henv hnarrowType
    (hfullType.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htermTarget.symm
  have hliftTyped' := hliftTyped.defeqU_r henv hruntimeWF htypeTarget.symm
  have hexpanded := hliftTyped'.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

/-- Weaken a translated type from the independent header scope into the
executable reader context.  Context conversion may choose a definitionally
equal target, so the transported target is returned existentially together
with its preserved typehood. -/
theorem NarrowRuntimeScope.transportType
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us scope e narrow')
    (htype : env.IsType Us.length scope.toCtx narrow') :
    ∃ runtime', TrExprS env Us runtime e runtime' ∧
      env.IsType Us.length runtime.toCtx runtime' := by
  have hweak : TrExprS env Us H.expanded e (narrow'.lift' H.shift) := by
    simpa using htr.weakFV' henv.ordered H.lift H.context.wf
  have hweakType : env.IsType Us.length H.expanded.toCtx
      (narrow'.lift' H.shift) :=
    htype.weak' henv.ordered H.lift.toCtx
  rcases hweak.defeqDFC henv H.context with ⟨runtime', hruntime⟩
  have heq := hweak.uniq henv H.context hruntime
  have hweakTypeRuntime := hweakType.defeqDFC henv.ordered
    H.context.defeqCtx
  have heqRuntime := heq.defeqDFC henv.ordered H.context.defeqCtx
  exact ⟨runtime', hruntime,
    hweakTypeRuntime.defeqU_l henv
      (H.context.symm henv.ordered).wf.toCtx heqRuntime⟩

/-- Weaken a term together with its independently translated type from the
narrow parameter scope into the executable runtime context. -/
theorem NarrowRuntimeScope.transportTypedTerm
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hterm : TrExprS env Us scope term termTarget)
    (htype : TrExprS env Us scope type typeTarget)
    (htyping : env.HasType Us.length scope.toCtx termTarget typeTarget)
    (htypeType : env.IsType Us.length scope.toCtx typeTarget) :
    ∃ termRuntime typeRuntime,
      TrExprS env Us runtime term termRuntime ∧
      TrExprS env Us runtime type typeRuntime ∧
      env.HasType Us.length runtime.toCtx termRuntime typeRuntime ∧
      env.IsType Us.length runtime.toCtx typeRuntime := by
  rcases H.transportType henv htype htypeType with
    ⟨typeRuntime, htypeRuntime, htypeRuntimeType⟩
  have htermWeak : TrExprS env Us H.expanded term
      (termTarget.lift' H.shift) := by
    simpa using hterm.weakFV' henv.ordered H.lift H.context.wf
  have htypeWeak : TrExprS env Us H.expanded type
      (typeTarget.lift' H.shift) := by
    simpa using htype.weakFV' henv.ordered H.lift H.context.wf
  rcases htermWeak.defeqDFC henv H.context with
    ⟨termRuntime, htermRuntime⟩
  have htermEq := htermWeak.uniq henv H.context htermRuntime
  have htypeEq := htypeWeak.uniq henv H.context htypeRuntime
  have htermEqRuntime :=
    htermEq.defeqDFC henv.ordered H.context.defeqCtx
  have htypeEqRuntime :=
    htypeEq.defeqDFC henv.ordered H.context.defeqCtx
  have htypingWeak := htyping.weak' henv.ordered H.lift.toCtx
  have htypingRuntime := htypingWeak.defeqDFC henv.ordered
    H.context.defeqCtx
  have htypingTerm := htypingRuntime.defeqU_l henv
    (H.context.symm henv.ordered).wf.toCtx htermEqRuntime
  have htypingBoth := htypingTerm.defeqU_r henv
    (H.context.symm henv.ordered).wf.toCtx htypeEqRuntime
  exact ⟨termRuntime, typeRuntime, htermRuntime, htypeRuntime,
    htypingBoth, htypeRuntimeType⟩

/-- Move a successful runtime result-sort check back to the independent
narrow header scope.  Both translations are tied to the same concrete
residual, so uniqueness in the runtime context followed by inverse weakening
provides the narrow result equality. -/
theorem NarrowRuntimeScope.resultSort
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full')
    (hsort : TrExpr env Us runtime (.sort level) full') :
    TrExpr env Us scope (.sort level) narrow' := by
  rcases hsort with ⟨sortFull, hsortFull, hsortTarget⟩
  have hclosed : Closed (.sort level) 0 := trivial
  have hfvars : FVarsIn (· ∈ scope.fvars) (.sort level) := by
    simpa [FVarsIn] using hsortFull.fvarsIn
  rcases H.restrictEq henv hsortFull hclosed hfvars with
    ⟨sortNarrow, hsortNarrow, hsortLift⟩
  have htarget := H.fullTargetEq henv hnarrow hfull
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (sortNarrow.lift' H.shift) (narrow'.lift' H.shift) :=
    hsortLift.symm.trans henv hruntimeWF <|
      hsortTarget.trans henv hruntimeWF htarget.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      sortNarrow narrow' :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨sortNarrow, hsortNarrow, hnarrowEq⟩

/-- Extend the embedding by a generated index free variable.  The new
runtime domain need only be definitionally equal to the weakened semantic
domain. -/
def NarrowRuntimeScope.withIndex
    (H : NarrowRuntimeScope env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u)) :
    NarrowRuntimeScope env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  frontSourceDomains := H.frontSourceDomains ++ [indexType]
  frontExpandedDomains :=
    H.frontExpandedDomains ++ [indexType.lift' H.shift]
  front := H.front.cons fv deps indexType hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := by
    change scope.bvars = 0
    exact H.noBV
  noIndConsts := fun names =>
    checkPositivityStep.VLCtx.NoIndConsts.cons
      (H.noIndConsts names) rfl

/-- Source-domain provenance for a dependency-closed narrowed context.
The context is newest first.  At each retained declaration, its original
Lean domain is translated in the already retained older tail; this is the
datum needed to reconstruct an independent closed forall telescope rather
than merely closing a later expression over anonymous target domains. -/
inductive FVarNarrowSources (env : VEnv) (Us : List Name) :
    VLCtx → Type
  | nil : FVarNarrowSources env Us []
  | cons
      (tail : FVarNarrowSources env Us scope)
      (name : Name) (binderInfo : BinderInfo)
      (domain : Expr)
      (translation : TrExprS env Us scope domain target) :
      FVarNarrowSources env Us
        ((some (fv, deps), .vlam target) :: scope)

def FVarNarrowSources.mono {env env' : VEnv} (henv : env ≤ env') :
    FVarNarrowSources env Us scope → FVarNarrowSources env' Us scope
  | .nil => .nil
  | .cons tail name binderInfo domain translation =>
    .cons (tail.mono henv) name binderInfo domain
      (translation.mono henv)

/-- Close a body through all retained source declarations.  Each newest
free variable is abstracted into the body before its forall is formed; the
recursive call then abstracts the older variables through both that domain
and body. -/
def FVarNarrowSources.closeSource
    (H : FVarNarrowSources env Us scope) (body : Expr) : Expr :=
  match H with
  | .nil => body
  | .cons (fv := fv) tail name binderInfo domain _ =>
    tail.closeSource (.forallE name domain
      (body.abstract1 fv) binderInfo)

@[simp] theorem FVarNarrowSources.closeSource_mono
    {env env' : VEnv} (henv : env ≤ env')
    (H : FVarNarrowSources env Us scope) (body : Expr) :
    (H.mono henv).closeSource body = H.closeSource body := by
  induction H generalizing body with
  | nil => rfl
  | cons tail name binderInfo domain translation ih =>
    exact ih _

@[simp] theorem FVarNarrowSources.closeSource_nil
    (body : Expr) :
    (FVarNarrowSources.nil : FVarNarrowSources env Us []).closeSource body =
      body := rfl

/-- A dependency-closed semantic subcontext of an executable all-lambda
context.  Unlike `NarrowRuntimeScope`, this deliberately has no contiguous
`front`: callers may retain one named local, skip the next, and retain a
later one.  That is the shape of the recursor context, where indices and
majors are interleaved with the motives selected by the generated telescope.
-/
structure FVarNarrowScope (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  declarations : List.Forall₂
    (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), .vlam type))
    scope.fvars scope
  sources : FVarNarrowSources env Us scope

def FVarNarrowScope.mono {env env' : VEnv} (henv : env ≤ env')
    (H : FVarNarrowScope env Us scope runtime) :
    FVarNarrowScope env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  declarations := H.declarations
  sources := H.sources.mono henv

/-- Retarget only the executable context while preserving every data
projection of a dependency-selected scope definitionally. -/
def FVarNarrowScope.retargetRuntime
    (H : FVarNarrowScope env Us scope runtime)
    (h : runtime = runtime') :
    FVarNarrowScope env Us scope runtime' where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := by cases h; exact H.context
  upset := by cases h; exact H.upset
  noBV := H.noBV
  declarations := H.declarations
  sources := H.sources

theorem FVarNarrowScope.scopeWF
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF) : scope.WF env Us.length :=
  H.lift.wf henv H.context.wf

theorem FVarNarrowScope.fvars_length
    (H : FVarNarrowScope env Us scope runtime) :
    scope.fvars.length = scope.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.declarations

theorem VLCtx.fvars_length_of_noBV {scope : VLCtx} (H : scope.NoBV) :
    scope.fvars.length = scope.length := by
  induction scope with
  | nil => rfl
  | cons entry scope ih =>
    rcases entry with ⟨ofv, decl⟩
    cases ofv with
    | none =>
      change VLCtx.bvars scope + 1 = 0 at H
      omega
    | some fv =>
      change VLCtx.bvars scope = 0 at H
      simp [ih H]

private theorem fvarNarrowDeclarations_toCtx_length
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) fvars scope) :
    scope.toCtx.length = scope.length := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simp [VLCtx.toCtx, ih]

theorem FVarNarrowScope.toCtx_length
    (H : FVarNarrowScope env Us scope runtime) :
    scope.toCtx.length = scope.length :=
  fvarNarrowDeclarations_toCtx_length H.declarations

def FVarNarrowScope.nil : FVarNarrowScope env Us [] [] where
  expanded := []
  shift := .refl
  lift := .refl
  context := .nil
  upset := trivial
  noBV := rfl
  declarations := .nil
  sources := .nil

/-- A translated local context is dependency-closed for `P` whenever every
selected concrete declaration records only dependencies satisfying `P`. -/
theorem TrLCtx'.isFVarUpSet
    (H : TrLCtx' env Us declarations runtime)
    (hdeps : ∀ declaration ∈ declarations,
      P declaration.fvarId → ∀ fv ∈ declaration.deps, P fv) :
    IsFVarUpSet P runtime := by
  induction H with
  | nil => trivial
  | @cons declarations runtime declaration target Htail Hdecl ih =>
    refine ⟨ih (by
      intro other hother
      exact hdeps other (by simp [hother])), ?_⟩
    intro hselected fv hfv
    exact hdeps declaration (by simp) hselected fv hfv

theorem FVarNarrowScope.restrict
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime source target)
    (hclosed : Closed source 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) source) :
    ∃ target', TrExprS env Us scope source target' := by
  exact htr.weakFV'_inv henv H.lift
    (H.context.symm henv.ordered) hclosed hfvars

/-- Restrict a translation to a non-contiguous dependency-closed scope and
retain the equality obtained by weakening the narrowed target back into the
executable context.  This is the non-contiguous counterpart of
`NarrowRuntimeScope.restrictEq`. -/
theorem FVarNarrowScope.restrictEq
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ narrow', TrExprS env Us scope e narrow' ∧
      env.IsDefEqU Us.length runtime.toCtx e'
        (narrow'.lift' H.shift) := by
  rcases H.restrict henv htr hclosed hfvars with ⟨narrow', hnarrow⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  exact ⟨narrow', hnarrow,
    htr.uniq henv (H.context.symm henv.ordered) hweak⟩

theorem FVarNarrowScope.fullTargetEq
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

/-- Transfer runtime typehood to a translation reconstructed in a
dependency-selected free-variable scope. -/
theorem FVarNarrowScope.hasTypeOfFull
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExprS env Us runtime e full')
    (htype : env.HasType Us.length runtime.toCtx full' (.sort u)) :
    env.HasType Us.length scope.toCtx narrow' (.sort u) := by
  have htarget := H.fullTargetEq henv hnarrow
    (hfull.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htarget.symm
  have hexpanded := hliftTyped.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

/-- Retain one newly introduced named lambda.  Its semantic domain is
obtained by inverse weakening; the executable domain need only be
definitionally equal after weakening back into the expanded context. -/
def FVarNarrowScope.withIndex
    (H : FVarNarrowScope env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (sourceName : Name) (sourceBinderInfo : BinderInfo)
    (sourceType : Expr)
    (hsource : TrExprS env Us scope sourceType indexType)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u)) :
    FVarNarrowScope env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := H.noBV
  declarations := .cons ⟨deps, indexType, rfl⟩ H.declarations
  sources := .cons H.sources sourceName sourceBinderInfo sourceType hsource

/-- Skip one newly introduced named lambda while preserving a previously
selected, possibly non-contiguous semantic scope. -/
def FVarNarrowScope.skipIndex
    (H : FVarNarrowScope env Us scope runtime)
    (henv : env.WF)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hskip : fv ∉ scope.fvars) :
    FVarNarrowScope env Us scope
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded := (some (fv, deps), .vlam runtimeType) :: H.expanded
  shift := H.shift.skipN 1
  lift := H.lift.skip_fvar (fv, deps) (.vlam runtimeType)
  context := by
    have Htype : env.IsType Us.length H.expanded.toCtx runtimeType :=
      hnewRuntime.2.2.defeqDFC henv.ordered
        (H.context.defeqCtx.symm henv.ordered)
    rcases Htype with ⟨level, Htype⟩
    exact .cons H.context (by
      have hfresh := hnewRuntime.2.1
      simpa [H.context.fvars] using hfresh)
      (VLocalDecl.IsDefEq.refl henv H.context.wf.toCtx
        ⟨level, Htype⟩)
  upset := by
    refine ⟨H.upset, ?_⟩
    intro hmem
    exact False.elim (hskip hmem)
  noBV := H.noBV
  declarations := H.declarations
  sources := H.sources

/-- Narrow an executable all-lambda context to exactly the free variables
selected by a dependency-closed predicate.  Retained source domains are
translated in the already narrowed tail; skipped declarations remain only
in the comparison context. -/
theorem narrowFVars
    (H : MLCtxOnlyLams c)
    (henv : env.WF)
    (Hwf : c.WF env Us)
    (P : FVarId → Prop) [DecidablePred P]
    (hup : IsFVarUpSet P c.vlctx) :
    ∃ scope, ∃ Hscope : FVarNarrowScope env Us scope c.vlctx,
      scope.fvars = c.vlctx.fvars.filter P := by
  induction c with
  | nil => exact ⟨[], .nil, rfl⟩
  | @vlam fv name type type' bi tail ih =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    rcases ih H.tail_vlam HtailWF hup.1 with
      ⟨tailScope, HtailScope, htailScopeFVars⟩
    by_cases hP : P fv
    · have hdeps : type.fvarsList ⊆ tailScope.fvars := by
        intro dep hdep
        rw [htailScopeFVars]
        exact List.mem_filter.mpr ⟨Htype.fvarsList hdep, by
          simpa using hup.2 hP dep hdep⟩
      have hclosed : Closed type 0 := by
        have h := Htype.closed
        rw [tail.noBV] at h
        exact h
      have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
        apply fvarsIn_iff.mpr
        refine ⟨hdeps, ?_⟩
        exact Htype.fvarsIn.mono fun _ _ => trivial
      rcases HtailScope.restrict henv Htype hclosed htypeFVars with
        ⟨narrowType, HnarrowType⟩
      have Hweak : TrExprS env Us HtailScope.expanded type
          (narrowType.lift' HtailScope.shift) := by
        simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
          HtailScope.context.wf
      have HtargetEq := Hweak.uniq henv HtailScope.context Htype
      have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
          type' :=
        HtypeType.defeqDFC henv.ordered
          (HtailScope.context.symm henv.ordered).defeqCtx
      rcases HtargetType with ⟨u, HtargetType⟩
      have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
          (narrowType.lift' HtailScope.shift) type' (.sort u) :=
        HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
      let Hnext := HtailScope.withIndex HruntimeWF hdeps name bi type
        HnarrowType Hdomain
      exact ⟨_, Hnext, by
        simp [Hnext, htailScopeFVars, hP]⟩
    · have hskip : fv ∉ tailScope.fvars := by
        rw [htailScopeFVars]
        simp [hP]
      let Hnext := HtailScope.skipIndex henv HruntimeWF hskip
      exact ⟨_, Hnext, by
        simp [Hnext, htailScopeFVars, hP]⟩
  | @vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

/-- In a duplicate-free ambient list, filtering for the members of an
ordered sublist recovers that sublist exactly. -/
theorem List.filter_mem_eq_of_sublist_nodup
    {selected ambient : List FVarId}
    (hsub : selected <+ ambient) (hnodup : ambient.Nodup) :
    ambient.filter (· ∈ selected) = selected := by
  induction hsub with
  | slnil => simp
  | @cons selected' ambient' a hsub ih =>
    have ha : a ∉ ambient' := (List.nodup_cons.mp hnodup).1
    have haselected : a ∉ selected' := fun hmem => ha (hsub.subset hmem)
    simp [haselected, ih (List.nodup_cons.mp hnodup).2]
  | @cons_cons selected' ambient' a hsub ih =>
    have ha : a ∉ ambient' := (List.nodup_cons.mp hnodup).1
    have htail : ambient'.filter (· ∈ a :: selected') =
        ambient'.filter (· ∈ selected') := by
      apply List.filter_congr
      intro x hx
      have hxa : x ≠ a := by
        intro heq
        subst x
        exact ha hx
      simp [hxa]
    simp only [List.filter_cons, List.mem_cons, true_or, decide_true,
      Bool.true_eq, ↓reduceIte, htail]
    rw [ih (List.nodup_cons.mp hnodup).2]

/-- Re-run source-aware narrowing at a completed semantic header scope.
This is deliberately a header-boundary theorem rather than a field of
`NarrowHeaderSynthesisCertificate`: constructor replay universe-instantiates
that generic certificate using arbitrary abstract levels, while the concrete
Lean source domains retained here exist only under the original header level
parameters. -/
theorem NarrowRuntimeScope.independentSourceScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : NarrowRuntimeScope Hc.venv c.lparams scope Hc.mlctx.vlctx) :
    ∃ sourceScope,
      ∃ Hsource : FVarNarrowScope Hc.venv c.lparams sourceScope
          Hc.mlctx.vlctx,
        sourceScope.fvars = scope.fvars := by
  rcases narrowFVars Hc.onlyLams Hc.checking.tr.wf Hc.mlctx_wf
      (· ∈ scope.fvars) H.upset with
    ⟨sourceScope, Hsource, hsourceFVars⟩
  refine ⟨sourceScope, Hsource, hsourceFVars.trans ?_⟩
  have hsub : scope.fvars <+ Hc.mlctx.vlctx.fvars := by
    rw [← H.context.fvars]
    exact H.lift.fvars_sublist
  exact List.filter_mem_eq_of_sublist_nodup hsub
    Hc.mlctx_wf.tr.wf.fvars_nodup

/-- At the parameter/index boundary, discard the ambient prefix retained
from previously checked mutual headers and keep the exact cached-parameter
suffix as the semantic scope. -/
def NarrowRuntimeScope.ofParameterSuffix
    (Hc : ContextWF c)
    (Hsuffix : ParameterContextSuffix Hc stats depth) :
    NarrowRuntimeScope Hc.venv c.lparams Hsuffix.parameterDecls
      Hc.mlctx.vlctx := by
  have hambient : Hsuffix.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend Hsuffix.ambientDecls
      Hsuffix.parameterDecls
    rw [← Hsuffix.context]
    exact Hc.mlctx.noBV
  let W := VLCtx.FVLift.to_append Hsuffix.parameterDecls hambient
  refine {
    expanded := Hc.mlctx.vlctx
    shift := .skipN .refl Hsuffix.ambientDecls.toCtx.length
    lift := ?_
    frontSourceDomains := []
    frontExpandedDomains := []
    front := ?_
    context := .refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := Hsuffix.noIndConsts }
  · rw [Hsuffix.context]
    exact W.toFVLift'
  · exact .zero (by
      rw [Hsuffix.context]
      exact W.toFVLift')
  · have hwf : VLCtx.WF Hc.venv c.lparams.length
        (Hsuffix.ambientDecls ++ Hsuffix.parameterDecls) := by
      rw [← Hsuffix.context]
      exact Hc.mlctx_wf.tr.wf
    simpa [Hsuffix.context] using
      (IsFVarUpSet.suffixFVars Hsuffix.parameterDecls
        Hsuffix.ambientDecls hwf)
  · have hfull : (Hsuffix.ambientDecls ++
        Hsuffix.parameterDecls).NoBV := by
      rw [← Hsuffix.context]
      exact Hc.mlctx.noBV
    change Hsuffix.parameterDecls.bvars = 0
    change (Hsuffix.ambientDecls ++
      Hsuffix.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega

/-- Relate a domain translated in the semantic scope to the annotation-
consumed domain installed by the executable checker. -/
theorem NarrowRuntimeScope.consumedDomain
    (Hc : ContextWF c)
    (H : NarrowRuntimeScope Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hdom : Hc.ConsumedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS Hc.venv c.lparams scope dom indexType) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS Hc.venv c.lparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' Hc.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq Hc.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    Hc.checking.tr.wf.ordered
    (H.context.defeqCtx.symm Hc.checking.tr.wf.ordered)
  have hdomainU := hsource.trans Hc.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r Hc.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

theorem NarrowRuntimeScope.recursorConsumedDomain
    (R : RecursorContextWF c recLparams)
    (H : NarrowRuntimeScope R.venv recLparams scope R.mlctx.vlctx)
    (Hdom : R.ConsumedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS R.venv recLparams scope dom indexType) :
    ∃ u, R.venv.IsDefEq recLparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS R.venv recLparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' R.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq R.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    R.checking.tr.wf.ordered
    (H.context.defeqCtx.symm R.checking.tr.wf.ordered)
  have hdomainU := hsource.trans R.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r R.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

/-- Shape of the CPS-retained runtime context after the first header has fixed
the block-wide parameter telescope.  Header indices form an ambient prefix;
the common parameters remain an exact suffix. -/
structure AmbientParamContext (Hc : ContextWF c) (params : List VExpr)
    (depth : Nat) where
  ambient : List VExpr
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (ambient ++ params.reverse) Hc.mlctx.vlctx.toCtx
  length : ambient.length = depth

/-- The exact cached-parameter suffix represents the common abstract
parameter telescope fixed by the first header.  The ambient prefixes may
differ definitionally, but have the same recorded depth and can be inverted
away from the context conversion. -/
theorem ParameterContextSuffix.paramsDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hparams : params.length = stats.params.size) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx := by
  have hcontext : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (Hambient.ambient ++ params.reverse)
      (Hsuffix.ambientDecls.toCtx ++ Hsuffix.parameterDecls.toCtx) := by
    simpa [Hsuffix.context] using Hambient.context
  have hparameterCtx : Hsuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    have hcachedLength : ∀ {ps : List Expr} {decls : VLCtx},
        List.Forall₂ CachedParameterDecl ps decls →
        decls.toCtx.length = ps.length := by
      intro ps decls hcached
      induction hcached with
      | nil => rfl
      | cons h _ ih =>
        rcases h with ⟨fv, deps, type, rfl, rfl⟩
        simp [VLCtx.toCtx, ih]
    simpa using hcachedLength Hsuffix.cached
  have hprefix : Hambient.ambient.length =
      Hsuffix.ambientDecls.toCtx.length := by
    have hlength := hcontext.length_eq
    simp only [List.length_append, List.length_reverse] at hlength
    omega
  exact VEnv.IsDefEqCtx.dropPrefixes hcontext hprefix

/-- Source-side account of the header telescope consumed by `loopType`.
`root` is the original normalized header and `current` is its unconsumed
suffix.  The context relation records that annotation erasure may change a
binder domain without changing the abstract telescope up to definitional
equality. -/
structure HeaderTelescopeCertificate (Hc : ContextWF c)
    (root current : VExpr) (params indices : List VExpr) where
  rebuild : root = VExpr.wrapForalls (params ++ indices) current
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx

theorem HeaderTelescopeCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeCertificate Hc root root [] [] where
  rebuild := by simp [VExpr.wrapForalls]
  context := by simpa using hctx

/-- Consume a common-parameter binder.  This operation is restricted to the
parameter phase, before any index binder has been seen. -/
theorem HeaderTelescopeCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (params ++ [sourceDom]) [] where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: params.reverse)
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

/-- Consume an index binder after the common parameters. -/
theorem HeaderTelescopeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params indices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body params (indices ++ [sourceDom]) where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: (indices.reverse ++ params.reverse))
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

theorem HeaderTelescopeCertificate.takeParameters
    (H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : params.length = nparams) :
    root.takeForalls nparams =
      some (params, VExpr.wrapForalls indices current) := by
  subst nparams
  rw [H.rebuild, VExpr.takeForalls_wrapForalls_append]

theorem HeaderTelescopeCertificate.takeIndices
    (_H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : indices.length = nindices) :
    (VExpr.wrapForalls indices current).takeForalls nindices =
      some (indices, current) := by
  subst nindices
  exact VExpr.takeForalls_wrapForalls indices current

/-- Type-valued state carried by the executable telescope loop.  It owns the
source parameter and index lists, and synchronizes their lengths with the two
counters maintained by `loopType`. -/
structure HeaderTelescopeLoopCertificate (Hc : ContextWF c)
    (root current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  telescope : HeaderTelescopeCertificate Hc root current params indices
  parameterCount : params.length = i
  indexCount : indices.length = nindices

/-- Definitional, rather than syntactic, header-telescope accumulator.  Its
`header` field relates the independent source header to the telescope
synthesized from every binder exposed by the executable per-binder `whnf`.
This is the state used by the complete loop refinement. -/
structure HeaderSynthesisCertificate (Hc : ContextWF c)
    (target : VInductiveTypeSkeleton) (current : VExpr)
    (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx
  currentType : Hc.venv.IsType c.lparams.length
    (indices.reverse ++ params.reverse) current
  exprType : VExpr
  header : Hc.venv.IsDefEq c.lparams.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def HeaderSynthesisCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c}
    {target : VInductiveTypeSkeleton} {current exprType : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx)
    (hcurrent : Hc.venv.IsType c.lparams.length [] current)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type current exprType) :
    HeaderSynthesisCertificate Hc target current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  context := by simpa using hctx
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

def HeaderSynthesisCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: H.params.reverse)
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      have hOld : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
          H.params.reverse Hc.mlctx.vlctx.toCtx := by
        simpa [hindices] using H.context
      exact .succ hOld
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (hOld.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [hindices, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv]
      using H.header

def HeaderSynthesisCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: (H.indices.reverse ++ H.params.reverse))
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [List.reverse_append, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv] using H.header

/-- Replace the residual telescope by a definitionally equal normal form and
close that equality over every already discovered binder. -/
noncomputable def HeaderSynthesisCertificate.normalize
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target current i nindices)
    (heq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx current next) :
    HeaderSynthesisCertificate Hc target next i nindices := by
  have heq' := heq.defeqDFC Hc.checking.tr.wf.ordered
    (H.context.symm Hc.checking.tr.wf.ordered)
  let currentLevel := Classical.choose H.currentType
  have hcurrent := Classical.choose_spec H.currentType
  have heqTyped := heq'.of_l Hc.checking.tr.wf H.context.isType hcurrent
  have heqTyped' : Hc.venv.IsDefEq c.lparams.length
      ((H.params ++ H.indices).reverse ++ []) current next
      (.sort currentLevel) := by
    simpa [List.reverse_append] using heqTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
      (domains := H.params ++ H.indices) (Γ := [])
      (by simpa [List.reverse_append] using H.context.isType)
      heqTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices
    parameterCount := H.parameterCount
    indexCount := H.indexCount
    context := H.context
    currentType := H.currentType.defeqU_l Hc.checking.tr.wf
      H.context.isType heq'
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r Hc.checking.tr.wf (by trivial)
      (by simpa using hwrapped) }

/-- Definitional header synthesis in a context narrower than the executable
reader context.  Later mutual headers retain indices introduced while
checking earlier family members; those declarations must not become part of
the later header's semantic telescope. -/
structure NarrowHeaderSynthesisCertificate
    (env : VEnv) (Us : List Name) (target : VInductiveTypeSkeleton)
    (scope : VLCtx) (current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  scopeLength : scope.length = i + nindices
  scopeCtx : scope.toCtx = indices.reverse ++ params.reverse
  scopeWF : scope.WF env Us.length
  currentType : env.IsType Us.length scope.toCtx current
  exprType : VExpr
  header : env.IsDefEq Us.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def NarrowHeaderSynthesisCertificate.empty
    {exprType : VExpr}
    (_htarget : env.IsType Us.length [] target.type)
    (hcurrent : env.IsType Us.length [] current)
    (hheader : env.IsDefEq Us.length [] target.type current exprType) :
    NarrowHeaderSynthesisCertificate env Us target [] current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  scopeLength := rfl
  scopeCtx := rfl
  scopeWF := by trivial
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

/-- Replace the current residual by a definitionally equal forall over the
next cached common-parameter type, then move that binder into the narrow
scope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i 0)
    (hindices : H.indices = [])
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE paramType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0 := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE paramType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hparamsCtx : OnCtx H.params.reverse (env.IsType Us.length) := by
    simpa [hindices, H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length (H.params.reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE paramType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [hindices, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params) (Γ := []) (by simpa using hparamsCtx)
      hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params ++ [paramType]
    indices := []
    parameterCount := by simp [H.parameterCount]
    indexCount := rfl
    scopeLength := by simp [H.scopeLength]
    scopeCtx := by simp [VLCtx.toCtx, H.scopeCtx, hindices]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append]
        using hwrapped }

/-- Move a definitionally equal residual forall into the narrow index
telescope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i nindices)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE indexType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam indexType) :: scope)
      next i (nindices + 1) := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE indexType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hdomainsCtx : OnCtx (H.params ++ H.indices).reverse
      (env.IsType Us.length) := by
    simpa [List.reverse_append, ← H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length
      ((H.params ++ H.indices).reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE indexType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [List.reverse_append, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params ++ H.indices) (Γ := [])
      (by simpa using hdomainsCtx) hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices ++ [indexType]
    parameterCount := H.parameterCount
    indexCount := by simp [H.indexCount]
    scopeLength := by simp [H.scopeLength, Nat.add_assoc]
    scopeCtx := by
      simp [VLCtx.toCtx, H.scopeCtx, List.reverse_append]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
        List.append_assoc] using hwrapped }

/-- Compare the next domain of a narrow replay state with the next domain of
another certified presentation of the same source header. -/
theorem NarrowHeaderSynthesisCertificate.nextDomainDefEq
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE currentDomain currentBody) i nindices)
    (hindices : H.indices = [])
    (hlen : H.params.length = expectedPrefix.length)
    (htarget : env.IsDefEq Us.length [] target.type
      (VExpr.wrapForalls expectedPrefix
        (.forallE expectedDomain expectedBody)) targetType) :
    ∃ u, env.IsDefEq Us.length H.params.reverse
      currentDomain expectedDomain (.sort u) := by
  have hleftTarget : env.IsDefEqU Us.length []
      (VExpr.wrapForalls H.params (.forallE currentDomain currentBody))
      target.type := ⟨_, by simpa [hindices] using H.header.symm⟩
  have htargetRight : env.IsDefEqU Us.length [] target.type
      (VExpr.wrapForalls expectedPrefix
        (.forallE expectedDomain expectedBody)) := ⟨_, htarget⟩
  have hboth := hleftTarget.trans henv (by trivial) htargetRight
  simpa using VEnv.IsDefEqU.wrapForalls_next henv (by trivial)
    hlen hboth

/-- Build the semantic parameter transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (hindices : H.indices = [])
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' paramType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam paramType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (paramType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope)
        normalized' (i + 1) 0) := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE paramType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      ⟨H.withParameter henv hindices hscopeWF hstep⟩⟩

/-- Build the semantic index transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i
      nindices)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' indexType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam indexType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      ∃ H' : NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam indexType) :: scope)
        normalized' i (nindices + 1),
        H'.params = H.params ∧ H'.indices = H.indices ++ [indexType] := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ indexType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam indexType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE indexType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      H.withIndex henv hscopeWF hstep, rfl, rfl⟩

theorem NarrowHeaderSynthesisCertificate.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env H.params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (env.IsType decl.uvars) := by
    simpa [huvars, ← H.scopeCtx] using H.scopeWF.toCtx
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := H.params) (ownParams := H.params) (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

theorem NarrowHeaderSynthesisCertificate.typeShapeWithParams
    {decl : VInductDecl} {target : VInductiveType}
    {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hparams : decl.ParamsDefEq env commonParams H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env commonParams target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := commonParams) (ownParams := H.params)
    (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShapeWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params : List VExpr}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hparams : decl.ParamsDefEq Hc.venv params H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    huvars H.context
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params target := by
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using H.context.isType
  exact H.typeShapeWithParams huvars
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

/-- Materialize the two semantic header fields from the successful executable
tail.  Unlike `typeShape`, this theorem does not require either field to have
been chosen before the traversal: the index counter and translated sort are
used to construct the target itself. -/
theorem HeaderSynthesisCertificate.synthesizedTypeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc target current
      decl.nparams nindices)
    (huvars : c.lparams.length = decl.uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params
      (target.toVInductiveType nindices resultLevel) := by
  apply H.typeShape (target := target.toVInductiveType nindices resultLevel)
    huvars
  · intro resultLevel' hofLevel'
    rw [hofLevel] at hofLevel'
    cases hofLevel'
    rfl
  · exact hsort

/-- How the normalized semantic parameter/index telescope sits in the
executable header context retained by an independently source-aware
narrowing.  The first header occupies the full context; later mutual headers
can skip indices left by earlier families. -/
inductive HeaderSourceScopeAlignment (env : VEnv) (Us : List Name)
    (sourceScope runtime : VLCtx) (ownParams indices : List VExpr) : Type
  | full
      (sourceFVars : sourceScope.fvars = runtime.fvars)
      (semanticContext : VEnv.IsDefEqCtx env Us.length []
        (indices.reverse ++ ownParams.reverse) runtime.toCtx) :
      HeaderSourceScopeAlignment env Us sourceScope runtime ownParams indices
  | narrow
      (semanticScope : VLCtx)
      (sourceFVars : sourceScope.fvars = semanticScope.fvars)
      (semantic : NarrowRuntimeScope env Us semanticScope runtime)
      (semanticContext : semanticScope.toCtx =
        indices.reverse ++ ownParams.reverse) :
      HeaderSourceScopeAlignment env Us sourceScope runtime ownParams indices

/-- Concrete source telescope retained only at the completed header
boundary.  Keeping this separate from `NarrowHeaderSynthesisCertificate` is
essential: constructor replay universe-instantiates that generic certificate
with abstract levels for which there need not be corresponding Lean source
syntax. -/
structure NormalizedHeaderSourceTelescope (env : VEnv) (Us : List Name)
    (commonParams : List VExpr) (nparams nindices : Nat) : Type where
  runtime : VLCtx
  sourceScope : VLCtx
  source : FVarNarrowScope env Us sourceScope runtime
  ownParams : List VExpr
  indices : List VExpr
  parameterCount : ownParams.length = nparams
  indexCount : indices.length = nindices
  sourceLength : sourceScope.length = nparams + nindices
  parameters : VEnv.IsDefEqCtx env Us.length []
    commonParams.reverse ownParams.reverse
  alignment : HeaderSourceScopeAlignment env Us sourceScope runtime
    ownParams indices

def HeaderSourceScopeAlignment.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : HeaderSourceScopeAlignment env Us sourceScope runtime
      ownParams indices) :
    HeaderSourceScopeAlignment env' Us sourceScope runtime
      ownParams indices := by
  cases H with
  | full sourceFVars semanticContext =>
    exact .full sourceFVars (semanticContext.mono henv)
  | narrow semanticScope sourceFVars semantic semanticContext =>
    exact .narrow semanticScope sourceFVars (semantic.mono henv)
      semanticContext

def NormalizedHeaderSourceTelescope.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : NormalizedHeaderSourceTelescope env Us commonParams
      nparams nindices) :
    NormalizedHeaderSourceTelescope env' Us commonParams
      nparams nindices where
  runtime := H.runtime
  sourceScope := H.sourceScope
  source := H.source.mono henv
  ownParams := H.ownParams
  indices := H.indices
  parameterCount := H.parameterCount
  indexCount := H.indexCount
  sourceLength := H.sourceLength
  parameters := H.parameters.mono henv
  alignment := H.alignment.mono henv

/-- Persistent result of checking one metadata-free source header.  The final
mutual declaration need not exist yet; only its two block-wide counters are
relevant to `TypeShape`.  This lets the outer traversal accumulate checked
headers and materialize the declaration after every family member has
supplied its metadata. -/
structure SynthesizedHeader (env : VEnv) (Us : List Name)
    (uvars nparams : Nat)
    (params : List VExpr) (source : VInductiveTypeSkeleton)
    (numIndices : Nat) (resultLevel : VLevel) : Prop where
  parameterCount : params.length = nparams
  levelCount : Us.length = uvars
  normalizedSource : Nonempty
    (NormalizedHeaderSourceTelescope env Us params nparams numIndices)
  typeShape : ∀ decl : VInductDecl,
    decl.uvars = uvars → decl.nparams = nparams →
    decl.TypeShape env params
      (source.toVInductiveType numIndices resultLevel)

theorem NarrowHeaderSynthesisCertificate.synthesizedHeaderWithParams
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us source scope current
      nparams nindices)
    (henv : env.WF)
    (Hruntime : NarrowRuntimeScope env Us scope runtime)
    (Hsource : FVarNarrowScope env Us sourceScope runtime)
    (hsourceFVars : sourceScope.fvars = scope.fvars)
    (huvars : Us.length = uvars)
    (hparams : VEnv.IsDefEqCtx env uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel Us level = some resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    SynthesizedHeader env Us uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  levelCount := huvars
  normalizedSource := by
    exact ⟨{
      runtime := runtime
      sourceScope := sourceScope
      source := Hsource
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = scope.fvars.length := congrArg List.length hsourceFVars
          _ = scope.length := VLCtx.fvars_length_of_noBV Hruntime.noBV
          _ = nparams + nindices := H.scopeLength
      parameters := by simpa [huvars] using hparams
      alignment := .narrow scope hsourceFVars Hruntime H.scopeCtx }⟩
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : Us.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq env commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      henv huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

theorem HeaderSynthesisCertificate.synthesizedHeader
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv c.lparams uvars nparams H.params source
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := huvars
  normalizedSource := by
    have hup := IsFVarUpSet.suffixFVars Hc.mlctx.vlctx ([] : VLCtx)
      (by simpa using Hc.mlctx_wf.tr.wf)
    rcases narrowFVars Hc.onlyLams Hc.checking.tr.wf Hc.mlctx_wf
        (· ∈ Hc.mlctx.vlctx.fvars) hup with
      ⟨sourceScope, Hsource, hsourceFVars⟩
    have hfilter : Hc.mlctx.vlctx.fvars.filter
        (· ∈ Hc.mlctx.vlctx.fvars) = Hc.mlctx.vlctx.fvars :=
      List.filter_mem_eq_of_sublist_nodup (.refl _)
        Hc.mlctx_wf.tr.wf.fvars_nodup
    exact ⟨{
      runtime := Hc.mlctx.vlctx
      sourceScope := sourceScope
      source := Hsource
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = Hc.mlctx.vlctx.fvars.length :=
            congrArg List.length (hsourceFVars.trans hfilter)
          _ = Hc.mlctx.length := Hc.onlyLams.fvars_length
          _ = Hc.mlctx.vlctx.toCtx.length :=
            Hc.onlyLams.toCtx_length.symm
          _ = (H.indices.reverse ++ H.params.reverse).length :=
            H.context.length_eq.symm
          _ = nparams + nindices := by
            simp [H.parameterCount, H.indexCount, Nat.add_comm]
      parameters := .refl (OnCtx.append_right H.context.isType)
      alignment := .full (hsourceFVars.trans hfilter) H.context }⟩
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    subst nparams
    apply H.synthesizedTypeShape (decl := decl)
    · exact huvars'
    · exact hofLevel
    · exact hsort

/-- Later mutual headers use the first header's parameter telescope.  Their
own synthesized domains are connected to it by the successful executable
`isDefEq` checks, represented here independently of the not-yet-materialized
declaration. -/
theorem HeaderSynthesisCertificate.synthesizedHeaderWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv c.lparams uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  levelCount := huvars
  normalizedSource := by
    have hup := IsFVarUpSet.suffixFVars Hc.mlctx.vlctx ([] : VLCtx)
      (by simpa using Hc.mlctx_wf.tr.wf)
    rcases narrowFVars Hc.onlyLams Hc.checking.tr.wf Hc.mlctx_wf
        (· ∈ Hc.mlctx.vlctx.fvars) hup with
      ⟨sourceScope, Hsource, hsourceFVars⟩
    have hfilter : Hc.mlctx.vlctx.fvars.filter
        (· ∈ Hc.mlctx.vlctx.fvars) = Hc.mlctx.vlctx.fvars :=
      List.filter_mem_eq_of_sublist_nodup (.refl _)
        Hc.mlctx_wf.tr.wf.fvars_nodup
    exact ⟨{
      runtime := Hc.mlctx.vlctx
      sourceScope := sourceScope
      source := Hsource
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = Hc.mlctx.vlctx.fvars.length :=
            congrArg List.length (hsourceFVars.trans hfilter)
          _ = Hc.mlctx.length := Hc.onlyLams.fvars_length
          _ = Hc.mlctx.vlctx.toCtx.length :=
            Hc.onlyLams.toCtx_length.symm
          _ = (H.indices.reverse ++ H.params.reverse).length :=
            H.context.length_eq.symm
          _ = nparams + nindices := by
            simp [H.parameterCount, H.indexCount, Nat.add_comm]
      parameters := by simpa [huvars] using hparams
      alignment := .full (hsourceFVars.trans hfilter) H.context }⟩
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq Hc.venv commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

structure SynthesizedHeaderMetadata (env : VEnv) (Us : List Name)
    (uvars nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : VInductiveTypeSkeleton) (data : Nat × VLevel) : Prop where
  header : SynthesizedHeader env Us uvars nparams params source data.1 data.2
  commonLevel : data.2 ≈ commonLevel

/-- Prefix of the metadata list built by the outer mutual-header traversal.
`Forall₂` fixes both ordering and cardinality, so later materialization cannot
associate a checked arity or universe with the wrong family member. -/
structure SynthesizedHeaderPrefix (env : VEnv) (Us : List Name)
    (skeleton : VInductDeclSkeleton) (params : List VExpr)
    (commonLevel : VLevel) (metadata : List (Nat × VLevel))
    (done : Nat) : Prop where
  parameterCount : params.length = skeleton.nparams
  covered : done ≤ skeleton.types.length
  checked : List.Forall₂
    (SynthesizedHeaderMetadata env Us skeleton.uvars skeleton.nparams
      params commonLevel)
    (skeleton.types.take done) metadata

theorem SynthesizedHeaderPrefix.first
    (hindex : 0 < skeleton.types.length)
    (Hheader : SynthesizedHeader env Us skeleton.uvars skeleton.nparams
      params skeleton.types[0] nindices resultLevel) :
    SynthesizedHeaderPrefix env Us skeleton params resultLevel
      [(nindices, resultLevel)] 1 where
  parameterCount := Hheader.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    simp only [List.take_zero, List.nil_append]
    exact .cons ⟨Hheader, by rfl⟩ .nil

theorem SynthesizedHeaderPrefix.push
    (H : SynthesizedHeaderPrefix env Us skeleton params commonLevel
      metadata done)
    (hindex : done < skeleton.types.length)
    (Hheader : SynthesizedHeader env Us skeleton.uvars skeleton.nparams
      params skeleton.types[done] nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    SynthesizedHeaderPrefix env Us skeleton params commonLevel
      (metadata ++ [(nindices, resultLevel)]) (done + 1) where
  parameterCount := H.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    exact Lean4Lean.VerifyInductive.List.Forall₂.append' H.checked
      (.cons ⟨Hheader, hlevel⟩ .nil)

/-- Every position of a completed header prefix retains the concrete source
telescope selected while checking that family. -/
theorem SynthesizedHeaderPrefix.normalizedSourceAt
    (H : SynthesizedHeaderPrefix env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (i : Nat) (hi : i < skeleton.types.length)
    (hmetadata : i < metadata.length) :
    Nonempty (NormalizedHeaderSourceTelescope env Us params
      skeleton.nparams metadata[i].1) := by
  have Hchecked := Lean4Lean.VerifyInductive.List.Forall₂.getElem H.checked i
    (by simpa using hi) hmetadata
  exact Hchecked.header.normalizedSource

/-- After exact materialization, the retained source telescope is indexed by
the corresponding family in the resulting declaration. -/
theorem SynthesizedHeaderPrefix.normalizedSourceAtMaterialized
    (H : SynthesizedHeaderPrefix env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.materialize metadata = some decl)
    (i : Nat) (hi : i < decl.types.length) :
    Nonempty (NormalizedHeaderSourceTelescope env Us params decl.nparams
      decl.types[i].numIndices) := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have hskeleton : i < skeleton.types.length := by omega
  have hmetadata : i < metadata.length := by
    rw [VInductDeclSkeleton.materialize_length Hmaterialize]
    exact hskeleton
  have Hsource := H.normalizedSourceAt i hskeleton hmetadata
  rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hskeleton with
    ⟨data, hdata, htarget⟩
  have hdataEq : data = metadata[i] := by
    rw [List.getElem?_eq_getElem hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have htargetEq : decl.types[i] = skeleton.types[i].toVInductiveType
      metadata[i].1 metadata[i].2 := by
    rw [List.getElem?_eq_getElem hi] at htarget
    exact Option.some.inj htarget
  have hindices : decl.types[i].numIndices = metadata[i].1 := by
    rw [htargetEq]
    simp [VInductiveTypeSkeleton.toVInductiveType]
  simpa [hfields.2.1, hindices] using Hsource

/-- Once every header has been visited, exact materialization turns the
metadata-prefix invariant into the public formation header certificate. -/
def SynthesizedHeaderPrefix.complete
    (H : SynthesizedHeaderPrefix env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    HeaderCertificate env decl := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have hcheckedLength :
      (skeleton.types.take skeleton.types.length).length = metadata.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.checked
  have hmetadata : metadata.length = skeleton.types.length := by
    simpa using hcheckedLength.symm
  have checkedAt : ∀ i (hi : i < skeleton.types.length),
      SynthesizedHeaderMetadata env Us skeleton.uvars skeleton.nparams
        params commonLevel skeleton.types[i] metadata[i] := by
    intro i hi
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.getElem H.checked i
      (by simpa using hi) (by simpa [hmetadata] using hi)
  have materializedAt : ∀ i (hi : i < skeleton.types.length),
      decl.types[i]'(by omega) =
        skeleton.types[i].toVInductiveType metadata[i].1 metadata[i].2 := by
    intro i hi
    rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hi with
      ⟨data, hdata, htarget⟩
    have hmetadataGet : metadata[i]? = some metadata[i] := by
      simp [hmetadata, hi]
    have hdataEq : data = metadata[i] := by
      rw [hmetadataGet] at hdata
      cases hdata
      rfl
    subst data
    rw [List.getElem?_eq_getElem (by omega)] at htarget
    exact Option.some.inj htarget
  refine {
    params := params
    resultLevel := commonLevel
    commonLevels := ?_
    typeShapes := ?_ }
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).commonLevel
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).header.typeShape decl
      hfields.1 hfields.2.1

/-- Exact coverage makes skeleton materialization total and packages the
resulting formation-header certificate. -/
theorem SynthesizedHeaderPrefix.materializes
    (H : SynthesizedHeaderPrefix env Us skeleton params commonLevel metadata
      skeleton.types.length) :
    ∃ decl, skeleton.materialize metadata = some decl ∧
      Nonempty (HeaderCertificate env decl) := by
  have hmetadata : metadata.length = skeleton.types.length := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      H.checked
    simpa using hlength.symm
  cases hmaterialize : skeleton.materialize metadata with
  | none => simp [VInductDeclSkeleton.materialize, hmetadata] at hmaterialize
  | some decl => exact ⟨decl, rfl, ⟨H.complete hmaterialize⟩⟩

def HeaderTelescopeLoopCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeLoopCertificate Hc root root 0 0 where
  params := []
  indices := []
  telescope := .empty hctx
  parameterCount := rfl
  indexCount := rfl

def HeaderTelescopeLoopCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  telescope := by
    have Htel := H.telescope
    rw [hindices] at Htel
    exact Htel.withParameter hdom
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount

def HeaderTelescopeLoopCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  telescope := H.telescope.withIndex hdom
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]

theorem HeaderTelescopeLoopCertificate.takeParameters
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    root.takeForalls i =
      some (H.params, VExpr.wrapForalls H.indices current) :=
  H.telescope.takeParameters H.parameterCount

theorem HeaderTelescopeLoopCertificate.takeIndices
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    (VExpr.wrapForalls H.indices current).takeForalls nindices =
      some (H.indices, current) :=
  H.telescope.takeIndices H.indexCount

def AmbientParamContext.ofFirst
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : Hc.mlctx.vlctx.toCtx = indices.reverse ++ params.reverse) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := by
    have hwf : OnCtx (indices.reverse ++ params.reverse)
        (Hc.venv.IsType c.lparams.length) := hctx ▸ Hc.mlctx_wf.tr.wf.toCtx
    simpa [hctx] using VEnv.IsDefEqCtx.refl hwf
  length := by simp

def AmbientParamContext.ofFirstDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := hctx
  length := by simp

def AmbientParamContext.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : AmbientParamContext Hc params depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    AmbientParamContext
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      params (depth + 1) where
  ambient := sourceTy :: H.ambient
  context := by
    rcases hsource with ⟨u, hsource⟩
    change VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceTy :: (H.ambient ++ params.reverse))
      (ty' :: Hc.mlctx.vlctx.toCtx)
    exact .succ H.context
      (hsource.defeqDFC Hc.checking.tr.wf.ordered
        (H.context.symm Hc.checking.tr.wf.ordered))
  length := by simp [H.length]

theorem ParameterCachePrefix.empty
    (hparams : stats.params = #[]) :
    ParameterCachePrefix env Us Δ stats 0 depth := by
  refine ⟨?_, ?_⟩
  · simpa [hparams]
  · simp [hparams]

def ParameterContextSuffix.empty
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (hparams : stats.params = #[]) :
    ParameterContextSuffix Hc stats 0 where
  ambientDecls := []
  parameterDecls := []
  context := by simpa using hctx
  prefixLength := rfl
  cached := by simp [hparams]
  narrowParams := by simp [hparams, cachedParamVars]

/-- The first-header parameter branch extends the cached suffix itself.  The
empty-prefix premise records that parameters are all introduced before any
index binder. -/
def ParameterContextSuffix.push
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats 0)
    (hprefix : H.ambientDecls = [])
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      0 := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := []
    parameterDecls := entry :: H.parameterDecls
    context := ?_
    prefixLength := rfl
    cached := ?_
    narrowParams := ?_ }
  · have hcontext := H.context
    rw [hprefix] at hcontext
    change entry :: Hc.mlctx.vlctx = [] ++ entry :: H.parameterDecls
    simp only [List.nil_append]
    simpa using congrArg (entry :: ·) hcontext
  · simp only [Array.toList_push, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    exact .cons ⟨⟨c.ngen.curr⟩, ty.fvarsList, ty', rfl, rfl⟩
      H.cached
  · let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    let W : VLCtx.FVLift H.parameterDecls
        (entry :: H.parameterDecls) 0 1 0 :=
      .skip_fvar _ _ .refl
    have hscope : Hc.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    have hnarrowWF : VLCtx.WF Hc'.venv c.lparams.length
        (entry :: H.parameterDecls) := by
      change VLCtx.WF Hc.venv c.lparams.length
        (entry :: H.parameterDecls)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hscope] using Hc.mlctx_wf.tr.wf
      · intro fv deps heq
        simp only [entry, Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨by simpa [hscope] using Hc.current_not_mem,
          by simpa [hscope] using htr.fvarsList⟩
      · change Hc.venv.IsType c.lparams.length
          H.parameterDecls.toCtx ty'
        simpa [hscope] using hty
    have hold : List.Forall₂
        (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
        stats.params.toList
        ((cachedParamVars stats.params.size 0).map
          fun e => e.liftN 1 0) := by
      have weakAll : ∀ {as bs},
          List.Forall₂
              (TrExprS Hc.venv c.lparams H.parameterDecls) as bs →
            List.Forall₂
              (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
              as (bs.map fun e => e.liftN 1 0) := by
        intro as bs hp
        induction hp with
        | nil => exact .nil
        | cons h _ ih =>
          exact .cons
            (h.weakFV Hc.checking.tr.wf.ordered W hnarrowWF) ih
      exact weakAll H.narrowParams
    have hnew : TrExprS Hc'.venv c.lparams
        (entry :: H.parameterDecls)
        (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
      apply TrExprS.fvar (A := ty'.lift)
      simp [entry, VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type]
    simpa [Array.toList_push, cachedParamVars_succ] using
      Lean4Lean.VerifyInductive.List.Forall₂.append' hold
        (.cons hnew .nil)

/-- Index binders extend only the ambient prefix and preserve the exact
cached-parameter suffix. -/
def ParameterContextSuffix.withIndex
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := ?_
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    narrowParams := H.narrowParams }
  change entry :: Hc.mlctx.vlctx =
    (entry :: H.ambientDecls) ++ H.parameterDecls
  simp only [List.cons_append]
  rw [H.context]

theorem ParameterContextSuffix.parameterDecls_length
    (H : ParameterContextSuffix Hc stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    H.cached
  simpa using hlength.symm

/-- Locate executable parameter `i` in the reverse-ordered local-context
suffix. -/
theorem ParameterContextSuffix.parameterAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := by
    exact hj
  have hcached := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change CachedParameterDecl stats.params[stats.params.size - 1 - j]
    H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

/-- Split the cached-parameter suffix at executable array index `i`.  Entries
in `newer` are precisely the cached declarations introduced after parameter
`i`; `older` contains those introduced before it. -/
theorem ParameterContextSuffix.splitAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      CachedParameterDecl stats.params[i] entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

/-- Expose the exact `FVLift` that removes the ambient declarations and the
cached parameters newer than executable parameter `i`, leaving that
parameter as the head of the retained suffix. -/
theorem ParameterContextSuffix.fvLiftAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      Hc.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        Hc.mlctx.vlctx
        0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : Hc.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older)
      hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, rfl,
    hcontext, hparam, hlift⟩

/-- Narrow concrete scope immediately before consuming cached parameter `i`.
Only parameters already consumed by this later header may occur; ambient
indices and the current-or-future cached parameters are excluded. -/
structure LaterParameterScope
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : Hc.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    Hc.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem LaterParameterScope.olderLength
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size) :
    H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

/-- The block-wide abstract parameter at the current position denotes the
exact cached local declaration type selected by `LaterParameterScope`.
Crucially, the equality lives in `older.toCtx`, the scope containing exactly
the parameters already replayed. -/
theorem LaterParameterScope.parameterDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    {params : List VExpr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.older.toCtx
      (params[i]'(hparams.symm ▸ hi)) H.paramType (.sort u) := by
  have hcachedLength :=
    CachedParameterDecl.forall₂_toCtx_length Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe := VLCtx.toCtx_length_le H.newer
  have holderLe := VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <| congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  let j := H.newer.toCtx.length
  have hj : j < params.reverse.length := by
    simp only [List.length_reverse, j, hnewerCtx, hparams,
      H.newerLength]
    omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  have hentry := VEnv.IsDefEqCtx.getElemRight
    Hc.checking.tr.wf.ordered hctx' hj
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have hsourceIndex : params.length - 1 - j = i := by
    rw [hparams, hjEq]
    omega
  have hsourceIndex' :
      params.length - 1 - H.newer.toCtx.length = i := by
    simpa [j] using hsourceIndex
  rcases hentry with ⟨u, hentry⟩
  simp [j] at hentry
  refine ⟨u, ?_⟩
  simpa only [List.getElem_reverse, hsourceIndex'] using hentry

/-- The already replayed common-parameter prefix and the concrete `older`
suffix are definitionally equal contexts. -/
theorem LaterParameterScope.parameterPrefixDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    {params : List VExpr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (params.take i).reverse H.older.toCtx := by
  have hcachedLength :=
    CachedParameterDecl.forall₂_toCtx_length Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe := VLCtx.toCtx_length_le H.newer
  have holderLe := VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <| congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  let j := H.newer.toCtx.length
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have htake : params.length - (j + 1) = i := by
    rw [hparams, hjEq]
    omega
  have htake' : params.length - (H.newer.toCtx.length + 1) = i := by
    simpa [j] using htake
  have hdrop := VEnv.IsDefEqCtx.dropHeads hctx' (j + 1)
  simp [j] at hdrop
  simpa [List.drop_reverse, htake'] using hdrop

/-- A family-local parameter domain selected by `TypeShape.ParamsDefEq` is
definitionally equal to the exact cached declaration type used by executable
parameter replay. -/
theorem LaterParameterScope.ownParameterDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    {decl : VInductDecl} {params ownParams : List VExpr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparamsLength : params.length = stats.params.size)
    (huvars : c.lparams.length = decl.uvars)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hown : decl.ParamsDefEq Hc.venv params ownParams) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.older.toCtx
      (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using hown.length_eq
        omega)) H.paramType (.sort u) := by
  have hiparams : i < params.length := by omega
  rcases VInductDecl.ParamsDefEq.getElem hown hiparams with
    ⟨u, hcommonOwn⟩
  have hcommonOwnAtRuntime : Hc.venv.IsDefEq c.lparams.length
      (params.take i).reverse params[i]
      (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using hown.length_eq
        omega)) (.sort u) := by
    simpa only [huvars] using hcommonOwn
  have hprefix := H.parameterPrefixDefEq hi hparamsLength hctx
  have hcommonOwn' := hcommonOwnAtRuntime.defeqDFC
    Hc.checking.tr.wf.ordered hprefix
  rcases H.parameterDefEq hi hparamsLength hctx with
    ⟨cachedLevel, hcommonCached⟩
  have holderWF :=
    (H.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf).1
  exact ⟨cachedLevel, hcommonOwn'.symm.trans_r Hc.checking.tr.wf
    holderWF.toCtx hcommonCached⟩

/-- The domain currently exposed by narrow header replay is the exact cached
parameter declaration selected by the executable traversal.  This joins the
independent source `TypeShape`, the narrow synthesis state, and the retained
parameter cache; no successful executable `isDefEq` comparison is used. -/
theorem LaterParameterScope.currentDomainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {decl : VInductDecl} {params : List VExpr}
    {target : VInductiveType}
    {currentDomain currentBody : VExpr}
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target.toSkeleton Hscope.older
      (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (hparams : stats.params.size = decl.nparams)
    (huvars : c.lparams.length = decl.uvars)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hshape : decl.TypeShape Hc.venv params target) :
    Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx
      currentDomain Hscope.paramType := by
  have hiDecl : i < decl.nparams := by omega
  rcases VInductDecl.TypeShape.nextParameter hshape hiDecl with
    ⟨ownParams, expectedDomain, expectedBody, targetType,
      hownLength, hget, hown, hpresentation⟩
  have hiOwn : i < ownParams.length := by omega
  have hexpected : expectedDomain = ownParams[i] := by
    have hget' : some ownParams[i] = some expectedDomain := by
      simpa [List.getElem?_eq_getElem hiOwn] using hget
    exact (Option.some.inj hget').symm
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have hprefixLength : Hsynthesis.params.length =
      (ownParams.take i).length := by
    rw [Hsynthesis.parameterCount, List.length_take]
    omega
  have hpresentation' : Hc.venv.IsDefEq c.lparams.length []
      target.toSkeleton.type
      (VExpr.wrapForalls (ownParams.take i)
        (.forallE expectedDomain expectedBody)) targetType := by
    simpa [VInductiveType.toSkeleton, huvars] using hpresentation
  rcases Hsynthesis.nextDomainDefEq Hc.checking.tr.wf hindices
      hprefixLength hpresentation' with ⟨nextLevel, hnext⟩
  have hscopeCtx : Hscope.older.toCtx = Hsynthesis.params.reverse := by
    simpa [hindices] using Hsynthesis.scopeCtx
  have hnext' : Hc.venv.IsDefEq c.lparams.length Hscope.older.toCtx
      currentDomain expectedDomain (.sort nextLevel) := by
    rw [hscopeCtx]
    exact hnext
  have hparamsLength : params.length = stats.params.size := by
    have hlength : params.length = ownParams.length := by
      simpa using hown.length_eq
    omega
  rcases Hscope.ownParameterDefEq hi hparamsLength huvars hctx hown with
    ⟨cachedLevel, hcached⟩
  have hcached' : Hc.venv.IsDefEq c.lparams.length Hscope.older.toCtx
      expectedDomain Hscope.paramType (.sort cachedLevel) := by
    simpa [hexpected] using hcached
  exact ⟨_, hnext'.trans_r Hc.checking.tr.wf
    (Hscope.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf).1.toCtx hcached'⟩

theorem LaterParameterScope.older_eq_nil
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

/-- After the final cached parameter is consumed, the accumulated narrow
scope is exactly the complete cached-parameter suffix. -/
theorem LaterParameterScope.completedScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

/-- Consecutive cached-parameter scopes agree on the consumed suffix. -/
theorem LaterParameterScope.nextOlder
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {e next : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (Hnext : LaterParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

theorem LaterParameterScope.openedFVars
    (H : LaterParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem LaterParameterScope.openedUpSet
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      Hc.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older) H.added
    (by simpa [H.context] using Hc.mlctx_wf.tr.wf)

/-- Substitution of the current cached parameter, followed by an executable
normalization step, cannot introduce dependencies outside the newly consumed
parameter scope. -/
theorem LaterParameterScope.consumedFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

/-- Forget the ambient prefix, the not-yet-consumed cached parameters, and
the current cached parameter.  A source domain at this point may depend only
on the already consumed parameters in `older`. -/
theorem LaterParameterScope.olderLift
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older Hc.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : Hc.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

/-- Restrict a translated later-header domain to precisely the cached
parameters already consumed by this header. -/
theorem LaterParameterScope.domainTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom') :
    ∃ sourceDom', TrExprS Hc.venv c.lparams H.older dom sourceDom' := by
  have hclosed : Closed dom 0 := by
    have := hdom.closed
    simpa [Hc.mlctx.noBV] using this
  exact hdom.weakFV_inv Hc.checking.tr.wf H.olderLift
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hclosed H.fvars.1

/-- Recover every premise needed by the executable cached-parameter branch
from the retained local-context translation. -/
theorem LaterParameterScope.typing
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' ∧
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? Hc.mlctx_wf.tr.wf hhead
  rcases hfull with hfull
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : Hc.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ Hc.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  have hlocal :=
    (Hc.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv
  rcases hlocal with ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← Hc.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ Hc.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact Hc.mlctx_wf.tr.wf.find?_wf Hc.checking.tr.wf hfind

/-- The successful executable comparison of a later parameter domain with
its cached local type descends to the narrowed, abstract context. -/
theorem LaterParameterScope.domainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {dom' paramTy' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTyEq : paramTy' = H.paramType.lift.liftN
      (VLCtx.toCtx H.added).length 0)
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' paramTy') :
    ∃ sourceDom',
      TrExprS Hc.venv c.lparams H.older dom sourceDom' ∧
      Hc.venv.IsDefEqU c.lparams.length H.older.toCtx
        sourceDom' H.paramType := by
  rcases H.domainTranslation hdom with ⟨sourceDom', hsourceDom⟩
  have hweak := hsourceDom.weakFV Hc.checking.tr.wf.ordered
    H.olderLift Hc.mlctx_wf.tr.wf
  have htranslated : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx dom'
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0) :=
    hdom.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hweak
  rw [hparamTyEq] at heq
  have hfull := htranslated.symm.trans Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq
  have hfull' : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0)
      (H.paramType.liftN (VLCtx.toCtx H.added).length.succ 0) := by
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hfull
  exact ⟨sourceDom', hsourceDom,
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      H.olderLift.toCtx).1 hfull'⟩

/-- A closed source header starts the later-parameter traversal with an empty
free-variable scope. -/
noncomputable def LaterParameterScope.ofNoFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    LaterParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

/-- Advance the narrow scope after substituting cached parameter `i` and
normalizing the resulting body.  The next parameter's older suffix is
exactly the current cached declaration followed by the current older suffix.
-/
noncomputable def LaterParameterScope.next
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    LaterParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp :
        H.newer ++ currentEntry :: H.older =
          (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hopened : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older))
        (body.instantiate1 stats.params[i]!) := by
      rw [Expr.instantiate1_eq, H.parameter]
      exact H.openedFVars
    have hnormalized : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older)) normalized :=
      hbelow _ H.openedUpSet hopened
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- The core later-parameter abstraction step.  Translation of the
executable cached substitution is first restricted to the current-and-older
parameter suffix, then the cached free variable is turned back into the
source binder. -/
theorem LaterParameterScope.uninstantiateEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        body' (body''.liftN (VLCtx.toCtx H.added).length 0) := by
  have hopened' : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1' (.fvar H.fv)) body' := by
    simpa [Expr.instantiate1_eq, H.parameter] using hopened
  have hsuffixWF := H.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hfresh : H.fv ∉ H.older.fvars :=
    (hsuffixWF.2.1 H.fv H.deps rfl).1
  have hsourceFresh : FVarsIn (· ≠ H.fv) body :=
    H.fvars.mono fun fv hfv heq => by
      subst fv
      exact hfresh hfv
  have hopenedClosed : Closed (body.instantiate1' (.fvar H.fv)) 0 := by
    have := hopened'.closed
    simpa [Hc.mlctx.noBV] using this
  exact hopened'.uninstantiateAfterWeakFV_eq Hc.checking.tr.wf H.lift
    (.refl Hc.checking.tr.wf.ordered Hc.mlctx_wf.tr.wf)
    hopenedClosed H.openedFVars hsourceFresh

/-- The core later-parameter abstraction step without exposing the equality
back to the retained runtime context. -/
theorem LaterParameterScope.uninstantiate
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
      ((none, .vlam H.paramType) :: H.older) body body'' := by
  rcases H.uninstantiateEq hopened with ⟨body'', hbody'', _⟩
  exact ⟨body'', hbody''⟩

/-- Restrict the post-substitution normal form to the consumed-parameter
suffix and relate it to the reconstructed source body.  This is the semantic
state transition used by the later-header telescope accumulator. -/
theorem LaterParameterScope.normalizedBody
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized body') :
    ∃ sourceBody' normalized',
      TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body sourceBody' ∧
      TrExprS Hc.venv c.lparams
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
        normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length
        ((H.paramType :: H.older.toCtx)) sourceBody' normalized' := by
  rcases H.uninstantiateEq hopened with
    ⟨sourceBody', hsourceBody, hopenedEq⟩
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  have hopenedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  have hnormalizedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized :=
    hbelow _ H.openedUpSet hopenedFVars
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf H.lift
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedFVars with
    ⟨normalized', hnormalized'⟩
  have hnormalizedWeak := hnormalized'.weakFV
    Hc.checking.tr.wf.ordered H.lift Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceBody'.liftN (VLCtx.toCtx H.added).length 0)
      (normalized'.liftN (VLCtx.toCtx H.added).length 0) :=
    hopenedEq.symm.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.symm.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hnormalizedUniq)
  have hnarrow : Hc.venv.IsDefEqU c.lparams.length
      (VLCtx.toCtx
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      sourceBody' normalized' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx H.lift.toCtx).1 hfull
  exact ⟨sourceBody', normalized', hsourceBody, hnormalized',
    by simpa [VLCtx.toCtx] using hnarrow⟩

/-- Adding a common parameter weakens every cached parameter translation and
appends the newly generated free variable, whose abstract image is `bvar 0`.
This is the exact state update performed by `loopType` on the first header. -/
theorem ParameterCachePrefix.push
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats done 0)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      (done + 1) 0 := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hold : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList
      ((cachedParamVars done 0).map fun e => e.liftN 1 0) := by
    have mapRight : ∀ {as bs},
        List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
        List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
          (bs.map fun e => e.liftN 1 0) := by
      intro as bs hp
      induction hp with
      | nil => exact .nil
      | cons h _ ih =>
        exact .cons
          (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
    exact mapRight H.params
  have hfresh : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
    exact TrExprS.fvar (A := ty'.lift) (by
      change VLCtx.find? ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type])
  refine ⟨?_, ?_⟩
  · simpa using Lean4Lean.VerifyInductive.List.Forall₂.append'
      hold (.cons hfresh .nil)
  · intro param hparam
    simp only [Array.mem_push] at hparam
    rcases hparam with hparam | rfl
    · exact H.paramFVars param hparam
    · exact ⟨⟨c.ngen.curr⟩, rfl⟩

/-- Index binders do not change the concrete parameter cache; they uniformly
shift its abstract de Bruijn interpretation. -/
theorem ParameterCachePrefix.withIndex
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats
      done depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats done (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  refine ⟨?_, H.paramFVars⟩
  rw [cachedParamVars_depth_succ]
  have mapRight : ∀ {as bs},
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
      List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
        (bs.map fun e => e.liftN 1 0) := by
    intro as bs hp
    induction hp with
    | nil => exact .nil
    | cons h _ ih =>
      exact .cons
        (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
  exact mapRight H.params

theorem ParameterCachePrefix.complete
    {decl : VInductDecl}
    (H : ParameterCachePrefix env Us Δ stats decl.nparams depth) :
    List.Forall₂ (TrExprS env Us Δ) stats.params.toList
      (decl.paramVars depth) := by
  rw [← cachedParamVars_eq_paramVars decl]
  exact H.params

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
      dom.consumeTypeAnnotationsVerified dom')
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
            dom.consumeTypeAnnotationsVerified bi }).WF Q) :
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

/-- Index verification with the WHNF free-variable bound retained for
narrow-scope consumers. -/
theorem index.scopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotationsVerified dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      FVarsBelow
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotationsVerified bi }).WF Q) :
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
  exact (whnfInContext.scopeWF Hc' hopened).bind
    fun normalized hnormalized =>
      Hrec normalized hnormalized.1 hnormalized.2

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
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.WF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- Source-facing index step retaining the WHNF free-variable bound. -/
theorem index.sourceScopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        FVarsBelow
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.scopeWF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hbelow hnormalized =>
      Hrec body'' hbodyEq normalized hbelow hnormalized)

/-- Index-step wrapper that transports the first-header parameter cache under
the newly introduced index binder. -/
theorem index.cacheWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
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
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.withIndex Hc Hdom.consumed Hdom.isType)

/-- Index-step wrapper carrying the translated parameter cache and the exact
source telescope/counter state in lockstep. -/
theorem index.cacheTelescopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' i (nindices + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withIndex Hdom)

/-- Complete index branch for the synthesized header telescope.  The source
body conversion and the following executable `whnf` are composed before the
recursive state is exposed. -/
theorem index.cacheSynthesisWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = c.env)
      (_hsafety : c'.safety = c.safety)
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = c.allowPrimitive)
      (_hfuel : c'.fuel = c.fuel)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats done (depth + 1) →
      ParameterContextSuffix Hc' stats (depth + 1) →
      HeaderSynthesisCertificate Hc' target next i (nindices + 1) →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        i (nindices + 1) fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  exact Hrec Hc' rfl rfl rfl rfl rfl rfl normalized next hnext Hcache'
    (Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
    ((Hsynthesis.withIndex Hdom).normalize hsourceNext)

/-- Later-header index step carrying both the translated parameter cache and
the ambient-prefix shape used at the constructor boundary. -/
theorem index.runtimeStateWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hambient : AmbientParamContext Hc params depth)
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
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        AmbientParamContext
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType) params (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  exact Hrec body'' hbodyEq normalized hnormalized Hcache'
    (Hambient.withIndex Hdom.consumed Hdom.isType Hdom.source_defeq)

/-- Verification step for a common parameter of the first mutual header.  In
addition to the opened-body relation, the continuation sees the exact fresh
free variable appended to the executable parameter cache. -/
theorem firstParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotationsVerified dom')
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
            dom.consumeTypeAnnotationsVerified bi }).WF Q) :
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
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact firstParameter.WF Hc hi hempty Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- First-parameter wrapper synchronized with the executable cache push. -/
theorem firstParameter.cacheWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
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
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.push Hc Hdom.consumed Hdom.isType)

/-- First-parameter wrapper carrying the cache and source telescope counters
through the same successful executable branch. -/
theorem firstParameter.cacheTelescopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Htelescope.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' (i + 1) nindices →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withParameter hindices Hdom)

/-- Complete first-parameter branch for the synthesized header telescope. -/
theorem firstParameter.cacheSynthesisWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hsuffix : ParameterContextSuffix Hc stats 0)
    (hprefix : Hsuffix.ambientDecls = [])
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Hsynthesis.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = c.env)
      (_hsafety : c'.safety = c.safety)
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = c.allowPrimitive)
      (_hfuel : c'.fuel = c.fuel)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        (done + 1) 0 →
      ParameterContextSuffix Hc'
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        0 →
      (Hsynthesis' : HeaderSynthesisCertificate
        Hc' target next (i + 1) nindices) →
      Hsynthesis'.indices = [] →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  let Hsynthesis' :=
    (Hsynthesis.withParameter hindices Hdom).normalize hsourceNext
  exact Hrec Hc' rfl rfl rfl rfl rfl rfl normalized next hnext Hcache'
    (Hsuffix.push Hc hprefix Hdom.consumed Hdom.isType)
    Hsynthesis' (by rfl)

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

/-- Complete cached-parameter step with the narrow concrete scope and the
reconstructed source binder exposed to the continuation. -/
theorem laterParameter.scopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
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
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
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
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind
    fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    let Hbody : LaterParameterScope Hsuffix i body := {
      Hscope with fvars := Hscope.fvars.2 }
    have habstract := Hbody.uninstantiate hopened
    exact (whnfInContext.scopeWF Hc hopened).bind
      fun normalized hnormalized =>
      Hrec heq habstract normalized hnormalized.1 hnormalized.2
        (Hbody.normalizedBody hopened hnormalized.1 hnormalized.2)
        (fun hnext => Hbody.next hnext hnormalized.1)

/-- Complete cached-parameter step driven only by the retained scope.  In
particular, lookup of the cached concrete parameter and all of its abstract
typing data are consequences of `Hscope`, rather than premises supplied by
the caller. -/
theorem laterParameter.checkedScopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ {paramTy' param'},
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' →
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      (∃ sourceDom',
        TrExprS Hc.venv c.lparams Hscope.older dom sourceDom' ∧
        Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx
          sourceDom' Hscope.paramType) →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hscope.typing with
    ⟨paramTy, paramTy', param', hget, hparamTy, hparamTyEq,
      hparam, hparamType⟩
  apply laterParameter.scopeWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty Hsuffix Hscope hget hdom hbody hparamTy hparam hparamType
  intro heq habstract normalized hbelow hnormalized htransition hnext
  exact Hrec hparam hparamType heq
    (Hscope.domainDefEq hdom hparamTyEq heq) habstract
    normalized hbelow hnormalized htransition hnext

/-- Reusing a cached parameter does not alter the retained ambient-prefix
shape. -/
theorem laterParameter.runtimeStateWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hambient : AmbientParamContext Hc params depth)
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
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
        AmbientParamContext Hc params depth →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply laterParameter.sourceWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty hget hdom hbody hparamTy hparam hparamType
  intro heq normalized hnormalized
  exact Hrec heq normalized hnormalized Hambient

/-- Recursive verifier for the first mutual header.  It follows the concrete
fuel recursion and carries both the parameter cache and the synthesized
abstract telescope to the terminal continuation. -/
theorem firstHeaderSynthesisWF
    {target : VInductiveTypeSkeleton}
    {sourceEnv : Environment}
    {sourceSafety : DefinitionSafety}
    {sourceAllowPrimitive : Bool}
    {sourceFuel : FuelConfig}
    {baseLevels : List Level} {baseNindices : Array Nat}
    {baseConsts : Array Expr}
    {R : VEnv → Prop}
    {α : Type} (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M α) (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {type' : Expr}
      {current' : VExpr} {i' nindices' : Nat}
      (Hc' : ContextWF c'),
      c'.env = sourceEnv →
      c'.safety = sourceSafety →
      c'.lparams = Us →
      c'.allowPrimitive = sourceAllowPrimitive →
      c'.fuel = sourceFuel →
      stats'.indConsts.isEmpty = true →
      stats'.levels = baseLevels →
      stats'.nindices = baseNindices →
      stats'.indConsts = baseConsts →
      R Hc'.venv →
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      i' = nparams →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' i' nindices' →
      ParameterContextSuffix Hc' stats' nindices' →
      HeaderSynthesisCertificate Hc' target current' i' nindices' →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      (k type' stats' nindices' c').WF Q)
    (Hc : ContextWF c)
    (henv : c.env = sourceEnv)
    (hsafety : c.safety = sourceSafety)
    (hlparams : c.lparams = Us)
    (hallowPrimitive : c.allowPrimitive = sourceAllowPrimitive)
    (hfuel : c.fuel = sourceFuel)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevelsStable : stats.levels = baseLevels)
    (hnindicesStable : stats.nindices = baseNindices)
    (hconstsStable : stats.indConsts = baseConsts)
    (HR : R Hc.venv)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats i nindices)
    (Hsuffix : ParameterContextSuffix Hc stats nindices)
    (Hsynthesis : HeaderSynthesisCertificate Hc target current i nindices)
    (hphase : i < nparams → Hsynthesis.indices = [] ∧ nindices = 0)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      fuel k c).WF Q := by
  induction fuel generalizing c stats type current i nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htype with
      | forallE hdomType hbodyType hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
        by_cases hi : i < nparams
        · rcases hphase hi with ⟨hindices, hnindices⟩
          subst nindices
          have hambient : Hsuffix.ambientDecls = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using Hsuffix.prefixLength
          apply firstParameter.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi hempty (by simpa using Hcache) Hsuffix hambient
            Hsynthesis hindices Hdom hbody
          intro c' Hc' henv' hsafety' hvenv' hlparams' hallowPrimitive'
            hfuel' normalized next hnext Hcache' Hsuffix'
            Hsynthesis' hindices'
          apply ih Hc' (henv'.trans henv) (hsafety'.trans hsafety)
            (hlparams'.trans hlparams)
            (hallowPrimitive'.trans hallowPrimitive)
            (hfuel'.trans hfuel)
            (by simpa using hempty)
            (by simpa using hlevelsStable)
            (by simpa using hnindicesStable)
            (by simpa using hconstsStable)
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro _
            exact ⟨hindices', rfl⟩
          · exact hnext
        · apply index.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi Hcache Hsuffix Hsynthesis Hdom hbody
          intro c' Hc' henv' hsafety' hvenv' hlparams' hallowPrimitive'
            hfuel' normalized next hnext Hcache' Hsuffix'
            Hsynthesis'
          apply ih Hc' (henv'.trans henv) (hsafety'.trans hsafety)
            (hlparams'.trans hlparams)
            (hallowPrimitive'.trans hallowPrimitive)
            (hfuel'.trans hfuel)
            hempty hlevelsStable
            hnindicesStable hconstsStable
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro hlt
            exact False.elim (hi hlt)
          · exact hnext
    · by_cases hi : i = nparams
      · exact result.WF hforall hi
          (Hresult Hc henv hsafety hlparams hallowPrimitive hfuel hempty
            hlevelsStable hnindicesStable
            hconstsStable HR hforall hi Hcache Hsuffix Hsynthesis htype)
      · exact parameterMismatch.WF hforall hi

/-- Follow the executable later-header loop through all cached common
parameters.  The retained suffix supplies each cached lookup and advances
after the executable normalization step.  Once `i = nparams`, ownership of
the unchanged loop state passes to the index/result verifier. -/
theorem laterParametersWF
    {alpha : Type} (Hc : ContextWF c)
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {type' current' i' fuel'},
      i' = nparams →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' current' →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        nindices fuel' k c).WF Q)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : i < stats.params.size →
      LaterParameterScope Hsuffix i type)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      nindices fuel k c).WF Q := by
  induction fuel generalizing type current i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htype with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix (Hscope histats) hdom hbody
        intro paramTy' param' _hparam _hparamType _heq _hdomain
          _habstract normalized _hbelow hnormalized _htransition hnext
        apply ih (i := i + 1) (current := body'.inst param')
        · omega
        · intro hlt
          exact hnext hlt
        · exact hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq htype

/-- Cached-parameter recursion with the independent narrow header telescope
accumulated in lockstep.  The executable reader context remains unchanged;
the synthesis scope grows only by the parameters consumed by this header. -/
theorem laterParameterSynthesisWF
    {alpha : Type} (Hc : ContextWF c)
    {target : VInductiveTypeSkeleton}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hresult : ∀ {type' narrowCurrent fullCurrent scope' i' fuel'},
      i' = nparams →
      NarrowHeaderSynthesisCertificate Hc.venv c.lparams target
        scope' narrowCurrent i' 0 →
      scope' = Hsuffix.parameterDecls →
      TrExprS Hc.venv c.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' fullCurrent →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        0 fuel' k c).WF Q)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : ∀ _h : i < stats.params.size,
      LaterParameterScope Hsuffix i type)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      0 fuel k c).WF Q := by
  induction fuel generalizing type scope narrowCurrent fullCurrent i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htypeFull with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := 0) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix Hcurrent hdom hbody
        intro paramTy' param' _hparam _hparamType _heq hdomain
          _habstract normalized hbelow hnormalized htransition hnext
        have hindices : Hsynthesis.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
        have hcurrentWF := Hcurrent.lift.wf Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf
        rcases Hsynthesis.consumeParameter Hc.checking.tr.wf hindices
            htypeNarrow hcurrentWF hdomain htransition with
          ⟨normalized', hnormalized', ⟨Hsynthesis'⟩⟩
        let Hbody : LaterParameterScope Hsuffix i body := {
          Hcurrent with fvars := Hcurrent.fvars.2 }
        exact ih (i := i + 1)
          (scope := (some (Hcurrent.fv, Hcurrent.deps),
            .vlam Hcurrent.paramType) :: Hcurrent.older)
          (narrowCurrent := normalized')
          (fullCurrent := body'.inst param')
          (hbound := by omega)
          (Hscope := fun hlt => hnext hlt)
          (hscopeEq := fun hlt =>
            Hcurrent.nextOlder (hnext hlt) hlt)
          (hcompleteScope := fun heq => by
            have hdone : i + 1 = stats.params.size := by
              rw [hparams]
              exact heq
            exact Hcurrent.completedScope hdone)
          Hsynthesis' hnormalized'
          (Hbody.consumedFVars hbelow) hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq Hsynthesis (hcompleteScope hieq)
        htypeNarrow htypeFVars htypeFull

/-- Traverse the index suffix of a later mutual header while keeping its
semantic telescope independent of ambient declarations retained by the
executable checker. -/
theorem laterIndexSynthesisWF
    {alpha : Type} {target : VInductiveTypeSkeleton}
    {commonParams : List VExpr}
    {paramU : Nat}
    {sourceEnv : Environment}
    {sourceSafety : DefinitionSafety}
    {sourceAllowPrimitive : Bool}
    {sourceFuel : FuelConfig}
    {R : VEnv → Prop}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = sourceEnv)
      (_hsafety : c'.safety = sourceSafety)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = sourceAllowPrimitive)
      (_hfuel : c'.fuel = sourceFuel)
      {type' narrowCurrent fullCurrent scope' nindices' fuel'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      (Hsynthesis' : NarrowHeaderSynthesisCertificate Hc'.venv c'.lparams
        target scope' narrowCurrent nparams nindices') →
      NarrowRuntimeScope Hc'.venv c'.lparams scope' Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' fullCurrent →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats nparams (depth + nindices') →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      AmbientParamContext Hc' commonParams (depth + nindices') →
      R Hc'.venv →
      VEnv.IsDefEqCtx Hc'.venv paramU []
        commonParams.reverse Hsynthesis'.params.reverse →
      (AddInductive.checkInductiveTypes.loopType nparams stats type'
        nparams nindices' (fuel' + 1) k c').WF Q)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hc : ContextWF c)
    (henv : c.env = sourceEnv)
    (hsafety : c.safety = sourceSafety)
    (hallowPrimitive : c.allowPrimitive = sourceAllowPrimitive)
    (hfuel : c.fuel = sourceFuel)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams (depth + nindices))
    (Hsuffix : ParameterContextSuffix Hc stats (depth + nindices))
    (Hambient : AmbientParamContext Hc commonParams
      (depth + nindices))
    (HR : R Hc.venv)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent nparams nindices)
    (Hparams : VEnv.IsDefEqCtx Hc.venv paramU []
      commonParams.reverse Hsynthesis.params.reverse)
    (Hruntime : NarrowRuntimeScope Hc.venv c.lparams
      scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type
      nparams nindices fuel k c).WF Q := by
  induction fuel generalizing c type scope narrowCurrent fullCurrent
      nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htypeNarrow with
      | @forallE indexType narrowBody _ _ _ _ _
          hdomType _hbodyType hdomNarrow hbodyNarrow =>
        rcases TrExpr.forallE_source htypeFull with
          ⟨sourceDom, fullBody, hdomFull, hbodyFull,
            hdomFullType, _hbodyFullType, _hfullCurrent⟩
        rcases hconsume c Hc hdomFull hdomFullType with
          ⟨consumedDom, Hdom⟩
        rcases Hdom.body Hc hbodyFull with
          ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
        apply index.scopeWF (stats := stats) (nparams := nparams)
          (i := nparams) (nindices := nindices) (fuel := fuel)
          (k := k) (Q := Q) Hc (by omega) Hdom.consumed Hdom.isType
          hbodyConsumed
        intro normalized hbelow hnormalized
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hdeps : dom.consumeTypeAnnotationsVerified.fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotationsVerified_fvarsIn htypeFVars.1)).1
        rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
          ⟨domainLevel, hdomain⟩
        let Hruntime' : NarrowRuntimeScope Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList),
              .vlam indexType) :: scope)
            Hc'.mlctx.vlctx :=
          Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
        have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
        have hopenedNarrow : TrExprS Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList),
              .vlam indexType) :: scope)
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
          rw [Expr.instantiate1_eq]
          exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
        have hopenedFVars : FVarsIn
            (· ∈ VLCtx.fvars ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList),
              .vlam indexType) :: scope))
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) := by
          rw [Expr.instantiate1_eq]
          apply (htypeFVars.2.mono fun fv hfv => by
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_of_mem _ hfv).instantiate1
          rw [VLCtx.fvars_cons_some]
          exact List.mem_cons_self
        have hnormalizedFVars := hbelow _ Hruntime'.upset hopenedFVars
        rcases hnormalized with
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
        have hnormalizedClosed : Closed normalized 0 := by
          have := hnormalizedFull.closed
          have hnoBV : Hc'.mlctx.vlctx.bvars = 0 := Hc'.mlctx.noBV
          rw [hnoBV] at this
          exact this
        rcases Hruntime'.restrictEq Hc'.checking.tr.wf
            hnormalizedFull hnormalizedClosed hnormalizedFVars with
          ⟨normalizedNarrow, hnormalizedNarrow, hnormalizedEq⟩
        have hopenedWeak : TrExprS Hc'.venv c.lparams Hruntime'.expanded
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
            (narrowBody.lift' Hruntime'.shift) := by
          simpa using hopenedNarrow.weakFV' Hc'.checking.tr.wf.ordered
            Hruntime'.lift Hruntime'.context.wf
        have hopenedFull := Hc.instantiateFresh
          (name := name) (bi := bi) Hdom.consumed Hdom.isType
          hbodyConsumed
        have hopenedEq := hopenedWeak.uniq Hc'.checking.tr.wf
          Hruntime'.context hopenedFull
        have hopenedEq' := hopenedEq.defeqDFC
          Hc'.checking.tr.wf.ordered Hruntime'.context.defeqCtx
        have hnormalizeU : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx consumedBody normalizedFull :=
          hnormalizeEq.symm
        have hsourceNormalized := hopenedEq'.trans Hc'.checking.tr.wf
          Hc'.mlctx_wf.tr.wf.toCtx hnormalizeU
        have hfull : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx
            (narrowBody.lift' Hruntime'.shift)
            (normalizedNarrow.lift' Hruntime'.shift) :=
          hsourceNormalized.trans Hc'.checking.tr.wf
            Hc'.mlctx_wf.tr.wf.toCtx hnormalizedEq
        have hexpanded := hfull.defeqDFC Hc'.checking.tr.wf.ordered
          (Hruntime'.context.defeqCtx.symm Hc'.checking.tr.wf.ordered)
        have hnarrow : Hc'.venv.IsDefEqU c.lparams.length
            (indexType :: scope.toCtx)
            narrowBody normalizedNarrow :=
          (VEnv.IsDefEqU.weak'_iff Hc'.checking.tr.wf
              Hruntime'.context.wf.toCtx Hruntime'.lift.toCtx).1 hexpanded
        have hdomainNarrow : ∃ sourceDom',
            TrExprS Hc'.venv c.lparams scope dom sourceDom' ∧
            Hc'.venv.IsDefEqU c.lparams.length scope.toCtx
              sourceDom' indexType :=
          ⟨_, hdomNarrow,
            ⟨.sort (Classical.choose hdomType),
              Classical.choose_spec hdomType⟩⟩
        have htransition : ∃ sourceBody' normalized',
            TrExprS Hc'.venv c.lparams
              ((none, .vlam indexType) :: scope)
              body sourceBody' ∧
            TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotationsVerified.fvarsList),
                .vlam indexType) :: scope)
              normalized normalized' ∧
            Hc'.venv.IsDefEqU c.lparams.length
              (indexType :: scope.toCtx)
              sourceBody' normalized' :=
          ⟨narrowBody, normalizedNarrow, hbodyNarrow,
            hnormalizedNarrow, hnarrow⟩
        rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
            Hc'.checking.tr.wf
            (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
            hscopeWF hdomainNarrow htransition with
          ⟨nextNarrow, hnextNarrow, Hsynthesis',
            ⟨hparamsPreserved, _hindicesPreserved⟩⟩
        exact ih (fun Hc'' henv'' hsafety'' hlparams'' hallowPrimitive''
            hfuel'' => Hresult Hc'' henv'' hsafety''
              (by simpa using hlparams'') hallowPrimitive'' hfuel'') Hc'
          (by simpa using henv) (by simpa using hsafety)
          (by simpa using hallowPrimitive) (by simpa using hfuel)
          (by simpa [Nat.add_assoc] using
            Hcache.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            (Hambient.withIndex Hdom.consumed Hdom.isType
              Hdom.source_defeq))
          (by change R Hc.venv; exact HR)
          Hsynthesis' (by
            rw [hparamsPreserved]
            change VEnv.IsDefEqCtx Hc.venv paramU []
              commonParams.reverse Hsynthesis.params.reverse
            exact Hparams) Hruntime' hnextNarrow
          hnormalizedFVars
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
    · exact Hresult Hc henv hsafety rfl hallowPrimitive hfuel hforall
        Hsynthesis Hruntime
        htypeNarrow
        htypeFVars htypeFull Hcache Hsuffix Hambient HR Hparams

end checkInductiveTypes.loopType


end VerifyInductive
end Lean4Lean
