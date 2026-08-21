import Lean4Lean.Verify.Inductive.Specification.Recursors

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Verification state for the outer inductive-construction monad. The local
context is represented by the same `MLCtx` used by the typechecker proof, while
the production reader retains the independently generated `_ind_fresh` names. -/
def MLCtxOnlyLams (m : TypeChecker.MLCtx) : Prop :=
  ∀ d ∈ m.decls, ∃ index fv name type bi kind,
    d = .cdecl index fv name type bi kind

theorem MLCtxOnlyLams.nil : MLCtxOnlyLams .nil := by
  intro d hd
  simp [TypeChecker.MLCtx.decls] at hd

theorem MLCtxOnlyLams.vlam
    (H : MLCtxOnlyLams m) :
    MLCtxOnlyLams (.vlam fv name type type' bi m) := by
  intro d hd
  simp only [TypeChecker.MLCtx.decls, List.mem_cons] at hd
  rcases hd with rfl | hd
  · exact ⟨_, _, _, _, _, _, rfl⟩
  · exact H d hd

theorem MLCtxOnlyLams.tail_vlam
    (H : MLCtxOnlyLams (.vlam fv name type type' bi m)) :
    MLCtxOnlyLams m := by
  intro d hd
  exact H d (by simp [TypeChecker.MLCtx.decls, hd])

theorem MLCtxOnlyLams.vlet_false
    (H : MLCtxOnlyLams (.vlet fv name type value type' value' m)) : False := by
  rcases H (.ldecl m.length fv name type value false default)
      (by simp [TypeChecker.MLCtx.decls]) with
    ⟨index, fv', name', type', bi, kind, h⟩
  cases h

/-- An all-lambda metacontext loses no declarations when projected to its
anonymous typing context. -/
theorem MLCtxOnlyLams.toCtx_length
    (H : MLCtxOnlyLams m) : m.vlctx.toCtx.length = m.length := by
  induction m with
  | nil => rfl
  | vlam fv name type type' bi tail ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
      TypeChecker.MLCtx.length, List.length_cons]
    rw [ih H.tail_vlam]
  | vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

/-- Every declaration of an all-lambda metacontext owns one free-variable
identifier, so its concrete free-variable list also preserves length. -/
theorem MLCtxOnlyLams.fvars_length
    (H : MLCtxOnlyLams m) : m.vlctx.fvars.length = m.length := by
  induction m with
  | nil => rfl
  | vlam fv name type type' bi tail ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      TypeChecker.MLCtx.length, List.length_cons]
    rw [ih H.tail_vlam]
  | vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

theorem MLCtxOnlyLams.dropN
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length) :
    MLCtxOnlyLams (m.dropN n hn) := by
  induction n generalizing m with
  | zero => simpa using H
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN] using
        ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Dropping a recent all-lambda prefix does not change lookup of any free
variable that remains in the older context. -/
theorem MLCtxOnlyLams.dropN_find?_eq
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us)
    (n : Nat) (hn : n ≤ m.length)
    (hfv : fv ∈ (m.dropN n hn).vlctx.fvars) :
    m.lctx.find? fv = (m.dropN n hn).lctx.find? fv := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam current name type type' bi tail =>
      have htailMem : fv ∈ tail.vlctx.fvars :=
        TypeChecker.MLCtx.dropN_fvars_subset n
          (Nat.le_of_succ_le_succ hn) hfv
      have hcurrentFresh : current ∉ tail.vlctx.fvars :=
        Hwf.1.tr.find?_eq_none.1 Hwf.2.1
      have hne : current ≠ fv := by
        intro heq
        exact hcurrentFresh (heq ▸ htailMem)
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
        LocalContext.find?]
      rw [Hwf.1.tr.1.map_wf.find?_insert, if_neg]
      · exact ih H.tail_vlam Hwf.1 (Nat.le_of_succ_le_succ hn) hfv
      · intro heq
        exact hne (LawfulBEq.eq_of_beq heq)
    | vlet current name type value type' value' tail =>
      exact H.vlet_false.elim

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
    c.mkForall' n hn body =
      VExpr.wrapForalls (MLCtxForallDomains c n hn) body := by
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

theorem TypeChecker.MLCtx.mkLambda'_eq_wrapLams
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkLambda' n hn body =
      VExpr.wrapLams (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains,
      VExpr.wrapLams]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains]
      rw [ih, VExpr.wrapLams_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

theorem MLCtxOnlyLams.forallDomains_length
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (MLCtxForallDomains c n hn).length = n := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [MLCtxForallDomains, List.length_append,
        List.length_singleton]
      rw [ih H.tail_vlam (Nat.le_of_succ_le_succ hn)]
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

theorem MLCtxOnlyLams.forallDomains_eq_take_reverse
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    MLCtxForallDomains c n hn = (c.vlctx.toCtx.take n).reverse := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [MLCtxForallDomains, TypeChecker.MLCtx.vlctx,
        VLCtx.toCtx, List.take_succ_cons, List.reverse_cons]
      rw [ih H.tail_vlam (Nat.le_of_succ_le_succ hn)]
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Splitting an all-lambda checker context after a recent prefix exposes
exactly the reversed `MLCtxForallDomains` followed by the older context. -/
theorem MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    c.vlctx.toCtx =
      (MLCtxForallDomains c n hn).reverse ++ (c.dropN n hn).vlctx.toCtx := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
        MLCtxForallDomains, List.reverse_append, List.reverse_singleton,
        List.singleton_append, TypeChecker.MLCtx.dropN]
      simpa [List.append_assoc] using congrArg (type' :: ·)
        (ih H.tail_vlam (Nat.le_of_succ_le_succ hn))
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

theorem MLCtxOnlyLams.toCtx_take
    (H : MLCtxOnlyLams c) (n : Nat) :
    VLCtx.toCtx (c.vlctx.take n) = c.vlctx.toCtx.take n := by
  induction n generalizing c with
  | zero => simp [VLCtx.toCtx]
  | succ n ih =>
    cases c with
    | nil => simp [TypeChecker.MLCtx.vlctx, VLCtx.toCtx]
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        VLCtx.toCtx]
      rw [ih H.tail_vlam]
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- The newest free-variable identifiers and verifier declarations of an
all-lambda metacontext are paired pointwise. -/
theorem MLCtxOnlyLams.fvarRevList_declarations
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      (c.fvarRevList n hn) (c.vlctx.take n) := by
  induction n generalizing c with
  | zero => exact .nil
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type target bi tail =>
      exact .cons ⟨type.fvarsList, target, rfl⟩
        (ih H.tail_vlam (Nat.le_of_succ_le_succ hn))
    | vlet fv name type value target valueTarget tail =>
      exact H.vlet_false.elim

/-- For a verifier context containing only local declarations, dropping the
newest `n` entries before or after erasing local metadata gives the same
ordinary typing context. -/
theorem MLCtxOnlyLams.toCtx_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (c.dropN n hn).vlctx.toCtx = c.vlctx.toCtx.drop n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        VLCtx.toCtx, List.drop_succ_cons] using
          ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

theorem MLCtxOnlyLams.vlctx_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (c.dropN n hn).vlctx = c.vlctx.drop n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        List.drop_succ_cons] using
          ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Dropping an ordinary-local suffix and then restoring it is precisely a
free-variable weakening.  The generated inductive contexts contain no local
lets, so the lift amount agrees with the number of dropped declarations. -/
theorem MLCtxOnlyLams.dropN_fvlift
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length) :
    VLCtx.FVLift (m.dropN n hn).vlctx m.vlctx 0 n 0 := by
  induction n generalizing m with
  | zero => exact .refl
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      have Htail := H.tail_vlam
      have W := ih Htail (Nat.le_of_succ_le_succ hn)
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        VLocalDecl.depth, Nat.add_comm] using
          VLCtx.FVLift.skip_fvar (fv, type.fvarsList) (.vlam type') W
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

@[simp] theorem TypeChecker.MLCtx.vlctx_length
    (m : TypeChecker.MLCtx) : m.vlctx.length = m.length := by
  induction m <;> simp_all [TypeChecker.MLCtx.vlctx]

/-- The newest `n` local declarations are exactly the prefix removed by
`dropN`.  This purely structural fact is useful when a semantic invariant
describes the older context as a distinguished suffix. -/
theorem TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    (m : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ m.length) :
    m.vlctx = m.vlctx.take n ++ (m.dropN n hn).vlctx := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        TypeChecker.MLCtx.dropN, List.cons_append]
      congr 1
      exact ih tail (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        TypeChecker.MLCtx.dropN, List.cons_append]
      congr 1
      exact ih tail (Nat.le_of_succ_le_succ hn)

/-- The free-variable identifiers in the newest `n` verifier declarations
are exactly `fvarRevList`. -/
theorem TypeChecker.MLCtx.vlctx_take_fvars
    (m : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ m.length) :
    VLCtx.fvars (m.vlctx.take n) = m.fvarRevList n hn := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        VLCtx.fvars_cons_some, TypeChecker.MLCtx.fvarRevList,
        List.cons.injEq]
      exact ⟨trivial, ih tail (Nat.le_of_succ_le_succ hn)⟩
    | vlet fv name type value type' value' tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        VLCtx.fvars_cons_some, TypeChecker.MLCtx.fvarRevList,
        List.cons.injEq]
      exact ⟨trivial, ih tail (Nat.le_of_succ_le_succ hn)⟩

structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  onlyLams : MLCtxOnlyLams mlctx
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
  onlyLams := MLCtxOnlyLams.nil
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun

/-- Retain the local checker state while moving to a production and abstract
environment pair known to represent the same extension. -/
def ContextWF.withEnv (H : ContextWF c)
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hle : H.venv ≤ venv') :
    ContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh

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
  onlyLams := H.onlyLams.vlam
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

theorem ContextWF.withLocalDecl_venv (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).venv = H.venv := rfl

theorem ContextWF.withLocalDecl_toCtx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

/-- Semantic local-context invariant for generated recursor frames.  Its
universe parameter list is deliberately independent of `c.lparams`: during
large elimination, `mkRecInfos` builds raw locals in the original reader
context, while their types are interpreted under the recursor's fresh
universe parameter. -/
structure RecursorContextWF (c : AddInductive.Context)
    (recLparams : List Name) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv recLparams
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv

/-- An ordinary verified context is already a recursor context when no
universe rebasing is required. -/
def ContextWF.toRecursorContextWF (H : ContextWF c) :
    RecursorContextWF c c.lparams where
  venv := H.venv
  checking := H.checking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh

/-- Reinterpret an already verified executable local context after prepending
one fresh recursor universe parameter.  Concrete declarations and free-variable
names are unchanged; only their stored abstract universe indices move. -/
def ContextWF.prependRecursorLevelParam
    (H : ContextWF c) (hfresh : fresh ∉ c.lparams) :
    RecursorContextWF c (fresh :: c.lparams) := by
  let mlctx := H.mlctx.prependLevelParam c.lparams.length
  have hfv : mlctx.vlctx.fvars = H.mlctx.vlctx.fvars := by
    dsimp [mlctx]
    rw [TypeChecker.MLCtx.prependLevelParam_vlctx]
    exact VLCtx.instL_fvars H.mlctx.vlctx
  exact {
    venv := H.venv
    checking := H.checking
    mlctx := mlctx
    mlctx_wf := H.mlctx_wf.prependLevelParam H.checking.tr.wf hfresh
    onlyLams := by
      intro d hd
      apply H.onlyLams d
      simpa [mlctx] using hd
    lctx_eq := by simpa [mlctx] using H.lctx_eq
    ngen_prefix := H.ngen_prefix
    indFresh := by
      intro fv hmem
      exact H.indFresh fv (hfv ▸ hmem)
    kernelFresh := by
      intro fv hmem
      exact H.kernelFresh fv (hfv ▸ hmem) }

@[simp] theorem ContextWF.prependRecursorLevelParam_venv
    (H : ContextWF c) (hfresh : fresh ∉ c.lparams) :
    (H.prependRecursorLevelParam hfresh).venv = H.venv := rfl

@[simp] theorem ContextWF.prependRecursorLevelParam_mlctx
    (H : ContextWF c) (hfresh : fresh ∉ c.lparams) :
    (H.prependRecursorLevelParam hfresh).mlctx =
      H.mlctx.prependLevelParam c.lparams.length := rfl

theorem RecursorContextWF.current_not_mem
    (H : RecursorContextWF c recLparams) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem RecursorContextWF.kernel_reserves_current
    (H : RecursorContextWF c recLparams) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

/-- Extend a universe-rebased recursor context by one semantically checked
raw local declaration. -/
def RecursorContextWF.withLocalDecl
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') :
    RecursorContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } recLparams where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := ⟨H.mlctx_wf,
    H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩
  onlyLams := H.onlyLams.vlam
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

@[simp] theorem RecursorContextWF.withLocalDecl_venv
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).venv = H.venv := rfl

@[simp] theorem RecursorContextWF.withLocalDecl_toCtx
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

/-- Close the `n` most recently introduced recursor locals into the exact
production `LocalContext.mkForall` telescope.  The free-variable equation is
the reviewable boundary connecting the executable selection array to the
semantic `MLCtx` suffix. -/
theorem RecursorContextWF.mkForallRecent
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx body body')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx body')
    (n : Nat) (hn : n ≤ H.mlctx.length) (xs : Array Expr)
    (hxs : xs.toList.reverse =
      (H.mlctx.fvarRevList n hn).map Expr.fvar) :
    TrExprS H.venv recLparams (H.mlctx.dropN n hn).vlctx
        (c.lctx.mkForall xs body) (H.mlctx.mkForall' n hn body') ∧
      H.venv.IsType recLparams.length
        (H.mlctx.dropN n hn).vlctx.toCtx
        (H.mlctx.mkForall' n hn body') := by
  have hsource : c.lctx.mkForall xs body =
      H.mlctx.mkForall n hn body := by
    rw [← H.lctx_eq]
    exact H.mlctx_wf.mkForall_eq n hn hxs
  rw [hsource]
  exact H.mlctx_wf.mkForall_trS H.checking.tr.wf htr hty n hn

theorem ContextWF.findCDecl (H : ContextWF c)
    (hmem : fv ∈ H.mlctx.vlctx.fvars) :
    ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
  rcases (H.mlctx_wf.tr.find?_eq_some (fv := fv)).2 hmem with
    ⟨decl, hfind⟩
  have hfindDecls : H.mlctx.decls.find? (fv == ·.fvarId) = some decl := by
    rw [← H.mlctx_wf.find?_eq]
    exact hfind
  have hdeclMem : decl ∈ H.mlctx.decls :=
    List.mem_of_find?_eq_some hfindDecls
  rcases H.onlyLams decl hdeclMem with
    ⟨index, fv', name, type, bi, kind, hdecl⟩
  subst decl
  have hfv : fv' = fv := by
    have hpred := List.find?_some hfindDecls
    have hfv' : fv = fv' := by simpa [LocalDecl.fvarId] using hpred
    exact hfv'.symm
  subst fv'
  refine ⟨index, name, type, bi, kind, ?_⟩
  rw [← H.lctx_eq]
  exact hfind

theorem RecursorContextWF.findCDecl
    (R : RecursorContextWF c recLparams)
    (hmem : fv ∈ R.mlctx.vlctx.fvars) :
    ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
  rcases (R.mlctx_wf.tr.find?_eq_some (fv := fv)).2 hmem with
    ⟨decl, hfind⟩
  have hfindDecls : R.mlctx.decls.find? (fv == ·.fvarId) = some decl := by
    rw [← R.mlctx_wf.find?_eq]
    exact hfind
  have hdeclMem : decl ∈ R.mlctx.decls :=
    List.mem_of_find?_eq_some hfindDecls
  rcases R.onlyLams decl hdeclMem with
    ⟨index, fv', name, type, bi, kind, hdecl⟩
  subst decl
  have hfv : fv' = fv := by
    have hpred := List.find?_some hfindDecls
    have hfv' : fv = fv' := by simpa [LocalDecl.fvarId] using hpred
    exact hfv'.symm
  subst fv'
  refine ⟨index, name, type, bi, kind, ?_⟩
  rw [← R.lctx_eq]
  exact hfind

/-- Operational local-context invariant used by structurally exploded
recursor traversals.  It records exactly what those proofs need in order to
retain generated binders, without claiming semantic typing for their domains. -/
structure BindingContextWF (c : AddInductive.Context) where
  wf : c.lctx.WF
  onlyLams : ∀ d ∈ c.lctx.toList, ∃ index fv name type bi kind,
    d = .cdecl index fv name type bi kind
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  fresh : ∀ fv ∈ c.lctx.fvars, c.ngen.Reserves fv
  findCDecl : ∀ fv ∈ c.lctx.fvars, ∃ index name type bi kind,
    c.lctx.find? fv = some (.cdecl index fv name type bi kind)

theorem ContextWF.toBindingContextWF (H : ContextWF c) :
    BindingContextWF c where
  wf := H.lctx_eq ▸ H.mlctx_wf.tr.1
  onlyLams := by
    intro d hd
    apply H.onlyLams d
    rw [← H.mlctx_wf.toList_eq, H.lctx_eq]
    exact hd
  ngen_prefix := H.ngen_prefix
  fresh := by
    intro fv hfv
    apply H.indFresh fv
    rw [← H.mlctx_wf.tr.fvars_eq, H.lctx_eq]
    exact hfv
  findCDecl fv hfv := H.findCDecl <| by
    rw [← H.mlctx_wf.tr.fvars_eq, H.lctx_eq]
    exact hfv

/-- A recursor-universe semantic context projects to the same concrete
binder/freshness invariant used by the structural traversals. -/
theorem RecursorContextWF.toBindingContextWF
    (R : RecursorContextWF c recLparams) : BindingContextWF c where
  wf := R.lctx_eq ▸ R.mlctx_wf.tr.1
  onlyLams := by
    intro d hd
    apply R.onlyLams d
    rw [← R.mlctx_wf.toList_eq, R.lctx_eq]
    exact hd
  ngen_prefix := R.ngen_prefix
  fresh := by
    intro fv hfv
    apply R.indFresh fv
    rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq]
    exact hfv
  findCDecl fv hfv := R.findCDecl <| by
    rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq]
    exact hfv

theorem BindingContextWF.current_not_mem (H : BindingContextWF c) :
    ⟨c.ngen.curr⟩ ∉ c.lctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.fresh _ hmem)

def BindingContextWF.withLocalDecl (H : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  wf := H.wf.mkLocalDecl <| by
    rw [H.wf.find?_eq_find?_toList]
    by_contra hne
    rcases Option.ne_none_iff_exists.mp hne with ⟨d, hfind⟩
    apply H.current_not_mem
    rw [LocalContext.fvars]
    apply List.mem_map.2
    have hfind' := hfind.symm
    refine ⟨d, List.mem_of_find?_eq_some hfind', ?_⟩
    have hp := List.find?_some hfind'
    have heq : ⟨c.ngen.curr⟩ = d.fvarId := by simpa using hp
    exact heq.symm
  onlyLams := by
    intro d hd
    simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨_, _, _, _, _, _, rfl⟩
    · exact H.onlyLams d hd
  ngen_prefix := H.ngen_prefix
  fresh := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.fresh _ hmem).mono NameGenerator.LE.next
  findCDecl := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨c.lctx.decls.size, name, ty, bi, .default, ?_⟩
      simp [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
    · rcases H.findCDecl fv hmem with
        ⟨index, oldName, oldType, oldBi, kind, hfind⟩
      refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
      simp only [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
      rw [if_neg]
      · exact hfind
      · intro heq
        have hsame : ⟨c.ngen.curr⟩ = fv := LawfulBEq.eq_of_beq heq
        have : fv = ⟨c.ngen.curr⟩ := hsame.symm
        subst fv
        exact H.current_not_mem hmem

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

theorem withLocalDecl.recursorWF {k : Expr → AddInductive.M α}
    (R : RecursorContextWF c recLparams)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  have _R' := R.withLocalDecl (name := name) (bi := bi) htr hty
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
  have hresult' := hresult.defeqDFC henv.ordered (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hresult'⟩

/-- Context- and result-conversion form of `typeShape`.  Repeated executable
`whnf` calls need only remain definitionally equal to the unconsumed source
telescope; they need not choose that telescope's exact syntax. -/
theorem TrExpr.typeShapeOfDefEqCtxResult
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result translatedResult exprType : VExpr}
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
    (hresultEq : env.IsDefEqU Us.length Δ.toCtx result translatedResult)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) translatedResult) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, htranslated⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hsourceType := htranslated.hasType.1.defeqU_l henv hctx.toCtx
    hresultEq.symm
  have hsourceEqU := hresultEq.trans henv hctx.toCtx ⟨_, htranslated⟩
  have hsourceEq := hsourceEqU.of_l henv hctx.toCtx hsourceType
  have hsourceEq' := hsourceEq.defeqDFC henv.ordered
    (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hsourceEq'⟩

/-- Close a sort-level definitional equality over a dependent forall
telescope.  This is the abstraction step needed when the executable checker
performs a fresh `whnf` after opening each binder. -/
theorem VExpr.wrapForalls_defeq
    {env : VEnv} {U : Nat} {domains Γ : List VExpr}
    {body body' : VExpr} {bodyLevel : VLevel}
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (hbody : env.IsDefEq U (domains.reverse ++ Γ)
      body body' (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U Γ
      (VExpr.wrapForalls domains body)
      (VExpr.wrapForalls domains body') (.sort resultLevel) := by
  induction domains generalizing Γ with
  | nil =>
    exact ⟨bodyLevel, by simpa [VExpr.wrapForalls] using hbody⟩
  | cons dom domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (dom :: Γ))
        (env.IsType U) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hdomCtx : OnCtx (dom :: Γ) (env.IsType U) :=
      OnCtx.append_right hctx'
    rcases hdomCtx.2 with ⟨domLevel, hdom⟩
    rcases ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using hbody) with
      ⟨resultLevel, hrest⟩
    exact ⟨.imax domLevel resultLevel, .forallEDF hdom hrest⟩

/-- A checked inductive header is definitionally equal to an exact telescope
of its recorded parameter and index arity ending in its recorded sort. -/
theorem typeShape_forallAritySort
    {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    {params : List VExpr}
    (huvars : target.uvars = decl.uvars)
    (henv : env.WF) (htarget : target.toVConstant.WF env)
    (H : decl.TypeShape env params target) :
    ∃ functionType typeLevel,
      env.IsDefEq decl.uvars [] target.type functionType (.sort typeLevel) ∧
      VExpr.ForallAritySort (decl.nparams + target.numIndices)
        functionType := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, hindicesTake, _hparams, hresult⟩
  rcases VExpr.takeForalls_rebuild hparamsTake with
    ⟨hnormalizedEq, hparamsLength⟩
  rcases VExpr.takeForalls_rebuild hindicesTake with
    ⟨hafterParamsEq, hindicesLength⟩
  have hnormalizedRebuild : normalized =
      VExpr.wrapForalls (ownParams ++ indices) result := by
    rw [hnormalizedEq, hafterParamsEq, VExpr.wrapForalls_append]
  have htarget' : env.IsType decl.uvars [] target.type := by
    change env.IsType target.uvars [] target.type at htarget
    rwa [huvars] at htarget
  have hnormalizedType : env.IsType decl.uvars [] normalized :=
    htarget'.defeqU_l henv (by trivial) ⟨exprType, hnormalized⟩
  rw [hnormalizedRebuild] at hnormalizedType hnormalized
  have htelescope := VEnv.IsType.wrapForalls_inv henv (by trivial)
    hnormalizedType
  have hctx : OnCtx ((ownParams ++ indices).reverse)
      (env.IsType decl.uvars) := by
    simpa using htelescope.1
  have hresult' : env.IsDefEq decl.uvars
      ((ownParams ++ indices).reverse) result (.sort target.resultLevel)
      (.sort (.succ target.resultLevel)) := by
    simpa [List.reverse_append] using hresult
  have hresult'' : env.IsDefEq decl.uvars
      ((ownParams ++ indices).reverse ++ []) result
      (.sort target.resultLevel) (.sort (.succ target.resultLevel)) := by
    simpa using hresult'
  rcases VExpr.wrapForalls_defeq
      (domains := ownParams ++ indices) (Γ := [])
      (bodyLevel := .succ target.resultLevel) (by simpa using hctx)
      hresult'' with
    ⟨typeLevel, hwrapped⟩
  have htypeEq := hnormalized.hasType.2.uniqU henv (by trivial)
    hwrapped.hasType.1
  have hnormalized' := VEnv.IsDefEqU.defeqDF henv (by trivial)
    htypeEq hnormalized
  refine ⟨VExpr.wrapForalls (ownParams ++ indices)
      (.sort target.resultLevel), typeLevel,
    hnormalized'.trans hwrapped, ?_⟩
  have hshape := VExpr.ForallAritySort.wrapForalls
    (ownParams ++ indices) target.resultLevel
  simpa [hparamsLength, hindicesLength] using hshape


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

/-- Recursor-universe analogue of `ContextWF.instantiateFresh`. -/
theorem RecursorContextWF.instantiateFresh
    (R : RecursorContextWF c recLparams)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (hbody : TrExprS R.venv recLparams
      ((none, .vlam ty') :: R.mlctx.vlctx) body body') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty')
      (name := name) (bi := bi) htr hty
    TrExprS R'.venv recLparams R'.mlctx.vlctx
      (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body' := by
  dsimp only
  rw [Expr.instantiate1_eq]
  exact hbody.inst_fvar R.checking.tr.wf.ordered
    (R.withLocalDecl htr hty).mlctx_wf.tr.wf

/-- Instantiate a recursor-universe source binder with an existing cached
argument whose semantic type is definitionally equal to its domain. -/
theorem RecursorContextWF.instantiateDefEq
    (R : RecursorContextWF c recLparams)
    (hbody : TrExprS R.venv recLparams
      ((none, .vlam dom') :: R.mlctx.vlctx) body body')
    (harg : TrExprS R.venv recLparams R.mlctx.vlctx arg arg')
    (hargType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      arg' argType')
    (heq : R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
      dom' argType') :
    TrExprS R.venv recLparams R.mlctx.vlctx
      (body.instantiate1 arg) (body'.inst arg') := by
  have hargType' := hargType.defeqU_r R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx heq.symm
  rw [Expr.instantiate1_eq]
  exact hbody.inst R.checking.tr.wf.ordered hargType' harg

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

theorem MLCtxOnlyLams.mkForall_consumeTypeAnnotations_eq_self
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length)
    (hbody : body.consumeTypeAnnotations = body) :
    (m.mkForall n hn body).consumeTypeAnnotations = m.mkForall n hn body := by
  induction n generalizing m body with
  | zero => exact hbody
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      apply ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
      apply Expr.consumeTypeAnnotations_eq_self <;> rfl
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Removing binder annotations only selects subexpressions of the original
domain, so it cannot introduce a new free-variable dependency. -/
theorem Expr.consumeTypeAnnotations_fvarsIn
    (H : FVarsIn P e) : FVarsIn P e.consumeTypeAnnotations := by
  rw (occs := .pos [1]) [Expr.consumeTypeAnnotations_eq]
  split
  · rename_i hannotation
    cases e <;> simp_all [Expr.isOptParam, Expr.isAutoParam,
      Expr.isAppOfArity, Expr.appFn!, Expr.appArg!, FVarsIn,
      -Expr.consumeTypeAnnotations_eq]
    case app fn arg =>
      cases fn <;> simp_all [Expr.isAppOfArity, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn' arg' =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.1.2
  · split
    · cases e <;> simp_all [Expr.isOutParam, Expr.isSemiOutParam,
        Expr.isAppOfArity, Expr.appArg!, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn arg =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.2
    · exact H
termination_by e

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

/-- Move the source/body conversion produced by `body` into the
annotation-consumed context installed by the executable checker. -/
theorem ContextWF.ConsumedDomain.bodyDefEqConsumed
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom : Expr} {source' consumed' sourceBody body'' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbodyEq : Hc.venv.IsDefEqU c.lparams.length
      (source' :: Hc.mlctx.vlctx.toCtx) sourceBody body'') :
    Hc.venv.IsDefEqU c.lparams.length
      (consumed' :: Hc.mlctx.vlctx.toCtx) sourceBody body'' := by
  rcases H.source_defeq with ⟨_, hsource⟩
  have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (source' :: Hc.mlctx.vlctx.toCtx)
      (consumed' :: Hc.mlctx.vlctx.toCtx) :=
    .succ (.refl Hc.mlctx_wf.tr.wf.toCtx) hsource
  exact hbodyEq.defeqDFC Hc.checking.tr.wf.ordered hctx

/-- Annotation-erased domain certificate interpreted under the universe list
of a generated recursor context. -/
structure RecursorContextWF.ConsumedDomain
    (R : RecursorContextWF c recLparams)
    (dom : Expr) (source' consumed' : VExpr) : Prop where
  source : TrExprS R.venv recLparams R.mlctx.vlctx dom source'
  consumed : TrExprS R.venv recLparams R.mlctx.vlctx
    dom.consumeTypeAnnotations consumed'
  isType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, R.venv.IsDefEq recLparams.length R.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

theorem RecursorContextWF.ConsumedDomain.unchanged
    (R : RecursorContextWF c recLparams)
    (heq : dom.consumeTypeAnnotations = dom)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx dom dom')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx dom') :
    R.ConsumedDomain dom dom' dom' := by
  rcases hty with ⟨u, hty⟩
  exact {
    source := htr
    consumed := heq.symm ▸ htr
    isType := ⟨u, hty⟩
    source_defeq := ⟨u, hty⟩ }

theorem RecursorContextWF.ConsumedDomain.body
    (R : RecursorContextWF c recLparams)
    {dom body : Expr} {source' consumed' body' : VExpr}
    (H : R.ConsumedDomain dom source' consumed')
    (hbody : TrExprS R.venv recLparams
      ((none, .vlam source') :: R.mlctx.vlctx) body body') :
    ∃ body'', TrExprS R.venv recLparams
        ((none, .vlam consumed') :: R.mlctx.vlctx) body body'' ∧
      R.venv.IsDefEqU recLparams.length
        (source' :: R.mlctx.vlctx.toCtx) body' body'' := by
  rcases H.source_defeq with ⟨_, hdom⟩
  have hctx : VLCtx.IsDefEq R.venv recLparams.length
      ((none, .vlam source') :: R.mlctx.vlctx)
      ((none, .vlam consumed') :: R.mlctx.vlctx) :=
    VLCtx.IsDefEq.cons
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun (.vlam hdom)
  rcases hbody.defeqDFC R.checking.tr.wf hctx with ⟨body'', hbody''⟩
  exact ⟨body'', hbody'', hbody.uniq R.checking.tr.wf hctx hbody''⟩

theorem RecursorContextWF.ConsumedDomain.bodyDefEqConsumed
    (R : RecursorContextWF c recLparams)
    {dom : Expr} {source' consumed' sourceBody body'' : VExpr}
    (H : R.ConsumedDomain dom source' consumed')
    (hbodyEq : R.venv.IsDefEqU recLparams.length
      (source' :: R.mlctx.vlctx.toCtx) sourceBody body'') :
    R.venv.IsDefEqU recLparams.length
      (consumed' :: R.mlctx.vlctx.toCtx) sourceBody body'' := by
  rcases H.source_defeq with ⟨_, hsource⟩
  have hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      (source' :: R.mlctx.vlctx.toCtx)
      (consumed' :: R.mlctx.vlctx.toCtx) :=
    .succ (.refl R.mlctx_wf.tr.wf.toCtx) hsource
  exact hbodyEq.defeqDFC R.checking.tr.wf.ordered hctx

/-- Semantic compatibility required of Lean's opaque annotation erasure.
It is kept as one named boundary condition until the translations of
`OptParam`, `AutoParam`, and output-parameter wrappers are verified directly. -/
def ConsumeTypeAnnotationsCompat : Prop :=
  ∀ (c : AddInductive.Context) (Hc : ContextWF c)
    {dom : Expr} {source' : VExpr},
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source' →
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx source' →
    ∃ consumed', Hc.ConsumedDomain dom source' consumed'

/-- Universe-parametric annotation-erasure boundary used after generated
recursor frames have made `ContextWF` unavailable. -/
def RecursorConsumeTypeAnnotationsCompat : Prop :=
  ∀ (c : AddInductive.Context) (recLparams : List Name)
    (R : RecursorContextWF c recLparams)
    {dom : Expr} {source' : VExpr},
    TrExprS R.venv recLparams R.mlctx.vlctx dom source' →
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx source' →
    ∃ consumed', R.ConsumedDomain dom source' consumed'

/-- Executable locality boundary for weak-head normalization.  `whnf` only
uses type inference in `inferOnly` mode, so changing the reader's admitted
universe-parameter names does not affect reduction.  Keeping this statement
separate makes the remaining implementation proof (by inspection of the
mutually recursive reduction functions) explicit, instead of baking it into
the recursor invariant. -/
def WhnfLParamsCompat : Prop :=
  ∀ (env : Environment) (safety : DefinitionSafety)
    (lctx : LocalContext) (lparams lparams' : List Name)
    (fuel : FuelConfig) (e : Expr),
    TypeChecker.M.run env safety lctx lparams fuel
        (TypeChecker.whnf e) =
      TypeChecker.M.run env safety lctx lparams' fuel
        (TypeChecker.whnf e)

set_option linter.unusedSimpArgs false in
/-- Inferring the type of a free variable only consults its local declaration.
In particular it is independent of the universe-parameter names installed in
the typechecker reader.  Unlike `WhnfLParamsCompat`, this narrow fact follows
directly by reducing the executable free-variable branch. -/
theorem inferTypeFVar_lparams_compat
    (env : Environment) (safety : DefinitionSafety)
    (lctx : LocalContext) (lparams lparams' : List Name)
    (fuel : FuelConfig) (fv : FVarId) :
    TypeChecker.M.run env safety lctx lparams fuel
        (TypeChecker.inferType (.fvar fv)) =
      TypeChecker.M.run env safety lctx lparams' fuel
        (TypeChecker.inferType (.fvar fv)) := by
  change ((((TypeChecker.Methods.withFuel fuel.recDepth).inferType
      (.fvar fv) true)
        { env, lctx, safety, lparams, fuel }).run' {}) =
    ((((TypeChecker.Methods.withFuel fuel.recDepth).inferType
      (.fvar fv) true)
        { env, lctx, safety, lparams := lparams', fuel }).run' {})
  cases hdepth : fuel.recDepth with
  | zero =>
      rfl
  | succ depth =>
      simp only [TypeChecker.Methods.withFuel]
      have hloose : (.fvar fv : Expr).hasLooseBVars = false := by
        simp [Expr.hasLooseBVars, Expr.looseBVarRange']
      unfold TypeChecker.Inner.inferType'
      simp only [hloose, Bool.false_eq_true, ↓reduceIte]
      simp [TypeChecker.Inner.inferFVar, ReaderT.bind, ReaderT.read,
        StateT.bind, StateT.get, StateT.modifyGet, _root_.modify, StateT.run',
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, getThe, modifyGetThe,
        instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
        ReaderT.instMonadLift, instMonadStateOfStateTOfMonad,
        MonadLiftT.monadLift, MonadLift.monadLift,
        liftM, monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        StateT.instMonadLift, StateT.lift]
      simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
        StateT.instMonad, StateT.bind, StateT.get, StateT.modifyGet,
        StateT.lift, Except.instMonad, Except.bind, Except.pure]
      simp only [Pure.pure, Functor.map, Applicative.toPure,
        Applicative.toFunctor, Monad.toApplicative, Except.instMonad,
        Except.pure, Except.map]
      simp [ReaderT.pure, ReaderT.bind, ReaderT.read, StateT.pure,
        StateT.bind, StateT.lift, StateT.map, StateT.modifyGet,
        readThe, MonadReaderOf.read, instMonadReaderOfOfMonadLift,
        instMonadReaderOfReaderTOfMonad, liftM, monadLift,
        MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, ReaderT.read]
      simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
        ReaderT.read, StateT.instMonad, StateT.bind, StateT.lift,
        StateT.map, StateT.modifyGet, Except.instMonad, Except.bind,
        Except.map]
      simp only [ReaderT.read, Pure.pure, Functor.map,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        StateT.instMonad, StateT.pure, Except.instMonad, Except.pure,
        Except.map, MonadReader.read, instMonadReaderOfMonadReaderOf,
        readThe, MonadReaderOf.read, instMonadReaderOfReaderTOfMonad]

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

/-- `whnf` preserves every admissible free-variable scope of its input, in
addition to preserving the abstract expression up to definitional equality.
The ordinary wrapper above projects this fact away; later mutual headers need
it to show normalization cannot introduce ambient or future cached
parameters. -/
theorem whnfInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc
    ((TypeChecker.Inner.whnf.WF he).run)

/-- Interpret typechecker verification under the recursor's universe
parameters while retaining the executable local context built by
`AddInductive`. -/
def RecursorContextWF.typeChecker
    (H : RecursorContextWF c recLparams) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC
    H.checking H.mlctx H.mlctx_wf c.fuel

@[simp] theorem RecursorContextWF.typeChecker_lctx
    (H : RecursorContextWF c recLparams) :
    H.typeChecker.lctx = c.lctx := by
  simp [RecursorContextWF.typeChecker,
    TypeChecker.VContext.mkCheckingValidMLC, H.lctx_eq]

/-- Run verified weak-head normalization in a universe-rebased recursor
context.  Production still executes with `c.lparams`; the locality boundary
rewrites that run to the `recLparams` under which the semantic local context
is well formed. -/
theorem whnfInRecursorContext.scopeWF
    (hwhnf : WhnfLParamsCompat)
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv recLparams Hc.mlctx.vlctx e₁ e' := by
  change (TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel
    (TypeChecker.whnf e)).WF _
  rw [hwhnf c.env c.safety c.lctx c.lparams recLparams c.fuel e]
  rw [← Hc.lctx_eq]
  have Hx : TypeChecker.M.WF Hc.typeChecker {}
      (TypeChecker.whnf e) (fun e₁ _ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv recLparams Hc.mlctx.vlctx e₁ e') :=
    (TypeChecker.Inner.whnf.WF he).run
  exact TypeChecker.M.WF.runCheckingValidMLC
    (lparams := recLparams) (fuel := c.fuel)
    Hc.kernelFresh Hx

/-- Verify production type inference for a retained free variable under the
recursor universe list.  The executable run still uses `c.lparams`; the
preceding computation lemma changes only that irrelevant reader field. -/
theorem inferTypeFVarInRecursorContext.WF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx (.fvar fv) e') :
    ((monadLift (TypeChecker.inferType (.fvar fv)) :
        AddInductive.M Expr) c).WF fun ty =>
      ∃ ty', TrTyping Hc.venv recLparams Hc.mlctx.vlctx
        (.fvar fv) ty e' ty' := by
  change (TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel
    (TypeChecker.inferType (.fvar fv))).WF _
  rw [inferTypeFVar_lparams_compat c.env c.safety c.lctx
    c.lparams recLparams c.fuel fv]
  rw [← Hc.lctx_eq]
  have Hx : TypeChecker.M.WF Hc.typeChecker {}
      (TypeChecker.inferType (.fvar fv)) (fun ty _ =>
        ∃ ty', TrTyping Hc.venv recLparams Hc.mlctx.vlctx
          (.fvar fv) ty e' ty') :=
    (TypeChecker.Inner.inferType.WF he).run
  exact TypeChecker.M.WF.runCheckingValidMLC
    (lparams := recLparams) (fuel := c.fuel)
    Hc.kernelFresh Hx

/-- Descend normalization of a closed source header from the full generated
recursor context to the empty semantic scope.  Earlier mutual-family frames
may occur in `R.mlctx`, but neither the source header nor its normal form owns
any of their free variables. -/
theorem RecursorContextWF.initialClosedHeaderDefEq
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (htarget : TrExprS R.venv recLparams [] source target)
    (hsource : TrExprS R.venv recLparams R.mlctx.vlctx
      source sourceTarget)
    (hnormalized : TrExpr R.venv recLparams R.mlctx.vlctx
      normalized sourceTarget)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalizedTarget,
      TrExprS R.venv recLparams [] normalized normalizedTarget ∧
      R.venv.IsDefEqU recLparams.length [] target normalizedTarget := by
  rcases hnormalized with
    ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  let W : VLCtx.FVLift [] R.mlctx.vlctx 0
      R.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil R.mlctx.noBV
  have hnormalizedClosed : Closed normalized 0 := by
    have hclosed := hnormalizedFull.closed
    simpa [R.mlctx.noBV] using hclosed
  have hnormalizedNoFVars :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) normalized := by
    simpa [VLCtx.fvars] using hfvars
  rcases hnormalizedFull.weakFV_inv R.checking.tr.wf W
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedNoFVars with
    ⟨normalizedTarget, hnormalizedTarget⟩
  have hsourceNoFVars : FVarsIn (fun _ => False) source :=
    htarget.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hsourceClosed : Closed source 0 := by
    have hclosed := hsource.closed
    simpa [R.mlctx.noBV] using hclosed
  have hsourceNoFVars' :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) source := by
    simpa [VLCtx.fvars] using hsourceNoFVars
  rcases hsource.weakFV_inv R.checking.tr.wf W
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf)
      hsourceClosed hsourceNoFVars' with
    ⟨sourceTarget', hsourceTarget'⟩
  have hnormalizedWeak := hnormalizedTarget.weakFV
    R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
  have hsourceWeak := hsourceTarget'.weakFV
    R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq R.checking.tr.wf
    (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hnormalizedWeak
  have hsourceUniq := hsource.uniq R.checking.tr.wf
    (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hsourceWeak
  have hfull : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx
      (normalizedTarget.liftN R.mlctx.vlctx.toCtx.length 0)
      (sourceTarget'.liftN R.mlctx.vlctx.toCtx.length 0) :=
    hnormalizedUniq.symm.trans R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.trans R.checking.tr.wf
        R.mlctx_wf.tr.wf.toCtx hsourceUniq)
  have hempty : R.venv.IsDefEqU recLparams.length []
      normalizedTarget sourceTarget' :=
    (VEnv.IsDefEqU.weakN_iff R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx W.toCtx).1 hfull
  have htargetEq : R.venv.IsDefEqU recLparams.length []
      target sourceTarget' :=
    htarget.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf (by trivial)) hsourceTarget'
  exact ⟨normalizedTarget, hnormalizedTarget,
    htargetEq.trans R.checking.tr.wf (by trivial) hempty.symm⟩

theorem ensureSortInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' ∧ ∃ u, e₁ = .sort u :=
  liftTypeChecker.WF Hc (TypeChecker.ensureSort.WF he)

theorem ensureSortInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF
      fun e₁ => Hc.typeChecker.FVarsBelow e e₁ ∧
        Hc.typeChecker.TrExpr e₁ e' ∧
        ∃ u, e₁ = .sort u := by
  change Hc.typeChecker.TrExprS e e' at he
  apply liftTypeChecker.WF (Q := fun e₁ =>
    Hc.typeChecker.FVarsBelow e e₁ ∧
      Hc.typeChecker.TrExpr e₁ e' ∧
      ∃ u, e₁ = .sort u) Hc
  simpa only [TypeChecker.ensureSort] using
    (TypeChecker.Inner.ensureSortCore.WF he).run.mono
      (fun _ _ _ h => And.intro h.2.2 (And.intro h.2.1 h.1))

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

/-- Verified boundary for the extra closed generated-recursor check. Unlike
`checkClosedType`, this runs with an empty local context and the recursor's
possibly extended universe-parameter list. -/
theorem AddInductive.declareRecursors.checkRecursorType.WF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (info : RecursorVal) :
    (AddInductive.declareRecursors.checkRecursorType info c).WF fun ty =>
      ∃ type', TrExprS venv info.levelParams [] info.type type' ∧
        venv.IsType info.levelParams.length [] type' := by
  unfold AddInductive.declareRecursors.checkRecursorType
  have hno : (c.env.checkNoMVarNoFVar info.name info.type).WF
      (fun _ => info.type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := info.name) h
  exact hno.bind fun _ hclosed => by
    have hfvars : info.type.FVarsIn fun fv => fv ∈
        (TypeChecker.VContext.mkCheckingValid Hvalid info.levelParams
          c.fuel).vlctx.fvars := by
      simpa [TypeChecker.VContext.mkCheckingValid,
        TypeChecker.VContext.mkChecking] using
          (hclosed.mono fun _ h => False.elim h)
    have Hcheck : TypeChecker.M.WF
        (TypeChecker.VContext.mkCheckingValid Hvalid info.levelParams c.fuel)
        {} (do
          let type ← TypeChecker.checkType info.type
          _ ← TypeChecker.ensureSort type info.type
          return type) fun _ _ =>
          ∃ type', TrExprS venv info.levelParams [] info.type type' ∧
            venv.IsType info.levelParams.length [] type' := by
      refine (TypeChecker.checkType.WF hfvars).bind
        fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
      refine (TypeChecker.ensureSort.WF hsort).bind
        fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => .pure ?_
      obtain ⟨u, rfl⟩ := hsortEq
      cases hsort' with
      | sort hu =>
        exact ⟨type', htype,
          ⟨_, hhasType.defeqU_r Hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
    exact TypeChecker.M.WF.runCheckingValid Hcheck

/-- Package the validated generated type as the abstract constant installed
by the recursor loop. -/
theorem AddInductive.declareRecursors.checkRecursorType.constWF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (info : RecursorVal)
    (hvisible : c.safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareRecursors.checkRecursorType info c).WF fun _ =>
      ∃ recursor : VConstVal,
        TrConstVal c.safety venv (.recInfo info) recursor ∧
        recursor.toVConstant.WF venv := by
  exact (AddInductive.declareRecursors.checkRecursorType.WF Hvalid info).mono
    fun _ ⟨type, Htyping, HwfType⟩ => by
      let recursor : VConstVal := {
        uvars := info.levelParams.length
        type := type
        name := info.name }
      refine ⟨recursor, ?_, HwfType⟩
      constructor
      · exact ⟨by simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial] using hvisible, rfl, Htyping⟩
      · rfl

/-- Definitionally equal translation contexts backed by lambda-only
`MLCtx`s retain the same declaration spine and free-variable identities.
Syntax-directed expressions therefore see them as a unique-context pair
even when annotation erasure changed corresponding declaration types. -/
theorem VLCtx.IsDefEq.toIsUniqueCtx_ofOnlyLams
    {m : TypeChecker.MLCtx}
    (H : VLCtx.IsDefEq env U Δ m.vlctx) (Hm : MLCtxOnlyLams m) :
    TrExprS.IsUniqueCtx Δ m.vlctx := by
  induction m generalizing Δ with
  | nil =>
    cases H
    exact .base
  | vlam fv name type type' bi tail ih =>
    cases H with
    | cons Htail _ hdecl =>
      cases hdecl with
      | vlam =>
        exact .cons (ih Htail Hm.tail_vlam) .vlam
  | vlet fv name type value type' value' tail ih =>
    exact Hm.vlet_false.elim

/-- Pointwise syntax-directed translation uniqueness, lifted to an aligned
list of source expressions. -/
theorem TrExprS.forall₂_unique
    (Hctx : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (Hunique : ∀ source ∈ sources, TrExprS.IsUnique source)
    (H₁ : List.Forall₂ (TrExprS env Us Δ₁) sources targets₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ₂) sources targets₂) :
    targets₁ = targets₂ := by
  induction H₁ generalizing targets₂ with
  | nil => cases H₂; rfl
  | @cons source target sources targets Hhead Htail ih =>
    cases H₂ with
    | cons Hhead₂ Htail₂ =>
      congr
      · exact TrExprS.unique' Hctx (Hunique source (by simp))
          Hhead Hhead₂
      · exact ih (fun later hlater => Hunique later (by simp [hlater]))
          Htail₂


end VerifyInductive
end Lean4Lean
