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

/-! ### The inductive checker's narrow checker context

`AddInductive.Context.checkLCtx` is the local context seen by embedded
typechecker runs.  It is always a sub-context of the main context
(`LocalContext.SubContextOf`), described semantically by a `CheckBase`: every
lifted run is verified in the checker context, and its facts are transferred
to the main context by weakening. -/

/-- Every declaration of `l` occurs in `l'` with the same content, up to its
position index. -/
def _root_.Lean.LocalContext.SubContextOf (l l' : LocalContext) : Prop :=
  ∀ fv d, l.find? fv = some d →
    ∃ d', l'.find? fv = some d' ∧ d'.setIndex 0 = d.setIndex 0

theorem _root_.Lean.LocalContext.find?_empty' (fv : FVarId) :
    ({} : LocalContext).find? fv = none := by
  show PersistentHashMap.find? PersistentHashMap.empty fv = none
  rw [PersistentHashMap.WF.empty.find?_eq, PersistentHashMap.toList'_empty]
  rfl

theorem _root_.Lean.LocalContext.SubContextOf.empty {l' : LocalContext} :
    ({} : LocalContext).SubContextOf l' := by
  intro fv d h
  rw [LocalContext.find?_empty'] at h
  cases h

theorem _root_.Lean.LocalContext.find?_mkLocalDecl
    {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (hwf : l.fvarIdToDecl.WF) :
    (l.mkLocalDecl fv name ty bi kind).find? fv' =
      if fv == fv' then some (.cdecl l.decls.size fv name ty bi kind)
      else l.find? fv' := by
  simp only [LocalContext.mkLocalDecl, LocalContext.find?]
  exact hwf.find?_insert

/-- Extending only the larger context by a fresh declaration keeps a
sub-context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkLocalDecl_right
    {l l' : LocalContext} {fv : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (h : l.SubContextOf l')
    (hwf : l'.fvarIdToDecl.WF) (hfresh : l'.find? fv = none) :
    l.SubContextOf (l'.mkLocalDecl fv name ty bi kind) := by
  intro fv' d hd
  rcases h fv' d hd with ⟨d', hd', heq⟩
  refine ⟨d', ?_, heq⟩
  rw [LocalContext.find?_mkLocalDecl hwf]
  have hne : (fv == fv') = false := by
    cases hb : fv == fv'
    · rfl
    · have : fv = fv' := LawfulBEq.eq_of_beq hb
      subst this
      rw [hfresh] at hd'
      cases hd'
  rw [hne]
  exact hd'

/-- Opening the same fresh declaration in both contexts keeps a
sub-context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkLocalDecl_both
    {l l' : LocalContext} {fv : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (h : l.SubContextOf l')
    (hwf : l.fvarIdToDecl.WF) (hwf' : l'.fvarIdToDecl.WF) :
    (l.mkLocalDecl fv name ty bi kind).SubContextOf
      (l'.mkLocalDecl fv name ty bi kind) := by
  intro fv' d hd
  rw [LocalContext.find?_mkLocalDecl hwf] at hd
  rw [LocalContext.find?_mkLocalDecl hwf']
  cases hb : fv == fv' with
  | true =>
    rw [hb] at hd
    cases hd
    exact ⟨_, rfl, rfl⟩
  | false =>
    rw [hb] at hd
    rw [if_neg (by simp)]
    exact h fv' d hd

/-- Closing over declarations of a sub-context gives the same result in the
larger context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkForall_eq {l l' : LocalContext}
    (H : l.SubContextOf l') {fvs : List FVarId}
    (hmem : ∀ fv ∈ fvs, ∃ d, l.find? fv = some d) (body : Expr) :
    l'.mkForall (fvs.map Expr.fvar).toArray body =
      l.mkForall (fvs.map Expr.fvar).toArray body := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  apply LocalContext.mkBindingListN_congr_setIndex
  intro fv hfv
  obtain ⟨d, hd⟩ := hmem fv hfv
  obtain ⟨d', hd', heq⟩ := H fv d hd
  simp [hd, hd', heq]

theorem _root_.Lean.LocalContext.SubContextOf.refl (l : LocalContext) :
    l.SubContextOf l := fun _ d h => ⟨d, h, rfl⟩

/-- A declaration found under `fv` in a well-formed context is stored under
its own identifier. -/
theorem _root_.Lean.LocalContext.WF.find?_fvarId {l : LocalContext}
    (hwf : l.WF) (h : l.find? fv = some d) : d.fvarId = fv := by
  rw [hwf.find?_eq_find?_toList] at h
  have hp := _root_.List.find?_some h
  simp only [beq_iff_eq] at hp
  exact hp.symm

/-! ### The semantic checker context

The checker context `checkLCtx` of `AddInductive.Context` is described by its
own `MLCtx` (`ContextWF.chk`), well formed by itself, whose semantic context
`ChkEmbeds` into the main one: it weakens (`VLCtx.FVLift'`) into a context
definitionally equal (`VLCtx.IsDefEq`) to the main semantic context.  Every
lifted checker run is verified in the checker context; facts about the main
context follow by weakening, which is valid. -/

/-- The semantic checker context `Δc` embeds into the main semantic context
`Δ`: it weakens into a context definitionally equal to `Δ`. -/
def ChkEmbeds (env : VEnv) (U : Nat) (Δc Δ : VLCtx) : Prop :=
  ∃ Δ' n, VLCtx.FVLift' Δc Δ' 0 n 0 ∧ VLCtx.IsDefEq env U Δ' Δ

theorem _root_.Lean4Lean.VLCtx.IsDefEq.isFVarUpSet {env : VEnv} {U : Nat} {P : FVarId → Prop} :
    ∀ {Δ₁ Δ₂ : VLCtx}, VLCtx.IsDefEq env U Δ₁ Δ₂ →
      (IsFVarUpSet P Δ₁ ↔ IsFVarUpSet P Δ₂)
  | _, _, .nil => .rfl
  | (none, _) :: _, (none, _) :: _, .cons H _ _ => H.isFVarUpSet
  | (some (_, _), _) :: _, (some (_, _), _) :: _, .cons H _ _ =>
    and_congr H.isFVarUpSet .rfl

theorem _root_.Lean4Lean.VLCtx.FVLift'.isFVarUpSet {P : FVarId → Prop} {Δ Δ' : VLCtx}
    {dk k : Nat} {n : Lift} (W : VLCtx.FVLift' Δ Δ' dk n k) (H : IsFVarUpSet P Δ') :
    IsFVarUpSet P Δ := by
  induction W with
  | refl => exact H
  | skip_fvar fv d _ ih => obtain ⟨fv, deps⟩ := fv; exact ih H.1
  | cons_fvar fv d _ _ ih => obtain ⟨fv, deps⟩ := fv; exact ⟨ih H.1, H.2⟩
  | cons_bvar d _ ih => exact ih H

namespace ChkEmbeds

variable {env : VEnv} {U : Nat} {Δc Δ : VLCtx}

theorem fvars_subset (H : ChkEmbeds env U Δc Δ) : Δc.fvars ⊆ Δ.fvars := by
  obtain ⟨Δ', n, W, hD⟩ := H
  rw [← hD.fvars]
  exact W.fvars_sublist.subset

theorem isFVarUpSet (H : ChkEmbeds env U Δc Δ) {P : FVarId → Prop}
    (hP : IsFVarUpSet P Δ) : IsFVarUpSet P Δc := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact W.isFVarUpSet (hD.isFVarUpSet.2 hP)

theorem refl (henv : VEnv.Ordered env) (hΔ : VLCtx.WF env U Δ) : ChkEmbeds env U Δ Δ :=
  ⟨Δ, .refl, .refl, .refl henv hΔ⟩

theorem from_nil (henv : VEnv.Ordered env) (hΔ : VLCtx.WF env U Δ) (hb : Δ.NoBV) :
    ChkEmbeds env U [] Δ :=
  ⟨Δ, _, .from_nil hb, .refl henv hΔ⟩

theorem mono {env' : VEnv} (hle : env ≤ env') (H : ChkEmbeds env U Δc Δ) :
    ChkEmbeds env' U Δc Δ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact ⟨Δ', n, W, hD.mono hle⟩

/-- Opening a binder only in the main context keeps the embedding. -/
theorem skip (henv : VEnv.Ordered env) (H : ChkEmbeds env U Δc Δ)
    (hfresh : fv ∉ Δ.fvars) (hdeps : deps ⊆ Δ.fvars)
    (hA : env.IsType U Δ.toCtx A) :
    ChkEmbeds env U Δc ((some (fv, deps), .vlam A) :: Δ) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hA' : env.IsType U Δ'.toCtx A := hA.defeqDFC henv (hD.defeqCtx.symm henv)
  obtain ⟨u, hu⟩ := hA'
  refine ⟨(some (fv, deps), .vlam A) :: Δ', _, .skip_fvar _ _ W, .cons hD ?_ (.vlam hu)⟩
  rintro _ _ ⟨⟩
  rw [hD.fvars]
  exact ⟨hfresh, hdeps⟩

/-- Opening the same binder in both contexts keeps the embedding. -/
theorem cons (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hfresh : fv ∉ Δ.fvars)
    (h₀ : TrExprS env Us Δc ty A₀) (h : TrExprS env Us Δ ty A)
    (hA : env.IsType Us.length Δ.toCtx A) :
    ChkEmbeds env Us.length ((some (fv, ty.fvarsList), .vlam A₀) :: Δc)
      ((some (fv, ty.fvarsList), .vlam A) :: Δ) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hw : TrExprS env Us Δ' ty (A₀.lift' (n.consN 0)) := h₀.weakFV' henv.ordered W hΔ'
  have hDsymm := hD.symm henv.ordered
  have hu : env.IsDefEqU Us.length Δ.toCtx A (A₀.lift' (n.consN 0)) :=
    h.uniq henv hDsymm hw
  have hA' : env.IsType Us.length Δ'.toCtx A := hA.defeqDFC henv.ordered (hD.defeqCtx.symm henv.ordered)
  have hu' : env.IsDefEqU Us.length Δ'.toCtx A (A₀.lift' (n.consN 0)) :=
    hu.defeqDFC henv.ordered (hD.defeqCtx.symm henv.ordered)
  obtain ⟨v, hAv⟩ := hA'
  have hv := hu'.symm.of_r henv hΔ'.toCtx hAv
  refine ⟨(some (fv, ty.fvarsList), .vlam (A₀.lift' n)) :: Δ', _,
    .cons_fvar _ _ h₀.fvarsList W, .cons hD ?_ (.vlam (by simpa using hv))⟩
  rintro _ _ ⟨⟩
  rw [hD.fvars]
  exact ⟨hfresh, h.fvarsList⟩

/-- A narrow translation weakens to a main translation of the same expression. -/
theorem trExprS (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (h : TrExprS env Us Δc e e₀) : ∃ e₁, TrExprS env Us Δ e e₁ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact (h.weakFV' henv.ordered W hD.wf).defeqDFC henv hD

/-- Transfer a narrow output relation to the main context, along given narrow
and main translations of the input. -/
theorem trExpr (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (h : TrExpr env Us Δc e₁ e₀) : TrExpr env Us Δ e₁ e' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have h' := h.weakFV' henv W hΔ'
  have hn' := hn.weakFV' henv.ordered W hΔ'
  obtain ⟨x, hx, hxe⟩ := h'
  have hx₂ := hx.defeqDFC' henv hD
  obtain ⟨y, hy, hyx⟩ := hx₂
  have hu := hn'.uniq henv hD he
  have hxe' := hxe.defeqDFC henv.ordered hD.defeqCtx
  have hu' := hu.defeqDFC henv.ordered hD.defeqCtx
  have hΔ := (hD.symm henv.ordered).wf
  exact ⟨y, hy, hyx.trans henv hΔ.toCtx (hxe'.trans henv hΔ.toCtx hu')⟩

/-- Transfer a narrow definitional equality to the main context, along given
narrow and main translations of both sides. -/
theorem isDefEqU (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn₁ : TrExprS env Us Δc e₁ a₁) (hn₂ : TrExprS env Us Δc e₂ a₂)
    (he₁ : TrExprS env Us Δ e₁ b₁) (he₂ : TrExprS env Us Δ e₂ b₂)
    (h : env.IsDefEqU Us.length Δc.toCtx a₁ a₂) :
    env.IsDefEqU Us.length Δ.toCtx b₁ b₂ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hΔ := (hD.symm henv.ordered).wf
  have h' := (h.weak' henv.ordered W.toCtx).defeqDFC henv.ordered hD.defeqCtx
  have hu₁ := ((hn₁.weakFV' henv.ordered W hΔ').uniq henv hD he₁).defeqDFC henv.ordered hD.defeqCtx
  have hu₂ := ((hn₂.weakFV' henv.ordered W hΔ').uniq henv hD he₂).defeqDFC henv.ordered hD.defeqCtx
  exact hu₁.symm.trans henv hΔ.toCtx (h'.trans henv hΔ.toCtx hu₂)

/-- Transfer a narrow typing judgement to the main context, along narrow and
main translations of the term and of its type. -/
theorem hasType (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (hTn : TrExprS env Us Δc T T₀) (hT : TrExprS env Us Δ T T')
    (h : env.HasType Us.length Δc.toCtx e₀ T₀) : env.HasType Us.length Δ.toCtx e' T' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hΔ := (hD.symm henv.ordered).wf
  have hh := (h.weak' henv.ordered W.toCtx).defeqDFC henv.ordered hD.defeqCtx
  have hu := ((hn.weakFV' henv.ordered W hΔ').uniq henv hD he).defeqDFC henv.ordered hD.defeqCtx
  have huT := ((hTn.weakFV' henv.ordered W hΔ').uniq henv hD hT).defeqDFC henv.ordered hD.defeqCtx
  exact (hh.defeqU_l henv hΔ.toCtx hu).defeqU_r henv hΔ.toCtx huT

/-- Transfer a narrow typing to the main context along a main translation of the
term. -/
theorem trTyping (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (he : TrExprS env Us Δ e e') (h : TrTyping env Us Δc e ty e₀ ty₀) :
    ∃ ty', TrTyping env Us Δ e ty e' ty' := by
  obtain ⟨hb, hn, hty, hhas⟩ := h
  obtain ⟨ty₁, hty₁⟩ := H.trExprS henv hty
  have hΔ : VLCtx.WF env Us.length Δ := by
    obtain ⟨Δ', n, W, hD⟩ := H; exact (hD.symm henv.ordered).wf
  refine ⟨ty₁, fun P hP hin => hb P (H.isFVarUpSet hP) hin, he, hty₁, ?_⟩
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hh := (hhas.weak' henv.ordered W.toCtx).defeqDFC henv.ordered hD.defeqCtx
  have hu := ((hn.weakFV' henv.ordered W hΔ').uniq henv hD he).defeqDFC henv.ordered hD.defeqCtx
  have huty := ((hty.weakFV' henv.ordered W hΔ').uniq henv hD hty₁).defeqDFC henv.ordered hD.defeqCtx
  exact (hh.defeqU_l henv hΔ.toCtx hu).defeqU_r henv hΔ.toCtx huty

/-- Transfer narrow typehood to the main context along a main translation. -/
theorem isType (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (h : env.IsType Us.length Δc.toCtx e₀) : env.IsType Us.length Δ.toCtx e' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ := (hD.symm henv.ordered).wf
  have hh := (h.weak' henv.ordered W.toCtx).defeqDFC henv.ordered hD.defeqCtx
  have hu := ((hn.weakFV' henv.ordered W hD.wf).uniq henv hD he).defeqDFC
    henv.ordered hD.defeqCtx
  exact hh.defeqU_l henv hΔ.toCtx hu

theorem fvarsBelow (H : ChkEmbeds env U Δc Δ) (h : FVarsBelow Δc e e₁) :
    FVarsBelow Δ e e₁ :=
  fun P hP hin => h P (H.isFVarUpSet hP) hin

end ChkEmbeds

theorem _root_.Lean4Lean.VLCtx.FVLift'.instL {ls : List VLevel} {Δ Δ' : VLCtx} {dk k : Nat}
    {n : Lift} (W : VLCtx.FVLift' Δ Δ' dk n k) :
    VLCtx.FVLift' (Δ.instL ls) (Δ'.instL ls) dk n k := by
  have hdepth : ∀ d : VLocalDecl, (d.instL ls).depth = d.depth := by
    intro d; cases d <;> rfl
  have hlift : ∀ (d : VLocalDecl) (l : Lift), (d.lift' l).instL ls = (d.instL ls).lift' l := by
    intro d l; cases d <;> simp [VLocalDecl.lift', VLocalDecl.instL, VExpr.instL_lift']
  induction W with
  | refl => exact .refl
  | skip_fvar fv d _ ih =>
    simpa [VLCtx.instL, hdepth] using VLCtx.FVLift'.skip_fvar fv (d.instL ls) ih
  | cons_fvar fv d hsub _ ih =>
    have := VLCtx.FVLift'.cons_fvar fv (d.instL ls) (by simpa using hsub) ih
    simpa [VLCtx.instL, hdepth, hlift] using this
  | cons_bvar d _ ih =>
    have := VLCtx.FVLift'.cons_bvar (d.instL ls) ih
    simpa [VLCtx.instL, hdepth, hlift] using this

theorem _root_.Lean4Lean.VLCtx.IsDefEq.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Δ₁ Δ₂ : VLCtx} (H : VLCtx.IsDefEq env U Δ₁ Δ₂) :
    VLCtx.IsDefEq env U' (Δ₁.instL ls) (Δ₂.instL ls) := by
  induction H with
  | nil => exact .nil
  | cons _ hfresh hdecl ih =>
    refine .cons ih (by simpa using hfresh) ?_
    cases hdecl with
    | vlam h => exact .vlam (VLCtx.instL_toCtx _ ▸ h.instL hls)
    | vlet h1 h2 =>
      exact .vlet (VLCtx.instL_toCtx _ ▸ h1.instL hls) (VLCtx.instL_toCtx _ ▸ h2.instL hls)

theorem ChkEmbeds.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Δc Δ : VLCtx} (H : ChkEmbeds env U Δc Δ) :
    ChkEmbeds env U' (Δc.instL ls) (Δ.instL ls) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact ⟨Δ'.instL ls, n, W.instL, hD.instL hls⟩

/-- A pure weakening followed by an embedding is an embedding. -/
theorem ChkEmbeds.of_fvLift {env : VEnv} {U : Nat} {Δ₁ Δ₂ Δ : VLCtx} {n : Lift}
    (W : VLCtx.FVLift' Δ₁ Δ₂ 0 n 0) (H : ChkEmbeds env U Δ₂ Δ) : ChkEmbeds env U Δ₁ Δ := by
  obtain ⟨Δ', n', W', hD⟩ := H
  exact ⟨Δ', _, W.comp W', hD⟩

/-- The free variables of an `MLCtx` in insertion order. -/
def _root_.Lean4Lean.TypeChecker.MLCtx.fvarList : TypeChecker.MLCtx → List FVarId
  | .nil => []
  | .vlam id _ _ _ _ c => c.fvarList ++ [id]
  | .vlet id _ _ _ _ _ c => c.fvarList ++ [id]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.fvarList_length (m : TypeChecker.MLCtx) :
    m.fvarList.length = m.length := by
  induction m <;> simp_all [TypeChecker.MLCtx.fvarList]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.decls_fvarId (m : TypeChecker.MLCtx) :
    m.decls.map (·.fvarId) = m.fvarList.reverse := by
  induction m <;> simp_all [TypeChecker.MLCtx.fvarList, TypeChecker.MLCtx.decls,
    LocalDecl.fvarId]

/-- The entry of a lambda-only `MLCtx` holding its `k`-th free variable, and
the context of the entries before it. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.dropN_of_fvarList_getElem? :
    ∀ (m : TypeChecker.MLCtx), MLCtxOnlyLams m → ∀ {k : Nat} {fv : FVarId},
      m.fvarList[k]? = some fv →
      ∃ (j : Nat) (hj : j + 1 ≤ m.length) (name : Name) (ty : Expr) (ty' : VExpr)
        (bi : BinderInfo),
        m.dropN j (Nat.le_of_succ_le hj) =
          .vlam fv name ty ty' bi (m.dropN (j + 1) hj) ∧
        m.fvarList.take k = (m.dropN (j + 1) hj).fvarList
  | .nil, _, _, _, h => by simp [TypeChecker.MLCtx.fvarList] at h
  | .vlet .., honly, _, _, _ => honly.vlet_false.elim
  | .vlam id name ty ty' bi c, honly, k, fv, h => by
    simp only [TypeChecker.MLCtx.fvarList] at h
    by_cases hk : k < c.fvarList.length
    · rw [List.getElem?_append_left hk] at h
      obtain ⟨j, hj, name', ty₁, ty₁', bi', heq, htake⟩ :=
        TypeChecker.MLCtx.dropN_of_fvarList_getElem? c honly.tail_vlam h
      refine ⟨j + 1, by simp; omega, name', ty₁, ty₁', bi', heq, ?_⟩
      simp only [TypeChecker.MLCtx.fvarList]
      rw [List.take_append_of_le_length (by omega)]
      exact htake
    · rw [List.getElem?_append_right (by omega)] at h
      have hk' : k = c.fvarList.length := by
        have := List.getElem?_eq_some_iff.mp h
        simp at this; omega
      subst hk'
      simp at h
      subst h
      refine ⟨0, by simp, name, ty, ty', bi, rfl, ?_⟩
      simp [TypeChecker.MLCtx.fvarList]

/-- Rebuilding a context from the declarations of a larger one, for the free
variables of a lambda-only `MLCtx` whose declarations it contains, gives back
that `MLCtx`'s local context. -/
theorem _root_.Lean.LocalContext.restrictTo_mlctx {env : VEnv} {Us : List Name}
    {l : LocalContext} {m : TypeChecker.MLCtx} (honly : MLCtxOnlyLams m) (hwf : m.WF env Us)
    (hsub : m.lctx.SubContextOf l) : l.restrictTo m.fvarList = m.lctx := by
  induction m with
  | nil => rfl
  | vlam id name ty ty' bi tail ih =>
    have htailMap : tail.lctx.fvarIdToDecl.WF := hwf.1.tr.1.map_wf
    have hfresh : tail.lctx.find? id = none := hwf.2.1
    have hsubTail : tail.lctx.SubContextOf l := by
      intro x d hd
      apply hsub x d
      change (tail.lctx.mkLocalDecl id name ty bi).find? x = some d
      rw [LocalContext.find?_mkLocalDecl htailMap]
      have hne : (id == x) = false := by
        cases h : id == x
        · rfl
        · have : id = x := LawfulBEq.eq_of_beq h
          subst this; rw [hfresh] at hd; cases hd
      rw [hne]; exact hd
    have ih' := ih honly.tail_vlam hwf.1 hsubTail
    have hself : (tail.lctx.mkLocalDecl id name ty bi).find? id =
        some (.cdecl tail.lctx.decls.size id name ty bi .default) := by
      rw [LocalContext.find?_mkLocalDecl htailMap]; simp
    obtain ⟨d', hd', heq⟩ := hsub id _ hself
    have hd'' : ∃ i, d' = .cdecl i id name ty bi .default := by
      cases d' with
      | cdecl i a b c d e =>
        simp only [LocalDecl.setIndex, LocalDecl.cdecl.injEq] at heq
        obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := heq
        exact ⟨i, rfl⟩
      | ldecl => simp [LocalDecl.setIndex] at heq
    obtain ⟨i, rfl⟩ := hd''
    unfold LocalContext.restrictTo at ih' ⊢
    rw [TypeChecker.MLCtx.fvarList, List.foldl_append, ih']
    simp only [List.foldl_cons, List.foldl_nil, hd']
    rfl
  | vlet => exact honly.vlet_false.elim

/-- The checker context and the main context of a semantic inductive-checker
context: a sub-context description of a candidate checker context `l`. -/
structure CheckBase (venv : VEnv) (Us : List Name) (main : TypeChecker.MLCtx)
    (lctx : LocalContext) (l : LocalContext) where
  m : TypeChecker.MLCtx
  wf : m.WF venv Us
  onlyLams : MLCtxOnlyLams m
  lctx_eq : m.lctx = l
  embed : ChkEmbeds venv Us.length m.vlctx main.vlctx
  sub : l.SubContextOf lctx

namespace CheckBase

variable {venv : VEnv} {Us : List Name} {main : TypeChecker.MLCtx} {lctx : LocalContext}

def cast {l l' : LocalContext} (B : CheckBase venv Us main lctx l) (h : l = l') :
    CheckBase venv Us main lctx l' where
  m := B.m
  wf := B.wf
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq.trans h
  embed := B.embed
  sub := h ▸ B.sub

@[simp] theorem cast_m {l l' : LocalContext} (B : CheckBase venv Us main lctx l)
    (h : l = l') : (B.cast h).m = B.m := rfl

def nil (henv : VEnv.Ordered venv) (hmain : main.WF venv Us) :
    CheckBase venv Us main lctx {} where
  m := .nil
  wf := trivial
  onlyLams := .nil
  lctx_eq := rfl
  embed := .from_nil henv hmain.tr.wf main.noBV
  sub := .empty

/-- The bottom of the main context. -/
def ofMain (henv : VEnv.Ordered venv) (hmain : main.WF venv Us) (honly : MLCtxOnlyLams main)
    (hlctx : main.lctx = lctx) (j : Nat) (hj : j ≤ main.length) :
    CheckBase venv Us main lctx (main.dropN j hj).lctx where
  m := main.dropN j hj
  wf := hmain.dropN j hj
  onlyLams := honly.dropN j hj
  lctx_eq := rfl
  embed := .of_fvLift (honly.dropN_fvlift j hj).toFVLift' (.refl henv hmain.tr.wf)
  sub := by
    intro fv d hd
    have hmem : fv ∈ (main.dropN j hj).vlctx.fvars :=
      ((hmain.dropN j hj).tr.find?_eq_some).1 ⟨d, hd⟩
    refine ⟨d, ?_, rfl⟩
    rw [← hlctx, honly.dropN_find?_eq hmain j hj hmem]
    exact hd

/-- The bottom of an embedded checker context. -/
def below {l : LocalContext} (B : CheckBase venv Us main lctx l) (j : Nat) (hj : j ≤ B.m.length) :
    CheckBase venv Us main lctx (B.m.dropN j hj).lctx where
  m := B.m.dropN j hj
  wf := B.wf.dropN j hj
  onlyLams := B.onlyLams.dropN j hj
  lctx_eq := rfl
  embed := .of_fvLift (B.onlyLams.dropN_fvlift j hj).toFVLift' B.embed
  sub := by
    intro fv d hd
    have hmem : fv ∈ (B.m.dropN j hj).vlctx.fvars :=
      ((B.wf.dropN j hj).tr.find?_eq_some).1 ⟨d, hd⟩
    have h1 : B.m.lctx.find? fv = some d := by
      rw [B.onlyLams.dropN_find?_eq B.wf j hj hmem]; exact hd
    rw [B.lctx_eq] at h1
    exact B.sub fv d h1

/-- A checker base stays a checker base when the main context is extended by
one fresh lambda declaration. -/
def skip {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.Ordered venv) (hmain : main.WF venv Us)
    (hlctx : main.lctx = lctx)
    {id : FVarId} {name : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo}
    (hwf' : (TypeChecker.MLCtx.vlam id name ty ty' bi main).WF venv Us) :
    CheckBase venv Us (.vlam id name ty ty' bi main) (lctx.mkLocalDecl id name ty bi) l where
  m := B.m
  wf := B.wf
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq
  embed := B.embed.skip henv (hmain.tr.find?_eq_none.1 hwf'.2.1) hwf'.2.2.1.fvarsList hwf'.2.2.2
  sub := B.sub.mkLocalDecl_right (by rw [← hlctx]; exact hmain.tr.1.map_wf)
    (by rw [← hlctx]; exact hwf'.2.1)

/-- Open one checked binder on top of a checker base. -/
def cons {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.WF venv)
    {id : FVarId} {name : Name} {ty : Expr} {ty' ty₀ : VExpr} {bi : BinderInfo}
    (hlctx : main.lctx = lctx)
    (hwf' : (TypeChecker.MLCtx.vlam id name ty ty' bi main).WF venv Us)
    (htr₀ : TrExprS venv Us B.m.vlctx ty ty₀)
    (hty₀ : venv.IsType Us.length B.m.vlctx.toCtx ty₀) :
    CheckBase venv Us (.vlam id name ty ty' bi main) (lctx.mkLocalDecl id name ty bi)
      (l.mkLocalDecl id name ty bi) where
  m := .vlam id name ty ty₀ bi B.m
  wf := ⟨B.wf, B.wf.tr.find?_eq_none.2 fun h =>
      (hwf'.1.tr.find?_eq_none.1 hwf'.2.1) (B.embed.fvars_subset h), htr₀, hty₀⟩
  onlyLams := B.onlyLams.vlam
  lctx_eq := by
    change B.m.lctx.mkLocalDecl id name ty bi = l.mkLocalDecl id name ty bi
    rw [B.lctx_eq]
  embed := B.embed.cons henv (hwf'.1.tr.find?_eq_none.1 hwf'.2.1) htr₀ hwf'.2.2.1 hwf'.2.2.2
  sub := B.sub.mkLocalDecl_both (by rw [← B.lctx_eq]; exact B.wf.tr.1.map_wf)
    (by rw [← hlctx]; exact hwf'.1.tr.1.map_wf)

def mono {venv' : VEnv} {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (hle : venv ≤ venv') : CheckBase venv' Us main lctx l where
  m := B.m
  wf := B.wf.mono hle
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq
  embed := B.embed.mono hle
  sub := B.sub

def prependLevelParam {l : LocalContext} {fresh : Name} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.WF venv) (hfresh : fresh ∉ Us) :
    CheckBase venv (fresh :: Us) (main.prependLevelParam Us.length) lctx l where
  m := B.m.prependLevelParam Us.length
  wf := B.wf.prependLevelParam henv hfresh
  onlyLams := by
    intro d hd
    apply B.onlyLams d
    simpa using hd
  lctx_eq := by simpa using B.lctx_eq
  embed := by
    simpa using B.embed.instL (U' := (fresh :: Us).length)
      (by simpa using VLevel.prependShift_wf (n := Us.length))
  sub := B.sub

/-- The free variables of the checker context, in order, restrict the main
local context to the checker context. -/
theorem restrictTo_eq {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (hlctx : lctx.WF) : lctx.restrictTo B.m.fvarList = l := by
  have hsub : B.m.lctx.SubContextOf lctx := by rw [B.lctx_eq]; exact B.sub
  rw [LocalContext.restrictTo_mlctx B.onlyLams B.wf hsub, B.lctx_eq]

end CheckBase

structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv

  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  typeCheckerLParams_eq : c.typeCheckerLParams = none
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv
  /-- The semantic checker context, embedded in the main one. -/
  check : CheckBase venv c.lparams mlctx c.lctx c.checkLCtx

def initialContext (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context where
  env; lparams; safety; allowPrimitive; fuel

def ContextWF.initial {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (safety : DefinitionSafety) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (hcorner : ∀ safety, ProjectionCorner safety env (ves.venv safety)) :
    ContextWF (initialContext env lparams safety allowPrimitive fuel) where
  venv := ves.venv safety
  checking := (wf.tr (safety := safety)).toCheckingValid
    (wf.hasPrimitives (safety := safety)) wf.safePrimitives
    wf.constructorOwners wf.projectionRegistryCoherent ((hcorner _))
  mlctx := .nil
  mlctx_wf := trivial
  typeCheckerLParams_eq := rfl
  onlyLams := MLCtxOnlyLams.nil
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun
  check := { m := .nil, wf := trivial, onlyLams := .nil, lctx_eq := rfl,
             embed := ⟨[], _, .refl, .nil⟩, sub := .empty }

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
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := H.check.mono hle

theorem ContextWF.current_not_mem (H : ContextWF c) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem ContextWF.kernel_reserves_current (H : ContextWF c) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

theorem ContextWF.lctxWF (H : ContextWF c) : c.lctx.WF :=
  H.lctx_eq ▸ H.mlctx_wf.tr.1

/-- The semantic checker context. -/
abbrev ContextWF.chk (H : ContextWF c) : TypeChecker.MLCtx := H.check.m

theorem ContextWF.checkSub (H : ContextWF c) : c.checkLCtx.SubContextOf c.lctx :=
  H.check.sub

/-- A candidate checker context beneath the main context of `H`. -/
abbrev ContextWF.Base (H : ContextWF c) (l : LocalContext) : Type :=
  CheckBase H.venv c.lparams H.mlctx c.lctx l

/-- The empty checker context. -/
def ContextWF.baseNil (H : ContextWF c) : H.Base {} :=
  .nil H.checking.tr.wf.ordered H.mlctx_wf

/-- A bottom part of the main context as checker context. -/
def ContextWF.baseMain (H : ContextWF c) (j : Nat) (hj : j ≤ H.mlctx.length) :
    H.Base (H.mlctx.dropN j hj).lctx :=
  .ofMain H.checking.tr.wf.ordered H.mlctx_wf H.onlyLams H.lctx_eq j hj

/-- Replace the checker context by a described sub-context of the main
context. -/
def ContextWF.withCheckLCtx (H : ContextWF c) (l : LocalContext) (B : H.Base l) :
    ContextWF { c with checkLCtx := l } where
  venv := H.venv
  checking := H.checking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := B

@[simp] theorem ContextWF.withCheckLCtx_venv (H : ContextWF c) (l B) :
    (H.withCheckLCtx l B).venv = H.venv := rfl

@[simp] theorem ContextWF.withCheckLCtx_mlctx (H : ContextWF c) (l B) :
    (H.withCheckLCtx l B).mlctx = H.mlctx := rfl

@[simp] theorem ContextWF.withCheckLCtx_chk (H : ContextWF c) (l B) :
    (H.withCheckLCtx l B).chk = B.m := rfl

/-- The narrow view of a semantic context: the checker context, described as
the main context of the context whose local context is the checker context.
Every embedded checker run reads only the checker context, so the narrow view
verifies the same runs, with facts about the checker context. -/
abbrev ContextWF.narrow (H : ContextWF c) : ContextWF { c with lctx := c.checkLCtx } where
  venv := H.venv
  checking := H.checking
  mlctx := H.chk
  mlctx_wf := H.check.wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.check.onlyLams
  lctx_eq := H.check.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := fun fv h => H.indFresh fv (H.check.embed.fvars_subset h)
  kernelFresh := fun fv h => H.kernelFresh fv (H.check.embed.fvars_subset h)
  check := { m := H.chk, wf := H.check.wf, onlyLams := H.check.onlyLams,
             lctx_eq := H.check.lctx_eq,
             embed := .refl H.checking.tr.wf.ordered H.check.wf.tr.wf,
             sub := .refl _ }

@[simp] theorem ContextWF.narrow_venv (H : ContextWF c) : H.narrow.venv = H.venv := rfl
@[simp] theorem ContextWF.narrow_mlctx (H : ContextWF c) : H.narrow.mlctx = H.chk := rfl
@[simp] theorem ContextWF.narrow_chk (H : ContextWF c) : H.narrow.chk = H.chk := rfl

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
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
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
  check := H.check.skip H.checking.tr.wf.ordered H.mlctx_wf H.lctx_eq
    (⟨H.mlctx_wf, H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩ :
      (TypeChecker.MLCtx.vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx).WF H.venv c.lparams)

/-- Bind at the reader level of the inductive-checker monad. -/
theorem AddInductive.M.WF_bind {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context} {P : α → Prop} {Q : β → Prop}
    (h1 : (x c).WF P) (h2 : ∀ a, P a → (f a c).WF Q) :
    ((x >>= f) c).WF Q :=
  Except.WF.bind h1 h2

@[simp] theorem AddInductive.withCheckLCtx_apply (l : LocalContext)
    (x : AddInductive.M α) (c : AddInductive.Context) :
    AddInductive.withCheckLCtx l x c = x { c with checkLCtx := l } := rfl

theorem AddInductive.readContext.WF {c : AddInductive.Context} :
    ((readThe AddInductive.Context : AddInductive.M AddInductive.Context) c).WF
      (c = ·) := by
  rintro _ ⟨⟩
  rfl

theorem AddInductive.getLCtx.WF {c : AddInductive.Context} :
    ((getLCtx : AddInductive.M LocalContext) c).WF (c.lctx = ·) := by
  rintro _ ⟨⟩
  rfl

theorem AddInductive.getType.run (e : Expr) (c : AddInductive.Context) :
    AddInductive.getType e c = .ok (c.lctx.get! e.fvarId!).type := rfl

/-- The checker base of a constructor field in the recursor first pass: the
parameters and the fields opened before it. -/
abbrev ctorFieldCheck (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (bu : Array Expr) : LocalContext :=
  c.lctx.restrictTo ((stats.params ++ bu).toList.map (·.fvarId!))

/-- The free variables of the first `n` parameters. -/
abbrev paramCheckFVars (stats : AddInductive.InductiveStats) (n : Nat) :
    List FVarId :=
  (stats.params.toList.take n).map (·.fvarId!)

/-- The executable parameter snapshot is the main context restricted to the
first `n` parameters. -/
theorem AddInductive.paramCheckLCtx.WF {stats : AddInductive.InductiveStats}
    {n : Nat} {c : AddInductive.Context} :
    (AddInductive.paramCheckLCtx stats n c).WF
      (· = c.lctx.restrictTo (paramCheckFVars stats n)) := by
  rintro _ ⟨⟩
  rfl

/-- The context in which a header or recursor index telescope is opened: the
checker context holds exactly the parameters. -/
abbrev headerCheckContext (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) : AddInductive.Context :=
  { c with checkLCtx := c.lctx.restrictTo (paramCheckFVars stats stats.params.size) }

/-- The parameter snapshot `n` as checker context, when the first `n`
parameters are the declarations at the bottom of the main context. -/
def ContextWF.baseParams (Hc : ContextWF c) (stats : AddInductive.InductiveStats)
    (n : Nat) (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats n = (Hc.mlctx.dropN j hj).fvarList) :
    Hc.Base (c.lctx.restrictTo (paramCheckFVars stats n)) :=
  (Hc.baseMain j hj).cast (by rw [hfv]; exact ((Hc.baseMain j hj).restrictTo_eq Hc.lctxWF).symm)

/-- The context of a run under the parameter snapshot `n`. -/
def ContextWF.paramCheck (Hc : ContextWF c) (stats : AddInductive.InductiveStats)
    (n : Nat) (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats n = (Hc.mlctx.dropN j hj).fvarList) :
    ContextWF { c with checkLCtx := c.lctx.restrictTo (paramCheckFVars stats n) } :=
  Hc.withCheckLCtx _ (Hc.baseParams stats n j hj hfv)

/-- Open a binder in both the main and the checker context.  The semantic
context records the main context and, for the checker context, the binder's
translation in the checker context. -/
def ContextWF.withCheckedLocalDecl (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    ContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  check := H.check.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

/-- Open a binder in the main context and on top of `base` in the checker
context. -/
def ContextWF.withCheckedLocalDeclOn (H : ContextWF c) (base : LocalContext)
    (B : H.Base base)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams B.m.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length B.m.vlctx.toCtx ty₀) :
    ContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  check := B.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

theorem ContextWF.withCheckedLocalDecl_venv (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).venv =
      H.venv := rfl

theorem ContextWF.withCheckedLocalDecl_mlctx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).mlctx =
      (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx := rfl

theorem ContextWF.withCheckedLocalDecl_toCtx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

theorem ContextWF.withCheckedLocalDecl_chk (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).chk =
      .vlam ⟨c.ngen.curr⟩ name ty ty₀ bi H.chk := rfl

theorem ContextWF.withLocalDecl_chk (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).chk = H.chk := rfl

theorem ContextWF.withLocalDecl_venv (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).venv = H.venv := rfl

theorem ContextWF.withLocalDecl_toCtx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

/-- The only universe rebasing performed for generated recursors: small
elimination keeps the declaration parameters, while large elimination
prepends its one fresh result-level parameter. -/
inductive RecursorLParams : List Name → List Name → Prop
  | same (lparams) : RecursorLParams lparams lparams
  | prepend (fresh lparams) (fresh_not_mem : fresh ∉ lparams) :
      RecursorLParams lparams (fresh :: lparams)

/-- Semantic local-context invariant for generated recursor frames.  The
embedded typechecker runs under exactly `recLparams`; the declaration's own
universe parameters remain separately available as `c.lparams` for the
installed recursor metadata. -/
structure RecursorContextWF (c : AddInductive.Context)
    (recLparams : List Name) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv

  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv recLparams
  typeCheckerLParams_eq : c.typeCheckerLParams = some recLparams
  lparams_origin : RecursorLParams c.lparams recLparams
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv
  /-- The semantic checker context, embedded in the main one. -/
  check : CheckBase venv recLparams mlctx c.lctx c.checkLCtx

/-- An ordinary verified context is already a recursor context when no
universe rebasing is required. -/
def ContextWF.toRecursorContextWF (H : ContextWF c) :
    RecursorContextWF
      { c with typeCheckerLParams := some c.lparams } c.lparams where
  venv := H.venv
  checking := H.checking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := rfl
  lparams_origin := .same _
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := H.check

/-- Reinterpret an already verified executable local context after prepending
one fresh recursor universe parameter.  Concrete declarations and free-variable
names are unchanged; only their stored abstract universe indices move. -/
def ContextWF.prependRecursorLevelParam
    (H : ContextWF c) (hfresh : fresh ∉ c.lparams) :
    RecursorContextWF
      { c with typeCheckerLParams := some (fresh :: c.lparams) }
      (fresh :: c.lparams) := by
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
    typeCheckerLParams_eq := rfl
    lparams_origin := .prepend fresh c.lparams hfresh
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
      exact H.kernelFresh fv (hfv ▸ hmem)
    check := H.check.prependLevelParam H.checking.tr.wf hfresh }

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

theorem RecursorContextWF.lctxWF (H : RecursorContextWF c recLparams) :
    c.lctx.WF :=
  H.lctx_eq ▸ H.mlctx_wf.tr.1

/-- The semantic checker context of a recursor frame. -/
abbrev RecursorContextWF.chk (H : RecursorContextWF c recLparams) : TypeChecker.MLCtx :=
  H.check.m

theorem RecursorContextWF.checkSub (H : RecursorContextWF c recLparams) :
    c.checkLCtx.SubContextOf c.lctx :=
  H.check.sub

/-- A candidate checker context beneath the main context of a recursor frame. -/
abbrev RecursorContextWF.Base (H : RecursorContextWF c recLparams) (l : LocalContext) :
    Type :=
  CheckBase H.venv recLparams H.mlctx c.lctx l

def RecursorContextWF.baseNil (H : RecursorContextWF c recLparams) : H.Base {} :=
  .nil H.checking.tr.wf.ordered H.mlctx_wf

def RecursorContextWF.baseMain (H : RecursorContextWF c recLparams) (j : Nat)
    (hj : j ≤ H.mlctx.length) : H.Base (H.mlctx.dropN j hj).lctx :=
  .ofMain H.checking.tr.wf.ordered H.mlctx_wf H.onlyLams H.lctx_eq j hj

def RecursorContextWF.withCheckLCtx (H : RecursorContextWF c recLparams)
    (l : LocalContext) (B : H.Base l) :
    RecursorContextWF { c with checkLCtx := l } recLparams where
  venv := H.venv
  checking := H.checking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  lparams_origin := H.lparams_origin
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := B

@[simp] theorem RecursorContextWF.withCheckLCtx_venv
    (H : RecursorContextWF c recLparams) (l B) :
    (H.withCheckLCtx l B).venv = H.venv := rfl

@[simp] theorem RecursorContextWF.withCheckLCtx_mlctx
    (H : RecursorContextWF c recLparams) (l B) :
    (H.withCheckLCtx l B).mlctx = H.mlctx := rfl

@[simp] theorem RecursorContextWF.withCheckLCtx_chk
    (H : RecursorContextWF c recLparams) (l B) :
    (H.withCheckLCtx l B).chk = B.m := rfl

/-- The narrow view of a recursor frame: its checker context as main context. -/
abbrev RecursorContextWF.narrow (H : RecursorContextWF c recLparams) :
    RecursorContextWF { c with lctx := c.checkLCtx } recLparams where
  venv := H.venv
  checking := H.checking
  mlctx := H.chk
  mlctx_wf := H.check.wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  lparams_origin := H.lparams_origin
  onlyLams := H.check.onlyLams
  lctx_eq := H.check.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := fun fv h => H.indFresh fv (H.check.embed.fvars_subset h)
  kernelFresh := fun fv h => H.kernelFresh fv (H.check.embed.fvars_subset h)
  check := { m := H.chk, wf := H.check.wf, onlyLams := H.check.onlyLams,
             lctx_eq := H.check.lctx_eq,
             embed := .refl H.checking.tr.wf.ordered H.check.wf.tr.wf,
             sub := .refl _ }

@[simp] theorem RecursorContextWF.narrow_venv (H : RecursorContextWF c recLparams) :
    H.narrow.venv = H.venv := rfl
@[simp] theorem RecursorContextWF.narrow_mlctx (H : RecursorContextWF c recLparams) :
    H.narrow.mlctx = H.chk := rfl

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
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  lparams_origin := H.lparams_origin
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
  check := H.check.skip H.checking.tr.wf.ordered H.mlctx_wf H.lctx_eq
    (⟨H.mlctx_wf, H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩ :
      (TypeChecker.MLCtx.vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx).WF H.venv recLparams)

/-- `ContextWF` for `headerCheckContext`. -/
def ContextWF.headerCheck (Hc : ContextWF c) (stats : AddInductive.InductiveStats)
    (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats stats.params.size = (Hc.mlctx.dropN j hj).fvarList) :
    ContextWF (headerCheckContext c stats) :=
  Hc.paramCheck stats stats.params.size j hj hfv

@[simp] theorem ContextWF.paramCheck_venv (Hc : ContextWF c) (stats n j hj hfv) :
    (Hc.paramCheck stats n j hj hfv).venv = Hc.venv := rfl

@[simp] theorem ContextWF.paramCheck_mlctx (Hc : ContextWF c) (stats n j hj hfv) :
    (Hc.paramCheck stats n j hj hfv).mlctx = Hc.mlctx := rfl

@[simp] theorem ContextWF.paramCheck_chk (Hc : ContextWF c) (stats n j hj hfv) :
    (Hc.paramCheck stats n j hj hfv).chk = Hc.mlctx.dropN j hj := rfl

@[simp] theorem ContextWF.headerCheck_venv (Hc : ContextWF c) (stats j hj hfv) :
    (Hc.headerCheck stats j hj hfv).venv = Hc.venv := rfl

@[simp] theorem ContextWF.headerCheck_mlctx (Hc : ContextWF c) (stats j hj hfv) :
    (Hc.headerCheck stats j hj hfv).mlctx = Hc.mlctx := rfl

@[simp] theorem ContextWF.headerCheck_chk (Hc : ContextWF c) (stats j hj hfv) :
    (Hc.headerCheck stats j hj hfv).chk = Hc.mlctx.dropN j hj := rfl

def RecursorContextWF.baseParams (Hc : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (n : Nat) (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats n = (Hc.mlctx.dropN j hj).fvarList) :
    Hc.Base (c.lctx.restrictTo (paramCheckFVars stats n)) :=
  (Hc.baseMain j hj).cast (by rw [hfv]; exact ((Hc.baseMain j hj).restrictTo_eq Hc.lctxWF).symm)

def RecursorContextWF.paramCheck (Hc : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (n : Nat) (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats n = (Hc.mlctx.dropN j hj).fvarList) :
    RecursorContextWF
      { c with checkLCtx := c.lctx.restrictTo (paramCheckFVars stats n) }
      recLparams :=
  Hc.withCheckLCtx _ (Hc.baseParams stats n j hj hfv)

@[simp] theorem RecursorContextWF.paramCheck_chk (Hc : RecursorContextWF c recLparams)
    (stats n j hj hfv) :
    (Hc.paramCheck stats n j hj hfv).chk = Hc.mlctx.dropN j hj := rfl

/-- Open a binder in both the main and the checker context of a recursor
frame. -/
def RecursorContextWF.withCheckedLocalDecl
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length H.chk.vlctx.toCtx ty₀) :
    RecursorContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      recLparams where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  lparams_origin := H.lparams_origin
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  check := H.check.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

def RecursorContextWF.withCheckedLocalDeclOn
    (H : RecursorContextWF c recLparams) (base : LocalContext)
    (B : H.Base base)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams B.m.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length B.m.vlctx.toCtx ty₀) :
    RecursorContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      recLparams where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  lparams_origin := H.lparams_origin
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  check := B.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

@[simp] theorem RecursorContextWF.withCheckedLocalDecl_venv
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).venv =
      H.venv := rfl

theorem RecursorContextWF.withCheckedLocalDecl_mlctx
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).mlctx =
      (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx := rfl

@[simp] theorem RecursorContextWF.withCheckedLocalDecl_toCtx
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

theorem RecursorContextWF.withCheckedLocalDecl_chk
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv recLparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType recLparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).chk =
      .vlam ⟨c.ngen.curr⟩ name ty ty₀ bi H.chk := rfl

theorem RecursorContextWF.withLocalDecl_chk
    (H : RecursorContextWF c recLparams)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).chk = H.chk := rfl

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
    exact H.mlctx_wf.mkForall_eq n hn hxs (by simpa [TypeChecker.MLCtx.noBV] using htr.closed)
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

theorem RecursorContextWF.lctxClosed (R : RecursorContextWF c recLparams) :
    LocalContext.LctxClosed c.lctx :=
  R.lctx_eq ▸ R.mlctx_wf.tr.lctxClosed

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

theorem BindingContextWF.withCheckedLocalDecl (H : BindingContextWF c)
    {base : LocalContext}
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } :=
  let H' := H.withLocalDecl name ty bi
  { wf := H'.wf
    onlyLams := H'.onlyLams
    ngen_prefix := H'.ngen_prefix
    fresh := H'.fresh
    findCDecl := H'.findCDecl }

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

theorem withCheckedLocalDecl.WF {k : Expr → AddInductive.M α} (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx ty ty₀)
    (hty₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx ty₀)
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
        checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (AddInductive.withCheckedLocalDecl name bi ty k c).WF Q := by
  have _Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀
  exact Hk

theorem withCheckedLocalDecl.recursorWF {k : Expr → AddInductive.M α}
    (R : RecursorContextWF c recLparams)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS R.venv recLparams R.chk.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx ty₀)
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
        checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (AddInductive.withCheckedLocalDecl name bi ty k c).WF Q := by
  have _R' := R.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀
  exact Hk

@[simp] theorem RecursorContextWF.withCheckedLocalDeclOn_venv
    (H : RecursorContextWF c recLparams) (base B)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr hty htr₀ hty₀).venv =
      H.venv := rfl

@[simp] theorem RecursorContextWF.withCheckedLocalDeclOn_toCtx
    (H : RecursorContextWF c recLparams) (base B)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr
      hty htr₀ hty₀).mlctx.vlctx.toCtx = ty' :: H.mlctx.vlctx.toCtx := rfl

theorem RecursorContextWF.withCheckedLocalDeclOn_chk
    (H : RecursorContextWF c recLparams) (base B)
    (htr : TrExprS H.venv recLparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType recLparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr
      hty htr₀ hty₀).chk = .vlam ⟨c.ngen.curr⟩ name ty ty₀ bi B.m := rfl

theorem ContextWF.withCheckedLocalDeclOn_venv
    (H : ContextWF c) (base B)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr hty
      htr₀ hty₀).venv = H.venv := rfl

theorem ContextWF.withCheckedLocalDeclOn_toCtx
    (H : ContextWF c) (base B)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr
      hty htr₀ hty₀).mlctx.vlctx.toCtx = ty' :: H.mlctx.vlctx.toCtx := rfl

theorem ContextWF.withCheckedLocalDeclOn_chk
    (H : ContextWF c) (base B)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') (htr₀ hty₀) :
    (H.withCheckedLocalDeclOn (name := name) (bi := bi) (ty₀ := ty₀) base B htr
      hty htr₀ hty₀).chk = .vlam ⟨c.ngen.curr⟩ name ty ty₀ bi B.m := rfl

theorem withCheckedLocalDeclOn.WF {k : Expr → AddInductive.M α}
    {c : AddInductive.Context} {base : LocalContext}
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
        checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (AddInductive.withCheckedLocalDeclOn base name bi ty k c).WF Q := Hk

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
    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumed'
  isType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, Hc.venv.IsDefEq c.lparams.length Hc.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

theorem ContextWF.ConsumedDomain.sourceIsType {Hc : ContextWF c}
    (H : Hc.ConsumedDomain dom source' consumed') :
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx source' :=
  let ⟨_, h⟩ := H.source_defeq; ⟨_, h.hasType.1⟩

theorem Expr.consumeTypeAnnotationsVerified_eq_self {dom : Expr}
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false) :
    (dom.consumeTypeAnnotationsVerified annOk) = dom := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ dom
  all_goals simp_all [Expr.isOptParam, Expr.isAutoParam,
    Expr.isOutParam, Expr.isSemiOutParam, Expr.isAppOfArity]

theorem MLCtxOnlyLams.mkForall_consumeTypeAnnotations_eq_self
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length)
    (hbody : (body.consumeTypeAnnotationsVerified annOk) = body) :
    ((m.mkForall n hn body).consumeTypeAnnotationsVerified annOk) = m.mkForall n hn body := by
  induction n generalizing m body with
  | zero => exact hbody
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      apply ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
      apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Removing binder annotations only selects subexpressions of the original
domain, so it cannot introduce a new free-variable dependency. -/
theorem Expr.consumeTypeAnnotationsVerified_fvarsIn
    (H : FVarsIn P e) : FVarsIn P (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 ih => exact ih H.1.2
  case case2 => exact H
  case case3 ih => exact ih H.2
  case case4 => exact H
  case case5 => exact H

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
    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumed'
  isType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, R.venv.IsDefEq recLparams.length R.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

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

set_option linter.unusedSimpArgs false in
/-! ### Contexts whose checker context is the main context

While the inductive checker opens every binder in both contexts, the checker
context agrees with the main context up to definitional equality of the
recorded types (`ContextWF.Aligned`).  Checker-context facts are then obtained
from main-context ones by context conversion. -/

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
  have hsym := h.symm henv.ordered
  obtain ⟨r, hr⟩ := hr₀.defeqDFC henv hsym
  have hu := hr₀.uniq henv hsym hr
  have hctx := h.defeqCtx.symm henv.ordered
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

/-- Type-hood transfers from a scope to an aligned checker context along a
definitional equality. -/
theorem _root_.Lean4Lean.VEnv.IsType.alignTo (henv : env.WF)
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hA : env.IsType Us.length scope.toCtx a)
    (hu : env.IsDefEqU Us.length scope.toCtx a b) :
    env.IsType Us.length chk.toCtx b :=
  (hA.defeqU_l henv h.wf.toCtx hu).defeqDFC henv.ordered h.defeqCtx

/-- A forall's domain and body, translated in a scope, transfer to an aligned
checker context. -/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.forallE_align (henv : env.WF)
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hdom : TrExprS env Us scope dom d)
    (hdomT : env.IsType Us.length scope.toCtx d)
    (hbody : TrExprS env Us ((none, .vlam d) :: scope) body b) :
    ∃ d₀ b₀, TrExprS env Us chk dom d₀ ∧
      env.IsType Us.length chk.toCtx d₀ ∧
      env.IsDefEqU Us.length scope.toCtx d d₀ ∧
      TrExprS env Us ((none, .vlam d₀) :: chk) body b₀ ∧
      env.IsDefEqU Us.length (d :: scope.toCtx) b b₀ := by
  obtain ⟨d₀, hd₀, hu⟩ := hdom.alignTo henv h
  have hd₀T := hdomT.alignTo henv h hu
  obtain ⟨v, hv⟩ := hdomT
  have hctx : VLCtx.IsDefEq env Us.length ((none, .vlam d) :: scope)
      ((none, .vlam d₀) :: chk) :=
    .cons h nofun (.vlam (hu.of_l henv h.wf.toCtx hv))
  obtain ⟨b₀, hb₀⟩ := hbody.defeqDFC henv hctx
  exact ⟨d₀, b₀, hd₀, hd₀T, hu, hb₀, hbody.uniq henv hctx hb₀⟩

/-- A checker-context typing of a translated term transfers back to the
scope translation of the same term. -/
theorem _root_.Lean4Lean.VEnv.HasType.alignBack (henv : env.WF)
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hn : TrExprS env Us scope e a) (h₀ : TrExprS env Us chk e b)
    (ht : env.HasType Us.length chk.toCtx b T) :
    env.HasType Us.length scope.toCtx a T := by
  have ht' := ht.defeqDFC henv.ordered (h.defeqCtx.symm henv.ordered)
  exact ht'.defeqU_l henv h.wf.toCtx (hn.uniq henv h h₀).symm

/-- Extend an alignment by a free-variable binder whose two domains are
definitionally equal. -/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.consAligned
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hfresh : fv ∉ scope.fvars) (hdeps : deps ⊆ scope.fvars)
    (hA : env.IsDefEq Us.length scope.toCtx A A₀ (.sort u)) :
    VLCtx.IsDefEq env Us.length ((some (fv, deps), .vlam A) :: scope)
      ((some (fv, deps), .vlam A₀) :: chk) :=
  .cons h (by rintro _ _ ⟨⟩; exact ⟨hfresh, hdeps⟩) (.vlam hA)

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

/-- Two executable contexts agree on their `n` most recent declarations: the
same named lambdas with the same source domains, possibly translated
differently.  This relates a main context to the checker context of the same
run. -/
inductive MLCtxTopAgree : TypeChecker.MLCtx → TypeChecker.MLCtx → Nat → Prop
  | zero (a b : TypeChecker.MLCtx) : MLCtxTopAgree a b 0
  | vlam {a b : TypeChecker.MLCtx} {n : Nat} (h : MLCtxTopAgree a b n)
      (fv name ty t₁ t₂ bi) :
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1)

theorem MLCtxTopAgree.fvarRevList_eq {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (ha : n ≤ a.length) (hb : n ≤ b.length) :
    a.fvarRevList n ha = b.fvarRevList n hb := by
  induction H with
  | zero => simp
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.fvarRevList]
    rw [ih]

theorem MLCtxTopAgree.stepDropEq {a b M : TypeChecker.MLCtx} {n : Nat}
    (fv name ty t₁ t₂ bi)
    (h : ∃ hn : n ≤ b.length, MLCtxTopAgree a b n ∧ b.dropN n hn = M) :
    ∃ hn : n + 1 ≤ (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).length,
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1) ∧
        (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).dropN (n + 1) hn = M := by
  obtain ⟨hn, hag, hd⟩ := h
  exact ⟨by simpa using hn, hag.vlam fv name ty t₁ t₂ bi, by simpa using hd⟩

/-- `stepDrop`, additionally carrying the closure of the checker translation
of the current telescope back to the base context. -/
theorem MLCtxTopAgree.stepDropForall {env : VEnv} {U : Nat}
    {a b : TypeChecker.MLCtx} {n : Nat} {V : VLCtx} {T₀ X : VExpr}
    (fv name ty t₁ t₂ bi)
    (h : ∃ hn : n ≤ b.length, MLCtxTopAgree a b n ∧ (b.dropN n hn).vlctx = V ∧
      env.IsDefEqU U V.toCtx T₀ (b.mkForall' n hn (.forallE t₂ X))) :
    ∃ hn : n + 1 ≤ (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).length,
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1) ∧
        ((TypeChecker.MLCtx.vlam fv name ty t₂ bi b).dropN (n + 1) hn).vlctx = V ∧
        env.IsDefEqU U V.toCtx T₀
          ((TypeChecker.MLCtx.vlam fv name ty t₂ bi b).mkForall' (n + 1) hn X) := by
  obtain ⟨hn, hag, hd, he⟩ := h
  exact ⟨by simpa using hn, hag.vlam fv name ty t₁ t₂ bi, by simpa using hd,
    by simpa using he⟩

theorem MLCtxTopAgree.forallDomains_length {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hn : n ≤ b.length) :
    (MLCtxForallDomains b n hn).length = n := by
  induction H with
  | zero => simp [MLCtxForallDomains]
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [MLCtxForallDomains, List.length_append, List.length_singleton]
    rw [ih]

theorem MLCtxTopAgree.toCtx_split {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hn : n ≤ b.length) :
    b.vlctx.toCtx =
      (MLCtxForallDomains b n hn).reverse ++ (b.dropN n hn).vlctx.toCtx := by
  induction H with
  | zero => simp [MLCtxForallDomains]
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
      MLCtxForallDomains, List.reverse_append, List.reverse_singleton,
      List.singleton_append, TypeChecker.MLCtx.dropN]
    simpa [List.append_assoc] using congrArg (t₂ :: ·)
      (ih (Nat.le_of_succ_le_succ hn))

/-- Opening a binder in both contexts extends a scope aligned with the
checker context by the scope translation of the binder's domain. -/
theorem ContextWF.alignedBinder (Hc : ContextWF c)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hdom : Hc.ConsumedDomain dom sourceDom consumedDom)
    (Hdom₀ : Hc.narrow.ConsumedDomain dom sourceDom₀ consumedDom₀)
    (hdomNarrow : TrExprS Hc.venv c.lparams scope dom narrowDom)
    (hdomNarrowType : Hc.venv.IsType c.lparams.length scope.toCtx narrowDom)
    (hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars) :
    VLCtx.IsDefEq Hc.venv c.lparams.length
      ((some (⟨c.ngen.curr⟩, (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
        .vlam narrowDom) :: scope)
      (Hc.withCheckedLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType).chk.vlctx := by
  have henv := Hc.checking.tr.wf
  have hscopeΓ := halign.wf.toCtx
  have hdomU := hdomNarrow.uniq henv halign Hdom₀.source
  rcases Hdom₀.source_defeq with ⟨u₀, hsc₀⟩
  have hsc₀' := hsc₀.defeqDFC henv.ordered (halign.defeqCtx.symm henv.ordered)
  have hdomC : Hc.venv.IsDefEqU c.lparams.length scope.toCtx
      narrowDom consumedDom₀ :=
    hdomU.trans henv hscopeΓ ⟨_, hsc₀'⟩
  rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
  have hfresh : (⟨c.ngen.curr⟩ : FVarId) ∉ scope.fvars := by
    intro hmem
    rw [halign.fvars] at hmem
    exact Hc.current_not_mem (Hc.check.embed.fvars_subset hmem)
  exact halign.consAligned hfresh hdeps (hdomC.of_l henv hscopeΓ hdomTyped)

/-- Recursor-frame analogue of `ContextWF.alignedBinder`. -/
theorem RecursorContextWF.alignedBinder (R : RecursorContextWF c recLparams)
    (halign : VLCtx.IsDefEq R.venv recLparams.length scope R.chk.vlctx)
    (Hdom : R.ConsumedDomain dom sourceDom consumedDom)
    (Hdom₀ : R.narrow.ConsumedDomain dom sourceDom₀ consumedDom₀)
    (hdomNarrow : TrExprS R.venv recLparams scope dom narrowDom)
    (hdomNarrowType : R.venv.IsType recLparams.length scope.toCtx narrowDom)
    (hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars) :
    VLCtx.IsDefEq R.venv recLparams.length
      ((some (⟨c.ngen.curr⟩, (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
        .vlam narrowDom) :: scope)
      (R.withCheckedLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType).chk.vlctx := by
  have henv := R.checking.tr.wf
  have hscopeΓ := halign.wf.toCtx
  have hdomU := hdomNarrow.uniq henv halign Hdom₀.source
  rcases Hdom₀.source_defeq with ⟨u₀, hsc₀⟩
  have hsc₀' := hsc₀.defeqDFC henv.ordered (halign.defeqCtx.symm henv.ordered)
  have hdomC : R.venv.IsDefEqU recLparams.length scope.toCtx
      narrowDom consumedDom₀ :=
    hdomU.trans henv hscopeΓ ⟨_, hsc₀'⟩
  rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
  have hfresh : (⟨c.ngen.curr⟩ : FVarId) ∉ scope.fvars := by
    intro hmem
    rw [halign.fvars] at hmem
    exact R.current_not_mem (R.check.embed.fvars_subset hmem)
  exact halign.consAligned hfresh hdeps (hdomC.of_l henv hscopeΓ hdomTyped)

/-- The checker-context normal form of an opened body, read back in a scope
aligned with the checker context: the scope translation of the source body
is definitionally equal to it. -/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.openedNormalForm {env : VEnv} {Us : List Name}
    {scope chk : VLCtx} (henv : env.WF)
    (halign : VLCtx.IsDefEq env Us.length scope chk)
    {indexType consumed₀ : VExpr} {u : VLevel}
    (hindex : env.IsDefEq Us.length scope.toCtx indexType consumed₀ (.sort u))
    (hfresh : ∀ fv deps, ofv = some (fv, deps) → fv ∉ scope.fvars ∧ deps ⊆ scope.fvars)
    {body : Expr} {narrowBody consumedBody₀ : VExpr}
    (hbodyNarrow : TrExprS env Us ((none, .vlam indexType) :: scope) body narrowBody)
    (hbodyConsumed₀ : TrExprS env Us ((none, .vlam consumed₀) :: chk) body consumedBody₀)
    {normalized : Expr} {normalizedC : VExpr}
    (hnormalizedC : TrExprS env Us ((ofv, .vlam consumed₀) :: chk) normalized normalizedC)
    (hnormalizedCEq : env.IsDefEqU Us.length (consumed₀ :: chk.toCtx)
      normalizedC consumedBody₀) :
    ∃ normalizedNarrow,
      TrExprS env Us ((ofv, .vlam indexType) :: scope) normalized normalizedNarrow ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx) narrowBody normalizedNarrow := by
  have halign' : VLCtx.IsDefEq env Us.length ((ofv, .vlam indexType) :: scope)
      ((ofv, .vlam consumed₀) :: chk) := .cons halign hfresh (.vlam hindex)
  obtain ⟨normalizedNarrow, hnormalizedNarrow⟩ :=
    hnormalizedC.defeqDFC henv (halign'.symm henv.ordered)
  have hnn := hnormalizedNarrow.uniq henv halign' hnormalizedC
  have hctxB : VLCtx.IsDefEq env Us.length ((none, .vlam indexType) :: scope)
      ((none, .vlam consumed₀) :: chk) := .cons halign nofun (.vlam hindex)
  have hbodyU := hbodyNarrow.uniq henv hctxB hbodyConsumed₀
  have hnormC : env.IsDefEqU Us.length (indexType :: scope.toCtx)
      normalizedC consumedBody₀ :=
    hnormalizedCEq.defeqDFC henv.ordered (hctxB.symm henv.ordered).defeqCtx
  have hΓ' : OnCtx (indexType :: scope.toCtx) (env.IsType Us.length) :=
    ⟨halign.wf.toCtx, _, hindex.hasType.1⟩
  have h1 : env.IsDefEqU Us.length (indexType :: scope.toCtx)
      normalizedNarrow normalizedC := hnn
  exact ⟨normalizedNarrow, hnormalizedNarrow,
    hbodyU.trans henv hΓ' (hnormC.symm.trans henv hΓ' h1.symm)⟩

/-- The checker context agrees with the main context, up to definitional
equality of the recorded binder types. -/
def ContextWF.Aligned (H : ContextWF c) : Prop :=
  VLCtx.IsDefEq H.venv c.lparams.length H.mlctx.vlctx H.chk.vlctx

theorem ContextWF.Aligned.tr {H : ContextWF c} (ha : H.Aligned)
    (h : TrExprS H.venv c.lparams H.mlctx.vlctx e e') :
    ∃ e₀, TrExprS H.venv c.lparams H.chk.vlctx e e₀ ∧
      H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx e' e₀ := by
  obtain ⟨e₀, h₀⟩ := h.defeqDFC H.checking.tr.wf ha
  exact ⟨e₀, h₀, h.uniq H.checking.tr.wf ha h₀⟩

theorem ContextWF.Aligned.isType {H : ContextWF c} (ha : H.Aligned)
    (h : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx e')
    (hu : H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx e' e₀) :
    H.venv.IsType c.lparams.length H.chk.vlctx.toCtx e₀ :=
  (h.defeqU_l H.checking.tr.wf H.mlctx_wf.tr.wf.toCtx hu).defeqDFC
    H.checking.tr.wf.ordered ha.defeqCtx

/-- The narrow annotation-consumption certificate of an aligned context. -/
theorem ContextWF.Aligned.consumedDomain {H : ContextWF c} (ha : H.Aligned)
    (Hdom : H.ConsumedDomain dom source' consumed') :
    ∃ source₀ consumed₀, H.narrow.ConsumedDomain dom source₀ consumed₀ ∧
      H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx source' source₀ ∧
      H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx consumed' consumed₀ := by
  obtain ⟨s₀, hs₀, hsu⟩ := ha.tr Hdom.source
  obtain ⟨c₀, hc₀, hcu⟩ := ha.tr Hdom.consumed
  have hΓ := H.mlctx_wf.tr.wf.toCtx
  have hct := ha.isType Hdom.isType hcu
  obtain ⟨u, hsd⟩ := Hdom.source_defeq
  have hsc : H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx source' consumed' :=
    ⟨_, hsd⟩
  have h1 : H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx s₀ c₀ :=
    hsu.symm.trans H.checking.tr.wf hΓ (hsc.trans H.checking.tr.wf hΓ hcu)
  have h1' := h1.defeqDFC H.checking.tr.wf.ordered ha.defeqCtx
  obtain ⟨v, hv⟩ := hct
  exact ⟨s₀, c₀, ⟨hs₀, hc₀, ⟨v, hv⟩, ⟨v, h1'.of_r H.checking.tr.wf
    (ha.symm H.checking.tr.wf.ordered).wf.toCtx hv⟩⟩, hsu, hcu⟩

/-- Convert a body under a domain of the main context to one under a
definitionally equal domain of the checker context. -/
theorem ContextWF.Aligned.body {H : ContextWF c} {body : Expr} (ha : H.Aligned)
    (hdomType : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx dom')
    (hu : H.venv.IsDefEqU c.lparams.length H.mlctx.vlctx.toCtx dom' dom₀)
    (hbody : TrExprS H.venv c.lparams ((none, .vlam dom') :: H.mlctx.vlctx) body body') :
    ∃ body₀, TrExprS H.venv c.lparams ((none, .vlam dom₀) :: H.chk.vlctx) body body₀ ∧
      H.venv.IsDefEqU c.lparams.length (dom' :: H.mlctx.vlctx.toCtx) body' body₀ := by
  obtain ⟨v, hv⟩ := hdomType
  have hctx : VLCtx.IsDefEq H.venv c.lparams.length
      ((none, .vlam dom') :: H.mlctx.vlctx) ((none, .vlam dom₀) :: H.chk.vlctx) :=
    .cons ha nofun (.vlam (hu.of_l H.checking.tr.wf H.mlctx_wf.tr.wf.toCtx hv))
  obtain ⟨b₀, hb₀⟩ := hbody.defeqDFC H.checking.tr.wf hctx
  exact ⟨b₀, hb₀, hbody.uniq H.checking.tr.wf hctx hb₀⟩

/-- Opening the same binder in both contexts keeps them aligned. -/
theorem ContextWF.Aligned.withCheckedLocalDecl {H : ContextWF c} (ha : H.Aligned)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv c.lparams H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType c.lparams.length H.chk.vlctx.toCtx ty₀) :
    (H.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀).Aligned := by
  obtain ⟨v, hv⟩ := hty
  have hu := htr.uniq H.checking.tr.wf ha htr₀
  refine .cons ha ?_ (.vlam (hu.of_l H.checking.tr.wf H.mlctx_wf.tr.wf.toCtx hv))
  rintro _ _ ⟨⟩
  exact ⟨H.current_not_mem, htr.fvarsList⟩

theorem ContextWF.chkKernelFresh (H : ContextWF c) :
    ∀ fv ∈ H.chk.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv :=
  fun fv h => H.kernelFresh fv (H.check.embed.fvars_subset h)

/-- The checker context as a type-checker context. -/
def ContextWF.checkTC (H : ContextWF c) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC H.checking H.chk H.check.wf c.fuel

/-- Reuse a verified typechecker computation inside `AddInductive.M`.  The
run happens in the checker context, and is verified there. -/
theorem liftTypeChecker.WF {x : TypeChecker.M α} (Hc : ContextWF c)
    (Hx : TypeChecker.M.WF Hc.checkTC {} x fun a _ => Q a) :
    ((monadLift x : AddInductive.M α) c).WF Q := by
  change (TypeChecker.M.run c.env c.safety c.checkLCtx
    (c.typeCheckerLParams.getD c.lparams) c.fuel x).WF Q
  rw [Hc.typeCheckerLParams_eq]
  simp only [Option.getD_none]
  rw [← Hc.check.lctx_eq]
  exact TypeChecker.M.WF.runCheckingValidMLC Hc.chkKernelFresh Hx

theorem checkTypeInContext.narrowWF (Hc : ContextWF c)
    (hfvars : e.FVarsIn (· ∈ Hc.chk.vlctx.fvars)) :
    ((monadLift (TypeChecker.checkType e) : AddInductive.M Expr) c).WF fun ty =>
      ∃ e' ty', TrTyping Hc.venv c.lparams Hc.chk.vlctx e ty e' ty' :=
  liftTypeChecker.WF Hc (TypeChecker.checkType.WF hfvars)

theorem checkTypeInContext.WF (Hc : ContextWF c)
    (hfvars : e.FVarsIn (· ∈ Hc.chk.vlctx.fvars)) :
    ((monadLift (TypeChecker.checkType e) : AddInductive.M Expr) c).WF fun ty =>
      ∃ e' ty', TrTyping Hc.venv c.lparams Hc.mlctx.vlctx e ty e' ty' :=
  (checkTypeInContext.narrowWF Hc hfvars).mono fun _ ⟨_, _, h⟩ => by
    obtain ⟨e', he'⟩ := Hc.check.embed.trExprS Hc.checking.tr.wf h.2.1
    obtain ⟨ty', h'⟩ := Hc.check.embed.trTyping Hc.checking.tr.wf he' h
    exact ⟨e', ty', h'⟩

theorem whnfInContext.narrowWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.chk.vlctx e e₁ ∧
      TrExpr Hc.venv c.lparams Hc.chk.vlctx e₁ e' :=
  liftTypeChecker.WF Hc ((TypeChecker.Inner.whnf.WF he).run)

/-- `whnf` preserves every admissible free-variable scope of its input, in
addition to preserving the abstract expression up to definitional equality.
Stated for the main context: the run is verified in the checker context, on
the checker translation `hn` of the input, and transferred. -/
theorem whnfInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  (whnfInContext.narrowWF Hc hn).mono fun _ ⟨h1, h2⟩ =>
    ⟨Hc.check.embed.fvarsBelow h1, Hc.check.embed.trExpr Hc.checking.tr.wf hn he h2⟩

/-- Both the checker-context facts and their main-context transfers. -/
theorem whnfInContext.dualWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      (FVarsBelow Hc.mlctx.vlctx e e₁ ∧
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e') ∧
      FVarsBelow Hc.chk.vlctx e e₁ ∧
        TrExpr Hc.venv c.lparams Hc.chk.vlctx e₁ e₀ :=
  (whnfInContext.narrowWF Hc hn).mono fun _ ⟨h1, h2⟩ =>
    ⟨⟨Hc.check.embed.fvarsBelow h1, Hc.check.embed.trExpr Hc.checking.tr.wf hn he h2⟩,
      h1, h2⟩

theorem whnfInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  (whnfInContext.scopeWF Hc he hn).mono fun _ h => h.2

/-- Interpret typechecker verification under the recursor's universe
parameters while retaining the executable local context built by
`AddInductive`. -/
def RecursorContextWF.typeChecker
    (H : RecursorContextWF c recLparams) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC
    H.checking H.mlctx H.mlctx_wf c.fuel

theorem RecursorContextWF.chkKernelFresh (H : RecursorContextWF c recLparams) :
    ∀ fv ∈ H.chk.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv :=
  fun fv h => H.kernelFresh fv (H.check.embed.fvars_subset h)

/-- The checker context of a recursor frame as a type-checker context. -/
def RecursorContextWF.checkTC (H : RecursorContextWF c recLparams) :
    TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC H.checking H.chk H.check.wf c.fuel

/-- Reuse a verified typechecker computation in a recursor frame; the run
happens in the checker context under the recursor universe parameters. -/
theorem liftTypeChecker.recursorWF {x : TypeChecker.M α}
    (Hc : RecursorContextWF c recLparams)
    (Hx : TypeChecker.M.WF Hc.checkTC {} x fun a _ => Q a) :
    ((monadLift x : AddInductive.M α) c).WF Q := by
  change (TypeChecker.M.run c.env c.safety c.checkLCtx
    (c.typeCheckerLParams.getD c.lparams) c.fuel x).WF Q
  rw [Hc.typeCheckerLParams_eq]
  simp only [Option.getD_some]
  rw [← Hc.check.lctx_eq]
  exact TypeChecker.M.WF.runCheckingValidMLC (lparams := recLparams) (fuel := c.fuel)
    Hc.chkKernelFresh Hx

theorem whnfInRecursorContext.narrowScopeWF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.chk.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.chk.vlctx e e₁ ∧
      TrExpr Hc.venv recLparams Hc.chk.vlctx e₁ e' :=
  liftTypeChecker.recursorWF Hc ((TypeChecker.Inner.whnf.WF he).run)

theorem whnfInRecursorContext.dualWF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv recLparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      (FVarsBelow Hc.mlctx.vlctx e e₁ ∧
        TrExpr Hc.venv recLparams Hc.mlctx.vlctx e₁ e') ∧
      FVarsBelow Hc.chk.vlctx e e₁ ∧
        TrExpr Hc.venv recLparams Hc.chk.vlctx e₁ e₀ :=
  (whnfInRecursorContext.narrowScopeWF Hc hn).mono fun _ ⟨h1, h2⟩ =>
    ⟨⟨Hc.check.embed.fvarsBelow h1, Hc.check.embed.trExpr Hc.checking.tr.wf hn he h2⟩,
      h1, h2⟩

/-- `getType` of a translated free variable returns its declared type, which
types the variable in the main context.  This replaces checker inference of
the variable's type (`inferFVar` returns the same declaration type). -/
theorem getTypeFVarInRecursorContext.WF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx (.fvar fv) e') :
    (AddInductive.getType (.fvar fv) c).WF fun ty =>
      ∃ ty', TrTyping Hc.venv recLparams Hc.mlctx.vlctx
        (.fvar fv) ty e' ty' := by
  have hmem : fv ∈ Hc.mlctx.vlctx.fvars := he.fvarsIn
  rcases (Hc.mlctx_wf.tr.find?_eq_some (fv := fv)).2 hmem with ⟨decl, hfind⟩
  have hdeclMem : decl ∈ Hc.mlctx.lctx.toList := by
    rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hfind
    exact List.mem_of_find?_eq_some hfind
  have hfv : decl.fvarId = fv := Hc.mlctx_wf.tr.1.find?_fvarId hfind
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hdeclMem with
    ⟨e, A, hlookup, _, hbelow, _, hA⟩
  rw [hfv] at hlookup hbelow
  have hfind' : c.lctx.find? fv = some decl := by
    rw [← Hc.lctx_eq]; exact hfind
  intro ty hty
  have htyEq : ty = decl.type := by
    change Except.ok (c.lctx.get! fv).type = Except.ok ty at hty
    simp only [LocalContext.get!, hfind', Except.ok.injEq] at hty
    exact hty.symm
  subst htyEq
  cases he with
  | fvar hlookup' =>
    rw [hlookup] at hlookup'
    cases hlookup'
    exact ⟨A, hbelow, .fvar hlookup, hA,
      Hc.mlctx_wf.tr.wf.find?_wf Hc.checking.tr.wf hlookup⟩

theorem ensureSortInContext.narrowScopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF
      fun e₁ => FVarsBelow Hc.chk.vlctx e e₁ ∧
        TrExpr Hc.venv c.lparams Hc.chk.vlctx e₁ e' ∧
        ∃ u, e₁ = .sort u := by
  change Hc.checkTC.TrExprS e e' at he
  apply liftTypeChecker.WF (Q := fun e₁ =>
    Hc.checkTC.FVarsBelow e e₁ ∧
      Hc.checkTC.TrExpr e₁ e' ∧
      ∃ u, e₁ = .sort u) Hc
  simpa only [TypeChecker.ensureSort] using
    (TypeChecker.Inner.ensureSortCore.WF he).run.mono
      (fun _ _ _ h => And.intro h.2.2 (And.intro h.2.1 h.1))

theorem ensureSortInContext.dualWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₂) :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF fun e₁ =>
      (TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' ∧ ∃ u, e₁ = .sort u) ∧
      TrExpr Hc.venv c.lparams Hc.chk.vlctx e₁ e₂ :=
  (ensureSortInContext.narrowScopeWF Hc hn).mono fun _ ⟨_, h2, h3⟩ =>
    ⟨⟨Hc.check.embed.trExpr Hc.checking.tr.wf hn he h2, h3⟩, h2⟩

theorem ensureTypeInContext.narrowWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e') :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ e'', TrExprS Hc.venv c.lparams Hc.chk.vlctx e e'' ∧
        ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
          Hc.venv.HasType c.lparams.length Hc.chk.vlctx.toCtx e'' (.sort u') :=
  liftTypeChecker.WF Hc (TypeChecker.ensureType.WF he)

theorem ensureTypeInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ e'', TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e'' ∧
        ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
          Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx e'' (.sort u') :=
  (ensureTypeInContext.narrowWF Hc hn).mono fun _ ⟨e₁, h1, u, u', hs, hu, hh⟩ =>
    ⟨e', he, u, u', hs, hu,
      Hc.check.embed.hasType Hc.checking.tr.wf h1 he (.sort hu) (.sort hu) hh⟩

/-- Both the checker-context sort of a type and its main-context transfer. -/
theorem ensureTypeInContext.dualWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e')
    (hn : TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
        Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx e' (.sort u') ∧
        ∃ e₁, TrExprS Hc.venv c.lparams Hc.chk.vlctx e e₁ ∧
          Hc.venv.HasType c.lparams.length Hc.chk.vlctx.toCtx e₁ (.sort u') :=
  (ensureTypeInContext.narrowWF Hc hn).mono fun _ ⟨e₁, h1, u, u', hs, hu, hh⟩ =>
    ⟨u, u', hs, hu,
      Hc.check.embed.hasType Hc.checking.tr.wf h1 he (.sort hu) (.sort hu) hh,
      e₁, h1, hh⟩

theorem isDefEqInContext.narrowWF (Hc : ContextWF c)
    (he₁ : TrExprS Hc.venv c.lparams Hc.chk.vlctx e₁ e₁')
    (he₂ : TrExprS Hc.venv c.lparams Hc.chk.vlctx e₂ e₂') :
    ((monadLift (TypeChecker.isDefEq e₁ e₂) : AddInductive.M Bool) c).WF fun b =>
      b → Hc.venv.IsDefEqU c.lparams.length Hc.chk.vlctx.toCtx e₁' e₂' :=
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
    TypeChecker.M.run c.env c.safety {}
      (c.typeCheckerLParams.getD c.lparams) c.fuel
      (TypeChecker.checkType type)).WF _
  have hno : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkTypeInContext.WF (Hc.withCheckLCtx {} Hc.baseNil)
      (hclosed.mono fun _ h => False.elim h)

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
