import Lean4Lean.Verify.Inductive.Nested.CompilationDataConstructors
import Lean4Lean.Verify.Inductive.Nested.RestoredRecursorTypes
import Lean4Lean.Verify.Inductive.Nested.WhnfHitShape

/-! Restored recursor list of the canonical restored block of a validated
nested run.

The recursor entries of `canonicalRestoredBlock` are the translations of the
restored recursors of the executable restoration folds: the primary recursors
selected by the source semantic trace, then the auxiliary recursors selected by
the auxiliary shape trace. Each of these is the abstract restoration
(`Restoration.recursor`) of the generated recursor of the same owner, so the
`recursors` field of `NestedCompilationPending` holds. -/


namespace Lean4Lean
namespace InductiveSignature

/-! ### Totality of restoration

`Restoration.expr` fails exactly at a restoration head applied to fewer
arguments than its parameter count, or at the wrong universe arity.
`Restoration.SpineOK r e k` states that neither happens in `e` when `e` is
applied to `k` further arguments. -/

/-- No restoration head of `e`, applied to `k` further arguments, is partially
applied or at the wrong universe arity. -/
def Restoration.SpineOK (r : Restoration) : VExpr → Nat → Prop
  | .app f a, k => r.SpineOK f (k + 1) ∧ r.SpineOK a 0
  | .const name levels, k => ∀ h, r.heads.find? (fun h => h.auxiliary == name) = some h →
      levels.length = h.uvars ∧ h.nparams ≤ k
  | .lam d b, _ => r.SpineOK d 0 ∧ r.SpineOK b 0
  | .forallE d b, _ => r.SpineOK d 0 ∧ r.SpineOK b 0
  | .proj _ _ e, _ => r.SpineOK e 0
  | .bvar _, _ => True
  | .sort _, _ => True
  | .elim .., _ => True

theorem Restoration.go_isSome_of_spineOK (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr), r.SpineOK e args.length →
      ∃ v, Restoration.expr.go r e args = some v
  | .bvar i, args, _ => ⟨_, rfl⟩
  | .sort u, args, _ => ⟨_, rfl⟩
  | .elim .., args, _ => ⟨_, rfl⟩
  | .app f a, args, H => by
    obtain ⟨a', ha⟩ := r.go_isSome_of_spineOK a [] H.2
    obtain ⟨v, hv⟩ := r.go_isSome_of_spineOK f (a' :: args) H.1
    exact ⟨v, by simp only [Restoration.expr.go, ha, Option.bind_eq_bind,
      Option.bind_some, hv]⟩
  | .const name levels, args, H => by
    simp only [Restoration.expr.go]
    cases hf : r.heads.find? (fun h => h.auxiliary == name) with
    | none => exact ⟨_, rfl⟩
    | some h =>
      obtain ⟨hl, hn⟩ := H h hf
      simp only [HeadSpecialization.apply, hl, bne_self_eq_false, Bool.false_or]
      have : ¬ args.length < h.nparams := by omega
      simp [this]
  | .lam d b, args, H => by
    obtain ⟨d', hd⟩ := r.go_isSome_of_spineOK d [] H.1
    obtain ⟨b', hb⟩ := r.go_isSome_of_spineOK b [] H.2
    exact ⟨_, by simp only [Restoration.expr.go, hd, hb, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩
  | .forallE d b, args, H => by
    obtain ⟨d', hd⟩ := r.go_isSome_of_spineOK d [] H.1
    obtain ⟨b', hb⟩ := r.go_isSome_of_spineOK b [] H.2
    exact ⟨_, by simp only [Restoration.expr.go, hd, hb, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩
  | .proj n i e, args, H => by
    obtain ⟨e', he⟩ := r.go_isSome_of_spineOK e [] H
    exact ⟨_, by simp only [Restoration.expr.go, he, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩

theorem Restoration.spineOK_of_go (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr) (v : VExpr),
      Restoration.expr.go r e args = some v → r.SpineOK e args.length
  | .bvar i, args, _, _ => trivial
  | .sort u, args, _, _ => trivial
  | .elim .., args, _, _ => trivial
  | .app f a, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases ha : Restoration.expr.go r a [] with
    | none => simp [ha] at H
    | some a' =>
      simp only [ha, Option.bind_some] at H
      exact ⟨r.spineOK_of_go f (a' :: args) v H, r.spineOK_of_go a [] a' ha⟩
  | .const name levels, args, v, H => by
    intro h hf
    simp only [Restoration.expr.go, hf, HeadSpecialization.apply] at H
    by_cases hl : levels.length = h.uvars
    · by_cases hn : args.length < h.nparams
      · simp [hl, hn] at H
      · exact ⟨hl, by omega⟩
    · simp [hl] at H
  | .lam d b, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases hd : Restoration.expr.go r d [] with
    | none => simp [hd] at H
    | some d' =>
      cases hb : Restoration.expr.go r b [] with
      | none => simp [hd, hb] at H
      | some b' => exact ⟨r.spineOK_of_go d [] d' hd, r.spineOK_of_go b [] b' hb⟩
  | .forallE d b, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases hd : Restoration.expr.go r d [] with
    | none => simp [hd] at H
    | some d' =>
      cases hb : Restoration.expr.go r b [] with
      | none => simp [hd, hb] at H
      | some b' => exact ⟨r.spineOK_of_go d [] d' hd, r.spineOK_of_go b [] b' hb⟩
  | .proj n i e, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases he : Restoration.expr.go r e [] with
    | none => simp [he] at H
    | some e' => exact r.spineOK_of_go e [] e' he

/-- Restoration is defined exactly on the expressions without partially
applied restoration heads. -/
theorem Restoration.expr_isSome_iff (r : Restoration) (e : VExpr) :
    (∃ v, r.expr e = some v) ↔ r.SpineOK e 0 :=
  ⟨fun ⟨v, h⟩ => r.spineOK_of_go e [] v h, fun h => r.go_isSome_of_spineOK e [] h⟩

theorem Restoration.spineOK_mkApps (r : Restoration) :
    ∀ (f : VExpr) (args : List VExpr) (k : Nat),
      r.SpineOK (VExpr.mkApps f args) k ↔
        r.SpineOK f (k + args.length) ∧ ∀ a ∈ args, r.SpineOK a 0
  | f, [], k => by simp [VExpr.mkApps]
  | f, a :: as, k => by
    have hm : VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as := rfl
    rw [hm, r.spineOK_mkApps (.app f a) as k]
    simp only [Restoration.SpineOK, List.mem_cons, forall_eq_or_imp, List.length_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by rwa [show k + (as.length + 1) = k + as.length + 1 by omega], h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by rwa [show k + (as.length + 1) = k + as.length + 1 by omega] at h1, h2⟩, h3⟩

theorem Restoration.spineOK_wrapForalls (r : Restoration) :
    ∀ (ds : List VExpr) (b : VExpr),
      r.SpineOK (VExpr.wrapForalls ds b) 0 ↔ (∀ d ∈ ds, r.SpineOK d 0) ∧ r.SpineOK b 0
  | [], b => by simp [VExpr.wrapForalls]
  | d :: ds, b => by
    have := r.spineOK_wrapForalls ds b
    simp only [VExpr.wrapForalls, List.foldr_cons] at this ⊢
    simp only [Restoration.SpineOK, this, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem Restoration.spineOK_wrapLams (r : Restoration) :
    ∀ (ds : List VExpr) (b : VExpr),
      r.SpineOK (VExpr.wrapLams ds b) 0 ↔ (∀ d ∈ ds, r.SpineOK d 0) ∧ r.SpineOK b 0
  | [], b => by simp [VExpr.wrapLams]
  | d :: ds, b => by
    have := r.spineOK_wrapLams ds b
    simp only [VExpr.wrapLams, List.foldr_cons] at this ⊢
    simp only [Restoration.SpineOK, this, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem Restoration.spineOK_liftN (r : Restoration) (n : Nat) :
    ∀ (e : VExpr) (j k : Nat), r.SpineOK (e.liftN n j) k ↔ r.SpineOK e k
  | .bvar i, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .sort u, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .const c us, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .elim .., j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .app f a, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n f, r.spineOK_liftN n a]
  | .proj m i e, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n e]
  | .lam d b, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n d, r.spineOK_liftN n b]
  | .forallE d b, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n d, r.spineOK_liftN n b]

theorem Restoration.spineOK_vars (r : Restoration) (n below : Nat) :
    ∀ a ∈ vars n below, r.SpineOK a 0 := by
  intro a ha
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at ha
  obtain ⟨_, _, rfl⟩ := ha
  trivial


theorem Restoration.spineOK_insertBinders (r : Restoration) (ds : List VExpr) (c : Nat) :
    (∀ d ∈ insertBinders ds c, r.SpineOK d 0) ↔ ∀ d ∈ ds, r.SpineOK d 0 := by
  simp only [insertBinders, List.mem_map, Prod.exists, forall_exists_index, and_imp]
  constructor
  · intro H d hd
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    have := H _ d i (List.mk_mem_zipIdx_iff_getElem?.mpr hi) rfl
    exact (r.spineOK_liftN c d i 0).mp this
  · rintro H _ d i hdi rfl
    exact (r.spineOK_liftN c d i 0).mpr (H d (List.fst_mem_of_mem_zipIdx hdi))

private theorem mem_zipIdx_of_mem {l : List α} {x : α} (h : x ∈ l) :
    ∃ i, (x, i) ∈ l.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩

theorem Restoration.spineOK_constructorApp (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) (extra below : Nat) :
    r.SpineOK (g.constructorApp ctor extra below) 0 ↔
      r.SpineOK (.const ctor.name g.levels) (s.params.length + ctor.fields.length) := by
  rw [Instance.constructorApp, r.spineOK_mkApps]
  simp only [List.length_append, vars, List.length_map, List.length_reverse,
    List.length_range, Nat.zero_add]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

/-- The pieces of a minor premise whose restoration determines the
restoration of the corresponding equation. -/
structure Restoration.MinorPiecesOK (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) : Prop where
  fields : ∀ d ∈ (s.fieldTypes ctor).map (·.instL g.levels), r.SpineOK d 0
  indices : ∀ e ∈ ctor.indices, r.SpineOK (e.instL g.levels) 0
  head : r.SpineOK (.const ctor.name g.levels) (s.params.length + ctor.fields.length)
  binders : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∀ e ∈ fr.2.binders, r.SpineOK (e.instL g.levels) 0
  recIndices : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∀ e ∈ fr.2.indices,
    r.SpineOK (e.instL g.levels) 0

theorem Restoration.minorPiecesOK (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) (prior : Nat)
    (H : r.SpineOK (g.minor ctor prior) 0) : r.MinorPiecesOK g ctor := by
  simp only [Instance.minor] at H
  rw [r.spineOK_wrapForalls, r.spineOK_mkApps] at H
  obtain ⟨Hdoms, -, Hargs⟩ := H
  have Hfields : ∀ d ∈ insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
      (s.families.size + prior), r.SpineOK d 0 :=
    fun d hd => Hdoms d (List.mem_append_left _ hd)
  rw [r.spineOK_insertBinders] at Hfields
  have Hihs : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∃ i,
      r.SpineOK (g.hypothesis ctor prior i fr.1 fr.2) 0 := by
    intro fr hfr
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hfr
    refine ⟨i, Hdoms _ (List.mem_append_right _ ?_)⟩
    exact List.mem_map.mpr ⟨(fr, i), hi, rfl⟩
  refine ⟨Hfields, ?_, ?_, ?_, ?_⟩
  · intro e he
    have := Hargs _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this
  · have := Hargs _ (List.mem_append_right _ List.mem_cons_self)
    exact (r.spineOK_constructorApp g ctor _ _).mp this
  · intro fr hfr e he
    obtain ⟨i, Hi⟩ := Hihs fr hfr
    simp only [Instance.hypothesis] at Hi
    rw [r.spineOK_wrapForalls] at Hi
    obtain ⟨j, hj⟩ := mem_zipIdx_of_mem he
    have := Hi.1 _ (List.mem_map.mpr ⟨(e, j), hj, rfl⟩)
    simp only [Instance.underFields] at this
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this
  · intro fr hfr e he
    obtain ⟨i, Hi⟩ := Hihs fr hfr
    simp only [Instance.hypothesis] at Hi
    rw [r.spineOK_wrapForalls, r.spineOK_mkApps] at Hi
    have := Hi.2.2 _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    simp only [Instance.underFields] at this
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this

/-- A generated recursor name that is not a restoration head is restorable at
any spine length. -/
theorem Restoration.spineOK_const_of_find_none (r : Restoration) {name : Name}
    {levels : List VLevel} (h : r.heads.find? (fun h => h.auxiliary == name) = none)
    (k : Nat) : r.SpineOK (.const name levels) k := by
  intro h' hf
  rw [h] at hf
  cases hf

/-- **Totality of equation restoration.** If restoration is defined on the
generated recursor types and no generated recursor name is a restoration
head, restoration is defined on every generated equation. -/
theorem Instance.restoredEquations_isSome (r : Restoration) {s : InductiveSignature}
    (g : Instance s)
    (hrec : ∀ owner, ∃ t, r.expr (g.recursorType owner) = some t)
    (hnames : ∀ owner, r.heads.find? (fun h => h.auxiliary == g.recursorName owner) = none) :
    ∃ rules, g.restoredEquations r = some rules := by
  have Hequation : ∀ index : Fin s.constructors.size,
      ∃ e, r.equation (g.equation index) = some e := by
    intro index
    let ctor := s.constructors[index]
    obtain ⟨t, ht⟩ := hrec ctor.owner
    obtain ⟨pre, major, hpre, -, -⟩ := r.expr_recursorType_eq_some ht
    have Hpre : ∀ d ∈ g.recursorPrefix ctor.owner, r.SpineOK d 0 := by
      intro d hd
      obtain ⟨d', -, hd'⟩ := Lean4Lean.List.Forall₂.forall_exists_l
        (List.mapM_eq_some.mp hpre) d hd
      exact (r.expr_isSome_iff d).mp ⟨d', hd'⟩
    simp only [Instance.recursorPrefix, List.mem_append] at Hpre
    have Hparams : ∀ d ∈ g.params, r.SpineOK d 0 := fun d hd => Hpre d (.inl (.inl (.inl hd)))
    have Hmotives : ∀ d ∈ g.motives, r.SpineOK d 0 :=
      fun d hd => Hpre d (.inl (.inl (.inr hd)))
    have Hminors : ∀ d ∈ g.minors, r.SpineOK d 0 := fun d hd => Hpre d (.inl (.inr hd))
    have hminor : g.minor ctor index.val ∈ g.minors := by
      refine List.mem_map.mpr ⟨(ctor, index.val), ?_, rfl⟩
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      simp [ctor]
    have M := r.minorPiecesOK g ctor index.val (Hminors _ hminor)
    have Hdomains : ∀ d ∈ g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
          (s.families.size + s.constructors.size), r.SpineOK d 0 := by
      intro d hd
      simp only [List.mem_append] at hd
      rcases hd with ((hd | hd) | hd) | hd
      · exact Hparams d hd
      · exact Hmotives d hd
      · exact Hminors d hd
      · exact (r.spineOK_insertBinders _ _).mpr M.fields d hd
    have Hindices : ∀ a ∈ ctor.indices.map (fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) ctor.fields.length), r.SpineOK a 0 := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [r.spineOK_liftN]
      exact M.indices e he
    have Hmajor : r.SpineOK (g.constructorApp ctor
        (s.families.size + s.constructors.size) 0) 0 :=
      (r.spineOK_constructorApp g ctor _ _).mpr M.head
    have Hcalls : ∀ fr ∈ Instance.recursiveFields (s := s) ctor,
        r.SpineOK (g.recursiveCall ctor fr.1 fr.2) 0 := by
      intro fr hfr
      simp only [Instance.recursiveCall, recursorHead]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨?_, r.spineOK_const_of_find_none (hnames _) _, ?_⟩
      · intro d hd
        simp only [List.mem_map, Prod.exists] at hd
        obtain ⟨e, j, hej, rfl⟩ := hd
        simp only [Instance.underFields]
        rw [r.spineOK_liftN, r.spineOK_liftN]
        exact M.binders fr hfr e (List.fst_mem_of_mem_zipIdx hej)
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with (ha | ha) | rfl
        · exact r.spineOK_vars _ _ a ha
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
          simp only [Instance.underFields]
          rw [r.spineOK_liftN, r.spineOK_liftN]
          exact M.recIndices fr hfr e he
        · rw [r.spineOK_mkApps]
          exact ⟨trivial, r.spineOK_vars _ _⟩
    have Hlhs : r.SpineOK (g.equation index).lhs 0 := by
      simp only [Instance.equation, recursorHead]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨Hdomains, r.spineOK_const_of_find_none (hnames _) _, ?_⟩
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · exact r.spineOK_vars _ _ a ha
      · exact Hindices a ha
      · exact Hmajor
    have Hrhs : r.SpineOK (g.equation index).rhs 0 := by
      simp only [Instance.equation]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨Hdomains, trivial, ?_⟩
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact r.spineOK_vars _ _ a ha
      · obtain ⟨fr, hfr, rfl⟩ := List.mem_map.mp ha
        exact Hcalls fr hfr
    have Htype : r.SpineOK (g.equation index).type 0 := by
      simp only [Instance.equation]
      rw [r.spineOK_wrapForalls, r.spineOK_mkApps]
      refine ⟨Hdomains, trivial, ?_⟩
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Hindices a ha
      · exact Hmajor
    obtain ⟨lhs, hlhs⟩ := (r.expr_isSome_iff _).mpr Hlhs
    obtain ⟨rhs, hrhs⟩ := (r.expr_isSome_iff _).mpr Hrhs
    obtain ⟨type, htype⟩ := (r.expr_isSome_iff _).mpr Htype
    exact ⟨{ g.equation index with lhs := lhs, rhs := rhs, type := type },
      by simp [Restoration.equation, hlhs, hrhs, htype]⟩
  have key : ∀ l : List (Fin s.constructors.size),
      ∃ rules, (l.map (fun index => g.equation index)).mapM r.equation = some rules := by
    intro l
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a l ih =>
      obtain ⟨rules, hrules⟩ := ih
      obtain ⟨e, he⟩ := Hequation a
      exact ⟨e :: rules, by simp [List.mapM_cons, he, hrules]⟩
  exact key _

end InductiveSignature
end Lean4Lean

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-! ### The recursor steps selected by the restoration traces -/

/-- The data of a restored recursor step fixing its translated constant. -/
def RestoredRecursorStepValue (env : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv) (w : VConstVal) : Prop :=
  w.name = Hstep.restored.newRecName ∧
    Hstep.restored.newInfo.levelParams.length = w.uvars ∧
    TrExprS env Hstep.restored.newInfo.levelParams []
      Hstep.restored.newInfo.type w.type

/-- The primary recursors of a source semantic trace, one per source family,
each the translation of the restored recursor at the family's recursor name. -/
theorem RestoredSourceInductiveSemanticTrace.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (fun (indType : InductiveType) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
          auxRec allIndNames (Lean.mkRecName indType.name) s t),
          RestoredRecursorStepValue envCtors Hstep w)
      types recursors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    refine .cons ⟨_, _, Hstep.restored.recursor, Hrecursor.name, ?_, ?_⟩ ih
    · rw [Hstep.restored.recursor.restored.restoration.levelParams]
      exact Hrecursor.uvars
    · rw [Hstep.restored.recursor.restored.restoration.levelParams]
      exact Hrecursor.type

/-- The auxiliary recursors of an auxiliary shape trace, one per restored
recursor name, each the translation of the restored recursor at that name. -/
theorem RestoredAuxiliaryShapeTrace.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    (H : RestoredAuxiliaryShapeTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules) :
    ∃ added, finalRecursors = priorRecursors ++ added ∧
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
          ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
            auxRec allIndNames name s t),
            RestoredRecursorStepValue trEnv Hstep w)
        names added := by
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
    obtain ⟨added, hfinal, Hadded⟩ := ih
    obtain ⟨⟨_, huvars, htype⟩, hname⟩ := Hsemantic.translated
    refine ⟨Hsemantic.recursor :: added, by simp [hfinal], .cons ⟨_, _, Hstep,
      ?_, huvars, htype⟩ Hadded⟩
    rw [← Hstep.restored.restoration.name]
    exact hname.symm

/-! ### One restored recursor -/

/-- The lowered recursor read back by a restoration step at a generated
owner's recursor name realizes the owner's generated recursor metadata. -/
theorem NestedValidatedRunResult.recursorMetadataOfStep
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    RecursorMetadataRealization E.production.production.completed.canonicalGeneration
      E.production.production.completed.outVEnv owner Hstep.oldInfo := by
  rcases E.production.production.completed.metadataRealization owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.production.production.entries.length := by
    rw [show E.production.production.entries =
      E.production.production.completed.entries from rfl,
      E.production.production.completed.entries_length_eq]
    exact owner.isLt
  have hmem := List.getElem_mem (l := E.production.production.entries)
    (n := owner.val) hlen
  have hfind := E.production.production.findRecursorOfMem
    (info := (E.production.production.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.production.production.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  rw [heq] at M
  exact M

/-- **One restored recursor.** The translation of the restored recursor of a
restoration step at a generated owner's lowered recursor name is the abstract
restoration (`Restoration.recursor`) of the owner's generated recursor, given
the hit shape of the lowered recursor type and the freshness of the
restorable names in the translation environment. -/
theorem NestedValidatedRunResult.restoredRecursor_of_step
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {oldRecName : Name} {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) oldRecName stepSource stepTarget)
    (hname : oldRecName =
      E.production.production.completed.canonicalGeneration.recursorName owner)
    (Hshape : Expr.HitShapeTele
      ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
      result.nparams (lparams.map Level.param) Hstep.oldInfo.type)
    {targetEnv : VEnv}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      targetEnv.constants n = none)
    {w : VConstVal} (Hw : RestoredRecursorStepValue targetEnv Hstep w) :
    (compilationRestoration sourceDecl auxiliaries).recursor
      (E.production.production.completed.canonicalGeneration.recursor owner) =
        some w := by
  subst hname
  obtain ⟨hwname, hwuvars, Ht⟩ := Hw
  have M := E.recursorMetadataOfStep owner Hstep
  have Hs := M.type
  rcases E.loweredRecursorParameterTelescope owner Hstep with ⟨suffix, Htel⟩
  have hclosed : Closed Hstep.oldInfo.type := by
    simpa [VLCtx.bvars] using Hs.closed
  have Hinput : Hstep.oldInfo.type.FVarsIn fun _ => False :=
    Hs.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h
  have htype : (compilationRestoration sourceDecl auxiliaries).expr
      (E.production.production.completed.canonicalGeneration.recursorType owner) =
        some w.type :=
    Hstep.restored.restoration.typeRestorationCommutes' hparamsSize
      (D.agreement targetEnv _) hscoped.argumentsClosed Hfresh Hshape
      (fun Hopen => Hopen.restoredBody_closed D Htel hclosed) Htel Hinput hclosed Hs Ht
  have hrecName : (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.production.production.completed.canonicalGeneration.recursorName owner) =
        w.name := by
    rw [D.recursorName, hwname, Hstep.restored.mappedName]
    exact (nameMap_getD_eq _ _ _).symm
  have huvars : E.production.production.completed.canonicalGeneration.uvars = w.uvars := by
    rw [← M.uvars, ← hwuvars, Hstep.restored.restoration.levelParams]
  simp only [Restoration.recursor, InductiveSignature.Instance.recursor, htype,
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, hrecName]
  rcases w with ⟨⟨wu, wt⟩, wn⟩
  simp only at huvars
  rw [huvars]

/-! ### Freshness of the restorable names in the source constructor environment -/

private theorem forall₂_take' {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.take k) (r.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons]
    exact .cons h (forall₂_take' t k)

/-- The source constructor names are constructor names of the source prefix of
the lowered declaration. -/
theorem NestedFinalAssemblyShape.sourceConstructorNames
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety) :
    ∀ c ∈ decl.constructorConstants,
      c.name ∈ familyNames (C.production.loweredDecl.types.take decl.types.length) := by
  intro c hc
  obtain ⟨src, hsrc, hcsrc⟩ := List.mem_flatMap.mp hc
  have HT := forall₂_take' C.formationAssembly.types decl.types.length
  rw [List.take_left' rfl, C.formationExpanded] at HT
  obtain ⟨t, ht, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT src hsrc
  obtain ⟨c', hc', hcc⟩ := Lean4Lean.List.Forall₂.forall_exists_l hT.constructors c hcsrc
  rw [← hcc.name]
  exact mem_familyNames_of_ctor ht hc'

/-- The restorable names of the compilation restoration of a validated nested
run are fresh in the source constructor environment. -/
theorem NestedValidatedRunResult.restorableNames_fresh_ctors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hctorNames : ∀ c ∈ sourceDecl.constructorConstants,
      c.name ∈ familyNames (E.production.loweredDecl.types.take sourceDecl.types.length))
    {envCtors : VEnv}
    (hctors : envTypes.addConstVals sourceDecl.constructorConstants = some envCtors) :
    ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envCtors.constants name = none := by
  have hfreshTypes := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  intro name hname
  cases hc : envCtors.constants name with
  | none => rfl
  | some ci =>
    exfalso
    rcases VEnv.addConstVals_lookup_origin hctors hc with hbase | ⟨entry, hentry, hn, -⟩
    · rw [hfreshTypes name hname] at hbase; cases hbase
    · have hsrc := hctorNames entry hentry
      rw [hn] at hsrc
      rcases List.mem_append.mp hname with h | h
      · rw [hheadNames] at h
        exact (List.nodup_append.mp hfamNodup).2.2 _ hsrc _ h rfl
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        have hp1 : p.1 ∈ auxiliaries.map (fun a => a.auxiliary.str "rec") := by
          rw [← compilationRestoration_recursors_fst]
          exact List.mem_map_of_mem hp
        obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp1
        have haux : a.auxiliary ∈
            (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
          rw [← auxiliarySpecializations_names Haux Hexpansion]
          exact List.mem_map_of_mem ha
        obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
        have h1 : p.1 ∈ familyNames E.production.loweredDecl.types := by
          have : familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ⊆
              familyNames E.production.loweredDecl.types := by
            intro x hx
            obtain ⟨t', ht', hx'⟩ := mem_familyNames.mp hx
            exact mem_familyNames.mpr ⟨t', List.mem_of_mem_take ht', hx'⟩
          exact this hsrc
        have h2 : p.1 ∈ E.production.loweredDecl.types.map
            (fun t => t.name.str "rec") := by
          rw [← hpa, ← hta]
          exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
            (List.mem_of_mem_drop ht)
        exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl

/-! ### The order of the restored recursors -/

private theorem forall₂_map_eq {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → l.map f = r.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.map_cons, hR _ _ h, forall₂_map_eq hR t]

/-- The generated recursor names, in owner order, are the recursor names of
the source families followed by the auxiliary recursor names restored by the
executable auxiliary fold. -/
theorem NestedValidatedRunResult.recursorNames_order
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnonempty : sourceTypes ≠ []) :
    (List.finRange
        E.production.production.completed.generationSignature.families.size).map
        E.production.production.completed.canonicalGeneration.recursorName =
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
  let P := E.production
  have hentries : P.production.entries.length = P.indTypes.toList.length := by
    rw [P.production.generated.length, P.production.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length P.constructors.core]
  -- generated names in owner order
  have hgen : (List.finRange
        E.production.production.completed.generationSignature.families.size).map
        E.production.production.completed.canonicalGeneration.recursorName =
      P.indTypes.toList.map (fun t => Lean.mkRecName t.name) := by
    have hN : E.production.production.completed.generationSignature.families.size =
        P.indTypes.toList.length := by
      rw [← E.production.production.completed.entries_length_eq]
      exact hentries
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange]; exact hN
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      have hiE : i < P.production.entries.length := by
        rw [hentries]; simpa using hi'
      obtain ⟨owner, hown, h⟩ := E.recursorOwnerOfEntry hiE
      have : owner = ⟨i, by simpa using hi⟩ := Fin.ext hown
      subst this
      rw [← h]
      congr 2
      have hi'' : i < P.indTypes.size := by simpa using hi'
      rw [getElem!_pos P.indTypes i hi'', Array.getElem_toList]
  -- source and lowered names
  have hloweredNames : P.indTypes.toList.map (·.name) =
      P.loweredDecl.types.map (·.name) :=
    forall₂_map_eq (fun a b h => h.header.name.symm) P.constructors.core.types
  have hsourceNames : sourceTypes.map (·.name) =
      (P.loweredDecl.types.take sourceTypes.length).map (·.name) :=
    forall₂_map_eq (fun a b h => h.name.symm) E.nativeSource.sourceHeaders
  have hsplit : P.indTypes.toList.map (·.name) =
      sourceTypes.map (·.name) ++
        (P.indTypes.toList.drop sourceTypes.length).map (·.name) := by
    rw [hsourceNames, List.map_take, ← hloweredNames, ← List.map_take,
      ← List.map_append, List.take_append_drop]
  -- the auxiliary recursor names
  obtain ⟨main, rest, rfl⟩ : ∃ main rest, sourceTypes = main :: rest := by
    cases sourceTypes with
    | nil => exact absurd rfl hnonempty
    | cons main rest => exact ⟨main, rest, rfl⟩
  obtain ⟨o, os, hos⟩ : ∃ o os, P.indTypes.toList = o :: os := by
    cases h : P.indTypes.toList with
    | nil => rw [h] at hsplit; simp at hsplit
    | cons o os => exact ⟨o, os, rfl⟩
  have hoName : o.name = main.name := by
    rw [hos] at hsplit
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at hsplit
    exact hsplit.1
  have Hc : ContextWF P.c := by
    rw [E.production_c]; exact E.productionContextWF
  obtain ⟨info, hfind, -, hall⟩ := P.production.findSourceHeader Hc
    (owner := o) (by rw [hos]; exact List.mem_cons_self)
  rw [hoName] at hfind
  have haux : (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 =
      (P.indTypes.toList.drop (main :: rest).length).map
        (fun t => Lean.mkRecName t.name) := by
    by_cases hlength : (main :: rest).length < info.all.length
    · rw [mkAuxRecNameMap_recNames main rest E.loweredEnv info hfind hlength, hall,
        ← List.map_drop, List.map_map]
      rfl
    · have hlength' : ¬ rest.length + 1 < info.all.length := by
        simpa using hlength
      have hnil : (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 = [] := by
        simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength']
        rfl
      rw [hnil]
      have : P.indTypes.toList.drop (main :: rest).length = [] := by
        apply List.drop_eq_nil_of_le
        have := congrArg List.length hall
        simp only [List.length_map] at this
        omega
      rw [this]; rfl
  rw [hgen, haux]
  conv => lhs; rw [← List.take_append_drop (main :: rest).length P.indTypes.toList]
  rw [List.map_append]
  congr 1
  have h := congrArg (List.take (main :: rest).length) hsplit
  rw [List.take_left' (by simp), ← List.map_take] at h
  have h2 := congrArg (List.map Lean.mkRecName) h
  simpa only [List.map_map, Function.comp_def] using h2

/-! ### The restored recursor list -/

/-- The recursor entries of the canonical restored block, in owner order:
each is the abstract restoration of the owner's generated recursor and the
translation of the restored recursor of a restoration step at the owner's
lowered recursor name. -/
theorem NestedValidatedRunResult.restoredRecursorEntries_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    List.Forall₂ (fun owner w =>
        (compilationRestoration sourceDecl auxiliaries).recursor
          (E.production.production.completed.canonicalGeneration.recursor owner) = some w ∧
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
          RestoredRecursorStepValue
            ((C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections
              sourceDecl.projectionEntries) Hstep w)
      (List.finRange
        E.production.production.completed.generationSignature.families.size)
      (C.primaryRecursors ++ C.auxiliaryRecursors) := by
  let r := compilationRestoration sourceDecl auxiliaries
  let trEnv := (C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections sourceDecl.projectionEntries
  -- freshness of the restorable names in the translation environment
  have htypesEq : C.canonical.venvTypes = envTypes := by
    have h := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.canonical.venvCtors := by
    have h := C.canonical.ctorsAdded.abstract
    rwa [C.constructorValues, htypesEq] at h
  have hctorNames := C.sourceConstructorNames
  rw [hC] at hctorNames
  have Hfresh : ∀ n ∈ r.restorableNames, trEnv.constants n = none := by
    intro n hn
    simp only [trEnv, VEnv.addEliminators_constants, VEnv.addProjections_constants]
    exact E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup hctorNames
      hctorsAdded n hn
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  -- the recursor steps selected by the two traces
  have Hprimary := C.sourceSemantics.recursorSteps
  obtain ⟨added, hadded', Hadded⟩ := C.auxiliarySemantics.recursorSteps
  simp only [List.nil_append] at hadded'
  rw [← hadded'] at Hadded
  have Hall : List.Forall₂ (fun (name : Name) (w : VConstVal) =>
      ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) name s t),
        RestoredRecursorStepValue trEnv Hstep w)
      ((List.finRange
          E.production.production.completed.generationSignature.families.size).map
          E.production.production.completed.canonicalGeneration.recursorName)
      (C.primaryRecursors ++ C.auxiliaryRecursors) := by
    have hnonempty : sourceTypes ≠ [] := C.sourceNonempty
    rw [E.recursorNames_order hnonempty]
    exact Lean4Lean.List.Forall₂.append_of_left (by
        rw [List.length_map]; exact Lean4Lean.List.Forall₂.length_eq Hprimary) |>.mpr
      ⟨List.forall₂_map_left_iff.mpr Hprimary, Hadded⟩
  rw [List.forall₂_map_left_iff] at Hall
  refine Lean4Lean.List.Forall₂.imp ?_ Hall
  rintro owner w ⟨s, t, Hstep, Hw⟩
  have Hshape := (E.recursorHitShape' wf Hsources owner Hstep).1
  rw [← hheads] at Hshape
  exact ⟨E.restoredRecursor_of_step hparamsSize D hscoped owner Hstep rfl Hshape
    Hfresh Hw, s, t, Hstep, Hw⟩



/-- **The `recursors` field of `NestedCompilationPending`.** For the
specializations of `restorationTablesRestoringAll`, the restored generated
recursor list of the lowered declaration is exactly the recursor list of the
canonical restored block (via `NestedValidatedRunResult.recursorHitShape'`). -/
theorem NestedValidatedRunResult.restoredRecursors_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    E.production.compilationInstance.restoredRecursors
        (compilationRestoration sourceDecl auxiliaries) =
      some (canonicalRestoredBlock sourceDecl C.primaryRecursors
        C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).recursors := by
  have Hrec := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1)
    (E.restoredRecursorEntries_of_hitShape C hC wf Hsources hadded Haux Hexpansion hnodup
      hparamsSize D hscoped)
  show List.mapM _ ((List.finRange _).map _) = _
  rw [List.mapM_map]
  exact List.mapM_eq_some.mpr Hrec

/-- Two restoration steps at the same lowered recursor name read back the
same lowered recursor and restore it to the same recursor. -/
theorem RestoredRecursorStep.info_eq
    (H₁ : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s₁ t₁)
    (H₂ : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s₂ t₂) :
    H₁.oldInfo = H₂.oldInfo ∧ H₁.restored.newInfo = H₂.restored.newInfo := by
  have h : some (ConstantInfo.recInfo H₁.oldInfo) = some (.recInfo H₂.oldInfo) :=
    H₁.lookup.symm.trans H₂.lookup
  have hold : H₁.oldInfo = H₂.oldInfo := by
    injection h with h
    injection h
  refine ⟨hold, ?_⟩
  rw [H₁.restored.produced, H₂.restored.produced, hold]

/-- **Shape fields of the restored recursors.** For every generated owner and
every restoration step at the owner's lowered recursor name, the final
abstract environment of the assembly shape stores the restored recursor at
the abstract restoration of the owner's generated recursor type, and the
restored recursor's parameter, index, motive and minor counts are the
signature's. These are the `type`, `numParams`, `numIndices`, `numMotives`
and `numMinors` clauses of `RestoredRecursorShapeInputs`. -/
theorem NestedValidatedRunResult.restoredRecursorShapeFields
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    ∀ (owner : Fin E.production.production.completed.generationSignature.families.size)
      {s t : Environment}
      (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name))
        (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
      (∃ type, (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.production.completed.canonicalGeneration.recursorType owner) =
            some type ∧
        C.finalBaseVEnv.constants Hstep.restored.newInfo.name =
          some ⟨Hstep.restored.newInfo.levelParams.length, type⟩) ∧
      Hstep.restored.newInfo.numParams =
        E.production.production.completed.generationSignature.params.length ∧
      Hstep.restored.newInfo.numIndices =
        E.production.production.completed.generationSignature.families[owner].indices.length ∧
      Hstep.restored.newInfo.numMotives =
        E.production.production.completed.generationSignature.families.size ∧
      Hstep.restored.newInfo.numMinors =
        E.production.production.completed.generationSignature.constructors.size := by
  intro owner s t Hstep
  have Hentries := E.restoredRecursorEntries_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  obtain ⟨w, hw, hrec, s', t', Hstep', hwname, hwuvars, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l Hentries owner (List.mem_finRange owner)
  obtain ⟨hold, hnew⟩ := Hstep'.info_eq Hstep
  have M := E.recursorMetadataOfStep owner Hstep
  have R := Hstep.restored.restoration
  refine ⟨?_, R.numParams.trans M.numParams, R.numIndices.trans M.numIndices,
    R.numMotives.trans M.numMotives, R.numMinors.trans M.numMinors⟩
  have hadd := C.canonical.recursorsAdded.abstract
  rw [C.recursorValues] at hadd
  have hconst := VEnv.addConstVals_get hadd hw
  simp only [Restoration.recursor, InductiveSignature.Instance.recursor,
    Option.bind_eq_bind, Option.pure_def] at hrec
  cases ht : (compilationRestoration sourceDecl auxiliaries).expr
      (E.production.production.completed.canonicalGeneration.recursorType owner) with
  | none => simp [ht] at hrec
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at hrec
    refine ⟨type, rfl, ?_⟩
    have hname : Hstep.restored.newInfo.name = w.name := by
      rw [hwname, ← hnew, Hstep'.restored.restoration.name]
    have hwtype : w.type = type := by rw [← hrec]
    rw [hname, hconst, ← hnew, hwuvars, ← hwtype]

/-- `RestoredRecursorShapeInputs` for the rule-free copy of the restored
recursor of every restoration step at a generated owner's lowered recursor
name, in the final abstract environment of the assembly shape, modulo its `k`
and `specialization` clauses (named hypotheses `hk` and `hspecialization`). -/
theorem NestedValidatedRunResult.restoredRecursorShapeInputs_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    ∀ (owner : Fin E.production.production.completed.generationSignature.families.size)
      {s t : Environment}
      (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name))
        (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
      Hstep.restored.newInfo.k = false →
      (∃ head : RestoredFamilyHead,
        Hstep.restored.newInfo.getMajorInduct = head.name ∧
        (∀ arg ∈ head.arguments,
          arg.ClosedN E.production.production.completed.generationSignature.params.length) ∧
        (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.production.completed.canonicalGeneration.familyApp owner
            (vars E.production.production.completed.generationSignature.params.length
              (E.production.production.completed.generationSignature.families.size +
                E.production.production.completed.generationSignature.constructors.size +
                E.production.production.completed.generationSignature.families[owner].indices.length))
            (vars E.production.production.completed.generationSignature.families[owner].indices.length
              0)) =
          some (VExpr.mkApps (.const head.name head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (E.production.production.completed.generationSignature.families.size +
                E.production.production.completed.generationSignature.constructors.size +
                E.production.production.completed.generationSignature.families[owner].indices.length)) ++
              vars E.production.production.completed.generationSignature.families[owner].indices.length
                0))) →
      RestoredRecursorShapeInputs E.production.production.completed.canonicalGeneration
        (compilationRestoration sourceDecl auxiliaries) C.finalBaseVEnv owner
        { Hstep.restored.newInfo with rules := [] } := by
  intro owner s t Hstep hk hspecialization
  obtain ⟨htype, hp, hi, hm, hn⟩ := E.restoredRecursorShapeFields C hC wf Hsources hadded Haux
    Hexpansion hnodup hparamsSize D hscoped owner Hstep
  exact ⟨htype, hp, hi, hm, hn, hk, hspecialization⟩

/-! ### `CompilationData` with an arbitrary equation list

`NestedValidatedRunResult.compilationData_of_specializations`
(`Nested/CompilationDataAssembly.lean`), with the rule lists of the canonical
restored block arbitrary: no field of `CompilationData` but `equations`
mentions the block's rules. -/


private theorem forall₂_take_rba {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.take k) (r.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons]
    exact .cons h (forall₂_take_rba t k)

private theorem forall₂_drop_rba {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.drop k) (r.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k + 1 => by
    simp only [List.drop_succ_cons]
    exact forall₂_drop_rba t k

private theorem forall₂_append_left_split_rba {R : α → β → Prop}
    {l₁ l₂ : List α} {r : List β} (H : List.Forall₂ R (l₁ ++ l₂) r) :
    List.Forall₂ R l₁ (r.take l₁.length) ∧
      List.Forall₂ R l₂ (r.drop l₁.length) := by
  have h₁ := forall₂_take_rba H l₁.length
  have h₂ := forall₂_drop_rba H l₁.length
  simp only [List.take_left', List.drop_left'] at h₁ h₂
  exact ⟨h₁, h₂⟩

private theorem forall₂_of_map_eq_rba {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, l.map f = r.map g →
      List.Forall₂ (fun a b => f a = g b) l r
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq_rba h.2)

private theorem forall₂_swap_rba {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r →
      List.Forall₂ (fun b a => R a b) r l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_swap_rba t)

private theorem forall₂_join_rba {R : α → β → Prop} {S : γ → β → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ}, List.Forall₂ R l m →
      List.Forall₂ S n m → List.Forall₂ (fun a c => ∃ b, R a b ∧ S c b) l n
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons ⟨_, h, h'⟩ (forall₂_join_rba t t')

/-- `compilationData_of_specializations` at arbitrary rule lists. -/
theorem NestedValidatedRunResult.compilationData_of_specializations_rules
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    {primaryRules auxiliaryRules : List VDefEq}
    {envTypes : VEnv} {auxiliaries : List ContainerSpecialization}
    (htypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (hnames : auxiliaries.map (·.auxiliary) =
      (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    (hwellFormed : ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
      E.production.constructors.completed.parameterScope.toCtx.reverse)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hdirect : ∀ (U : Nat) (params : List VExpr), ∃ direct,
      auxiliaries.mapM (fun a => a.directFamily U params) = some direct ∧
      List.Forall₂ (DirectFamilyShape U) auxiliaries direct)
    (Hpending : NestedCompilationPending
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.production.compilationSignature E.production.compilationInstance
      auxiliaries
      (canonicalRestoredBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors
        primaryRules auxiliaryRules)) :
    CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.production.loweredDecl E.production.compilationSignature
      E.production.compilationInstance auxiliaries
      (canonicalRestoredBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors
        primaryRules auxiliaryRules) := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hexpanded : C.formationAssembly.expanded = E.production.loweredDecl := by
    rw [C.formationExpanded, hC]
  have HexpandedSource : E.production.loweredDecl.SourceWF
      (ves.venv (if isUnsafe then .unsafe else .safe)) :=
    hexpanded ▸ C.formationAssembly.expandedSource
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.consumedGeneration.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceNonempty : sourceDecl.types ≠ [] := by
    rw [C.typesSource]; simp
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.production.loweredDecl.typeConstants =
        some E.production.constructors.completed.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.completed.headerVEnv) hinit)
      E.production.constructors.completed.core.typesAdded
  have hloweredCtors := E.production.constructors.completed.core.ctorsAdded
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hlowered := VEnv.addConstVals_append hloweredTypes hloweredCtors
  have hrecursorsAdded := E.production.production.installed.abstract
  have hrecursorValues : E.production.production.entries.map Prod.snd =
      E.production.compilationInstance.recursors :=
    E.production.production.completed.canonicalRecursors
  rw [hrecursorValues] at hrecursorsAdded
  have hrecursorsFresh := VEnv.addConstVals_names_fresh hrecursorsAdded
  simp only [VEnv.addEliminators_constants, VEnv.addProjections_constants] at hrecursorsFresh
  have hctorFresh : ∀ recursor ∈ E.production.compilationInstance.recursors,
      E.production.constructors.completed.ctorVEnv.constants recursor.name = none :=
    hrecursorsFresh.2
  have HsourceWF := TrInductDeclCore.sourceWF_ofNonempty Hsource hsourceNonempty
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars :=
    hexpanded ▸ C.formationAssembly.uvars
  refine {
    sourceWF := HsourceWF
    sourceParameters := C.formationAssembly.sourceParameters
    expandedWF := HexpandedSource
    headerPrefix := by
      have h := E.nativeSource.sourceTypeValues
      rw [E.nativeSourceDecl_eq] at h
      rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
    expandedFormation := hexpanded ▸ C.formationAssembly.expandedFormation
    model := Hmodels
    uvars := hexpanded ▸ C.formationAssembly.uvars
    nparams := hexpanded ▸ C.formationAssembly.nparams
    safety := hexpanded ▸ C.formationAssembly.isUnsafe
    restorationScoped := hscoped
    correspondence := by
      have hparams : E.production.compilationSignature.params =
          E.production.constructors.completed.parameterScope.toCtx.reverse :=
        E.production.loweredConstruction.consumedGeneration.params
      obtain ⟨direct, hmapM, hshapes⟩ :=
        hdirect sourceDecl.uvars E.production.compilationSignature.params
      refine ⟨envTypes, direct, htypes, hmapM, hparams ▸ hwellFormed, ?_⟩
      have HT := C.formationAssembly.types
      rw [hexpanded] at HT
      obtain ⟨HTsource, HTgenerated⟩ := forall₂_append_left_split_rba HT
      have HM := Hmodels.families
      have hle := VEnv.addConstVals_le htypes
      have hsplit := List.take_append_drop sourceDecl.types.length
        E.production.compilationSignature.declaration.types
      rw [← hsplit]
      have hprefixLength :
          (E.production.compilationSignature.declaration.types.take
            sourceDecl.types.length).length = sourceDecl.types.length := by
        rw [Lean4Lean.List.Forall₂.length_eq (forall₂_take_rba HM sourceDecl.types.length)]
        exact (Lean4Lean.List.Forall₂.length_eq HTsource).symm
      refine (Lean4Lean.List.Forall₂.append_of_left hprefixLength).mpr ⟨?_, ?_⟩
      · have HMp := forall₂_take_rba HM sourceDecl.types.length
        have HP := Hpending.sourceConstructors envTypes htypes
        obtain ⟨_, _, _, hheaders, _, _⟩ := C.formationAssembly.sourceParameters
        have H1 := forall₂_join_rba HMp HTsource
        refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and H1 HP))
        rintro a src ⟨⟨⟨x, hM, hT⟩, hP⟩, ha, hsrc⟩
        have hres : a.resultLevel ≈ src.resultLevel := by
          rw [← hT.resultLevel]; exact hM.2.2.2.1
        obtain ⟨domains, body, exprType, _, htype, hbody⟩ := (hheaders src hsrc).header
        refine ⟨hM.1.trans hT.name, hM.2.1.trans hT.uvars,
          hM.2.2.1.trans hT.numIndices, hres,
          ⟨domains, body, src.resultLevel, exprType, hres.symm, htype.mono hle,
            hbody.mono hle⟩, ?_⟩
        have Hnames := Lean4Lean.List.Forall₂.trans
          (fun _ _ _ h1 h2 => h1.trans h2.name)
          (forall₂_of_map_eq_rba (f := VConstVal.name) (g := VConstVal.name) hM.2.2.2.2) (forall₂_swap_rba hT.constructors)
        refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and Hnames hP))
        rintro n c ⟨⟨hname, hRT⟩, hn, hc⟩
        refine ⟨hname, ?_, hRT⟩
        rw [E.production.compilationSignature.declaration_ctor_uvars a
          (List.mem_of_mem_take ha) n hn, Hmodels.uvars, hloweredUvars,
          HsourceWF.2.2.2.1 c (List.mem_flatMap.mpr ⟨src, hsrc, hc⟩)]
      · have HMd := forall₂_drop_rba HM sourceDecl.types.length
        have HP := Hpending.auxiliaryFamilies envTypes direct htypes hmapM
        have Hnames := forall₂_of_map_eq_rba (f := ContainerSpecialization.auxiliary)
          (g := fun t : VInductiveType => t.name) hnames
        have Hdirect := forall₂_join_rba (forall₂_swap_rba Hnames) (forall₂_swap_rba hshapes)
        have H1 := forall₂_join_rba HMd (forall₂_swap_rba Hdirect)
        refine Lean4Lean.List.Forall₂.imp ?_
          (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and H1 HP))
        rintro a d ⟨⟨⟨x, hM, aux, hname, hshape⟩, hP⟩, ha, _⟩
        refine ⟨hM.1.trans (hname.symm.trans hshape.name.symm), ?_, hP.1, hP.2.1,
          hP.2.2.1, hP.2.2.2⟩
        rw [E.production.compilationSignature.declaration_type_uvars a
          (List.mem_of_mem_drop ha), Hmodels.uvars, hloweredUvars, hshape.uvars]
    admissible := ⟨_, hloweredTypes,
      E.production.loweredConstruction.consumedGeneration.admissible⟩
    recursiveTypesWF := by
      refine ⟨_, _, E.production.constructors.completed.eliminators, hloweredTypes,
        hloweredCtors, ?_, ?_, ?_⟩
      · have hown := E.production.constructors.completed.eliminatorsOrdinary.own
        generalize E.production.constructors.completed.eliminators = es at hown ⊢
        rw [hinit] at hown
        exact hown
      · rw [← E.production.constructors.completed.contextVEnv]
        exact E.production.loweredConstruction.consumedGeneration.recursiveTypesWF
      · rw [← E.production.constructors.completed.contextVEnv]
        exact E.production.loweredConstruction.consumedGeneration.familyTypesWF
    familyTypesWF := by
      refine ⟨_, _, E.production.constructors.completed.eliminators, hloweredTypes,
        hloweredCtors, ?_, ?_⟩
      · have hown := E.production.constructors.completed.eliminatorsOrdinary.own
        generalize E.production.constructors.completed.eliminators = es at hown ⊢
        rw [hinit] at hown
        exact hown
      · rw [← E.production.constructors.completed.contextVEnv]
        exact E.production.loweredConstruction.consumedGeneration.familyTypesWF
    recursorNames := E.production.loweredConstruction.consumedGeneration.names
    generatedNames := by
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨VEnv.addConstVals_names_nodup hlowered,
        hrecursorsFresh.1, ?_⟩
      intro x hx y hy hxy
      subst hxy
      rcases List.mem_map.mp hx with ⟨ci, hci, rfl⟩
      rcases List.mem_map.mp hy with ⟨recursor, hrecursor, hname⟩
      have hsome := VEnv.addConstVals_get hlowered hci
      rw [← hname, hctorFresh recursor hrecursor] at hsome
      cases hsome
    recursorsFresh := by
      intro recursor hrecursor
      cases hbase : (ves.venv (if isUnsafe then .unsafe else .safe)).constants
          recursor.name with
      | none => rfl
      | some c =>
        have := (VEnv.addConstVals_le hlowered).constants hbase
        rw [hctorFresh recursor hrecursor] at this
        cases this
    types := rfl
    ctors := rfl
    projections := rfl
    recursors := Hpending.recursors
    equations := Hpending.equations
    names := by
      have hvalues :
          (C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map
              Prod.snd =
            (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors primaryRules auxiliaryRules).types ++
              (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors primaryRules auxiliaryRules).ctors ++
              (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors primaryRules auxiliaryRules).recursors := by
        simp only [List.map_append, canonicalRestoredBlock]
        rw [C.typeValues, C.constructorValues, C.recursorValues]
      rw [← hvalues]
      exact VEnv.addConstVals_names_nodup C.canonical.productionTrace.abstract }


/-! ### Generated recursor names are not restoration heads -/

/-- Every generated recursor name is the recursor name of a lowered family. -/
theorem NestedValidatedRunResult.recursorName_mem_lowered
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.production.production.completed.generationSignature.families.size) :
    E.production.production.completed.canonicalGeneration.recursorName owner ∈
      E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
  have hiE : owner.val < E.production.production.entries.length := by
    rw [show E.production.production.entries =
      E.production.production.completed.entries from rfl,
      E.production.production.completed.entries_length_eq]
    exact owner.isLt
  obtain ⟨owner', hown, h⟩ := E.recursorOwnerOfEntry hiE
  have : owner' = owner := Fin.ext hown
  subst this
  rw [← h]
  have hloweredNames : E.production.indTypes.toList.map (·.name) =
      E.production.loweredDecl.types.map (·.name) :=
    forall₂_map_eq (fun a b h => h.header.name.symm) E.production.constructors.core.types
  have hlt : owner'.val < E.production.indTypes.size := by
    have := E.production.production.generated.length
    rw [E.production.production.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        E.production.constructors.core] at this
    rw [this] at hiE
    simpa using hiE
  have hmem : E.production.indTypes[owner'.val]!.name ∈
      E.production.indTypes.toList.map (·.name) := by
    rw [getElem!_pos E.production.indTypes owner'.val hlt]
    exact List.mem_map_of_mem (Array.getElem_mem_toList hlt)
  rw [hloweredNames] at hmem
  obtain ⟨t, ht, hname⟩ := List.mem_map.mp hmem
  rw [← hname]
  exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec") ht

/-- No generated recursor name is a restoration head. -/
theorem NestedValidatedRunResult.recursorName_not_head
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (owner : Fin E.production.production.completed.generationSignature.families.size) :
    (compilationRestoration sourceDecl auxiliaries).heads.find?
        (fun h => h.auxiliary ==
          E.production.production.completed.canonicalGeneration.recursorName owner) =
      none := by
  apply List.find?_eq_none.mpr
  intro h hh heq
  have heq' : h.auxiliary =
      E.production.production.completed.canonicalGeneration.recursorName owner := by
    simpa using heq
  have hmem : h.auxiliary ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
      (·.auxiliary) := List.mem_map_of_mem hh
  rw [compilationRestoration_heads_auxiliary,
    auxiliarySpecializations_headNames Haux Hexpansion] at hmem
  have h1 : h.auxiliary ∈ familyNames E.production.loweredDecl.types := by
    obtain ⟨t, ht, hx⟩ := mem_familyNames.mp hmem
    exact mem_familyNames.mpr ⟨t, List.mem_of_mem_drop ht, hx⟩
  have h2 := E.recursorName_mem_lowered owner
  rw [← heq'] at h2
  exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl

/-! ### `CompilationData` of a validated nested run -/

/-- **`CompilationData` of a validated nested run from the hit-shape
provenance.** For the specializations of `restorationTablesRestoringAll`:

* the restored generated recursor list is the recursor list of the canonical
  restored block (`restoredRecursors_of_hitShape`), unconditionally (see
  `recursorHitShape'`);
* given totality of restoration on the normalized constructor types
  (`normalizedTotal`, the hypothesis of `compilationData_of_pending'`),
  restoration is defined on every generated equation, and the canonical
  restored block with the restored equations as its rules is the block of a
  `CompilationData` (`Instance.restoredEquations_isSome`);
* given moreover that the final assembly shape's own rule lists are the
  restored equations, its canonical restored block is the block of a
  `CompilationData`.

The rule lists of an arbitrary `NestedFinalAssemblyShape` are not determined
by its fields (`VInductDecl.NestedIotaRule` leaves the binder domains and the
recursive-call arguments of the right-hand side free, and
`RestoredAuxiliaryStepShape` fixes only the number and guardedness of the
auxiliary rules), so the last item keeps that identity as a hypothesis. -/
theorem NestedValidatedRunResult.compilationData_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production) :
    ∃ (envTypes : VEnv) (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      auxiliaries.flatMap (·.headNames) =
        familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
      CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (∀ params : List VExpr,
        VEnv.IsDefEqCtx envTypes sourceDecl.uvars [] params.reverse
          E.production.headers.commonParameterContext →
        ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl params) ∧
      (∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
        E.production.constructors.completed.parameterScope.toCtx.reverse) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ (U : Nat) (params : List VExpr), ∃ direct,
        auxiliaries.mapM (fun a => a.directFamily U params) = some direct ∧
        List.Forall₂ (DirectFamilyShape U) auxiliaries direct) ∧
      (∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
        result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            (a.constructorName ctor)) ∧
      (∀ name, (compilationRestoration sourceDecl auxiliaries).recursorName name =
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.find? name).getD
          name) ∧
      (E.production.compilationInstance.restoredRecursors
          (compilationRestoration sourceDecl auxiliaries) =
        some (canonicalRestoredBlock sourceDecl C.primaryRecursors
          C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).recursors ∧
      ((∀ normalized ∈ E.production.compilationSignature.declaration.types,
          ∀ ctor ∈ normalized.ctors, ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored) →
        (∃ rules, E.production.compilationInstance.restoredEquations
            (compilationRestoration sourceDecl auxiliaries) = some rules ∧
          Nonempty (CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
            sourceDecl E.production.loweredDecl E.production.compilationSignature
            E.production.compilationInstance auxiliaries
            (canonicalRestoredBlock sourceDecl C.primaryRecursors
              C.auxiliaryRecursors rules []))) ∧
        (E.production.compilationInstance.restoredEquations
            (compilationRestoration sourceDecl auxiliaries) =
          some (canonicalRestoredBlock sourceDecl C.primaryRecursors
            C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).rules →
          Nonempty (CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
            sourceDecl E.production.loweredDecl E.production.compilationSignature
            E.production.compilationInstance auxiliaries
            (canonicalRestoredBlock sourceDecl C.primaryRecursors
              C.auxiliaryRecursors C.primaryRules C.auxiliaryRules))))) := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hP := E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnames, hheadNames, -, -, hwellFormed, hscoped, hdirect, -⟩ := hP
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames
  have hrecursors := E.restoredRecursors_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  refine ⟨envTypes, auxiliaries,
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D ⟨hrecursors, ?_⟩⟩
  intro htotal
  have HsourceCtors := E.sourceConstructors_of_evidence wf hadded henvTypes Haux Hexpansion
    hnodup hfresh hrecFresh
    ⟨E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring hlevels,
      fun n hn => htotal n (List.mem_of_mem_take hn)⟩
  have HauxFamilies := E.auxiliaryFamiliesField_of_evidence wf hadded henvTypes Haux
    Hexpansion
    (E.auxiliaryConstructors_of_evidence wf Hsources hadded henvTypes Haux Hexpansion
      HauxRestoring hnodup (fun n hn => htotal n (List.mem_of_mem_drop hn)))
  refine ⟨?_, fun hequations => ⟨E.compilationData_of_specializations C hC hadded hnames
    hwellFormed hscoped hdirect
    { sourceConstructors := HsourceCtors
      auxiliaryFamilies := HauxFamilies
      recursors := hrecursors
      equations := hequations }⟩⟩
  -- totality of equation restoration
  have hrecTypes : ∀ owner, ∃ t, r.expr
      (E.production.compilationInstance.recursorType owner) = some t := by
    intro owner
    have Hall := List.mapM_eq_some.mp hrecursors
    have hmem : E.production.compilationInstance.recursor owner ∈
        E.production.compilationInstance.recursors :=
      List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩
    obtain ⟨w, -, hw⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hall _ hmem
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hw
    cases ht : r.expr (E.production.compilationInstance.recursor owner).type with
    | none => simp [r, ht] at hw
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrules⟩ := E.production.compilationInstance.restoredEquations_isSome r
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  refine ⟨rules, hrules, ⟨E.compilationData_of_specializations_rules C hC hadded hnames
    hwellFormed hscoped hdirect
    { sourceConstructors := HsourceCtors
      auxiliaryFamilies := HauxFamilies
      recursors := hrecursors
      equations := by simpa [canonicalRestoredBlock] using hrules }⟩⟩

end VerifyInductive
end Lean4Lean
