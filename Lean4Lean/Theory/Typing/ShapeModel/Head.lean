import Lean4Lean.Theory.Typing.HeadSeparationModel
import Lean4Lean.Theory.Typing.ShapeModel.Sound

/-!
# Head classification in the shape model, and separation

The shape model (`Interp`, read at the base valuation `Valuation.nil`) is an instance of the
`HeadModel` interface (`Theory/Typing/HeadSeparationModel.lean`), so it yields the separation
half of `VEnv.HeadInversion` (`headSeparation_of_shapeModel`).

* `Shape.headOf`, `TShape.headOf`: the head class of a shape (sort with its level, Pi, rigid
  former with its name and levels, other). Compatible non-bottom shapes have the same head
  (`TShape.headOf_compat`).
* `head D`: the head of a set of approximations, that of any non-bottom element (chosen
  classically), `other` if there is none. For the approximations of one term all non-bottom
  elements have the same head (`Interp.compat`), so `head` is well defined (`head_eq`).
* `head_sort`, `head_forallE`, `head_rigid`: the heads of sorts, Pi types, and rigid
  applications typed at a sort. `head_rigid` uses the soundness theorem (the typing records of
  the spine), the `rigid` clause of `Const` and the typing filter of `Interp.const`.
* `headModel_of_shapeModel` (with `headModel_of_shapeModel_compositional`) and
  `headSeparation_of_shapeModel`.

The facts about the environment used beyond `SemSig.EnvFactsIn env env` are collected in
`SemSig.HeadFacts`; see the docstring of each field.

Deviations from the milestone specification:
* `headModel_of_shapeModel` is a `def`, not a `theorem`: `HeadModel` carries data.
* The environment hypothesis is `env.Ordered` (what `sound_nil` and `IsDefEq.strong` need);
  `VEnv.WF.ordered` gives it for well-formed environments
  (`headSeparation_of_shapeModel_of_wf`).
* `SemSig.HeadFacts.ctorType` only asks for the constructor's type to be, up to a derivation in
  the empty context, a telescope ending in an application of a rigid former (its family, at any
  levels and arguments); the number of binders is not needed. It does not ask the family to be
  a non-constructor, only to head no rule: a sort telescope shape approximates neither a rigid
  shape nor a constructor shape (`Interp.nestPi_fam_absurd`). For a real environment, that the
  family of a constructor is not itself a constructor is a consequence of head inversion when the
  constructor is a major of a generic eliminator equation outside the constructor table, so it
  is not available here.
* `SemSig.HeadFacts.famType` is a chain of two derivations (the declared type to a telescope,
  the telescope to the telescope ending in the sort): composing them into one derivation needs
  uniqueness of typing, and the model only needs each step to be sound.
* For the signature of a well-formed environment the head facts are proved in
  `EnvSigHead.lean` (`envSig_headFacts`), and `Separation.lean` assembles
  `headSeparation_of_valid`.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

/-! ### Head classification of shapes -/

/-- The head class of a shape. -/
def Shape.headOf : ∀ {n}, Shape n → HeadClass
  | 0, .sort r | _+1, .sort r => .sort r
  | _+1, .forallE _ _ => .pi
  | _+1, .rigid c ls _ _ => .rigid c ls
  | _, _ => .other

theorem Shape.headOf_bot : (Shape.bot : Shape n).headOf = .other := by cases n <;> rfl

theorem Shape.headOf_lift {s : Shape n} (h : n ≤ m) : (s.lift m).headOf = s.headOf := by
  cases n with
  | zero =>
    cases s with
    | bot =>
      exact (congrArg Shape.headOf (Shape.lift_bot (n := 0) (m := m))).trans
        (by rw [headOf_bot]; rfl)
    | sort r =>
      exact (congrArg Shape.headOf (Shape.lift_sort (n := 0) (m := m) (r := r))).trans
        (by cases m <;> rfl)
  | succ n =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    cases s <;> rfl

/-- Compatible non-bottom shapes have the same head class. -/
theorem Shape.headOf_compat {s t : Shape n} (h : s.Compat t) (hs : s ≠ .bot) (ht : t ≠ .bot) :
    s.headOf = t.headOf := by
  cases n with
  | zero =>
    cases s <;> cases t <;> simp_all [Shape.Compat, Shape.headOf] <;>
      first | exact absurd rfl hs | exact absurd rfl ht
  | succ n =>
    cases s <;> cases t <;> simp_all [Shape.Compat, Shape.headOf] <;>
      first | exact absurd rfl hs | exact absurd rfl ht

noncomputable section

variable [ShapeParams]

/-- The head class of a shape at any depth. -/
def TShape.headOf (x : TShape) : HeadClass := x.2.1.headOf

theorem TShape.val_ne_bot {x : TShape} (h : ¬x ≤ .bot) : x.2.1 ≠ .bot :=
  fun e => h (TShape.le_bot.2 (WShape.ext e))

/-- Compatible non-bottom shapes have the same head class. -/
theorem TShape.headOf_compat {x y : TShape} (h : x.Compat y) (hx : ¬x ≤ .bot) (hy : ¬y ≤ .bot) :
    x.headOf = y.headOf := by
  have h1 := Nat.le_max_left x.1 y.1; have h2 := Nat.le_max_right x.1 y.1
  have hc : Shape.Compat (x.2.lift (max x.1 y.1)).1 (y.2.lift (max x.1 y.1)).1 := h
  rw [WShape.lift_val h1, WShape.lift_val h2] at hc
  unfold TShape.headOf
  rw [← Shape.headOf_lift (s := x.2.1) h1, ← Shape.headOf_lift (s := y.2.1) h2]
  exact Shape.headOf_compat hc (mt (Shape.lift_eq_bot h1).1 (TShape.val_ne_bot hx))
    (mt (Shape.lift_eq_bot h2).1 (TShape.val_ne_bot hy))

open Classical in
/-- The head class of a set of approximations: that of a non-bottom element if there is one,
`other` otherwise. -/
def head (D : TShape → Prop) : HeadClass :=
  if h : ∃ m, D m ∧ ¬m ≤ TShape.bot then (Classical.choose h).headOf else .other

/-- `head` is well defined on sets of pairwise compatible shapes: it is the head class of any
non-bottom element. -/
theorem head_eq {D : TShape → Prop} (hD : ∀ {m₁ m₂}, D m₁ → D m₂ → m₁.Compat m₂)
    (hm : D m) (hnb : ¬m ≤ TShape.bot) : head D = m.headOf := by
  have h : ∃ m, D m ∧ ¬m ≤ TShape.bot := ⟨m, hm, hnb⟩
  rw [head, dif_pos h]
  have ⟨h1, h2⟩ := Classical.choose_spec h
  exact TShape.headOf_compat (hD h1 hm) h2 hnb

theorem head_of_le_bot {D : TShape → Prop} (hD : ∀ m, D m → m ≤ TShape.bot) :
    head D = .other := by
  rw [head, dif_neg]; exact fun ⟨m, h1, h2⟩ => h2 (hD m h1)

theorem TShape.sort_not_le_bot : ¬TShape.sort r ≤ .bot := fun h => by
  have := TShape.le_bot.1 h; cases congrArg (·.1) this

theorem TShape.forallE_not_le_sort {b : WShape n} {f : WShapeFun n} :
    ¬(WShape.forallE b f).T ≤ TShape.sort r := by
  intro h
  rw [TShape.LE.def (m := n+1) (Nat.le_refl _) (Nat.zero_le _)] at h
  simp only [TShape.sort, WShape.lift_sort, WShape.lift_self] at h
  rcases WShape.le_sort.1 h with e | e <;> cases congrArg (·.1) e

theorem TShape.rigid_not_le_bot {l : List (WShape n)} {t} :
    ¬(WShape.rigid c ls l t).T ≤ .bot := fun h => by
  have := TShape.le_bot.1 h; cases congrArg (·.1) this

theorem TShape.forallE_not_le_bot {b : WShape n} {f : WShapeFun n} :
    ¬(WShape.forallE b f).T ≤ .bot := fun h => by
  have := TShape.le_bot.1 h; cases congrArg (·.1) this

end

/-! ### The facts about the environment read by the head classification -/

/-- The facts about the environment `env` and the semantic signature that the head
classification reads, besides `SemSig.EnvFactsIn env env`. Each is a property of real
environments, to be proved when the signature is built. -/
structure SemSig.HeadFacts [S : SemSig] (env : VEnv) : Prop where
  /-- A constant heading a computation rule of the signature is not rigid in the environment
  (rigidity, `VEnv.Rigid`, only looks at the definitional rules `env.defeqs`; the signature's
  rules headed by a constant are its delta and quotient rules). -/
  ruleNotRigid : ∀ {r c}, S.rules r → r.head = .const c → ¬env.Rigid c
  /-- The constructors of a family are declared constructors. -/
  famCtors : ∀ {c c'}, c' ∈ S.famCtors c → ∃ ci k, env.constants c' = some ci ∧ S.ctor c' = some k
  /-- The type of a family is, up to a derivation in the empty context, a telescope ending in
  the family's sort. -/
  famType : ∀ {c l ci}, S.famLevel c = some l → env.constants c = some ci →
    ∃ W doms T T', env.IsDefEq ci.uvars [] ci.type W T ∧
      env.IsDefEq ci.uvars [] W (VExpr.wrapForalls doms (.sort l)) T'
  /-- The type of a constructor is, up to a derivation in the empty context, a telescope ending
  in an application of its family, which heads no rule. -/
  ctorType : ∀ {c k ci}, S.ctor c = some k → env.constants c = some ci →
    (∀ r, S.rules r → r.head ≠ .const k.family) ∧
    ∃ doms ls args T, env.IsDefEq ci.uvars [] ci.type
      (VExpr.wrapForalls doms (VExpr.mkApps (.const k.family ls) args)) T

/-! ### Heads at the base valuation -/

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

theorem head_interp (hm : Interp env ρ m e) (hnb : ¬m ≤ TShape.bot) :
    head (fun m => Interp env ρ m e) = m.headOf :=
  head_eq (fun h1 h2 => Interp.compat h1 h2) hm hnb

theorem head_sort : head (fun m => Interp env .nil m (.sort u)) = .sort u.eval := by
  rw [head_interp Interp.sort' TShape.sort_not_le_bot]; rfl

theorem head_forallE : head (fun m => Interp env .nil m (.forallE A B)) = .pi := by
  have : Interp env .nil (WShape.forallE (n := 0) .bot .bot).T (.forallE A B) :=
    .forallE' .bot .bot (WShape.HasDom.bot (.bot' .sort_type)) fun x _ => by
      rw [WShapeFun.bot_app]; exact .bot
  rw [head_interp this TShape.forallE_not_le_bot]; rfl

theorem Interp.forallE_cases (H : Interp env ρ m (.forallE A B)) :
    m ≤ .bot ∨ ∃ n, ∃ b : WShape n, ∃ f, m ≤ (WShape.forallE b f).T := by
  cases H with
  | bot => exact .inl TShape.bot_eqv.1
  | forallE _ _ _ _ h => exact .inr ⟨_, _, _, h⟩

theorem Interp.sort_not_forallE (H : Interp env ρ (TShape.sort r) (.forallE A B)) : False := by
  rcases Interp.forallE_cases H with h | ⟨_, _, _, h⟩
  · exact TShape.sort_not_le_bot h
  · exact TShape.sort_not_le_forallE h

/-- A telescope shape ending in a sort that approximates a telescope ending in a sort has the
same number of binders, and the two sorts have the same level. -/
theorem Interp.nestPi_sort_inv {ps : List (TShape × TShape)} {Ds : List VExpr}
    (H : Interp env ρ (nestPi ps (TShape.sort r)) (Ds.foldr .forallE (.sort l))) :
    r = l.eval := by
  induction ps generalizing ρ Ds with
  | nil =>
    cases Ds with
    | nil => exact TShape.sort_le_sort H.le_sort
    | cons D Ds => exact (Interp.sort_not_forallE H).elim
  | cons p ps ih =>
    cases Ds with
    | nil => exact absurd H.le_sort TShape.forallE_not_le_sort
    | cons D Ds => exact ih (Interp.pi_inv H).2

/-- The approximations of a constant heading no rule, applied to arguments, are bottom, a
lambda, a constructor shape or a rigid shape. -/
theorem Interp.headless_inv (hr : ∀ r, SemSig.rules r → r.head ≠ .const s)
    (H : Interp env ρ m (VExpr.mkApps (.const s ls) args)) :
    m ≤ .bot ∨ (∃ n, ∃ g : WShapeFun n, m ≤ (WShape.lam' g).T) ∨
    (∃ n, ∃ c, ∃ fs : List (WShape n), m ≤ (WShape.ctor' c fs).T) ∨
    ∃ n, ∃ c ls', ∃ l : List (WShape n), ∃ t, m ≤ (WShape.rigid c ls' l t).T := by
  rcases Interp.mkApps_const_inv hr H with h | ⟨n, rargs, y, hC, hy, -⟩
  · exact .inl h
  cases hC with
  | bot => exact .inl (hy.trans TShape.bot_eqv.1)
  | lam _ h2 => exact .inr (.inl ⟨_, _, hy.trans h2⟩)
  | ctor _ _ _ h4 => exact .inr (.inr (.inl ⟨_, _, _, hy.trans h4⟩))
  | rigid _ _ _ _ _ h6 => exact .inr (.inr (.inr ⟨_, _, _, _, _, hy.trans h6⟩))
  | rule h1 h2 => cases hr _ h1 h2
  | ruleAB h1 h2 => cases hr _ h1 h2
  | ruleC h1 h2 => cases hr _ h1 h2

/-- A telescope shape ending in a sort does not approximate a telescope ending in an application
of a constant heading no rule (a rigid former, or even a constructor). -/
theorem Interp.nestPi_fam_absurd (hr : ∀ r, SemSig.rules r → r.head ≠ .const s)
    {ps : List (TShape × TShape)} {Ds : List VExpr}
    (H : Interp env ρ (nestPi ps (TShape.sort r))
      (Ds.foldr .forallE (VExpr.mkApps (.const s ls) args))) : False := by
  induction ps generalizing ρ Ds with
  | nil =>
    cases Ds with
    | nil =>
      rcases Interp.headless_inv hr H with h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
      · exact TShape.sort_not_le_bot h
      · exact TShape.sort_not_le_lam' h
      · exact TShape.sort_not_le_ctor' h
      · exact TShape.sort_not_le_rigid h
    | cons D Ds => exact Interp.sort_not_forallE H
  | cons p ps ih =>
    cases Ds with
    | nil =>
      rcases Interp.headless_inv hr H with h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
      · exact TShape.forallE_not_le_bot h
      · exact TShape.forallE_not_le_lam' h
      · exact TShape.forallE_not_le_ctor' h
      · exact TShape.forallE_not_le_rigid h
    | cons D Ds => exact ih (Interp.pi_inv H).2

theorem onCtx_levelWF : ∀ {Γ}, OnCtx Γ (env.IsType U) → OnCtx Γ fun _ A => A.LevelWF U
  | [], _ => trivial
  | _::_, ⟨h1, _, h2⟩ => ⟨onCtx_levelWF h1, (h2.levelWF (onCtx_levelWF h1)).1⟩

theorem VExpr.LevelWF.mkApps_fn :
    ∀ {args : List VExpr} {f : VExpr}, (VExpr.mkApps f args).LevelWF U → f.LevelWF U
  | [], _, h => h
  | _ :: _, _, h => (VExpr.LevelWF.mkApps_fn (f := .app _ _) h).1

theorem forall₂_bot (ρ : Valuation) :
    ∀ l : List VExpr, List.Forall₂ (fun x A => Interp env ρ x A) (l.map fun _ => TShape.bot) l
  | [] => .nil
  | _ :: l => .cons .bot (forall₂_bot ρ l)

theorem forall₂_wbot (ρ : Valuation) :
    ∀ l : List VExpr, List.Forall₂ (fun x A => Interp env ρ (WShape.T x) A)
      (l.map fun _ => (WShape.bot : WShape 0)) l
  | [] => .nil
  | _ :: l => .cons .bot (forall₂_wbot ρ l)

/-- Transport an approximation of an instance of a constant type along a derivation of its
type in the empty context. -/
theorem interp_instL_of_defeq (henv : env.Ordered) (hEF : SemSig.EnvFactsIn env env)
    (hextra : ∀ df, env.defeqs df → ExtraValid env df) (helim : ElimValidIn env env)
    (hD : env.IsDefEq U₀ [] X Y T) (hls : ∀ l ∈ ls, l.WF U)
    (H : Interp env .nil m (X.instL ls)) : Interp env .nil m (Y.instL ls) :=
  (sound_nil henv hEF hextra helim (hD.instL hls (U' := U)) trivial m).1 H

/-- A rigid former applied to arguments and typed at a sort has a rigid head recording the
former and its evaluated levels. -/
theorem head_rigid (henv : env.Ordered) (hEF : SemSig.EnvFactsIn env env)
    (hHF : SemSig.HeadFacts env)
    (hextra : ∀ df, env.defeqs df → ExtraValid env df) (helim : ElimValidIn env env)
    (hΓ : OnCtx Γ (env.IsType U)) (hc : env.Rigid c)
    (H : env.HasType U Γ (.mkApps (.const c ls) args) (.sort u)) :
    head (fun m => Interp env .nil m (.mkApps (.const c ls) args)) =
      .rigid c (ls.map (·.eval)) := by
  have hcl : ConstClosed env := hEF.constClosed
  have hS : StrongSound env Γ (VExpr.mkApps (.const c ls) args.reverse.reverse) (.sort u) := by
    rw [List.reverse_reverse]
    exact (StrongSoundEq.of_isDefEqStrong VEnv.LE.rfl hEF
      (fun _ h => ⟨(henv.closed.2 h).1.1, (henv.closed.2 h).2.1⟩) hextra helim
      (H.strong henv hΓ)).left
  have W : Valuation.Fits env Γ Γ .nil := .nil
  obtain ⟨ci, v, hci, hlsl, -⟩ := Spine.constInfo hS
  have hls : ∀ l ∈ ls, l.WF U :=
    VExpr.LevelWF.mkApps_fn (H.levelWF (onCtx_levelWF hΓ)).1
  have hr : ∀ r, SemSig.rules r → r.head ≠ .const c := fun r h1 h2 =>
    hHF.ruleNotRigid h1 h2 hc
  obtain ⟨qs, -, -, -, hq⟩ := Spine.typed W hS hci (forall₂_bot .nil args.reverse)
    (R := TShape.sort u.eval) Interp.sort'
  cases hk : SemSig.ctor c with
  | some k =>
    exfalso
    obtain ⟨hIr, doms, ls', args', T, hD⟩ := hHF.ctorType hk hci
    have := interp_instL_of_defeq henv hEF hextra helim hD hls hq
    rw [VExpr.wrapForalls, VExpr.instL_foldr_forallE, VExpr.instL_mkApps] at this
    exact Interp.nestPi_fam_absurd hIr this
  | none =>
    have hprop : SLvl.IsZero u.eval → SemSig.famProp c (ls.map (·.eval)) = true := by
      intro hz
      cases hl : SemSig.famLevel c with
      | none => simp [SemSig.famProp, hl]
      | some l =>
        obtain ⟨W, doms, T, T', hD₁, hD₂⟩ := hHF.famType hl hci
        have := interp_instL_of_defeq henv hEF hextra helim hD₂ hls
          (interp_instL_of_defeq henv hEF hextra helim hD₁ hls hq)
        rw [VExpr.wrapForalls, VExpr.instL_foldr_forallE] at this
        have he := Interp.nestPi_sort_inv this
        rw [SemSig.famProp_eval hl, ← he]; exact decide_eq_true hz
    let rargs : List (WShape 0) := args.reverse.map fun _ => WShape.bot
    let cts : List (Name × WShape 0) := (SemSig.famCtors c).map fun c' => (c', WShape.bot)
    let m' : TShape := (WShape.rigid c (ls.map (·.eval)) rargs.reverse cts).T
    have hcts : WShape.CtsTypes cts := by
      intro p hp
      simp only [cts, List.mem_map] at hp
      obtain ⟨_, _, rfl⟩ := hp
      exact .bot' .sort_type
    have hmty : m'.HasType (TShape.sort u.eval) := TShape.HasType.rigid hprop hcts
    have hC : Const env (Interp env) (.const c) ls rargs m' := by
      refine Const.rigid rfl hk hr (by simp [cts, Function.comp_def]) ?_ TShape.LE.rfl
      intro p hp
      simp only [cts, List.mem_map] at hp
      obtain ⟨c', hc', rfl⟩ := hp
      obtain ⟨ci', k', h1, h2⟩ := hHF.famCtors hc'
      exact ⟨ci', k', _, h1, h2, Interp.bot (n := 0), TShape.bot_le'⟩
    have hm := Spine.realize hcl W hmty Interp.sort' hS (forall₂_wbot .nil args.reverse) hC
    rw [List.reverse_reverse] at hm
    rw [head_interp hm TShape.rigid_not_le_bot]; rfl

/-! ### The shape model as a `HeadModel` -/

/-- The shape model, read at the base valuation, is a `HeadModel`: the denotation of `e` is the
set of its approximations under `Valuation.nil`. -/
def headModel_of_shapeModel (henv : env.Ordered) (hEF : SemSig.EnvFactsIn env env)
    (hHF : SemSig.HeadFacts env) (hextra : ∀ df, env.defeqs df → ExtraValid env df)
    (helim : ElimValidIn env env) : HeadModel env where
  D := TShape → Prop
  den _ _ e := fun m => Interp env .nil m e
  sound hΓ H := funext fun m => propext (sound_nil henv hEF hextra helim H hΓ m)
  head := head
  head_sort := head_sort
  head_forallE := head_forallE
  head_rigid hΓ hc H := head_rigid henv hEF hHF hextra helim hΓ hc H

/-- The shape model is compositional in application. -/
theorem headModel_of_shapeModel_compositional (henv : env.Ordered)
    (hEF : SemSig.EnvFactsIn env env)
    (hHF : SemSig.HeadFacts env) (hextra : ∀ df, env.defeqs df → ExtraValid env df)
    (helim : ElimValidIn env env) :
    (headModel_of_shapeModel henv hEF hHF hextra helim).Compositional where
  app {U Γ f f' a a'} hf ha := by
    have hf : ∀ x, Interp env .nil x f ↔ Interp env .nil x f' := fun x =>
      Iff.of_eq (congrFun hf x)
    have ha : ∀ x, Interp env .nil x a ↔ Interp env .nil x a' := fun x =>
      Iff.of_eq (congrFun ha x)
    funext m; apply propext
    constructor <;> intro h <;> cases h with
    | bot => exact .bot
    | app h1 h2 h3 =>
      first
      | exact .app ((hf _).1 h1) ((ha _).1 h2) h3
      | exact .app ((hf _).2 h1) ((ha _).2 h2) h3

/-- **Separation from the shape model.** -/
theorem headSeparation_of_shapeModel (henv : env.Ordered) (hEF : SemSig.EnvFactsIn env env)
    (hHF : SemSig.HeadFacts env) (hextra : ∀ df, env.defeqs df → ExtraValid env df)
    (helim : ElimValidIn env env) : env.HeadSeparation :=
  (headModel_of_shapeModel henv hEF hHF hextra helim).separation

theorem headSeparation_of_shapeModel_of_wf (henv : env.WF) (hEF : SemSig.EnvFactsIn env env)
    (hHF : SemSig.HeadFacts env) (hextra : ∀ df, env.defeqs df → ExtraValid env df)
    (helim : ElimValidIn env env) : env.HeadSeparation :=
  headSeparation_of_shapeModel henv.ordered hEF hHF hextra helim

end

end Lean4Lean.ShapeModel
