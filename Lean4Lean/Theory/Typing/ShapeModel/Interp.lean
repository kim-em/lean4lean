import Lean4Lean.Theory.Typing.ShapeModel.Signature

/-!
# Interpretation of `VExpr` in the shape domain

This is a port of the interpretation part of Mario Carneiro's prototype
(`Lean4Lean/Experimental/ShapeLogRel.lean`, `Valuation` up to `LE_Interp.lam_inv'`) to the real
calculus `VExpr`, over the shape domain of `Domain.lean` and `ShapeTyping.lean`, reading the
environment through a semantic signature `SemSig` (`Signature.lean`). See
`docs/inductives/PHASE1_NOTES.md`, section 3.

`Interp env ρ m e` says that the shape `m` approximates `e` under the valuation `ρ`. It is
downward closed in `m` and upward closed in `ρ` (`Interp.mono`, `Interp.mono_l`). The clauses for
`bvar`, `sort`, `app`, `lam`, `forallE` are the prototype's; `const` and `elim` filter the table
produced by the spine machine `Const` through an approximation of the head's type; `proj s i e`
reads the `i`-th field of a constructor shape of the structure constructor of `s`.

`Const env R h ls rargs m` (the spine machine) says that `m` approximates the head `h` at levels
`ls` applied to arguments approximated by `rargs.reverse`. Its clauses: `bot`; `lam` (a table over
one more argument); `ctor` (a constructor with all its parameters and fields gives `ctor'` of the
fields); `rigid` (a constant that is not a constructor and heads no rule gives a rigid shape, with
a constructor table bounded by the constructor types instantiated at the parameter arguments,
`ctsBound`); and the rule clauses `rule` (no major), `ruleAB` (the major's family is not a
proposition: the major shape is above `ctor' c fs` and the rule binders are read from the
arguments and from `fs`, aligned at the end) and `ruleC` (the major's family is a proposition with
one constructor: the major is ignored and its fields are read from index arguments), each followed by the interpretation of the right-hand side under the
valuation `ruleVal` read off the match.

Main results: `Interp.mono`, `Interp.mono_l`, `Interp.lift`/`unlift`, `Interp.closed`,
`Interp.weak'_iff`/`weak_iff`/`weak`, `Interp.compat_join` (with `compat`, `join'`, `join`),
`Interp.subst`, `Interp.inst`, `Interp.forallE_inv`/`forallE_inv'`, `Interp.lam_inv`/`lam_inv'`,
`Interp.le_sort`, `Interp.bvar_iff`, and `Interp.instL_equiv` (from the general
`Interp.lvlEqv`: expressions equal up to `≈` of their levels have the same approximations). The
lemmas from `compat_join` on need `SemSig.Coherent`.

Design decisions and deviations from the milestone specification, with rationale:

* `Interp` and `Const` are not a syntactic mutual inductive. As in the prototype, `Const` is
  parametrised by a relation `R : Valuation → TShape → VExpr → Prop` standing for `Interp` (used
  by the rule right-hand sides, under `ruleVal`, and by the constructor types of the rigid
  clause, under `Valuation.nil`), and `Interp.const`/`Interp.elim` choose `R` with
  `∀ ρ m e, R ρ m e → Interp ρ m e`. This is equivalent to the mutual definition and keeps the
  `induction` tactic usable.
* The type of a constant (`ci.type.instL ls`) or eliminator (`T.instL ls`) is interpreted under
  `Valuation.nil` rather than under `ρ`. Constant types and eliminator types are closed, where the
  two agree (`Interp.closed`); with `nil` the clauses do not depend on `ρ`, so `closed`,
  `weak'_iff` and `subst` hold without a closedness hypothesis on the environment.
* Mode AB matches when `ctor' mj.ctor fs ≤ a` for the last argument shape `a`, not when
  `a = ctor' mj.ctor fs`. With equality, `Const.mono_l` (monotonicity in the arguments, needed by
  `compat_join`) is false: a structure major with all-bottom fields collapses to bottom, which
  is below argument shapes that are not constructor shapes of that structure. For a
  non-structure constructor, `ctor' c fs ≤ a` forces `a = ctor c fs'` with `fs ≤ fs'`, so the
  only new matches read lower field approximations, which monotonicity already covers; for a
  structure constructor it lets the rule fire with all-bottom fields, which is what structure
  eta forces for typed arguments.
* The rule clause is split into three constructors `rule`, `ruleAB`, `ruleC` (one per mode).
  In `ruleAB` the major is the head of `rargs` (the arguments are stored reversed).
* Rule matching does not depend on the constructor's parameter/field split agreeing with the
  rule's (a constructor can be registered with several splits, and a native rule's field count
  is tied to the constructor's arity only up to definitional equality; `PHASE1_NOTES.md`, D6).
  In `ruleAB` the stored fields `fs` have the constructor's stored count
  (`fs.length = SemSig.nfields mj.ctor`), not the rule's `mj.fields.length`. `ruleVal` aligns the
  `k` rule fields with the `nf` stored fields at the end: rule field `i` is stored field
  `nf - k + i` when `k ≤ i + nf`; otherwise, and for every field in mode C, it is read from the
  argument at position `r.fieldIndex[i]` (`some j`), else bottom. A binder that is not a rule
  field is read from its first literal occurrence among the arguments (`lookupVar`), else
  bottom; a binder occurring several times among the fields takes its first occurrence.
* "`T'` instantiated at the first `k'.nparams` argument shapes" is `ctsBound T' args k'.nparams`:
  the codomain table of the Pi shape `T'` applied successively (`WShape.piApp`, bottom on a
  non-Pi shape; `TShape.piApp` works at a common depth), and bottom with fewer arguments.
* The `rigid` clause has no arity, so for a rigid head both `rigid c ls [] cts` and
  `lam' {x ↦ rigid c ls [x] cts'}` are tables at no arguments, and they are incompatible.
  `Interp.compat_join` still holds because of the typing filter of `Interp.const` (a nonzero
  function shape has a Pi type, a rigid shape a sort type, `lam_rigid_excl`). Accordingly
  `Const.compat_join` is stated for shapes `x₁ ≤ m₁`, `x₂ ≤ m₂` typed at compatible types, and
  concludes at a lifted depth `N` (the entries of the joined table may be deeper than the
  arguments).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

noncomputable section

variable [ShapeParams]

/-! ### Valuations -/

def Valuation := Nat → TShape

def Valuation.nil : Valuation := fun _ => .bot
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

def Valuation.LE (ρ ρ' : Valuation) : Prop := ∀ n, ρ n ≤ ρ' n

theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ := fun _ => .rfl

theorem Valuation.LE.trans {ρ₁ ρ₂ ρ₃ : Valuation} (h1 : ρ₁.LE ρ₂) (h2 : ρ₂.LE ρ₃) : ρ₁.LE ρ₃ :=
  fun _ => (h1 _).trans (h2 _)

theorem Valuation.LE.push {ρ ρ' : Valuation} :
    (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

theorem Valuation.nil_le {ρ : Valuation} : Valuation.nil.LE ρ := fun _ => TShape.bot_le

/-- Two valuations are compatible if their entries are compatible at each index. -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop := ∀ i, (ρ₁ i).Compat (ρ₂ i)

/-- Pointwise join of two valuations. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) :=
  ⟨fun i => (TShape.Join.mk (hc i)).le.1, fun i => (TShape.Join.mk (hc i)).le.2⟩

/-! ### Application of the codomain of a Pi shape -/

/-- Apply the codomain table of a Pi shape (bottom if the shape is not a Pi). -/
def Shape.piApp : Shape (n + 1) → Shape n → Shape n
  | .forallE _ f, x => ShapeFun.app f x
  | _, _ => .bot

def WShape.piApp (T : WShape (n+1)) (x : WShape n) : WShape n := by
  refine ⟨Shape.piApp T.1 x.1, ?_⟩
  obtain ⟨⟨⟩, wf⟩ := T <;> try exact .bot
  exact (WShapeFun.app ⟨_, wf.2⟩ _).2

theorem WShape.piApp_val {T : WShape (n+1)} {x : WShape n} :
    (T.piApp x).1 = Shape.piApp T.1 x.1 := rfl

@[simp] theorem WShape.piApp_forallE {a : WShape n} {f : WShapeFun n} {x : WShape n} :
    (WShape.forallE a f).piApp x = f.app x := rfl

theorem WShape.piApp_of_ne {T : WShape (n+1)} (h : ∀ a f, T ≠ .forallE a f) (x : WShape n) :
    T.piApp x = .bot := by
  obtain ⟨⟨⟩, wf⟩ := T <;> try rfl
  exact absurd rfl (h ⟨_, wf.1⟩ ⟨_, wf.2⟩)

@[simp] theorem WShape.bot_piApp {x : WShape n} : (WShape.bot : WShape (n+1)).piApp x = .bot :=
  rfl

theorem WShape.piApp_mono_l {T T' : WShape (n+1)} (h : T ≤ T') (x : WShape n) :
    T.piApp x ≤ T'.piApp x := by
  cases T using WShape.casesOn' with
  | forallE a f =>
    obtain ⟨a', f', -, hf, rfl⟩ := WShape.forallE_le.1 h
    exact WShapeFun.app_mono_l hf x
  | bot => exact WShape.bot_le
  | sort => rw [piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact WShape.bot_le
  | lam => rw [piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact WShape.bot_le
  | ctor => rw [piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact WShape.bot_le
  | rigid => rw [piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact WShape.bot_le

theorem WShape.piApp_mono_r (T : WShape (n+1)) {x x' : WShape n} (h : x ≤ x') :
    T.piApp x ≤ T.piApp x' := by
  cases T using WShape.casesOn' with
  | forallE a f => exact WShapeFun.app_mono_r h
  | _ => rw [piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h),
      piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact WShape.LE.rfl

theorem WShape.lift_piApp {T : WShape (n+1)} {x : WShape n} (le : n ≤ m) :
    (T.piApp x).lift m = (T.lift (m+1)).piApp (x.lift m) := by
  cases T using WShape.casesOn' with
  | forallE a f => simp [WShape.lift_forallE le, WShapeFun.lift_app le]
  | bot => simp
  | sort =>
    rw [WShape.lift_sort, piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h),
      piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; simp
  | lam f hl =>
    rw [WShape.lift_lam le, piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h),
      piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; simp
  | ctor c l hc =>
    rw [WShape.lift_ctor le, piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h),
      piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; simp
  | rigid c ls l t =>
    rw [WShape.lift_rigid le, piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h),
      piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; simp

/-- Application of the codomain of a Pi shape, at a common depth. -/
def TShape.piApp (T x : TShape) : TShape :=
  ⟨max (T.1 - 1) x.1, (T.2.lift (max (T.1 - 1) x.1 + 1)).piApp (x.2.lift _)⟩

theorem TShape.piApp_lift {T x : TShape} (hT : T.1 ≤ k + 1) (hx : x.1 ≤ k) :
    (T.piApp x).1 ≤ k ∧ (T.piApp x).2.lift k = (T.2.lift (k+1)).piApp (x.2.lift k) := by
  have h1 : max (T.1 - 1) x.1 ≤ k := Nat.max_le.2 ⟨by omega, hx⟩
  refine ⟨h1, ?_⟩
  simp only [TShape.piApp]
  rw [WShape.lift_piApp h1, WShape.lift_lift (.inl (by omega)), WShape.lift_lift (.inl (by omega))]

theorem TShape.piApp_mono {T T' x x' : TShape} (hT : T ≤ T') (hx : x ≤ x') :
    T.piApp x ≤ T'.piApp x' := by
  let k := max (max T.1 T'.1) (max x.1 x'.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have ⟨a1, a2⟩ := TShape.piApp_lift (T := T) (x := x) (k := k) (by omega) hk.2.1
  have ⟨b1, b2⟩ := TShape.piApp_lift (T := T') (x := x') (k := k) (by omega) hk.2.2
  rw [TShape.LE.def a1 b1, a2, b2]
  exact (WShape.piApp_mono_l ((TShape.LE.def (by omega) (by omega)).1 hT) _).trans
    (WShape.piApp_mono_r _ ((TShape.LE.def hk.2.1 hk.2.2).1 hx))

omit [ShapeParams] in
theorem forall₂_take {R : α → β → Prop} :
    ∀ {l l'} (_ : List.Forall₂ R l l') (k : Nat), List.Forall₂ R (l.take k) (l'.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k+1 => by simpa using ⟨h, forall₂_take t k⟩

omit [ShapeParams] in
theorem forall₂_drop {R : α → β → Prop} :
    ∀ {l l'} (_ : List.Forall₂ R l l') (k : Nat), List.Forall₂ R (l.drop k) (l'.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k+1 => by simpa using forall₂_drop t k

/-- The bound on the constructor-table entry of a constructor with `k` parameters, from an
approximation `T` of its type and the argument shapes `args` of the family: the codomain of
`T` applied to the first `k` arguments (bottom if there are fewer than `k` arguments). -/
def ctsBound (T : TShape) (args : List TShape) (k : Nat) : TShape :=
  if k ≤ args.length then (args.take k).foldl TShape.piApp T else .bot

theorem foldl_piApp_mono {T T' : TShape} {args args' : List TShape}
    (hT : T ≤ T') (h : args.Forall₂ (· ≤ ·) args') :
    args.foldl TShape.piApp T ≤ args'.foldl TShape.piApp T' := by
  induction h generalizing T T' with
  | nil => exact hT
  | cons h1 _ ih => exact ih (TShape.piApp_mono hT h1)

theorem ctsBound_mono {T T' : TShape} {args args' : List TShape}
    (hT : T ≤ T') (h : args.Forall₂ (· ≤ ·) args') :
    ctsBound T args k ≤ ctsBound T' args' k := by
  simp only [ctsBound, h.length_eq]
  split
  · exact foldl_piApp_mono hT (forall₂_take h _)
  · exact .rfl

/-! ### Rule matching -/

/-- The shape of the first argument that is the variable `b` (bottom if there is none). -/
def lookupVar (b : Nat) : List (Option Nat) → List TShape → TShape
  | some b' :: vs, a :: as => if b' = b then a else lookupVar b vs as
  | none :: vs, _ :: as => lookupVar b vs as
  | _, _ => .bot

/-- The position of the first occurrence of `b` in a list of binders. -/
def fieldPos (b : Nat) : List Nat → Option Nat
  | [] => none
  | b' :: bs => if b' = b then some 0 else (fieldPos b bs).map (· + 1)

/-- Rule field `i` read from an index argument through `r.fieldIndex` (bottom if `none`, or if
the position is out of range). -/
def indexField (r : Rule) (args : List TShape) (i : Nat) : TShape :=
  match r.fieldIndex[i]? with
  | some (some j) => args.getD j .bot
  | _ => .bot

/-- Rule field `i` (of `k` rule fields). In mode AB (`fs? = some fs`, the stored fields of the
major) the fields are aligned at the end: rule field `i` is stored field `fs.length - k + i` if
that is an index (`k ≤ i + fs.length`), and is otherwise read through `r.fieldIndex`. In mode C
(`fs? = none`) every field is read through `r.fieldIndex`. -/
def ruleField (r : Rule) (args : List TShape) (fs? : Option (List TShape)) (k i : Nat) : TShape :=
  match fs? with
  | some fs => if k ≤ i + fs.length then fs.getD (i + fs.length - k) .bot else indexField r args i
  | none => indexField r args i

/-- The valuation of the binders of a rule read off the arguments `args` (before the major) and,
in mode AB, the stored fields `fs` of the major. A binder `b < r.nbind` that is a rule field
(first occurrence `i` in `mj.fields`) takes `ruleField`; any other binder takes its first literal
occurrence in `r.vars` (`lookupVar`), else bottom. -/
def ruleVal (r : Rule) (args : List TShape) (fs? : Option (List TShape)) : Valuation := fun b =>
  if b < r.nbind then
    match r.major with
    | some mj =>
      match fieldPos b mj.fields with
      | some i => ruleField r args fs? mj.fields.length i
      | none => lookupVar b r.vars args
    | none => lookupVar b r.vars args
  else .bot

@[simp] theorem lookupVar_nil : lookupVar b vs [] = .bot := by
  rcases vs with _ | ⟨_ | _, _⟩ <;> rfl

theorem lookupVar_mono {args args' : List TShape} (h : args.Forall₂ (· ≤ ·) args') :
    lookupVar b vs args ≤ lookupVar b vs args' := by
  induction h generalizing vs with
  | nil => rw [lookupVar_nil]; exact .rfl
  | cons h1 _ ih =>
    rcases vs with _ | ⟨_ | b', vs⟩
    · exact .rfl
    · exact ih
    · simp only [lookupVar]; split
      · exact h1
      · exact ih

theorem getD_bot_mono {args args' : List TShape} (h : args.Forall₂ (· ≤ ·) args') :
    args.getD j .bot ≤ args'.getD j .bot := by
  induction h generalizing j with
  | nil => exact .rfl
  | cons h1 _ ih => cases j with
    | zero => exact h1
    | succ j => exact ih

theorem indexField_mono {args args' : List TShape} (h : args.Forall₂ (· ≤ ·) args') :
    indexField r args i ≤ indexField r args' i := by
  simp only [indexField]; split
  · exact getD_bot_mono h
  · exact .rfl

theorem ruleVal_mono {args args' : List TShape} (h : args.Forall₂ (· ≤ ·) args')
    {fs? fs?' : Option (List TShape)}
    (hf : fs? = none ∧ fs?' = none ∨ ∃ fs fs', fs? = some fs ∧ fs?' = some fs' ∧
      fs.Forall₂ (· ≤ ·) fs') :
    (ruleVal r args fs?).LE (ruleVal r args' fs?') := by
  intro b; simp only [ruleVal]; split
  · cases r.major with
    | none => exact lookupVar_mono h
    | some mj =>
      simp only; split
      · rcases hf with ⟨rfl, rfl⟩ | ⟨fs, fs', rfl, rfl, hf⟩
        · exact indexField_mono h
        · simp only [ruleField, hf.length_eq]; split
          · exact getD_bot_mono hf
          · exact indexField_mono h
      · exact lookupVar_mono h
  · exact .rfl

end

/-! ### The interpretation -/

noncomputable section

variable (env : VEnv) [SemSig]

/-- An entry `(c', T)` of the constructor table of a rigid family applied to `args`: `c'` is a
constructor with a declared type, and `T` is below an approximation (under `R`) of that type
instantiated at the levels and at the parameter arguments. -/
def CtorEntry (R : Valuation → TShape → VExpr → Prop) (ls : List VLevel) (args : List TShape)
    (p : Name × WShape n) : Prop :=
  ∃ ci k T', env.constants p.1 = some ci ∧ SemSig.ctor p.1 = some k ∧
    R .nil T' (ci.type.instL ls) ∧ p.2.T ≤ ctsBound T' args k.nparams

/-- The spine machine: `Const R h ls rargs m` says that `m` approximates the head `h` at levels
`ls` applied to arguments approximated by `rargs.reverse` (all at a common depth `n`).
The relation `R` stands for the interpretation (`Interp`) at the valuations used by rule
right-hand sides and constructor types; `Interp.const` and `Interp.elim` require
`∀ ρ m e, R ρ m e → Interp ρ m e`. -/
inductive Const (R : Valuation → TShape → VExpr → Prop) (h : Head) (ls : List VLevel) :
    ∀ {n}, List (WShape n) → TShape → Prop
  | bot {rargs : List (WShape n)} : Const R h ls rargs (WShape.T (n := n') .bot)
  | lam {rargs : List (WShape n)} {f : WShapeFun n} :
    (∀ x y : WShape n, (x, y) ∈ f → Const R h ls (x :: rargs) y.T) →
    m ≤ WShape.T (n := n + 1) (.lam' f) → Const R h ls rargs m
  | ctor {rargs : List (WShape n)} :
    h = .const c → SemSig.ctor c = some ci → rargs.length = ci.nparams + ci.nfields →
    m ≤ (WShape.ctor' c (rargs.reverse.drop ci.nparams)).T → Const R h ls rargs m
  | rigid {rargs : List (WShape n)} {cts : List (Name × WShape n)} :
    h = .const c → SemSig.ctor c = none → (∀ r, SemSig.rules r → r.head ≠ .const c) →
    cts.map (·.1) = SemSig.famCtors c →
    (∀ p ∈ cts, CtorEntry env R ls (rargs.reverse.map (·.T)) p) →
    m ≤ (WShape.rigid c (ls.map (·.eval)) rargs.reverse cts).T → Const R h ls rargs m
  | rule {rargs : List (WShape n)} :
    SemSig.rules r → r.head = h → ls.length = r.uvars → r.major = none →
    rargs.length = r.vars.length →
    R (ruleVal r (rargs.reverse.map (·.T)) none) m (r.rhs.instL ls) → Const R h ls rargs m
  | ruleAB {rargs : List (WShape (n+1))} {a : WShape (n+1)} {fs : List (WShape n)} :
    SemSig.rules r → r.head = h → ls.length = r.uvars → r.major = some mj →
    SemSig.ctor mj.ctor = some ci → SemSig.famProp ci.family (mj.lvls ls) = false →
    rargs.length = r.vars.length → fs.length = SemSig.nfields mj.ctor →
    WShape.ctor' mj.ctor fs ≤ a →
    R (ruleVal r (rargs.reverse.map (·.T)) (some (fs.map (·.T)))) m (r.rhs.instL ls) →
    Const R h ls (a :: rargs) m
  | ruleC {rargs : List (WShape n)} :
    SemSig.rules r → r.head = h → ls.length = r.uvars → r.major = some mj →
    SemSig.ctor mj.ctor = some ci → SemSig.famProp ci.family (mj.lvls ls) = true →
    SemSig.famCtors ci.family = [mj.ctor] → rargs.length = r.vars.length + 1 →
    R (ruleVal r (rargs.reverse.map (·.T)) none) m (r.rhs.instL ls) → Const R h ls rargs m

/-- `Interp ρ m e`: the shape `m` approximates the expression `e` under the valuation `ρ`. -/
inductive Interp : Valuation → TShape → VExpr → Prop
  | bot : Interp ρ (WShape.T (n := n) .bot) e
  | bvar : m ≤ ρ i → Interp ρ m (.bvar i)
  | sort : m ≤ .sort l.eval → Interp ρ m (.sort l)
  | app {f : WShape (n+1)} {a : WShape n} : Interp ρ f.T F → Interp ρ a.T A →
    m ≤ (f.app a).T → Interp ρ m (.app F A)
  | lam {a : WShape n} {f : WShapeFun n} : Interp ρ a.T A → WShape.HasDom f a →
    (∀ x, x.HasType a → Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.lam' f) → Interp ρ m (.lam A F)
  | forallE {b b' : WShape n} {f : WShapeFun n} : Interp ρ b.T B → Interp ρ b'.T B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.forallE b f) → Interp ρ m (.forallE B F)
  | const {R : Valuation → TShape → VExpr → Prop} :
    env.constants c = some ci → ls.length = ci.uvars → m ≤ m' → m'.HasType a →
    Interp .nil a (ci.type.instL ls) → Const env R (.const c) ls (n := k) [] m' →
    (∀ ρ m e, R ρ m e → Interp ρ m e) → Interp ρ m (.const c ls)
  | elim {R : Valuation → TShape → VExpr → Prop} :
    SemSig.elimType b o = some T → m ≤ m' → m'.HasType a →
    Interp .nil a (T.instL ls) → Const env R (.elim b o) ls (n := k) [] m' →
    (∀ ρ m e, R ρ m e → Interp ρ m e) → Interp ρ m (.elim b o ls)
  | proj {fs : List (WShape n)} : SemSig.structCtor s = some c →
    Interp ρ (WShape.ctor' c fs).T e → (hi : i < fs.length) → m ≤ fs[i].T →
    Interp ρ m (.proj s i e)

end

/-! ### Basic properties -/

noncomputable section

variable {env : VEnv} [SemSig]

/-- A relation standing for the interpretation: downward closed in the shape, upward closed in
the valuation. -/
structure RelMono (R : Valuation → TShape → VExpr → Prop) : Prop where
  mono : ∀ {ρ ρ' a a' e}, ρ.LE ρ' → a ≤ a' → R ρ a' e → R ρ' a e

theorem forall₂_rev_T {rargs rargs' : List (WShape n)} (h : rargs.Forall₂ (· ≤ ·) rargs') :
    (rargs.reverse.map (·.T)).Forall₂ (· ≤ ·) (rargs'.reverse.map (·.T)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact (List.Forall₂.reverse.2 h).imp fun _ _ h => WShape.LE.T h

theorem forall₂_lift_T {rargs : List (WShape n)} (le : n ≤ n') :
    (rargs.map (·.T)).Forall₂ (· ≤ ·) (rargs.map (fun x => (x.lift n').T)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.Forall₂.rfl fun x _ => (TShape.lift_eqv (a := x.T) le).2

namespace Const

theorem imp {R R' : Valuation → TShape → VExpr → Prop} (hR : ∀ {ρ a e}, R ρ a e → R' ρ a e)
    {rargs : List (WShape n)} (H : Const env R h ls rargs m) : Const env R' h ls rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ctor h1 h2 h3 h4 => exact .ctor h1 h2 h3 h4
  | rigid h1 h2 h3 h4 h5 h6 =>
    refine .rigid h1 h2 h3 h4 (fun p hp => ?_) h6
    have ⟨_, _, _, a1, a2, a3, a4⟩ := h5 p hp; exact ⟨_, _, _, a1, a2, hR a3, a4⟩
  | rule h1 h2 h3 h4 h5 h6 => exact .rule h1 h2 h3 h4 h5 (hR h6)
  | ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 (hR h10)
  | ruleC h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact .ruleC h1 h2 h3 h4 h5 h6 h7 h8 (hR h9)

theorem mono {R R' : Valuation → TShape → VExpr → Prop} (hm : m ≤ m')
    (hR : ∀ {ρ a a' e}, a ≤ a' → R ρ a' e → R' ρ a e)
    {rargs : List (WShape n)} (H : Const env R h ls rargs m') : Const env R' h ls rargs m := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (hm.trans TShape.bot_eqv.1) ▸ .bot
  | lam _ h2 ih => exact .lam (ih · · · .rfl) (hm.trans h2)
  | ctor h1 h2 h3 h4 => exact .ctor h1 h2 h3 (hm.trans h4)
  | rigid h1 h2 h3 h4 h5 h6 =>
    refine .rigid h1 h2 h3 h4 (fun p hp => ?_) (hm.trans h6)
    have ⟨_, _, _, a1, a2, a3, a4⟩ := h5 p hp; exact ⟨_, _, _, a1, a2, hR .rfl a3, a4⟩
  | rule h1 h2 h3 h4 h5 h6 => exact .rule h1 h2 h3 h4 h5 (hR hm h6)
  | ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 (hR hm h10)
  | ruleC h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact .ruleC h1 h2 h3 h4 h5 h6 h7 h8 (hR hm h9)

theorem mono_l {R : Valuation → TShape → VExpr → Prop} (hR : RelMono R)
    {rargs rargs' : List (WShape n)} (hl : rargs.Forall₂ (· ≤ ·) rargs')
    (H : Const env R h ls rargs m) : Const env R h ls rargs' m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam (fun x y h' => ih _ _ h' (.cons .rfl hl)) h2
  | ctor h1 h2 h3 h4 =>
    refine .ctor h1 h2 (hl.length_eq ▸ h3) (h4.trans (WShape.ctor'_le_ctor' ?_).T)
    exact forall₂_drop (List.Forall₂.reverse.2 hl) _
  | rigid h1 h2 h3 h4 h5 h6 =>
    refine .rigid h1 h2 h3 h4 (fun p hp => ?_) (h6.trans ?_)
    · have ⟨_, _, _, a1, a2, a3, a4⟩ := h5 p hp
      exact ⟨_, _, _, a1, a2, a3, a4.trans (ctsBound_mono .rfl (forall₂_rev_T hl))⟩
    · exact WShape.LE.T <| WShape.rigid_le_rigid.2
        ⟨rfl, rfl, List.Forall₂.reverse.2 hl, CtsRel.rfl fun _ _ => WShape.LE.rfl⟩
  | rule h1 h2 h3 h4 h5 h6 =>
    exact .rule h1 h2 h3 h4 (hl.length_eq ▸ h5)
      (hR.mono (ruleVal_mono (forall₂_rev_T hl) (.inl ⟨rfl, rfl⟩)) .rfl h6)
  | ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    let .cons ha hl := hl
    exact .ruleAB h1 h2 h3 h4 h5 h6 (hl.length_eq ▸ h7) h8 (h9.trans ha)
      (hR.mono (ruleVal_mono (forall₂_rev_T hl) (.inr ⟨_, _, rfl, rfl, .rfl fun _ _ => .rfl⟩))
        .rfl h10)
  | ruleC h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .ruleC h1 h2 h3 h4 h5 h6 h7 (hl.length_eq ▸ h8)
      (hR.mono (ruleVal_mono (forall₂_rev_T hl) (.inl ⟨rfl, rfl⟩)) .rfl h9)

theorem lift {R : Valuation → TShape → VExpr → Prop} (hR : RelMono R) (hn : n₁ ≤ n₂)
    {rargs : List (WShape n₁)} (H : Const env R h ls rargs m) :
    Const env R h ls (rargs.map (.lift n₂)) m := by
  induction H generalizing n₂ with
  | bot => exact .bot
  | @lam _ m rargs f h1 h2 ih =>
    refine .lam (f := f.lift n₂) (fun _ _ h => ?_) ?_
    · obtain ⟨x, y, h', rfl, rfl⟩ := (WShapeFun.mem_lift hn).1 h
      exact Const.mono (R := R) (R' := R) (TShape.lift_eqv (a := y.T) hn).1
        (fun le hr => hR.mono .rfl le hr) (ih _ _ h' hn)
    · exact WShape.lift_lam' hn ▸ h2.trans (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | ctor h1 h2 h3 h4 =>
    refine .ctor h1 h2 (by rw [List.length_map]; exact h3) (h4.trans ?_)
    rw [← List.map_reverse, ← List.map_drop, ← WShape.lift_ctor' hn]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | @rigid _ c m rargs cts h1 h2 h3 h4 h5 h6 =>
    refine .rigid (cts := ctsMap (.lift n₂) cts) h1 h2 h3
      (by simpa [ctsMap, Function.comp_def] using h4)
      (fun p hp => ?_) (h6.trans ?_)
    · obtain ⟨q, hq, rfl⟩ := mem_ctsMap.1 hp
      have ⟨_, _, _, a1, a2, a3, a4⟩ := h5 q hq
      refine ⟨_, _, _, a1, a2, a3, (TShape.lift_eqv hn).1.trans (a4.trans ?_)⟩
      rw [← List.map_reverse, List.map_map]
      exact ctsBound_mono .rfl (forall₂_lift_T hn)
    · rw [← List.map_reverse, ← WShape.lift_rigid hn]
      exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | rule h1 h2 h3 h4 h5 h6 =>
    refine .rule h1 h2 h3 h4 (by rw [List.length_map]; exact h5) (hR.mono ?_ .rfl h6)
    rw [← List.map_reverse, List.map_map]
    exact ruleVal_mono (forall₂_lift_T hn) (.inl ⟨rfl, rfl⟩)
  | @ruleAB _ _ _ _ _ rargs a fs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    obtain ⟨n₂, rfl⟩ : ∃ k, n₂ = k + 1 := ⟨n₂ - 1, by omega⟩
    have hn' := Nat.le_of_succ_le_succ hn
    rw [List.map_cons]
    refine .ruleAB (fs := fs.map (.lift n₂)) h1 h2 h3 h4 h5 h6 (by rw [List.length_map]; exact h7)
      (by rw [List.length_map]; exact h8) ?_ (hR.mono ?_ .rfl h10)
    · rw [← WShape.lift_ctor' hn']; exact WShape.lift_mono hn h9
    · rw [← List.map_reverse, List.map_map, List.map_map]
      exact ruleVal_mono (forall₂_lift_T hn) (.inr ⟨_, _, rfl, rfl, forall₂_lift_T hn'⟩)
  | ruleC h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    refine .ruleC h1 h2 h3 h4 h5 h6 h7 (by rw [List.length_map]; exact h8) (hR.mono ?_ .rfl h9)
    rw [← List.map_reverse, List.map_map]
    exact ruleVal_mono (forall₂_lift_T hn) (.inl ⟨rfl, rfl⟩)

end Const

namespace Interp

theorem bvar' : Interp env ρ (ρ i) (.bvar i) := .bvar .rfl
theorem bvar0 : Interp env (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem sort' : Interp env ρ (.sort l.eval) (.sort l) := .sort .rfl
theorem app' {f : WShape (n+1)} {a : WShape n}
    (h1 : Interp env ρ f.T F) (h2 : Interp env ρ a.T A) :
    Interp env ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem lam' {f : WShapeFun n} {a : WShape n}
    (h1 : Interp env ρ a.T A) (h2 : WShape.HasDom f a)
    (h3 : ∀ x, x.HasType a → Interp env (ρ.push x.T) (f.app x).T F) :
    Interp env ρ (WShape.T (n := n+1) (WShape.lam' f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem forallE' {f : WShapeFun n} {b b' : WShape n}
    (h1 : Interp env ρ b.T B) (h2 : Interp env ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → Interp env (ρ.push x.T) (f.app x).T F) :
    Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F) := .forallE h1 h2 h3 h4 .rfl

theorem bvar_iff : Interp env ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem le_sort (H : Interp env ρ m (.sort u)) : m ≤ .sort u.eval := by
  generalize eq : VExpr.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h

theorem mono (h : m ≤ m') (H : Interp env ρ m' M) : Interp env ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 (h.trans h3) h4 h5 h6 h7
  | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 (h.trans h3) h4 h5 h6 h7
  | proj h1 h2 hi h3 => exact .proj h1 h2 hi (h.trans h3)

theorem mono_l (hρ : ρ.LE ρ') (H : Interp env ρ m M) : Interp env ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 h3 h4 h5 h6 h7
  | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 h3 h4 h5 h6 h7
  | proj h1 _ hi h3 ih => exact .proj h1 (ih hρ) hi h3

theorem relMono : RelMono (Interp env) := ⟨fun hρ hm H => (H.mono hm).mono_l hρ⟩

theorem unlift (le : m.1 ≤ n)
    (H : Interp env ρ (m.2.lift n).T M) : Interp env ρ m M := H.mono (TShape.lift_eqv le).2

theorem lift (le : m.1 ≤ n)
    (H : Interp env ρ m M) : Interp env ρ (m.2.lift n).T M := H.mono (TShape.lift_eqv le).1

theorem closed (cl : VExpr.ClosedN M k) (h : ∀ i < k, ρ i = ρ' i)
    (H : Interp env ρ m M) : Interp env ρ' m M := by
  induction H generalizing k ρ' with
  | bot => exact .bot
  | sort h1 => exact .sort h1
  | bvar h1 => exact .bvar ((h _ cl).symm ▸ h1)
  | app hf ha h1 ih_f ih_a => exact .app (ih_f cl.1 h) (ih_a cl.2 h) h1
  | lam ha hdom hbody h1 ih_a ih_body =>
    refine .lam (ih_a cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | j+1, hi => exact h j (Nat.lt_of_succ_lt_succ hi)
  | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b cl.1 h) (ih_b' cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | i+1, hi => exact h i (Nat.lt_of_succ_lt_succ hi)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 h3 h4 h5 h6 h7
  | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 h3 h4 h5 h6 h7
  | proj h1 _ hi h3 ih => exact .proj h1 (ih cl h) hi h3

theorem closed_iff {M : VExpr} (cl : VExpr.ClosedN M)
    {ρ ρ' : Valuation} {m : TShape} : Interp env ρ m M ↔ Interp env ρ' m M :=
  ⟨closed cl nofun, closed cl nofun⟩

theorem weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    Interp env ρ' m (M.lift' l) ↔ Interp env ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 h3 h4 h5 h6 h7
    | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 h3 h4 h5 h6 h7
    | proj h1 _ hi h3 ih => exact .proj h1 (ih _ h rfl) hi h3
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 h3 h4 h5 h6 h7
    | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 h3 h4 h5 h6 h7
    | proj h1 _ hi h3 ih => exact .proj h1 (ih l h) hi h3

theorem weak_iff : Interp env (ρ.push x) m M.lift ↔ Interp env ρ m M := by
  rw [VExpr.lift_eq_lift']; exact weak'_iff (.skip .refl) (fun _ => rfl)

theorem weak (H : Interp env ρ m M) : Interp env (ρ.push x) m M.lift := weak_iff.2 H

end Interp

end

/-! ### Auxiliary facts about shapes -/

section
variable [ShapeParams]

theorem TShape.Compat.symm' {x y : TShape} (h : x.Compat y) : y.Compat x :=
  let ⟨z, a, b⟩ := TShape.Compat.def'.1 h; TShape.Compat.def'.2 ⟨z, b, a⟩

theorem forall₂_map_T {l l' : List (WShape n)} (h : l.Forall₂ (· ≤ ·) l') :
    (l.map (·.T)).Forall₂ (· ≤ ·) (l'.map (·.T)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ h => WShape.LE.T h

theorem TShape.join_le {x y z : TShape} (c : x.Compat y) (h1 : x ≤ z) (h2 : y ≤ z) :
    x.join y ≤ z := (TShape.Join.mk c z).2 ⟨h1, h2⟩

theorem TShape.join_le_join {x₁ x₂ m₁ m₂ : TShape} (cx : x₁.Compat x₂) (cm : m₁.Compat m₂)
    (h1 : x₁ ≤ m₁) (h2 : x₂ ≤ m₂) : x₁.join x₂ ≤ m₁.join m₂ :=
  TShape.join_le cx (h1.trans (TShape.Join.mk cm).le.1) (h2.trans (TShape.Join.mk cm).le.2)

theorem TShape.le_bot_iff_lift {x : TShape} (h : x.1 ≤ k) : x ≤ .bot ↔ x.2.lift k = .bot := by
  rw [TShape.LE.def h (Nat.zero_le _)]
  simp only [TShape.bot, WShape.lift_bot, WShape.le_bot]

theorem WShapeFun.Compat.app₂ {f f' : WShapeFun n} {x x' : WShape n}
    (hf : f.Compat f') (hx : x.Compat x') : (f.app x).Compat (f'.app x') :=
  have ⟨F, a1, a2⟩ := WShapeFun.Compat.iff.1 hf
  have ⟨X, b1, b2⟩ := WShape.Compat.iff.1 hx
  WShape.Compat.iff.2 ⟨F.app X, (WShapeFun.app_mono_l a1 _).trans (WShapeFun.app_mono_r b1),
    (WShapeFun.app_mono_l a2 _).trans (WShapeFun.app_mono_r b2)⟩

theorem lam'_T_le_bot {f : WShapeFun n} (H : ∀ x y, (x, y) ∈ f → y.T ≤ .bot) :
    (WShape.lam' f).T ≤ .bot := by
  by_cases hf : f.NonZero
  · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
    have := H s t hxy
    exact absurd (WShape.le_bot.2 (TShape.le_bot.1 this)) hn
  · rw [WShape.lam', dif_neg hf]; exact TShape.bot_eqv.1

theorem WShape.HasType.lam'_inv {g : WShapeFun n} {A : WShape (n+1)}
    (H : WShape.HasType (.lam' g) A) (hne : WShape.lam' g ≠ .bot) :
    ∃ b G, A = .forallE b G ∧ WShape.HasTypeLam g b G := by
  by_cases hg : g.NonZero
  case neg => exact absurd (by rw [WShape.lam', dif_neg hg]) hne
  obtain ⟨b, G, rfl⟩ : ∃ b G, A = .forallE b G := by
    rw [WShape.lam', dif_pos hg] at H
    generalize eq : WShape.lam g hg = x at H
    cases H.unfold with
    | lam => exact ⟨_, _, rfl⟩
    | _ => cases congrArg (·.1) eq
  obtain ⟨g', e, h⟩ := WShape.HasType.forallE_inv H
  refine ⟨b, G, rfl, ?_⟩
  rw [WShape.lam', dif_pos hg] at e
  unfold WShape.lam' at e; split at e <;> rename_i hg'
  · cases (WShape.lam.inj.1 e); exact h
  · cases congrArg (·.1) e

theorem WShape.HasType.rigid_l_inv {l : List (WShape n)} {t} {A : WShape (n+1)}
    (H : WShape.HasType (.rigid c ls l t) A) : ∃ r, A = .sort r := by
  generalize eq : WShape.rigid c ls l t = x at H
  cases H.unfold with
  | rigid => exact ⟨_, rfl⟩
  | lam => unfold WShape.lam' at eq; split at eq <;> cases congrArg (·.1) eq
  | _ => cases congrArg (·.1) eq

/-- A function shape and a rigid shape, typed at compatible types, cannot both be nonzero. -/
theorem lam_rigid_excl {x₁ x₂ a₁ a₂ : TShape} {f : WShapeFun n} {l : List (WShape n')} {t}
    (le1 : x₁ ≤ (WShape.lam' f).T) (le2 : x₂ ≤ (WShape.rigid c lv l t).T)
    (t1 : x₁.HasType a₁) (t2 : x₂.HasType a₂) (ca : a₁.Compat a₂) : x₁ ≤ .bot ∨ x₂ ≤ .bot := by
  let K := max (max (max x₁.1 x₂.1) (max a₁.1 a₂.1)) (max n n')
  have hk := Nat.max_le.1 (Nat.le_refl K); simp only [Nat.max_le] at hk
  have e1 := (TShape.LE.def (m := K+1) (by omega) (by simp; omega)).1 le1
  rw [WShape.lift_lam' (by omega)] at e1
  obtain ⟨g, eg⟩ := WShape.LE.le_lam' e1
  have e2 := (TShape.LE.def (m := K+1) (by omega) (by simp; omega)).1 le2
  rw [WShape.lift_rigid (by omega)] at e2
  obtain eq | ⟨l', t', eq, -, -⟩ := WShape.le_rigid.1 e2
  · exact .inr ((TShape.le_bot_iff_lift (by omega)).2 eq)
  by_cases hg : WShape.lam' g = .bot
  · exact .inl ((TShape.le_bot_iff_lift (by omega)).2 (eg.trans hg))
  exfalso
  have t1 := (TShape.HasType.def (m := K+1) (by omega) (by omega)).1 t1
  have t2 := (TShape.HasType.def (m := K+1) (by omega) (by omega)).1 t2
  rw [eg] at t1; rw [eq] at t2
  obtain ⟨b, G, e1, -⟩ := WShape.HasType.lam'_inv t1 hg
  obtain ⟨r, e2⟩ := WShape.HasType.rigid_l_inv t2
  have ca := (TShape.Compat.def (m := K+1) (by omega) (by omega)).1 ca
  rw [e1, e2] at ca
  simp [WShape.Compat, WShape.forallE, WShape.sort, Shape.sort, Shape.Compat] at ca

/-- The entries of a nonzero function shape typed at `a` are typed along the codomain of `a`. -/
theorem lam_entries_typed {g : WShapeFun N} {a : TShape} (hK : N ≤ K) (ha : a.1 ≤ K + 1)
    (t : (WShape.lam' g).T.HasType a) (hne : WShape.lam' g ≠ .bot) :
    ∃ b G, a.2.lift (K+1) = .forallE b G ∧
      ∀ y z, (y, z) ∈ g → (z.lift K).HasType (G.app (y.lift K)) := by
  have t := (TShape.HasType.def (m := K+1) (Nat.succ_le_succ hK) ha).1 t
  rw [WShape.lift_lam' hK] at t
  have hne' : WShape.lam' (g.lift K) ≠ .bot := by
    rw [← WShape.lift_lam' hK]; intro h
    exact hne ((WShape.lift_eq_bot (Nat.succ_le_succ hK)).1 h)
  obtain ⟨b, G, e, hl⟩ := WShape.HasType.lam'_inv t hne'
  refine ⟨b, G, e, fun y z h => ?_⟩
  exact (WShape.HasTypeLam.def.1 hl).2.2 _ _ ((WShapeFun.mem_lift hK).2 ⟨_, _, h, rfl, rfl⟩)

end

/-! ### Compatibility of constant spines -/

section
variable [SemSig]

omit [SemSig] in
theorem lvls_map_eq_of_equiv {l₁ l₂ : List VLevel} (h : List.Forall₂ (· ≈ ·) l₁ l₂) :
    l₁.map (fun l => (l.inst ls).eval) = l₂.map (fun l => (l.inst ls).eval) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih, VLevel.equiv_def'.1 (VLevel.inst_congr_l h)]

omit [SemSig] in
theorem RuleMajor.lvls_eq_of_equiv {mj₁ mj₂ : RuleMajor}
    (h : List.Forall₂ (· ≈ ·) mj₁.levels mj₂.levels) : mj₁.lvls ls = mj₂.lvls ls :=
  lvls_map_eq_of_equiv h

theorem forall₂_compat_of_bot_r {l₁ l₂ : List (WShape n)} (hl : l₁.length = l₂.length)
    (h : ∀ x ∈ l₂, x ≤ .bot) : l₁.Forall₂ WShape.Compat l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at hl
    | cons b l₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons,
        forall_eq_or_imp] at hl h
      exact .cons (WShape.Compat.mono .rfl h.1 .bot_r) (ih hl h.2)

theorem WShape.ctor'_compat_fields {fs₁ fs₂ : List (WShape n)} (hl : fs₁.length = fs₂.length)
    (h : (WShape.ctor' c fs₁).Compat (WShape.ctor' c fs₂)) : fs₁.Forall₂ WShape.Compat fs₂ := by
  have allbot {fs : List (WShape n)} (h : ¬(IsStruct c → WShape.ListNonZero fs)) :
      ∀ x ∈ fs, x ≤ .bot := by
    intro x hx; exact Classical.byContradiction fun hn => h fun _ => ⟨x, hx, hn⟩
  unfold WShape.ctor' at h; split at h <;> rename_i h1 <;> split at h <;> rename_i h2
  · exact (WShape.Compat.ctor_ctor.1 h).2
  · exact forall₂_compat_of_bot_r hl (allbot h2)
  · exact (forall₂_compat_of_bot_r hl.symm (allbot h1)).flip.imp fun _ _ h => WShape.Compat.symm h
  · exact forall₂_compat_of_bot_r hl (allbot h2)

/-- The head `h` has a terminal clause (constructor or rule) at `k` arguments. -/
def Terminal (h : Head) (k : Nat) : Prop :=
  (∃ c ci, h = .const c ∧ SemSig.ctor c = some ci ∧ k = ci.nparams + ci.nfields) ∨
  (∃ r, SemSig.rules r ∧ r.head = h ∧ k = r.arity)

variable [SemSig.Coherent] {env : VEnv}

theorem Rule.arity_eq (h1 : SemSig.rules r₁) (h2 : SemSig.rules r₂) (hh : r₁.head = r₂.head) :
    r₁.arity = r₂.arity := by
  have ⟨a, b⟩ := SemSig.Coherent.same_shape h1 h2 hh; simp [Rule.arity, a, b]

theorem Const.le_bot_of_terminal {R} (ht : Terminal h k)
    {rargs : List (WShape n)} (H : Const env R h ls rargs m) (hk : k < rargs.length) :
    m ≤ .bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | lam _ h2 ih => exact h2.trans (lam'_T_le_bot fun x y hm => ih x y hm (by simp; omega))
  | ctor h1 h2 h3 _ =>
    exfalso
    obtain ⟨c', ci', e1, e2, e3⟩ | ⟨r, hr, e1, e2⟩ := ht
    · subst h1; cases e1; cases h2.symm.trans e2; omega
    · subst h1; exact SemSig.Coherent.ctor_no_rule h2 hr e1
  | rigid h1 h2 h3 =>
    exfalso
    obtain ⟨c', ci', e1, e2, e3⟩ | ⟨r, hr, e1, e2⟩ := ht
    · subst h1; cases e1; cases h2.symm.trans e2
    · subst h1; exact h3 r hr e1
  | rule h1 h2 _ h4 h5 =>
    exfalso
    obtain ⟨c', ci', e1, e2, e3⟩ | ⟨r', hr, e1, e2⟩ := ht
    · subst e1; exact SemSig.Coherent.ctor_no_rule e2 h1 h2
    · rw [Rule.arity_eq hr h1 (e1.trans h2.symm)] at e2; simp [Rule.arity, h4] at e2; omega
  | ruleAB h1 h2 _ h4 _ _ h7 =>
    exfalso
    obtain ⟨c', ci', e1, e2, e3⟩ | ⟨r', hr, e1, e2⟩ := ht
    · subst e1; exact SemSig.Coherent.ctor_no_rule e2 h1 h2
    · rw [Rule.arity_eq hr h1 (e1.trans h2.symm)] at e2; simp [Rule.arity, h4] at e2
      simp at hk; omega
  | ruleC h1 h2 _ h4 _ _ _ h8 =>
    exfalso
    obtain ⟨c', ci', e1, e2, e3⟩ | ⟨r', hr, e1, e2⟩ := ht
    · subst e1; exact SemSig.Coherent.ctor_no_rule e2 h1 h2
    · rw [Rule.arity_eq hr h1 (e1.trans h2.symm)] at e2; simp [Rule.arity, h4] at e2; omega

theorem Const.lam_le_bot_of_terminal {R} {rargs : List (WShape n)} {f : WShapeFun n}
    (hf : ∀ x y, (x, y) ∈ f → Const env R h ls (x :: rargs) y.T) (ht : Terminal h rargs.length) :
    (WShape.lam' f).T ≤ .bot :=
  lam'_T_le_bot fun x y hm => (hf x y hm).le_bot_of_terminal ht (by simp)

omit [SemSig] [SemSig.Coherent] in
theorem ctsZip_names {cts₁ : List (Name × α)} {cts₂ : List (Name × β)} (f : α → β → γ)
    (h : cts₁.map (·.1) = cts₂.map (·.1)) : (ctsZip f cts₁ cts₂).map (·.1) = cts₁.map (·.1) := by
  induction cts₁ generalizing cts₂ with
  | nil => rfl
  | cons p cts₁ ih =>
    cases cts₂ with
    | nil => simp at h
    | cons q cts₂ =>
      simp only [List.map_cons, List.cons.injEq] at h; simp [ctsZip_cons_cons, ih h.2]

variable {R₁ R₂ R₃ : Valuation → TShape → VExpr → Prop}

omit [SemSig.Coherent] in
theorem ctsEntries_join
    (hRR : ∀ {m₁ m₂ e}, R₁ .nil m₁ e → R₂ .nil m₂ e → m₁.Compat m₂ ∧ R₃ .nil (m₁.join m₂) e)
    {args1 args2 argsJ : List TShape} (h1 : args1.Forall₂ (· ≤ ·) argsJ)
    (h2 : args2.Forall₂ (· ≤ ·) argsJ)
    {cts₁ cts₂ : List (Name × WShape n)} (hn : cts₁.map (·.1) = cts₂.map (·.1))
    (H1 : ∀ p ∈ cts₁, CtorEntry env R₁ ls args1 p) (H2 : ∀ p ∈ cts₂, CtorEntry env R₂ ls args2 p) :
    CtsRel WShape.Compat cts₁ cts₂ ∧
      ∀ p ∈ ctsZip WShape.join cts₁ cts₂, CtorEntry env R₃ ls argsJ p := by
  induction cts₁ generalizing cts₂ with
  | nil =>
    cases cts₂ with
    | nil => exact ⟨.nil, by simp [ctsZip]⟩
    | cons => simp at hn
  | cons p cts₁ ih =>
    cases cts₂ with
    | nil => simp at hn
    | cons q cts₂ =>
      simp only [List.map_cons, List.cons.injEq] at hn
      simp only [List.mem_cons, forall_eq_or_imp] at H1 H2
      have ⟨ihc, ihj⟩ := ih hn.2 H1.2 H2.2
      obtain ⟨ci, k, T₁, c1, k1, r1, b1⟩ := H1.1
      obtain ⟨ci', k', T₂, c2, k2, r2, b2⟩ := H2.1
      rw [← hn.1] at c2 k2
      cases c1.symm.trans c2; cases k1.symm.trans k2
      have ⟨cT, rJ⟩ := hRR r1 r2
      have hJ := TShape.Join.mk cT
      have B1 := b1.trans (ctsBound_mono hJ.le.1 h1)
      have B2 := b2.trans (ctsBound_mono hJ.le.2 h2)
      have cpq : p.2.Compat q.2 := WShape.Compat.T_iff.2 (TShape.Compat.def'.2 ⟨_, B1, B2⟩)
      refine ⟨.cons ⟨hn.1, cpq⟩ ihc, ?_⟩
      simp only [ctsZip_cons_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨⟨ci, k, _, c1, k1, rJ, ?_⟩, ihj⟩
      rw [← WShape.T_join]; exact TShape.join_le (WShape.Compat.T_iff.1 cpq) B1 B2

omit [SemSig.Coherent] in
theorem Const.join_bot_l (hR₃ : RelMono R₃) (hR₂ : ∀ {ρ a e}, R₂ ρ a e → R₃ ρ a e)
    {rargs1 rargs2 : List (WShape n)} (hc : rargs1.Forall₂ WShape.Compat rargs2)
    {x₁ x₂ : TShape} (H2 : Const env R₂ h ls rargs2 m₂) (le2 : x₂ ≤ m₂) (b1 : x₁ ≤ .bot)
    (hN : n ≤ N) :
    x₁.Compat x₂ ∧
      Const env R₃ h ls ((rargs1.zipWith WShape.join rargs2).map (.lift N)) (x₁.join x₂) := by
  have c : x₁.Compat x₂ := TShape.Compat.mono b1 .rfl .bot_l
  refine ⟨c, Const.mono (R := R₃) (TShape.join_le c (b1.trans TShape.bot_le) le2)
    (fun le hr => hR₃.mono .rfl le hr) ?_⟩
  exact ((H2.imp (R' := R₃) hR₂).mono_l hR₃ (WShape.le_zipWith_join hc).2).lift hR₃ hN

omit [SemSig.Coherent] in
theorem Const.join_bot_r (hR₃ : RelMono R₃) (hR₁ : ∀ {ρ a e}, R₁ ρ a e → R₃ ρ a e)
    {rargs1 rargs2 : List (WShape n)} (hc : rargs1.Forall₂ WShape.Compat rargs2)
    {x₁ x₂ : TShape} (H1 : Const env R₁ h ls rargs1 m₁) (le1 : x₁ ≤ m₁) (b2 : x₂ ≤ .bot)
    (hN : n ≤ N) :
    x₁.Compat x₂ ∧
      Const env R₃ h ls ((rargs1.zipWith WShape.join rargs2).map (.lift N)) (x₁.join x₂) := by
  have c : x₁.Compat x₂ := TShape.Compat.mono .rfl b2 .bot_r
  refine ⟨c, Const.mono (R := R₃) (TShape.join_le c le1 (b2.trans TShape.bot_le))
    (fun le hr => hR₃.mono .rfl le hr) ?_⟩
  exact ((H1.imp (R' := R₃) hR₁).mono_l hR₃ (WShape.le_zipWith_join hc).1).lift hR₃ hN


theorem Const.compat_join_aux (hR₃ : RelMono R₃)
    (hR₁ : ∀ {ρ a e}, R₁ ρ a e → R₃ ρ a e) (hR₂ : ∀ {ρ a e}, R₂ ρ a e → R₃ ρ a e)
    (hRR : ∀ {ρ₁ ρ₂ ρ m₁ m₂ e}, ρ₁.LE ρ → ρ₂.LE ρ → R₁ ρ₁ m₁ e → R₂ ρ₂ m₂ e →
      m₁.Compat m₂ ∧ R₃ ρ (m₁.join m₂) e)
    {rargs1 : List (WShape n)} (H1 : Const env R₁ h ls rargs1 m₁) :
    ∀ {rargs2 : List (WShape n)} {m₂ x₁ x₂ a₁ a₂ : TShape} {N : Nat},
      rargs1.Forall₂ WShape.Compat rargs2 → Const env R₂ h ls rargs2 m₂ →
      x₁ ≤ m₁ → x₂ ≤ m₂ → x₁.HasType a₁ → x₂.HasType a₂ → a₁.Compat a₂ →
      n ≤ N → x₁.1 ≤ N + 1 → x₂.1 ≤ N + 1 → ¬x₁ ≤ .bot → ¬x₂ ≤ .bot →
      x₁.Compat x₂ ∧
        Const env R₃ h ls ((rargs1.zipWith WShape.join rargs2).map (.lift N)) (x₁.join x₂) := by
  have ruleJ {ρ₁ ρ₂ ρ m₁ m₂ x₁ x₂ e} (h1 : ρ₁.LE ρ) (h2 : ρ₂.LE ρ) (r1 : R₁ ρ₁ m₁ e)
      (r2 : R₂ ρ₂ m₂ e) (le1 : x₁ ≤ m₁) (le2 : x₂ ≤ m₂) : x₁.Compat x₂ ∧ R₃ ρ (x₁.join x₂) e :=
    have ⟨cm, rJ⟩ := hRR h1 h2 r1 r2
    have cx := TShape.Compat.mono le1 le2 cm
    ⟨cx, hR₃.mono .rfl (TShape.join_le_join cx cm le1 le2) rJ⟩
  induction H1 with
  | bot =>
    intro _ _ _ _ _ _ _ _ _ le1 _ _ _ _ _ _ _ nb1 _
    exact absurd (le1.trans TShape.bot_eqv.1) nb1
  | @lam n m₁ rargs1 f₁ h1 h2 ih =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    have lamT {ht : Terminal h rargs1.length} : False :=
      nb1 (le1.trans (h2.trans (Const.lam_le_bot_of_terminal h1 ht)))
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | ctor f1 f2 f3 => exact (lamT (ht := .inl ⟨_, _, f1, f2, hl.trans f3⟩)).elim
    | rule f1 f2 _ f4 f5 =>
      exact (lamT (ht := .inr ⟨_, f1, f2, by simp [Rule.arity, f4, hl, f5]⟩)).elim
    | ruleAB f1 f2 _ f4 _ _ f7 =>
      exact (lamT (ht := .inr ⟨_, f1, f2, by simp [Rule.arity, f4, hl, f7]⟩)).elim
    | ruleC f1 f2 _ f4 _ _ _ f8 =>
      exact (lamT (ht := .inr ⟨_, f1, f2, by simp [Rule.arity, f4, hl, f8]⟩)).elim
    | rigid _ _ _ _ _ f6 =>
      exact (lam_rigid_excl (le1.trans h2) (le2.trans f6) t1 t2 ca).elim
        (absurd · nb1) (absurd · nb2)
    | @lam _ _ _ f₂ h1' h2' =>
    -- normalize both sides to function shapes at depth `N + 1`
    have e1 := (TShape.LE.def (m := N+1) d1 (by simp; omega)).1 (le1.trans h2)
    rw [WShape.lift_lam' hN] at e1
    obtain ⟨g₁, eg₁⟩ := WShape.LE.le_lam' e1
    rw [eg₁, WShape.lam'_le_lam'] at e1
    have e2 := (TShape.LE.def (m := N+1) d2 (by simp; omega)).1 (le2.trans h2')
    rw [WShape.lift_lam' hN] at e2
    obtain ⟨g₂, eg₂⟩ := WShape.LE.le_lam' e2
    rw [eg₂, WShape.lam'_le_lam'] at e2
    have q1 : x₁ ≤ (WShape.lam' g₁).T ∧ (WShape.lam' g₁).T ≤ x₁ :=
      eg₁ ▸ ⟨(TShape.lift_eqv d1).2, (TShape.lift_eqv d1).1⟩
    have q2 : x₂ ≤ (WShape.lam' g₂).T ∧ (WShape.lam' g₂).T ≤ x₂ :=
      eg₂ ▸ ⟨(TShape.lift_eqv d2).2, (TShape.lift_eqv d2).1⟩
    have ne1 : WShape.lam' g₁ ≠ .bot := fun e => nb1 ((TShape.le_bot_iff_lift d1).2 (eg₁.trans e))
    have ne2 : WShape.lam' g₂ ≠ .bot := fun e => nb2 ((TShape.le_bot_iff_lift d2).2 (eg₂.trans e))
    -- the entries are typed along compatible codomains
    let K := max N (max a₁.1 a₂.1)
    have hK : N ≤ K := Nat.le_max_left ..
    have hK1 : a₁.1 ≤ K + 1 := by omega
    have hK2 : a₂.1 ≤ K + 1 := by omega
    obtain ⟨B₁, G₁, eA₁, ty₁⟩ := lam_entries_typed hK hK1 (t1.mono_l q1.1 q1.2) ne1
    obtain ⟨B₂, G₂, eA₂, ty₂⟩ := lam_entries_typed hK hK2 (t2.mono_l q2.1 q2.2) ne2
    have cG : G₁.Compat G₂ := by
      have := (TShape.Compat.def (m := K+1) hK1 hK2).1 ca
      rw [eA₁, eA₂, WShape.Compat.forallE_forallE] at this; exact this.2
    have C : ∀ y z y' z', (y, z) ∈ g₁ → (y', z') ∈ g₂ → y.Compat y' →
        z.Compat z' ∧ Const env R₃ h ls
          ((y.join y') :: (rargs1.zipWith WShape.join rargs2).map (.lift N)) (z.join z').T := by
      intro y z y' z' hm hm' cy
      have z_le := ((WShapeFun.app_of_mem hm).2).trans (WShapeFun.app_mono_l e1 y)
      obtain ⟨u₀, hu₀, hmu⟩ := WShapeFun.app_eq (f₁.lift N) y
      obtain ⟨u, w, huw, rfl, hw⟩ := (WShapeFun.mem_lift hN).1 hmu
      rw [hw] at z_le
      have z'_le := ((WShapeFun.app_of_mem hm').2).trans (WShapeFun.app_mono_l e2 y')
      obtain ⟨u₀', hu₀', hmu'⟩ := WShapeFun.app_eq (f₂.lift N) y'
      obtain ⟨u', w', huw', rfl, hw'⟩ := (WShapeFun.mem_lift hN).1 hmu'
      rw [hw'] at z'_le
      have cu : u.Compat u' := (WShape.Compat.lift hN).1 (WShape.Compat.mono hu₀ hu₀' cy)
      have zle : z.T ≤ w.T := (TShape.LE.def (m := N) (Nat.le_refl _) hN).2 <| by
        rw [WShape.lift_self]; exact z_le
      have zle' : z'.T ≤ w'.T := (TShape.LE.def (m := N) (Nat.le_refl _) hN).2 <| by
        rw [WShape.lift_self]; exact z'_le
      have IH : z.T.Compat z'.T ∧ Const env R₃ h ls
          (((u :: rargs1).zipWith WShape.join (u' :: rargs2)).map (.lift N)) (z.T.join z'.T) := by
        by_cases bz : z.T ≤ .bot
        · exact Const.join_bot_l hR₃ hR₂ (.cons cu hc) (h1' u' w' huw') zle' bz hN
        by_cases bz' : z'.T ≤ .bot
        · exact Const.join_bot_r hR₃ hR₁ (.cons cu hc) (h1 u w huw) zle bz' hN
        have tz : z.T.HasType (G₁.app (y.lift K)).T :=
          (TShape.HasType.def (m := K) hK (Nat.le_refl _)).2 <| by
            rw [WShape.lift_self]; exact ty₁ y z hm
        have tz' : z'.T.HasType (G₂.app (y'.lift K)).T :=
          (TShape.HasType.def (m := K) hK (Nat.le_refl _)).2 <| by
            rw [WShape.lift_self]; exact ty₂ y' z' hm'
        exact ih u w huw (.cons cu hc) (h1' u' w' huw') zle zle' tz tz'
          (WShape.Compat.T_iff.1 (cG.app₂ ((WShape.Compat.lift hK).2 cy))) hN
          (by simp) (by simp) bz bz'
      refine ⟨WShape.Compat.T_iff.2 IH.1, ?_⟩
      have IH2 := IH.2
      rw [WShape.T_join] at IH2
      refine IH2.mono_l hR₃ (.cons ?_ (.rfl fun _ _ => .rfl))
      rw [WShape.lift_join hN]
      exact (WShape.Join.mk ((WShape.Compat.lift hN).2 cu) _).2
        ⟨hu₀.trans (WShape.Join.mk cy).le.1, hu₀'.trans (WShape.Join.mk cy).le.2⟩
    have cg : g₁.Compat g₂ := WShapeFun.Compat.def.2 fun p hp q hq hpq => (C _ _ _ _ hp hq hpq).1
    have cx : x₁.Compat x₂ :=
      TShape.Compat.mono q1.1 q2.1 (WShape.Compat.T_iff.1 (WShape.Compat.lam'.2 cg))
    refine ⟨cx, ?_⟩
    have jl := WShape.Join.lam'.2 (WShapeFun.Join.mk cg)
    refine .lam (f := g₁.join g₂) (fun Y Z hYZ => ?_)
      (TShape.join_le cx (q1.1.trans jl.le.1.T) (q2.1.trans jl.le.2.T))
    obtain ⟨p, -, q, -, -, rfl, rfl⟩ := (WShapeFun.mem_join cg).1 hYZ
    obtain ⟨y₁, hy₁, hm₁⟩ := WShapeFun.app_eq g₁ (p.1.join q.1)
    obtain ⟨y₂, hy₂, hm₂⟩ := WShapeFun.app_eq g₂ (p.1.join q.1)
    have cy := WShape.Compat.iff.2 ⟨_, hy₁, hy₂⟩
    have hC := (C _ _ _ _ hm₁ hm₂ cy).2
    exact hC.mono_l hR₃ (.cons ((WShape.Join.mk cy _).2 ⟨hy₁, hy₂⟩) (.rfl fun _ _ => .rfl))
  | @ctor n c ci m₁ rargs1 e1 e2 e3 e4 =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | lam f1 f2 =>
      exact absurd (le2.trans (f2.trans (Const.lam_le_bot_of_terminal f1
        (.inl ⟨_, _, e1, e2, hl.symm.trans e3⟩)))) nb2
    | rigid f1 f2 => subst e1; cases f1; cases e2.symm.trans f2
    | rule f1 f2 => exact absurd (f2.trans e1) (SemSig.Coherent.ctor_no_rule e2 f1)
    | ruleAB f1 f2 => exact absurd (f2.trans e1) (SemSig.Coherent.ctor_no_rule e2 f1)
    | ruleC f1 f2 => exact absurd (f2.trans e1) (SemSig.Coherent.ctor_no_rule e2 f1)
    | ctor f1 f2 f3 f4 =>
      subst e1; cases f1; cases e2.symm.trans f2
      have hrev := forall₂_drop (List.Forall₂.reverse.2 hc) ci.nparams
      have cC := WShape.Compat.ctor'_ctor' (c := c) hrev
      have cx := TShape.Compat.mono (le1.trans e4) (le2.trans f4) cC.T
      refine ⟨cx, Const.lift hR₃ hN
        (.ctor rfl e2 (by rw [List.length_zipWith, ← hl, Nat.min_self]; exact e3) ?_)⟩
      rw [List.reverse_zipWith hl, List.drop_zipWith, ← WShape.ctor'_join hrev, ← WShape.T_join]
      exact TShape.join_le_join cx cC.T (le1.trans e4) (le2.trans f4)
  | @rigid n c m₁ rargs1 cts₁ e1 e2 e3 e4 e5 e6 =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | lam _ f2 =>
      exact (lam_rigid_excl (le2.trans f2) (le1.trans e6) t2 t1 ca.symm').elim
        (absurd · nb2) (absurd · nb1)
    | ctor f1 f2 => subst e1; cases f1; cases e2.symm.trans f2
    | rule f1 f2 => exact absurd (f2.trans e1) (e3 _ f1)
    | ruleAB f1 f2 => exact absurd (f2.trans e1) (e3 _ f1)
    | ruleC f1 f2 => exact absurd (f2.trans e1) (e3 _ f1)
    | @rigid _ _ _ _ cts₂ f1 f2 f3 f4 f5 f6 =>
      subst e1; cases f1
      have hJ1 := forall₂_rev_T (WShape.le_zipWith_join hc).1
      have hJ2 := forall₂_rev_T (WShape.le_zipWith_join hc).2
      have ⟨hcts, hJ⟩ := ctsEntries_join (fun r1 r2 => hRR .rfl .rfl r1 r2) hJ1 hJ2
        (e4.trans f4.symm) e5 f5
      have cR := (WShape.Compat.rigid_rigid (c := c) (c' := c) (ls := ls.map (·.eval))
        (ls' := ls.map (·.eval))).2 ⟨rfl, rfl, List.Forall₂.reverse.2 hc, hcts⟩
      have cx := TShape.Compat.mono (le1.trans e6) (le2.trans f6) cR.T
      refine ⟨cx, Const.lift hR₃ hN (.rigid rfl e2 e3
        (by rw [ctsZip_names _ (e4.trans f4.symm)]; exact e4) hJ ?_)⟩
      rw [List.reverse_zipWith hl,
        ← WShape.rigid_join_rigid (List.Forall₂.reverse.2 hc) hcts, ← WShape.T_join]
      exact TShape.join_le_join cx cR.T (le1.trans e6) (le2.trans f6)
  | @rule n r₁ m₁ rargs1 e1 e2 e3 e4 e5 e6 =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | lam f1 f2 =>
      exact absurd (le2.trans (f2.trans (Const.lam_le_bot_of_terminal f1
        (.inr ⟨_, e1, e2, by simp [Rule.arity, e4, ← hl, e5]⟩)))) nb2
    | ctor f1 f2 => exact absurd (e2.trans f1) (SemSig.Coherent.ctor_no_rule f2 e1)
    | rigid f1 _ f3 => exact absurd (e2.trans f1) (f3 _ e1)
    | ruleAB f1 f2 _ f4 =>
      have := (SemSig.Coherent.same_shape e1 f1 (e2.trans f2.symm)).2; simp [e4, f4] at this
    | ruleC f1 f2 _ f4 =>
      have := (SemSig.Coherent.same_shape e1 f1 (e2.trans f2.symm)).2; simp [e4, f4] at this
    | rule f1 f2 f3 f4 f5 f6 =>
      cases SemSig.Coherent.no_major_eq e1 f1 (e2.trans f2.symm) e4 f4
      have hJ1 := forall₂_rev_T (WShape.le_zipWith_join hc).1
      have hJ2 := forall₂_rev_T (WShape.le_zipWith_join hc).2
      have ⟨cx, rJ⟩ := ruleJ (ruleVal_mono hJ1 (.inl ⟨rfl, rfl⟩))
        (ruleVal_mono hJ2 (.inl ⟨rfl, rfl⟩)) e6 f6 le1 le2
      exact ⟨cx, Const.lift hR₃ hN
        (.rule e1 e2 e3 e4 (by rw [List.length_zipWith, ← hl, Nat.min_self]; exact e5) rJ)⟩
  | @ruleAB n r₁ mj₁ ci₁ m₁ rargs1 b₁ fs₁ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | lam f1 f2 =>
      exact absurd (le2.trans (f2.trans (Const.lam_le_bot_of_terminal f1
        (.inr ⟨_, e1, e2, by simp [Rule.arity, e4, ← hl, e7]⟩)))) nb2
    | ctor f1 f2 => exact absurd (e2.trans f1) (SemSig.Coherent.ctor_no_rule f2 e1)
    | rigid f1 _ f3 => exact absurd (e2.trans f1) (f3 _ e1)
    | rule f1 f2 _ f4 =>
      have := (SemSig.Coherent.same_shape e1 f1 (e2.trans f2.symm)).2; simp [e4, f4] at this
    | ruleC f1 f2 _ f4 f5 f6 =>
      have ⟨hfam, hlev⟩ := SemSig.Coherent.major_family e1 f1 (e2.trans f2.symm) e4 f4 e5 f5
      rw [hfam, RuleMajor.lvls_eq_of_equiv hlev, f6] at e6; cases e6
    | @ruleAB _ r₂ mj₂ ci₂ _ rargs2 b₂ fs₂ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 =>
      let .cons cb hc := hc
      have hh := e2.trans f2.symm
      have ⟨hfam, hlev⟩ := SemSig.Coherent.major_family e1 f1 hh e4 f4 e5 f5
      have cmj : mj₁.ctor = mj₂.ctor := by
        by_cases s1 : IsStruct mj₁.ctor
        · exact (SemSig.Coherent.struct_unique s1 e5 f5 hfam.symm).symm
        by_cases s2 : IsStruct mj₂.ctor
        · exact SemSig.Coherent.struct_unique s2 f5 e5 hfam
        obtain ⟨_, _, rfl, -⟩ := WShape.ctor'_le.1 e9 (fun h => absurd h s1)
        obtain ⟨_, _, rfl, -⟩ := WShape.ctor'_le.1 f9 (fun h => absurd h s2)
        exact (WShape.Compat.ctor_ctor.1 cb).1
      cases SemSig.Coherent.major_ctor_eq e1 f1 hh e4 f4 cmj
      cases e4.symm.trans f4; cases e5.symm.trans f5
      have cfs := WShape.ctor'_compat_fields (e8.trans f8.symm) (WShape.Compat.mono e9 f9 cb)
      have hJ1 := forall₂_rev_T (WShape.le_zipWith_join hc).1
      have hJ2 := forall₂_rev_T (WShape.le_zipWith_join hc).2
      have ⟨cx, rJ⟩ := ruleJ
        (ruleVal_mono hJ1 (.inr ⟨_, _, rfl, rfl, forall₂_map_T (WShape.le_zipWith_join cfs).1⟩))
        (ruleVal_mono hJ2 (.inr ⟨_, _, rfl, rfl, forall₂_map_T (WShape.le_zipWith_join cfs).2⟩))
        e10 f10 le1 le2
      refine ⟨cx, Const.lift hR₃ hN (.ruleAB e1 e2 e3 e4 e5 e6
        (by rw [List.length_zipWith, ← hc.length_eq, Nat.min_self]; exact e7)
        (by simp [List.length_zipWith, e8, f8]) ?_ rJ)⟩
      rw [← WShape.ctor'_join cfs]
      exact (WShape.Join.mk (WShape.Compat.ctor'_ctor' cfs) _).2
        ⟨e9.trans (WShape.Join.mk cb).le.1, f9.trans (WShape.Join.mk cb).le.2⟩
  | @ruleC n r₁ mj₁ ci₁ m₁ rargs1 e1 e2 e3 e4 e5 e6 e7 e8 e9 =>
    intro rargs2 m₂ x₁ x₂ a₁ a₂ N hc H2 le1 le2 t1 t2 ca hN d1 d2 nb1 nb2
    have hl := hc.length_eq
    cases H2 with
    | bot => exact absurd (le2.trans TShape.bot_eqv.1) nb2
    | lam f1 f2 =>
      exact absurd (le2.trans (f2.trans (Const.lam_le_bot_of_terminal f1
        (.inr ⟨_, e1, e2, by simp [Rule.arity, e4, ← hl, e8]⟩)))) nb2
    | ctor f1 f2 => exact absurd (e2.trans f1) (SemSig.Coherent.ctor_no_rule f2 e1)
    | rigid f1 _ f3 => exact absurd (e2.trans f1) (f3 _ e1)
    | rule f1 f2 _ f4 =>
      have := (SemSig.Coherent.same_shape e1 f1 (e2.trans f2.symm)).2; simp [e4, f4] at this
    | ruleAB f1 f2 _ f4 f5 f6 =>
      have ⟨hfam, hlev⟩ := SemSig.Coherent.major_family e1 f1 (e2.trans f2.symm) e4 f4 e5 f5
      rw [hfam, RuleMajor.lvls_eq_of_equiv hlev, f6] at e6; cases e6
    | ruleC f1 f2 f3 f4 f5 f6 f7 f8 f9 =>
      have hh := e2.trans f2.symm
      have hfam := (SemSig.Coherent.major_family e1 f1 hh e4 f4 e5 f5).1
      have e7' := e7; rw [hfam, f7] at e7'
      cases SemSig.Coherent.major_ctor_eq e1 f1 hh e4 f4 (List.cons.inj e7').1.symm
      have hJ1 := forall₂_rev_T (WShape.le_zipWith_join hc).1
      have hJ2 := forall₂_rev_T (WShape.le_zipWith_join hc).2
      have ⟨cx, rJ⟩ := ruleJ (ruleVal_mono hJ1 (.inl ⟨rfl, rfl⟩))
        (ruleVal_mono hJ2 (.inl ⟨rfl, rfl⟩)) e9 f9 le1 le2
      exact ⟨cx, Const.lift hR₃ hN (.ruleC e1 e2 e3 e4 e5 e6 e7
        (by rw [List.length_zipWith, ← hl, Nat.min_self]; exact e8) rJ)⟩

omit [SemSig] [SemSig.Coherent] in
theorem forall₂_getElem {R : α → β → Prop} {l : List α} {l' : List β} (h : l.Forall₂ R l')
    (hi : i < l.length) : R l[i] (l'[i]'(h.length_eq ▸ hi)) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons h _ ih => cases i with | zero => exact h | succ i => exact ih (by simpa using hi)

theorem Const.compat_join (hR₃ : RelMono R₃)
    (hR₁ : ∀ {ρ a e}, R₁ ρ a e → R₃ ρ a e) (hR₂ : ∀ {ρ a e}, R₂ ρ a e → R₃ ρ a e)
    (hRR : ∀ {ρ₁ ρ₂ ρ m₁ m₂ e}, ρ₁.LE ρ → ρ₂.LE ρ → R₁ ρ₁ m₁ e → R₂ ρ₂ m₂ e →
      m₁.Compat m₂ ∧ R₃ ρ (m₁.join m₂) e)
    {rargs1 rargs2 : List (WShape n)} (hc : rargs1.Forall₂ WShape.Compat rargs2)
    (H1 : Const env R₁ h ls rargs1 m₁) (H2 : Const env R₂ h ls rargs2 m₂)
    {x₁ x₂ a₁ a₂ : TShape} (le1 : x₁ ≤ m₁) (le2 : x₂ ≤ m₂)
    (t1 : x₁.HasType a₁) (t2 : x₂.HasType a₂) (ca : a₁.Compat a₂)
    (hN : n ≤ N) (d1 : x₁.1 ≤ N + 1) (d2 : x₂.1 ≤ N + 1) :
    x₁.Compat x₂ ∧
      Const env R₃ h ls ((rargs1.zipWith WShape.join rargs2).map (.lift N)) (x₁.join x₂) := by
  by_cases b1 : x₁ ≤ .bot; · exact Const.join_bot_l hR₃ hR₂ hc H2 le2 b1 hN
  by_cases b2 : x₂ ≤ .bot; · exact Const.join_bot_r hR₃ hR₁ hc H1 le1 b2 hN
  exact Const.compat_join_aux hR₃ hR₁ hR₂ hRR H1 hc H2 le1 le2 t1 t2 ca hN d1 d2 b1 b2

/-- The monotone closure of a relation. -/
def RelClosure (R : Valuation → TShape → VExpr → Prop) : Valuation → TShape → VExpr → Prop :=
  fun ρ m e => ∃ ρ₀ m₀, ρ₀.LE ρ ∧ m ≤ m₀ ∧ R ρ₀ m₀ e

omit [SemSig.Coherent] in
theorem RelClosure.relMono : RelMono (RelClosure R) :=
  ⟨fun hρ hm ⟨_, _, a1, a2, a3⟩ => ⟨_, _, a1.trans hρ, hm.trans a2, a3⟩⟩

/-- The two constant tables of `Interp.const` (or `Interp.elim`) derivations, typed at
compatible types, are compatible, and their join is again a table. -/
theorem Const.compat_join_closure
    (h7 : ∀ ρ m e, R₁ ρ m e → Interp env ρ m e) (a7 : ∀ ρ m e, R₂ ρ m e → Interp env ρ m e)
    (hRR : ∀ {ρ₁ ρ₂ ρ m₁ m₂ e}, ρ₁.LE ρ → ρ₂.LE ρ → R₁ ρ₁ m₁ e → R₂ ρ₂ m₂ e →
      m₁.Compat m₂ ∧ Interp env ρ (m₁.join m₂) e)
    (H1 : Const env R₁ h ls (n := k₁) [] m₁) (H2 : Const env R₂ h ls (n := k₂) [] m₂)
    {a₁ a₂ : TShape} (t1 : m₁.HasType a₁) (t2 : m₂.HasType a₂) (ca : a₁.Compat a₂) :
    m₁.Compat m₂ ∧
      Const env (Interp env) h ls (n := max (max k₁ k₂) (max m₁.1 m₂.1)) [] (m₁.join m₂) := by
  have g1 := (H1.imp (R' := RelClosure R₁) fun r => ⟨_, _, .rfl, .rfl, r⟩).lift
    RelClosure.relMono (Nat.le_max_left k₁ k₂)
  have g2 := (H2.imp (R' := RelClosure R₂) fun r => ⟨_, _, .rfl, .rfl, r⟩).lift
    RelClosure.relMono (Nat.le_max_right k₁ k₂)
  have := Const.compat_join (R₃ := Interp env) (N := max (max k₁ k₂) (max m₁.1 m₂.1))
    Interp.relMono
    (fun ⟨_, _, l, lm, r⟩ => ((h7 _ _ _ r).mono lm).mono_l l)
    (fun ⟨_, _, l, lm, r⟩ => ((a7 _ _ _ r).mono lm).mono_l l)
    (fun hρ₁ hρ₂ ⟨_, _, la, lma, ra⟩ ⟨_, _, lb, lmb, rb⟩ => by
      have ⟨c, j⟩ := hRR (la.trans hρ₁) (lb.trans hρ₂) ra rb
      have cx := TShape.Compat.mono lma lmb c
      exact ⟨cx, j.mono (TShape.join_le_join cx c lma lmb)⟩)
    .nil g1 g2 .rfl .rfl t1 t2 ca (Nat.le_max_left ..) (by omega) (by omega)
  exact this

theorem Interp.compat_join {m₁ m₂ : TShape} {ρ ρ' : Valuation}
    (hρ : ρ'.LE ρ) (H1 : Interp env ρ' m₁ M) (H2 : Interp env ρ m₂ M) :
    m₁.Compat m₂ ∧ Interp env ρ (m₁.join m₂) M := by
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : Interp env ρ m M) :
      m₁.Compat m₂ ∧ Interp env ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : Interp env ρ' m₁ M) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧ Interp env ρ (m₁.join (WShape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 h2 (.sort .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | @lam n₁ ρ' A F m₁ a₁ f₁ ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | @lam n₂ _ _ _ _ a₂ f₂ ha' hdom' he' h1'
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ Interp env (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom' x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he' x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      refine mk ?_ ?_ hle'
      · exact (WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1
      · exact (WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : WShapeFun.Compat (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom' := (WShape.HasDom.lift le₂).2 hdom'
    have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h1'.trans ?_) <| .lam' ia (hdom.join cf ca_w hdom') fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
        WShape.lift_lam' le₁ ▸ WShape.lam'_le_lam'.2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
        WShape.lift_lam' le₂ ▸ WShape.lam'_le_lam'.2 jf.le.2
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
    exact (ja _).2 (WShape.Join.mk oy_c).le |>.T
  | @forallE n₁ ρ' B F m₁ b₁ b₁' f₁ hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | @forallE n₂ _ _ _ _ b₂ b₂' f₂ hb2 ha2 hdom2 he2 h12
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ Interp env (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_forallE le₁ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_forallE le₂ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | @const c ci m₁ m'₁ a₁ ls k₁ _ R₁ h1 h2 h3 h4 h5 h6 h7 ih5 ih7 =>
    cases H2 with
    | bot => exact bot_r hρ (.const h1 h2 h3 h4 h5 h6 h7)
    | @const _ ci' _ m'₂ a₂ _ k₂ _ R₂ a1 a2 a3 a4 a5 a6 a7 =>
    cases h1.symm.trans a1
    have ⟨ac, alej⟩ := ih5 .rfl a5
    have ⟨hc1, hj1⟩ := Const.compat_join_closure (k₁ := k₁) (k₂ := k₂) h7 a7
      (fun hρ₁ hρ₂ r1 r2 => ih7 _ _ _ r1 hρ₁ ((a7 _ _ _ r2).mono_l hρ₂)) h6 a6 h4 a4 ac
    have ⟨b1, b2⟩ := (TShape.Join.mk hc1).le
    have ⟨b3, b4⟩ := (TShape.Join.mk ac).le
    have hc := TShape.Compat.mono h3 a3 hc1
    refine ⟨hc, .const h1 h2 (TShape.join_le hc (h3.trans b1) (a3.trans b2)) ?_ alej hj1
      fun _ _ _ => id⟩
    have aty := h4.isType.join ac a4.isType
    exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)
  | @elim b o T m₁ m'₁ a₁ ls k₁ _ R₁ h1 h3 h4 h5 h6 h7 ih5 ih7 =>
    cases H2 with
    | bot => exact bot_r hρ (.elim h1 h3 h4 h5 h6 h7)
    | @elim _ _ T' _ m'₂ a₂ _ k₂ _ R₂ a1 a3 a4 a5 a6 a7 =>
    cases h1.symm.trans a1
    have ⟨ac, alej⟩ := ih5 .rfl a5
    have ⟨hc1, hj1⟩ := Const.compat_join_closure (k₁ := k₁) (k₂ := k₂) h7 a7
      (fun hρ₁ hρ₂ r1 r2 => ih7 _ _ _ r1 hρ₁ ((a7 _ _ _ r2).mono_l hρ₂)) h6 a6 h4 a4 ac
    have ⟨b1, b2⟩ := (TShape.Join.mk hc1).le
    have ⟨b3, b4⟩ := (TShape.Join.mk ac).le
    have hc := TShape.Compat.mono h3 a3 hc1
    refine ⟨hc, .elim h1 (TShape.join_le hc (h3.trans b1) (a3.trans b2)) ?_ alej hj1
      fun _ _ _ => id⟩
    have aty := h4.isType.join ac a4.isType
    exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)
  | @proj n₁ s c ρ' e i m₁ fs₁ h1 h2 hi h3 ih =>
    cases H2 with
    | bot => exact bot_r hρ (.proj h1 h2 hi h3)
    | @proj n₂ _ c' _ _ _ _ fs₂ a1 a2 hi' a3 =>
    cases h1.symm.trans a1
    by_cases b1 : m₁ ≤ .bot
    · exact mk (b1.trans TShape.bot_le) .rfl (.proj h1 a2 hi' a3)
    by_cases b2 : m₂ ≤ .bot
    · exact mk .rfl (b2.trans TShape.bot_le) ((Interp.proj h1 h2 hi h3).mono_l hρ)
    have ⟨cC, jC⟩ := ih hρ a2
    let D := max n₁ n₂
    have le₁ : n₁ ≤ D := Nat.le_max_left ..
    have le₂ : n₂ ≤ D := Nat.le_max_right ..
    have nz₁ : IsStruct c → WShape.ListNonZero fs₁ := fun _ =>
      ⟨_, List.getElem_mem hi, fun h => b1 (h3.trans (TShape.le_bot.2 (WShape.le_bot.1 h)))⟩
    have nz₂ : IsStruct c → WShape.ListNonZero fs₂ := fun _ =>
      ⟨_, List.getElem_mem hi', fun h => b2 (a3.trans (TShape.le_bot.2 (WShape.le_bot.1 h)))⟩
    have cC' := (TShape.Compat.def (m := D+1) (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 cC
    simp only [WShape.lift_ctor' le₁, WShape.lift_ctor' le₂] at cC'
    have nz₁' : IsStruct c → WShape.ListNonZero (fs₁.map (WShape.lift D)) :=
      fun h => (WShape.ListNonZero.lift_iff le₁).2 (nz₁ h)
    have nz₂' : IsStruct c → WShape.ListNonZero (fs₂.map (WShape.lift D)) :=
      fun h => (WShape.ListNonZero.lift_iff le₂).2 (nz₂ h)
    rw [← WShape.ctor_eq_ctor' (h := nz₁'), ← WShape.ctor_eq_ctor' (h := nz₂')] at cC'
    have hfs := (WShape.Compat.ctor_ctor.1 cC').2
    let gs := (fs₁.map (WShape.lift D)).zipWith WShape.join (fs₂.map (WShape.lift D))
    have le_g : (WShape.ctor' c gs).T ≤ (WShape.ctor' c fs₁).T.join (WShape.ctor' c fs₂).T := by
      rw [TShape.LE.def (m := D+1) (Nat.le_refl _) (by simp [TShape.join]; omega),
        TShape.lift_join (by simp; omega) (by simp; omega)]
      simp only [WShape.lift_self, WShape.lift_ctor' le₁, WShape.lift_ctor' le₂,
        WShape.ctor'_join hfs]
      exact WShape.LE.rfl
    have hi₁ : i < (fs₁.map (WShape.lift D)).length := by simpa using hi
    have hi₂ : i < (fs₂.map (WShape.lift D)).length := by simpa using hi'
    have hg := WShape.le_zipWith_join hfs
    have g1 := forall₂_getElem hg.1 hi₁
    have g2 := forall₂_getElem hg.2 hi₂
    simp only [List.getElem_map] at g1 g2
    have u1 : m₁ ≤ (gs[i]'(hg.1.length_eq ▸ hi₁)).T :=
      h3.trans ((TShape.lift_eqv (a := fs₁[i].T) le₁).2.trans g1.T)
    have u2 : m₂ ≤ (gs[i]'(hg.1.length_eq ▸ hi₁)).T :=
      a3.trans ((TShape.lift_eqv (a := fs₂[i].T) le₂).2.trans g2.T)
    exact mk u1 u2 (.proj h1 (jC.mono le_g) _ .rfl)

theorem Interp.compat (H1 : Interp env ρ m₁ M) (H2 : Interp env ρ m₂ M) : m₁.Compat m₂ :=
  (compat_join .rfl H1 H2).1

theorem Interp.join' (H1 : Interp env ρ m₁ M) (H2 : Interp env ρ m₂ M) :
    Interp env ρ (m₁.join m₂) M :=
  (compat_join .rfl H1 H2).2

theorem Interp.join (J : m₁.Join m₂ m) (H1 : Interp env ρ m₁ M) (H2 : Interp env ρ m₂ M) :
    Interp env ρ m M :=
  (H1.join' H2).mono ((J _).2 (TShape.Join.mk (H1.compat H2)).le)

theorem Interp.subst : Interp env ρ m (M.subst σ) ↔
    ∃ ρ', Interp env ρ' m M ∧ ∀ i, Interp env ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · suffices ∀ {ρ m N}, Interp env ρ m N → ∀ (M : VExpr) (σ : VExpr.Subst), M.subst σ = N →
        ∃ ρ', Interp env ρ' m M ∧ ∀ i, Interp env ρ (ρ' i) (σ i) from this H M σ rfl
    intro ρ m N H M σ eq
    have bvar {ρ : Valuation} {m N} {σ : VExpr.Subst} {j} (hσj : σ j = N) (hN : Interp env ρ m N) :
        ∃ ρ', Interp env ρ' m (.bvar j) ∧ ∀ i, Interp env ρ (ρ' i) (σ i) := by
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, .bvar (if_pos rfl ▸ .rfl), fun k => ?_⟩
      dsimp; split <;> rename_i ek
      · subst ek; exact hσj ▸ hN
      · exact .bot
    induction H generalizing M σ with
    | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | sort h1 =>
      cases M with | bvar => exact bvar eq (.sort h1) | sort => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .sort h1, fun _ => .bot⟩
    | bvar h1 => cases M with | bvar => exact bvar eq (.bvar h1) | _ => cases eq
    | app hf ha h1 ih_f ih_a =>
      cases M with | bvar => exact bvar eq (.app hf ha h1) | app F' A' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hF, h₁⟩ := ih_f F' σ rfl
      have ⟨ρ₂, hA, h₂⟩ := ih_a A' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | @lam n₁ ρ A F m_orig a f ha hdom hbody h1 ih_a ih_body =>
      cases M with | bvar => exact bvar eq (.lam ha hdom hbody h1) | lam A' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', Interp env ρ' a.T A' ∧ (∀ i, Interp env ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, Interp env (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', ha', hρ, H⟩ := this
        refine ⟨ρ', .lam ha' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1.T⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', Interp env ρ' x.2.T F' ∧ ∀ i, Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρA, ha', hρA⟩ := ih_a A' σ rfl
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', Interp env ρ' x.2.T F' ∧ ∀ i, Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', Interp env ρ' a.T A' ∧ (∀ i, Interp env ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              Interp env (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with | nil => exact ⟨ρA, ha', hρA, nofun⟩ | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, ha₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : Interp env ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha₂.mono_l hj2, fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @forallE n₁ ρ B F m_orig b b' f hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.forallE hb hb' hdom hbody h1) | forallE B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', Interp env ρ' b.T B' ∧ Interp env ρ' b'.T B' ∧
          (∀ i, Interp env ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, Interp env (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', Interp env ρ' x.2.T F' ∧ ∀ i, Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', Interp env ρ' x.2.T F' ∧ ∀ i, Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', Interp env ρ' b.T B' ∧ Interp env ρ' b'.T B' ∧ (∀ i, Interp env ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              Interp env (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : Interp env ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        refine hy.mono_l ?_
        rw [← show ρ₁'.push (ρ₁ 0) = ρ₁ from by funext i; cases i <;> rfl]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | const h1 h2 h3 h4 h5 h6 h7 =>
      cases M with
      | bvar => exact bvar eq (.const h1 h2 h3 h4 h5 h6 h7) | const => ?_ | _ => cases eq
      cases eq
      exact ⟨.nil, .const h1 h2 h3 h4 h5 h6 h7, fun _ => .bot⟩
    | elim h1 h3 h4 h5 h6 h7 =>
      cases M with
      | bvar => exact bvar eq (.elim h1 h3 h4 h5 h6 h7) | elim => ?_ | _ => cases eq
      cases eq
      exact ⟨.nil, .elim h1 h3 h4 h5 h6 h7, fun _ => .bot⟩
    | proj h1 h2 hi h3 ih =>
      cases M with
      | bvar => exact bvar eq (.proj h1 h2 hi h3) | proj => ?_ | _ => cases eq
      cases eq
      have ⟨ρ', a, b⟩ := ih _ σ rfl
      exact ⟨ρ', .proj h1 a hi h3, b⟩
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 h3 h4 h5 h6 h7
    | elim h1 h3 h4 h5 h6 h7 => exact .elim h1 h3 h4 h5 h6 h7
    | proj h1 _ hi h3 ih => exact .proj h1 (ih h) hi h3

theorem Interp.inst : Interp env ρ f (F.inst A) ↔
    ∃ a, Interp env (ρ.push a) f F ∧ Interp env ρ a A := by
  rw [VExpr.inst_eq]
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · have ⟨ρ', hF, hσ⟩ := Interp.subst.1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · exact Interp.subst.2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem Interp.forallE_inv {b} {f : WShapeFun n} {B F}
    (H : Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    Interp env ρ b.T B ∧ ∀ {{X x}}, Interp env ρ x.T X → Interp env ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem Interp.forallE_inv' {b} {f : WShapeFun n} {B F}
    (H : Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    Interp env ρ b.T B ∧ ∀ x, Interp env (ρ.push x.T) (f.app x).T F := by
  refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (Interp.weak (x := x.T) H).forallE_inv.2 .bvar0
  rwa [show (F.liftN 1 1).inst (.bvar 0) = F from VExpr.inst_liftN_bvar F 0] at this

theorem Interp.lam_inv {f : WShapeFun n} {B F}
    (H : Interp env ρ (WShape.T (n := n+1) (.lam' f)) (.lam B F))
    {{X x}} (hx : Interp env ρ x.T X) : Interp env ρ (f.app x).T (F.inst X) := by
  unfold WShape.lam' at H; split at H <;> rename_i hn; rotate_left
  · by_cases hl : f.app x ≤ .bot; · exact .mono hl.T .bot
    have ⟨_, _, h⟩ := f.app_eq x; exact absurd ⟨_, h, hl⟩ hn
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') := by
    rw [WShape.lam_eq_lam' (hl := hn)] at le; exact le.lam'_decomp
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    rw [WShape.LE.def, WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiF x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans ((TShape.LE.def le₂ le₁).2 le2_w)⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono (?_ : (f.app x).T ≤ (f₁.app x₁w).T)
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    show ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem Interp.lam_inv' {f : WShapeFun n} {hl : f.NonZero} {B F}
    (H : Interp env ρ (WShape.T (n := n+1) (WShape.lam f hl)) (.lam B F)) (x : WShape n) :
    Interp env (ρ.push x.T) (f.app x).T F := by
  have := (WShape.lam_eq_lam' ▸ Interp.weak (x := x.T) H).lam_inv .bvar0
  rwa [show (F.liftN 1 1).inst (.bvar 0) = F from VExpr.inst_liftN_bvar F 0] at this


end

/-! ### Equivalent universe levels -/

/-- Two expressions are equal up to `≈` of their universe levels. -/
inductive LvlEqv : VExpr → VExpr → Prop
  | bvar : LvlEqv (.bvar i) (.bvar i)
  | sort : u ≈ u' → LvlEqv (.sort u) (.sort u')
  | const : List.Forall₂ (· ≈ ·) us us' → LvlEqv (.const c us) (.const c us')
  | elim : List.Forall₂ (· ≈ ·) us us' → LvlEqv (.elim b o us) (.elim b o us')
  | app : LvlEqv f f' → LvlEqv a a' → LvlEqv (.app f a) (.app f' a')
  | proj : LvlEqv e e' → LvlEqv (.proj s i e) (.proj s i e')
  | lam : LvlEqv A A' → LvlEqv F F' → LvlEqv (.lam A F) (.lam A' F')
  | forallE : LvlEqv A A' → LvlEqv F F' → LvlEqv (.forallE A F) (.forallE A' F')

theorem levels_inst_equiv {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls')
    (us : List VLevel) :
    List.Forall₂ (· ≈ ·) (us.map (VLevel.inst ls)) (us.map (VLevel.inst ls')) := by
  induction us with
  | nil => exact .nil
  | cons u us ih => exact .cons (VLevel.inst_congr (VLevel.equiv_def'.2 rfl) h) ih

theorem LvlEqv.instL {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ e : VExpr, LvlEqv (e.instL ls) (e.instL ls')
  | .bvar _ => .bvar
  | .sort _ => .sort (VLevel.inst_congr (VLevel.equiv_def'.2 rfl) h)
  | .const _ us => .const (levels_inst_equiv h us)
  | .elim _ _ us => .elim (levels_inst_equiv h us)
  | .app f a => .app (LvlEqv.instL h f) (LvlEqv.instL h a)
  | .proj _ _ e => .proj (LvlEqv.instL h e)
  | .lam A F => .lam (LvlEqv.instL h A) (LvlEqv.instL h F)
  | .forallE A F => .forallE (LvlEqv.instL h A) (LvlEqv.instL h F)

theorem levels_equiv_symm {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    List.Forall₂ (· ≈ ·) ls' ls :=
  h.flip.imp fun _ _ h => VLevel.equiv_def'.2 (VLevel.equiv_def'.1 h).symm

theorem levels_map_eval {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    ls.map (·.eval) = ls'.map (·.eval) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih, VLevel.equiv_def'.1 h]

section
variable [SemSig] {env : VEnv}

theorem Const.lvlEqv {R : Valuation → TShape → VExpr → Prop} {ls ls' : List VLevel}
    (hls : List.Forall₂ (· ≈ ·) ls ls') {rargs : List (WShape n)}
    (H : Const env R h ls rargs m) :
    Const env (fun ρ m e => ∃ e₀, LvlEqv e₀ e ∧ R ρ m e₀) h ls' rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ctor h1 h2 h3 h4 => exact .ctor h1 h2 h3 h4
  | rigid h1 h2 h3 h4 h5 h6 =>
    refine .rigid h1 h2 h3 h4 (fun p hp => ?_) (levels_map_eval hls ▸ h6)
    have ⟨_, _, _, a1, a2, a3, a4⟩ := h5 p hp
    exact ⟨_, _, _, a1, a2, ⟨_, LvlEqv.instL hls _, a3⟩, a4⟩
  | rule h1 h2 h3 h4 h5 h6 =>
    exact .rule h1 h2 (hls.length_eq ▸ h3) h4 h5 ⟨_, LvlEqv.instL hls _, h6⟩
  | ruleAB h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .ruleAB h1 h2 (hls.length_eq ▸ h3) h4 h5 (RuleMajor.lvls_congr hls ▸ h6) h7 h8 h9
      ⟨_, LvlEqv.instL hls _, h10⟩
  | ruleC h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .ruleC h1 h2 (hls.length_eq ▸ h3) h4 h5 (RuleMajor.lvls_congr hls ▸ h6) h7 h8
      ⟨_, LvlEqv.instL hls _, h9⟩

/-- Expressions equal up to equivalence of their levels have the same approximations. -/
theorem Interp.lvlEqv (H : Interp env ρ m e) (h : LvlEqv e e') : Interp env ρ m e' := by
  induction H generalizing e' with
  | bot => exact .bot
  | bvar h1 => cases h; exact .bvar h1
  | sort h1 => let .sort hu := h; exact .sort (VLevel.equiv_def'.1 hu ▸ h1)
  | app _ _ h1 ih_f ih_a => let .app hf ha := h; exact .app (ih_f hf) (ih_a ha) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    let .lam hA hF := h; exact .lam (ih_a hA) hdom (fun x hx => ih_body x hx hF) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    let .forallE hA hF := h
    exact .forallE (ih_b hA) (ih_b' hA) hdom (fun x hx => ih_body x hx hF) h1
  | const h1 h2 h3 h4 _ h6 _ ih5 ih7 =>
    let .const hus := h
    exact .const h1 (hus.length_eq ▸ h2) h3 h4 (ih5 (LvlEqv.instL hus _)) (h6.lvlEqv hus)
      fun _ _ _ ⟨_, a1, a2⟩ => ih7 _ _ _ a2 a1
  | elim h1 h3 h4 _ h6 _ ih5 ih7 =>
    let .elim hus := h
    exact .elim h1 h3 h4 (ih5 (LvlEqv.instL hus _)) (h6.lvlEqv hus)
      fun _ _ _ ⟨_, a1, a2⟩ => ih7 _ _ _ a2 a1
  | proj h1 _ hi h3 ih => let .proj he := h; exact .proj h1 (ih he) hi h3

theorem Interp.instL_equiv {e : VExpr} {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    Interp env ρ m (e.instL ls) ↔ Interp env ρ m (e.instL ls') :=
  ⟨(·.lvlEqv (LvlEqv.instL h e)), (·.lvlEqv (LvlEqv.instL (levels_equiv_symm h) e))⟩

end

end Lean4Lean.ShapeModel
