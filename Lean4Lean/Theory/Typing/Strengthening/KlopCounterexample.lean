import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.EnvLemmas

/-! # A candidate counterexample to strengthening under canonical `Eq`

Klop's counterexample to confluence of the λ-calculus with a non-left-linear rule
`D x x → E` transfers to this calculus, because `Eq.rec` at a constant motive is such a rule
(`@Eq.rec T a (fun _ _ => T) E b h ≡ E` exactly when `a ≡ b`) and `mutualDef` admits looping
definitions. Take an environment with canonical `Eq` and

```text
T   : Type                         (axiom)
E   : T                            (axiom)
P   : Prop                         (axiom)
H   : ∀ x y : T, x = y             (axiom)
C   : T → T := fun x => @Eq.rec T x (fun _ _ => T) E (C x) (H x (C x))     (looping)
Fix : P → T := fun p => C (Fix p)                                           (looping)
```

Under a hypothesis `z : P` the term `Fix z` is a fixed point of `C`, so the `Eq.rec` in
`C (Fix z)` has definitionally equal endpoints and computes: `Fix z ≡ C (Fix z) ≡ E`. Hence
`C E ≡ C (Fix z) ≡ Fix z ≡ E` in the context `[P]` (`KlopEnv.above`). The two closed terms
`C E` and `E` do not mention the hypothesis.

Without the hypothesis, `C E` unfolds to an `Eq.rec` whose endpoints are `E` and `C E`: it
computes only if `C E ≡ E` already holds. The equation supports itself and nothing grounds it,
since `Fix` cannot be applied without a proof of `P`. That `C E ≡ E` is not derivable in the
empty context is **not proved here** (`KlopEnv.Separated`); see `FIRST_PRINCIPLES.md` §7 for
the argument. Given it, `IsDefEqU.weakN_iff` fails for this environment
(`KlopEnv.not_strengthening`).
-/

namespace Lean4Lean
open VExpr

namespace VEnv.Strengthening

/-- Normalize instantiations and lifts of equality syntax. -/
local macro "eqnorm" : tactic => `(tactic| simp [VEnv.HasType, VExpr.inst, VExpr.liftN, VExpr.lift, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift])
local macro "eqnorm" " at " h:ident : tactic =>
  `(tactic| simp [VExpr.inst, VExpr.liftN, VExpr.lift, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift] at $h:ident)

abbrev klopT : VExpr := .const `Klop.T []
abbrev klopE : VExpr := .const `Klop.E []
abbrev klopP : VExpr := .const `Klop.P []
abbrev klopH : VExpr := .const `Klop.H []
abbrev klopC : VExpr := .const `Klop.C []
abbrev klopFix : VExpr := .const `Klop.Fix []

/-- The constant motive `fun (y : T) (_ : a = y) => T`. -/
def klopMotive (a : VExpr) : VExpr :=
  .lam klopT (.lam (VExpr.eqApp (.succ .zero) klopT a.lift (.bvar 0)) klopT)

/-- `@Eq.rec T a (fun _ _ => T) E b h`. -/
def klopD (a b h : VExpr) : VExpr :=
  VExpr.eqRecApp (.succ .zero) (.succ .zero) klopT a (klopMotive a) klopE b h

/-- The body of `C`: `fun x => @Eq.rec T x (fun _ _ => T) E (C x) (H x (C x))`. -/
def klopCBody : VExpr :=
  .lam klopT (klopD (.bvar 0) (.app klopC (.bvar 0))
    (.app (.app klopH (.bvar 0)) (.app klopC (.bvar 0))))

/-- The body of `Fix`: `fun p => C (Fix p)`. -/
def klopFixBody : VExpr := .lam klopP (.app klopC (.app klopFix (.bvar 0)))

/-- The constants `T`, `E`, `H`, `C` of the counterexample are present in `env`. -/
structure KlopSig (env : VEnv) : Prop where
  T : env.constants `Klop.T = some ⟨0, .sort (.succ .zero)⟩
  E : env.constants `Klop.E = some ⟨0, klopT⟩
  H : env.constants `Klop.H = some
    ⟨0, .forallE klopT (.forallE klopT (VExpr.eqApp (.succ .zero) klopT (.bvar 1) (.bvar 0)))⟩
  C : env.constants `Klop.C = some ⟨0, .forallE klopT klopT⟩

/-- The declarations of the counterexample are present in `env`. -/
structure KlopEnv (env : VEnv) : Prop extends KlopSig env where
  P : env.constants `Klop.P = some ⟨0, .sort .zero⟩
  Fix : env.constants `Klop.Fix = some ⟨0, .forallE klopP klopT⟩
  Cdef : env.defeqs ⟨0, klopC, klopCBody, .forallE klopT klopT⟩
  Fixdef : env.defeqs ⟨0, klopFix, klopFixBody, .forallE klopP klopT⟩

variable {env : VEnv} {U : Nat}

namespace KlopSig
variable (K : KlopSig env)
include K

theorem hasT : env.HasType U Γ klopT (.sort (.succ .zero)) := by
  have := HasType.const (U := U) (Γ := Γ) K.T (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasE : env.HasType U Γ klopE klopT := by
  have := HasType.const (U := U) (Γ := Γ) K.E (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasC : env.HasType U Γ klopC (.forallE klopT klopT) := by
  have := HasType.const (U := U) (Γ := Γ) K.C (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasH : env.HasType U Γ klopH
    (.forallE klopT (.forallE klopT (VExpr.eqApp (.succ .zero) klopT (.bvar 1) (.bvar 0)))) := by
  have := HasType.const (U := U) (Γ := Γ) K.H (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst, VExpr.eqApp] using this

theorem hasCApp (ha : env.HasType U Γ a klopT) : env.HasType U Γ (.app klopC a) klopT := by
  simpa [VExpr.inst] using (K.hasC (U := U) (Γ := Γ)).app ha

theorem hasHApp (ha : env.HasType U Γ a klopT) (hb : env.HasType U Γ b klopT) :
    env.HasType U Γ (.app (.app klopH a) b) (VExpr.eqApp (.succ .zero) klopT a b) := by
  have h1 := (K.hasH (U := U) (Γ := Γ)).app ha
  eqnorm at h1
  have h2 := HasType.app (by simpa [VEnv.HasType] using h1) hb
  simpa [VEnv.HasType, VExpr.inst, VExpr.liftN, VExpr.lift, instVar, VExpr.eqApp, inst_lift]
    using h2

variable (henv : env.Ordered) (heq : env.HasCanonicalEq)
include henv heq

theorem motive_inner (ha : env.HasType U Γ a klopT) :
    env.HasType U (klopT :: Γ) (VExpr.eqApp (.succ .zero) klopT a.lift (.bvar 0)) (.sort .zero) :=
  HasType.eqApp heq (show (VLevel.succ .zero).WF U from trivial) K.hasT (ha.weak henv)
    (.bvar .zero)

theorem hasMotive (ha : env.HasType U Γ a klopT) :
    env.HasType U Γ (klopMotive a)
      (.forallE klopT (.forallE (VExpr.eqApp (.succ .zero) klopT a.lift (.bvar 0))
        (.sort (.succ .zero)))) :=
  .lam K.hasT (.lam (K.motive_inner henv heq ha) K.hasT)

/-- Two beta steps: `(fun y _ => T) b h ≡ T`. -/
theorem motive_app (ha : env.HasType U Γ a klopT) (hb : env.HasType U Γ b klopT)
    (hh : env.HasType U Γ h (VExpr.eqApp (.succ .zero) klopT a b)) :
    env.IsDefEq U Γ (.app (.app (klopMotive a) b) h) klopT (.sort (.succ .zero)) := by
  have hinner : env.HasType U (klopT :: Γ)
      (.lam (VExpr.eqApp (.succ .zero) klopT a.lift (.bvar 0)) klopT)
      (.forallE (VExpr.eqApp (.succ .zero) klopT a.lift (.bvar 0)) (.sort (.succ .zero))) :=
    .lam (K.motive_inner henv heq ha) K.hasT
  have hb1 := IsDefEq.beta hinner hb
  eqnorm at hb1
  have hb2 := IsDefEq.appDF hb1 (by simpa [VEnv.HasType, VExpr.eqApp] using hh)
  have hb3 := IsDefEq.beta (K.hasT (U := U) (Γ := VExpr.eqApp (.succ .zero) klopT a b :: Γ))
    (by simpa [VEnv.HasType, VExpr.eqApp] using hh)
  eqnorm at hb2
  eqnorm at hb3
  simpa [klopMotive, VExpr.eqApp, VExpr.lift] using hb2.trans hb3

theorem hasMinor (ha : env.HasType U Γ a klopT) :
    env.HasType U Γ klopE
      (.app (.app (klopMotive a) a) (VExpr.eqReflApp (.succ .zero) klopT a)) :=
  (K.motive_app henv heq ha ha
    (HasType.eqReflApp heq (show (VLevel.succ .zero).WF U from trivial) K.hasT ha)).symm.defeq
    K.hasE

/-- `@Eq.rec T a (fun _ _ => T) E b h : T`. -/
theorem hasD (ha : env.HasType U Γ a klopT) (hb : env.HasType U Γ b klopT)
    (hh : env.HasType U Γ h (VExpr.eqApp (.succ .zero) klopT a b)) :
    env.HasType U Γ (klopD a b h) klopT := by
  have hw : (VLevel.succ .zero).WF U := trivial
  have hr := HasType.eqRecApp heq hw hw K.hasT ha
    (by simpa [VExpr.liftN, VExpr.lift] using K.hasMotive henv heq ha)
    (K.hasMinor henv heq ha) hb hh
  exact (K.motive_app henv heq ha hb hh).defeq hr

end KlopSig

namespace KlopEnv
variable (K : KlopEnv env)
include K

theorem hasP : env.HasType U Γ klopP (.sort .zero) := by
  have := HasType.const (U := U) (Γ := Γ) K.P (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasFix : env.HasType U Γ klopFix (.forallE klopP klopT) := by
  have := HasType.const (U := U) (Γ := Γ) K.Fix (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

variable (henv : env.WF) (heq : env.HasCanonicalEq)
include henv heq

/-- **The non-left-linear rule.** `@Eq.rec T a (fun _ _ => T) E b h ≡ E` when `a ≡ b`: proof
irrelevance makes `h` a reflexivity proof and the ι rule of `Eq.rec` fires. -/
theorem D_eq (hΓ : OnCtx Γ (env.IsType U)) (hab : env.IsDefEq U Γ a b klopT)
    (hh : env.HasType U Γ h (VExpr.eqApp (.succ .zero) klopT a b)) :
    env.IsDefEq U Γ (klopD a b h) klopE klopT := by
  have hw : (VLevel.succ .zero).WF U := trivial
  have ho := henv.ordered
  have ha := hab.hasType.1
  have hb := hab.hasType.2
  have hrefl := HasType.eqReflApp heq hw (K.hasT (U := U) (Γ := Γ)) ha
  have hP := HasType.eqApp heq hw (K.hasT (U := U) (Γ := Γ)) ha hb
  have hreflB : env.HasType U Γ (VExpr.eqReflApp (.succ .zero) klopT a)
      (VExpr.eqApp (.succ .zero) klopT a b) :=
    (IsDefEq.eqApp_r heq hw K.hasT ha hab).defeq hrefl
  have hirr : env.IsDefEq U Γ h (VExpr.eqReflApp (.succ .zero) klopT a)
      (VExpr.eqApp (.succ .zero) klopT a b) := .proofIrrel hP hh hreflB
  have h4 := HasType.eqRec4 heq hw hw K.hasT ha
    (by simpa [VExpr.liftN, VExpr.lift] using K.hasMotive ho heq ha) (K.hasMinor ho heq ha)
  have hc1 := IsDefEq.appDF h4 hab.symm
  eqnorm at hc1
  have hc2 := IsDefEq.appDF hc1 (by simpa [VExpr.eqApp] using hirr)
  eqnorm at hc2
  have hiota := IsDefEq.canonicalEqRec_iota henv heq hΓ
    (v := .succ .zero) (w := .succ .zero) (α := klopT) (a := a) (motive := klopMotive a)
    (minor := klopE) (b := a) (w' := .succ .zero) (α' := klopT) (a' := a)
    (by simpa [VEnv.HasType, VExpr.eqRecApp, VExpr.eqApp, VExpr.eqReflApp] using hc2.hasType.2)
  have hT := K.motive_app ho heq ha hb hh
  have h1 : env.IsDefEq U Γ (klopD a b h) _ klopT := .defeqDF hT (by
    simpa [klopD, VExpr.eqRecApp, VExpr.eqApp, VExpr.eqReflApp] using hc2)
  have h2 : env.IsDefEq U Γ _ klopE klopT := .defeqDF hT (by
    simpa [klopD, VExpr.eqRecApp, VExpr.eqApp, VExpr.eqReflApp] using hiota)
  exact h1.trans h2

/-- Unfolding `C`: `C a ≡ @Eq.rec T a (fun _ _ => T) E (C a) (H a (C a))`. -/
theorem C_unfold (ha : env.HasType U Γ a klopT) :
    env.IsDefEq U Γ (.app klopC a)
      (klopD a (.app klopC a) (.app (.app klopH a) (.app klopC a))) klopT := by
  have ho := henv.ordered
  have hx : env.HasType U (klopT :: Γ) (.bvar 0) klopT := .bvar .zero
  have hbody := K.hasD ho heq hx (K.hasCApp hx) (K.hasHApp hx (K.hasCApp hx))
  have hd := IsDefEq.extra (uvars := U) (Γ := Γ) K.Cdef (ls := []) (by simp) rfl
  have hd' : env.IsDefEq U Γ klopC klopCBody (.forallE klopT klopT) := by
    simpa [VExpr.instL, VLevel.inst, klopCBody, klopD, klopMotive, VExpr.eqRecApp, VExpr.eqApp] using hd
  have h1 := IsDefEq.appDF hd' ha
  have h2 := IsDefEq.beta hbody ha
  simp [VExpr.inst] at h1
  simp [klopD, klopMotive, VExpr.eqRecApp, VExpr.eqApp, VExpr.inst, VExpr.liftN, VExpr.lift,
    instVar, liftN_liftN, inst_liftN_lo, inst_lift] at h2
  simpa [klopCBody, klopD, klopMotive, VExpr.eqRecApp, VExpr.eqApp, VExpr.lift] using h1.trans h2

/-- Unfolding `Fix`: `Fix p ≡ C (Fix p)`. -/
theorem Fix_unfold (hp : env.HasType U Γ p klopP) :
    env.IsDefEq U Γ (.app klopFix p) (.app klopC (.app klopFix p)) klopT := by
  have hx : env.HasType U (klopP :: Γ) (.bvar 0) klopP := .bvar .zero
  have hfx : env.HasType U (klopP :: Γ) (.app klopFix (.bvar 0)) klopT := by
    simpa [VExpr.inst] using (K.hasFix (U := U) (Γ := klopP :: Γ)).app hx
  have hbody := K.hasCApp hfx
  have hd := IsDefEq.extra (uvars := U) (Γ := Γ) K.Fixdef (ls := []) (by simp) rfl
  have hd' : env.IsDefEq U Γ klopFix klopFixBody (.forallE klopP klopT) := by
    simpa [VExpr.instL, VLevel.inst, klopFixBody] using hd
  have h1 := IsDefEq.appDF hd' hp
  have h2 := IsDefEq.beta hbody hp
  simp [VExpr.inst] at h1
  simp [VExpr.inst, instVar] at h2
  simpa [klopFixBody] using h1.trans h2

/-- A fixed point of `C` is `E`: Klop's collapse. -/
theorem fixed_point_eq (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.IsDefEq U Γ A (.app klopC A) klopT) : env.IsDefEq U Γ A klopE klopT := by
  have ha := hA.hasType.1
  have hCA := hA.hasType.2
  exact hA.trans ((K.C_unfold henv heq ha).trans
    (K.D_eq henv heq hΓ hA (K.hasHApp ha hCA)))

/-- **The larger context.** Under a hypothesis of type `P`, `C E ≡ E`. -/
theorem above : env.IsDefEqU U [klopP] (.app klopC klopE) klopE := by
  have hΓ : OnCtx [klopP] (env.IsType U) := ⟨trivial, _, K.hasP⟩
  have hz : env.HasType U [klopP] (.bvar 0) klopP := .bvar .zero
  have hAE := K.fixed_point_eq henv heq hΓ (K.Fix_unfold henv heq hz)
  have h1 : env.IsDefEq U [klopP] (.app klopC klopE) (.app klopC (.app klopFix (.bvar 0)))
      klopT := by
    simpa [VExpr.inst] using IsDefEq.appDF (K.hasC (U := U) (Γ := [klopP])) hAE.symm
  exact ⟨_, h1.trans ((K.Fix_unfold henv heq hz).symm.trans hAE)⟩

/-- The missing half: `C E ≡ E` is not derivable in the empty context. Not proved here. -/
def Separated (_ : KlopEnv env) (U : Nat) : Prop :=
  ¬ env.IsDefEqU U [] (.app klopC klopE) klopE

/-- Given the separation in the empty context, strengthening of definitional equality fails
for this environment, although it has canonical `Eq`. -/
theorem not_strengthening (hsep : K.Separated U) :
    ¬ ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) := by
  intro H
  have hΓ : OnCtx [klopP] (env.IsType U) := ⟨trivial, _, K.hasP⟩
  have W : Ctx.LiftN 1 0 [] [klopP] := .one
  exact hsep ((H (e1 := .app klopC klopE) (e2 := klopE) hΓ W).1
    (by simpa [VExpr.liftN] using K.above henv heq (U := U)))

end KlopEnv

/-! ## The environment exists

Any well-formed environment with canonical `Eq` in which the six names are fresh extends to a
well-formed environment with canonical `Eq` satisfying `KlopEnv`: four axioms and two
single-constant `mutualDef` blocks. -/

theorem hasT_of {env : VEnv} (h : env.constants `Klop.T = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType U Γ klopT (.sort (.succ .zero)) := by
  have := HasType.const (U := U) (Γ := Γ) h (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasP_of {env : VEnv} (h : env.constants `Klop.P = some ⟨0, .sort .zero⟩) :
    env.HasType U Γ klopP (.sort .zero) := by
  have := HasType.const (U := U) (Γ := Γ) h (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem hasFix_of {env : VEnv} (h : env.constants `Klop.Fix = some ⟨0, .forallE klopP klopT⟩) :
    env.HasType U Γ klopFix (.forallE klopP klopT) := by
  have := HasType.const (U := U) (Γ := Γ) h (ls := []) (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

/-- Add an axiom to a well-formed environment. -/
theorem exists_axiom {env : VEnv} (h : env.WF) (ci : VConstVal)
    (hw : ci.toVConstant.WF env) (hf : env.constants ci.name = none) :
    ∃ env', env'.WF ∧ env ≤ env' ∧ env'.constants ci.name = some ci.toVConstant ∧
      ∀ n, n ≠ ci.name → env'.constants n = env.constants n := by
  obtain ⟨env', a⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) hf
  obtain ⟨ds, h⟩ := h
  refine ⟨env', ⟨_, .decl (.axiom hw a) h⟩, VEnv.addConst_le a, VEnv.addConst_self a, ?_⟩
  intro n hn
  rw [VEnv.addConst_constants_eq a]
  simp [Ne.symm hn]

/-- Add a single-constant `mutualDef` block to a well-formed environment. The value is typed
in the environment extended by the constant, so it may mention the constant: the definition
may loop. -/
theorem exists_mutualDef {env : VEnv} (h : env.WF) (ci : VDefVal)
    (hty : ci.toVConstant.WF env) (hf : env.constants ci.name = none)
    (hval : ∀ env', env'.Ordered → env ≤ env' →
      env'.constants ci.name = some ci.toVConstant → ci.WF env') :
    ∃ env', env'.WF ∧ env ≤ env' ∧ env'.constants ci.name = some ci.toVConstant ∧
      env'.defeqs ci.toDefEq ∧ ∀ n, n ≠ ci.name → env'.constants n = env.constants n := by
  obtain ⟨e', a⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) hf
  have a' : env.addConsts [ci] = some e' := by simp [VEnv.addConsts, a]
  have ord' := VEnv.addConsts_ordered h.ordered (cis := [ci]) (by simpa using hty) a'
  have hv := hval e' ord' (VEnv.addConst_le a) (VEnv.addConst_self a)
  have W : VDecl.WF env (.mutualDef [ci]) (e'.addDefEqs [ci]) :=
    .mutualDef (by simpa using hty) a' (by simpa using hv)
  obtain ⟨ds, h⟩ := h
  refine ⟨e'.addDefEqs [ci], ⟨_, .decl W h⟩, (VEnv.addConst_le a).trans VEnv.addDefEq_le,
    VEnv.addDefEq_le.constants (VEnv.addConst_self a), .inl rfl, ?_⟩
  intro n hn
  show e'.constants n = _
  rw [VEnv.addConst_constants_eq a]
  simp [Ne.symm hn]

/-- **The environment of the counterexample exists.** -/
theorem exists_klopEnv {env₀ : VEnv} (h₀ : env₀.WF) (heq₀ : env₀.HasCanonicalEq)
    (fT : env₀.constants `Klop.T = none) (fE : env₀.constants `Klop.E = none)
    (fP : env₀.constants `Klop.P = none) (fH : env₀.constants `Klop.H = none)
    (fC : env₀.constants `Klop.C = none) (fFix : env₀.constants `Klop.Fix = none) :
    ∃ env, env.WF ∧ env.HasCanonicalEq ∧ env₀ ≤ env ∧ KlopEnv env := by
  have hw : (VLevel.succ .zero).WF 0 := trivial
  -- T
  obtain ⟨e1, w1, l1, cT1, k1⟩ := exists_axiom h₀ ⟨⟨0, .sort (.succ .zero)⟩, `Klop.T⟩
    ⟨_, HasType.sort hw⟩ fT
  -- E
  obtain ⟨e2, w2, l2, cE2, k2⟩ := exists_axiom w1 ⟨⟨0, klopT⟩, `Klop.E⟩
    ⟨_, hasT_of cT1⟩ (by rw [k1 _ (by decide)]; exact fE)
  -- P
  obtain ⟨e3, w3, l3, cP3, k3⟩ := exists_axiom w2 ⟨⟨0, .sort .zero⟩, `Klop.P⟩
    ⟨_, HasType.sort (show VLevel.zero.WF 0 from trivial)⟩
    (by rw [k2 _ (by decide), k1 _ (by decide)]; exact fP)
  have cT3 := l3.constants (l2.constants cT1)
  have heq3 := heq₀.mono (l1.trans (l2.trans l3))
  -- H
  obtain ⟨e4, w4, l4, cH4, k4⟩ := exists_axiom w3
    ⟨⟨0, .forallE klopT (.forallE klopT
      (VExpr.eqApp (.succ .zero) klopT (.bvar 1) (.bvar 0)))⟩, `Klop.H⟩
    ⟨_, .forallE (hasT_of cT3) (.forallE (hasT_of cT3)
      (HasType.eqApp heq3 hw (hasT_of cT3) (.bvar (.succ .zero)) (.bvar .zero)))⟩
    (by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]; exact fH)
  have cT4 := l4.constants cT3
  have cE4 := l4.constants (l3.constants cE2)
  have heq4 := heq3.mono l4
  -- C
  obtain ⟨e5, w5, l5, cC5, dC5, k5⟩ := exists_mutualDef w4
    ⟨⟨⟨0, .forallE klopT klopT⟩, `Klop.C⟩, klopCBody⟩
    ⟨_, .forallE (hasT_of cT4) (hasT_of cT4)⟩
    (by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]; exact fC)
    (fun e' ord' le' cC' => by
      have S : KlopSig e' := ⟨le'.constants cT4, le'.constants cE4, le'.constants cH4, cC'⟩
      have hx : e'.HasType 0 [klopT] (.bvar 0) klopT := .bvar .zero
      exact .lam S.hasT (S.hasD ord' (heq4.mono le') hx (S.hasCApp hx)
        (S.hasHApp hx (S.hasCApp hx))))
  have S5 : KlopSig e5 :=
    ⟨l5.constants cT4, l5.constants cE4, l5.constants cH4, cC5⟩
  have cP5 := l5.constants (l4.constants cP3)
  -- Fix
  obtain ⟨e6, w6, l6, cF6, dF6, k6⟩ := exists_mutualDef w5
    ⟨⟨⟨0, .forallE klopP klopT⟩, `Klop.Fix⟩, klopFixBody⟩
    ⟨_, .forallE (hasP_of cP5) S5.hasT⟩
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide),
          k1 _ (by decide)]; exact fFix)
    (fun e' ord' le' cF' => by
      have S : KlopSig e' := ⟨le'.constants S5.T, le'.constants S5.E, le'.constants S5.H,
        le'.constants S5.C⟩
      have hx : e'.HasType 0 [klopP] (.bvar 0) klopP := .bvar .zero
      have hfx : e'.HasType 0 [klopP] (.app klopFix (.bvar 0)) klopT := by
        simpa [VExpr.inst] using (hasFix_of (U := 0) (Γ := [klopP]) cF').app hx
      exact .lam (hasP_of (le'.constants cP5)) (S.hasCApp hfx))
  refine ⟨e6, w6, (heq4.mono l5).mono l6, l1.trans (l2.trans (l3.trans (l4.trans (l5.trans l6)))),
    ⟨⟨l6.constants S5.T, l6.constants S5.E, l6.constants S5.H, l6.constants S5.C⟩,
      l6.constants cP5, cF6, ?_, ?_⟩⟩
  · simpa [VDefVal.toDefEq, VLevel.params] using l6.defeqs dC5
  · simpa [VDefVal.toDefEq, VLevel.params] using dF6

end VEnv.Strengthening
end Lean4Lean
