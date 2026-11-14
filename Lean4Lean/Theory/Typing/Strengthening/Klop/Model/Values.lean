import Lean4Lean.Theory.VExpr

/-! # Proof values and candidates

`PVal` is the untyped λ-calculus with tokens `r`, `bot` and a `case` construct. `Step` is one
step of weak head reduction; it is deterministic. A `Candidate` is a set of values closed
under `Step` in both directions; it is `Good` when it is empty or contains every value that
reduces to `bot`. Propositions of the model denote good candidates, and a proof realizes a
proposition when its value is in the candidate.

`r` and `bot` are distinct normal forms, so the candidate `botOnly` does not contain `r`
while `rOrBot` does: this is how the model tells a proof by `Eq.refl` from a proof by the
axiom `H`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- Untyped proof values. -/
inductive PVal where
  | var (i : Nat)
  | lam (body : PVal)
  | app (f a : PVal)
  | r
  | bot
  | case (scrut ifR other : PVal)

namespace PVal

/-- Shift the variables `≥ k` by `n` (mirrors `VExpr.liftN`). -/
def liftN (n : Nat) : PVal → (k : Nat := 0) → PVal
  | .var i, k => .var (liftVar n i k)
  | .lam b, k => .lam (b.liftN n (k + 1))
  | .app f a, k => .app (f.liftN n k) (a.liftN n k)
  | .r, _ => .r
  | .bot, _ => .bot
  | .case s u v, k => .case (s.liftN n k) (u.liftN n k) (v.liftN n k)

/-- Substitute `e` for variable `k` (mirrors `VExpr.inst`). -/
def inst : PVal → PVal → (k : Nat := 0) → PVal
  | .var i, e, k => if i < k then .var i else if i = k then e.liftN k else .var (i - 1)
  | .lam b, e, k => .lam (b.inst e (k + 1))
  | .app f a, e, k => .app (f.inst e k) (a.inst e k)
  | .r, _, _ => .r
  | .bot, _, _ => .bot
  | .case s u v, e, k => .case (s.inst e k) (u.inst e k) (v.inst e k)

theorem liftN_zero (e : PVal) (k : Nat) : e.liftN 0 k = e := by
  induction e generalizing k with
  | var i => simp [liftN, liftVar]
  | lam b ih => simp [liftN, ih]
  | app f a ihf iha => simp [liftN, ihf, iha]
  | r => rfl
  | bot => rfl
  | case s u v ihs ihu ihv => simp [liftN, ihs, ihu, ihv]

/-- Instantiating a variable that a lift has skipped undoes one level of the lift. -/
theorem inst_liftN (e a : PVal) (n j k : Nat) (hj : j ≤ k) (hk : k ≤ n + j) :
    (e.liftN (n + 1) j).inst a k = e.liftN n j := by
  induction e generalizing j k with
  | var i =>
    simp only [liftN, inst, liftVar]
    split
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega
  | lam b ih => simp [liftN, inst, ih (j + 1) (k + 1) (by omega) (by omega)]
  | app f x ihf ihx => simp [liftN, inst, ihf j k hj hk, ihx j k hj hk]
  | r => rfl
  | bot => rfl
  | case s u v ihs ihu ihv => simp [liftN, inst, ihs j k hj hk, ihu j k hj hk, ihv j k hj hk]

/-- One step of weak head reduction. -/
inductive Step : PVal → PVal → Prop where
  | beta : Step (.app (.lam b) a) (b.inst a)
  | botApp : Step (.app .bot a) .bot
  | appL : Step f f' → Step (.app f a) (.app f' a)
  | caseR : Step (.case .r u v) u
  | caseBot : Step (.case .bot u v) v
  | caseS : Step s s' → Step (.case s u v) (.case s' u v)

theorem lam_not_step : ¬ Step (.lam b) v := nofun
theorem r_not_step : ¬ Step .r v := nofun
theorem bot_not_step : ¬ Step .bot v := nofun

/-- Weak head reduction is deterministic. -/
theorem Step.deterministic (h1 : Step a b) (h2 : Step a c) : b = c := by
  induction h1 generalizing c with
  | beta => cases h2 with
    | beta => rfl
    | appL h => exact absurd h lam_not_step
  | botApp => cases h2 with
    | botApp => rfl
    | appL h => exact absurd h bot_not_step
  | appL h ih => cases h2 with
    | beta => exact absurd h lam_not_step
    | botApp => exact absurd h bot_not_step
    | appL h' => rw [ih h']
  | caseR => cases h2 with
    | caseR => rfl
    | caseS h => exact absurd h r_not_step
  | caseBot => cases h2 with
    | caseBot => rfl
    | caseS h => exact absurd h bot_not_step
  | caseS h ih => cases h2 with
    | caseR => exact absurd h r_not_step
    | caseBot => exact absurd h bot_not_step
    | caseS h' => rw [ih h']

/-- Weak head reduction. -/
inductive Steps : PVal → PVal → Prop where
  | rfl : Steps a a
  | head : Step a b → Steps b c → Steps a c

theorem Steps.trans (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | rfl => exact h2
  | head h _ ih => exact .head h (ih h2)

theorem Steps.single (h : Step a b) : Steps a b := .head h .rfl

/-- Two reductions from the same value are comparable. -/
theorem Steps.linear (h1 : Steps a b) (h2 : Steps a c) : Steps b c ∨ Steps c b := by
  induction h1 generalizing c with
  | rfl => exact .inl h2
  | head h _ ih => cases h2 with
    | rfl => exact .inr (.head h ‹_›)
    | head h' h2 => cases h.deterministic h'; exact ih h2

theorem Steps.caseS (h : Steps s s') : Steps (.case s u v) (.case s' u v) := by
  induction h with
  | rfl => exact .rfl
  | head h _ ih => exact .head (.caseS h) ih

/-- `v` reduces to the token `r`. -/
def ToR (v : PVal) : Prop := Steps v .r

/-- `v` reduces to the token `bot`. -/
def ToBot (v : PVal) : Prop := Steps v .bot

theorem steps_r (h : Steps .r v) : v = .r := by
  cases h with
  | rfl => rfl
  | head h _ => exact absurd h r_not_step

theorem steps_bot (h : Steps .bot v) : v = .bot := by
  cases h with
  | rfl => rfl
  | head h _ => exact absurd h bot_not_step

/-- No value reduces both to `r` and to `bot`. -/
theorem not_toR_toBot (h1 : ToR v) (h2 : ToBot v) : False := by
  rcases Steps.linear h1 h2 with h | h
  · cases steps_r h
  · cases steps_bot h

end PVal

/-- A candidate: a set of values closed under weak head reduction and expansion. -/
structure Candidate where
  mem : PVal → Prop
  step : ∀ {a b}, PVal.Step a b → (mem a ↔ mem b)

namespace Candidate

theorem steps (S : Candidate) (h : PVal.Steps a b) : S.mem a ↔ S.mem b := by
  induction h with
  | rfl => exact .rfl
  | head h _ ih => exact (S.step h).trans ih

/-- The empty candidate. -/
def empty : Candidate := ⟨fun _ => False, fun _ => .rfl⟩

/-- The full candidate. -/
def full : Candidate := ⟨fun _ => True, fun _ => .rfl⟩

/-- A reduction to a normal form factors through the first step. -/
theorem _root_.Lean4Lean.VEnv.Strengthening.PVal.steps_of_step {a b t : PVal}
    (h : PVal.Step a b) (ha : PVal.Steps a t) (ht : ∀ v, ¬ PVal.Step t v) : PVal.Steps b t := by
  cases ha with
  | rfl => exact absurd h (ht _)
  | head h' ha => cases h.deterministic h'; exact ha

/-- Values reducing to `bot`: the realizers of a true equation with distinct endpoints. -/
def botOnly : Candidate where
  mem := PVal.ToBot
  step h := ⟨fun ha => PVal.steps_of_step h ha fun _ => PVal.bot_not_step, fun hb => .head h hb⟩

/-- Values reducing to `r` or to `bot`: the realizers of an equation with identical
endpoints. -/
def rOrBot : Candidate where
  mem v := PVal.ToR v ∨ PVal.ToBot v
  step h := ⟨fun ha => ha.imp (fun x => PVal.steps_of_step h x fun _ => PVal.r_not_step)
      (fun x => PVal.steps_of_step h x fun _ => PVal.bot_not_step),
    fun hb => hb.imp (.head h) (.head h)⟩

/-- A candidate of the model: empty, or containing `bot`. -/
def Good (S : Candidate) : Prop := (∀ v, ¬ S.mem v) ∨ S.mem .bot

theorem good_empty : empty.Good := .inl fun _ h => h
theorem good_full : full.Good := .inr trivial
theorem good_botOnly : botOnly.Good := .inr .rfl
theorem good_rOrBot : rOrBot.Good := .inr (.inr .rfl)

/-- The realizers of a function proposition: values sending every member of `A` to a member
of `B`. -/
def arrow (A B : Candidate) : Candidate where
  mem v := ∀ u, A.mem u → B.mem (.app v u)
  step h := ⟨fun H u hu => (B.step (.appL h)).1 (H u hu),
    fun H u hu => (B.step (.appL h)).2 (H u hu)⟩

end Candidate

end VEnv.Strengthening
end Lean4Lean
