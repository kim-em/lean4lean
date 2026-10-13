import Lean4Lean.Theory.Typing.Strengthening.DevelopmentRounds

/-! # A finite development including upward-created beta redexes

`superdevelop` recursively develops a function and its argument, then contracts if the
developed function is a lambda. It does not recurse into the result of substitution.
Thus it handles upward creation along an application spine in one pass while leaving
downward-created redexes for a later pass. The recursion is structural in the original
term and needs no normalization assumption.

The distinction is the type I/II versus type III creation distinction discussed in
Bonelli--Barenbaum, *Superdevelopments for Weak Reduction*, §1,
https://arxiv.org/pdf/1001.4429. The operation below is on the full annotated `VExpr`
syntax, including reduction under binders and inside annotations.
-/

namespace Lean4Lean.VEnv.Strengthening.Developments
open VExpr

/-- Contract a root redex if present, without visiting the contractum. -/
def contractApp : VExpr → VExpr → VExpr
  | .lam _ b, a => b.inst a
  | f, a => .app f a

def superdevelop : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => contractApp (superdevelop f) (superdevelop a)
  | .lam A b => .lam (superdevelop A) (superdevelop b)
  | .forallE A b => .forallE (superdevelop A) (superdevelop b)
  | .proj c i m => .proj c i (superdevelop m)

theorem contractApp_betaRed (f a : VExpr) : BetaRed (.app f a) (contractApp f a) := by
  cases f <;> first | exact .beta | exact .refl

/-- The structurally computed superdevelopment is a finite beta reduction. -/
theorem superdevelop_betaRed (e : VExpr) : BetaRed e (superdevelop e) := by
  induction e with
  | bvar | sort | const => exact .refl
  | app f a ihf iha => exact (BetaRed.app ihf iha).trans (contractApp_betaRed _ _)
  | lam A b ihA ihb => exact .lam ihA ihb
  | forallE A b ihA ihb => exact .forallE ihA ihb
  | proj c i m ih => exact .proj ih

/-- Superdevelopment preserves every original typing in a well-formed context. -/
theorem superdevelop_simAt {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (e : VExpr) :
    env.SimAt U Γ e (superdevelop e) :=
  (superdevelop_betaRed e).simAt henv.orderedStrong henv.betaSubjectReduction hΓ

theorem contractApp_liftN (f a : VExpr) (n k : Nat) :
    contractApp (f.liftN n k) (a.liftN n k) = (contractApp f a).liftN n k := by
  cases f <;> simp only [contractApp, liftN]
  exact (liftN_inst_hi ..).symm

/-- Superdevelopment commutes with binder insertion, so it preserves the required
syntactic absence of the removed variables. -/
theorem superdevelop_liftN (e : VExpr) (n k : Nat) :
    superdevelop (e.liftN n k) = (superdevelop e).liftN n k := by
  induction e generalizing k with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [liftN, superdevelop, ihf, iha, contractApp_liftN]
  | lam A b ihA ihb | forallE A b ihA ihb => simp only [liftN, superdevelop, ihA, ihb]
  | proj c i m ih => simp only [liftN, superdevelop, ih]

/-- Developing both endpoints preserves and reflects their fixed-type equality.
This uses their original typings, not context strengthening. -/
theorem superdevelop_eq_iff {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.HasType U Γ a T) (hb : env.HasType U Γ b T) :
    env.IsDefEq U Γ (superdevelop a) (superdevelop b) T ↔ env.IsDefEq U Γ a b T := by
  have h₁ := superdevelop_simAt henv hΓ a T ha
  have h₂ := superdevelop_simAt henv hΓ b T hb
  exact ⟨fun h => h₁.trans (h.trans h₂.symm), fun h => h₁.symm.trans (h.trans h₂)⟩

/-- Any hypothetical typed-front failure remains a failure after this pass, with
smaller-context typings and the lifted equation still available. What remains missing
for an iterative proof is a well-founded order for the downward-created obstructing
comparisons; termination of one pass does not supply it. -/
theorem superdevelop_front_failure {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U Γ a T) (hb : env.HasType U Γ b T)
    (hab : env.IsDefEq U (Q :: Γ) a.lift b.lift T.lift)
    (hne : ¬ env.IsDefEq U Γ a b T) :
    env.HasType U Γ (superdevelop a) T ∧
    env.HasType U Γ (superdevelop b) T ∧
    env.IsDefEq U (Q :: Γ) (superdevelop a).lift (superdevelop b).lift T.lift ∧
    ¬ env.IsDefEq U Γ (superdevelop a) (superdevelop b) T := by
  refine ⟨(superdevelop_simAt henv hΓ.1 a T ha).hasType.2,
    (superdevelop_simAt henv hΓ.1 b T hb).hasType.2, ?_, ?_⟩
  · have h := (superdevelop_eq_iff henv hΓ (ha.weak henv.ordered)
      (hb.weak henv.ordered)).2 hab
    simpa only [lift, superdevelop_liftN] using h
  · exact fun h => hne ((superdevelop_eq_iff henv hΓ.1 ha hb).1 h)

theorem superdevelop_tower (n : Nat) : superdevelop (tower n) = tower n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, superdevelop, ih]

theorem superdevelop_ident (k : Nat) : superdevelop (ident k) = ident k := by
  simp only [ident, superdevelop, superdevelop_tower]

/-- The unbounded ordinary-round example is completely handled by upward creation
in a single structural pass. It is not a counterexample to superdevelopments. -/
theorem superdevelop_chain (n k : Nat) : superdevelop (chain n k) = ident k := by
  induction n generalizing k with
  | zero => exact superdevelop_ident k
  | succ n ih =>
    simp only [chain, superdevelop, ih, ident, superdevelop_tower, contractApp,
      VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, liftN_zero]

/-- A variable in function position becomes a lambda through substitution. -/
def downwardExample : VExpr :=
  .app (.lam (tower 2) (.app (.bvar 0) (ident 0))) (ident 1)

theorem downwardExample_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ downwardExample (tower 1) := by
  have hf : env.HasType U (tower 2 :: Γ) (.bvar 0) (tower 2) := by
    have h : env.HasType U (tower 2 :: Γ) (.bvar 0) (tower 2).lift := .bvar .zero
    simpa only [lift, tower_liftN] using h
  have hb := hf.app (ident_typed env U (tower 2 :: Γ) 0)
  have hl := HasType.lam (tower_typed env U Γ 2) hb
  simpa only [downwardExample, tower_inst] using hl.app (ident_typed env U Γ 1)

theorem superdevelop_downwardExample : superdevelop downwardExample = chain 1 0 := by
  simp [downwardExample, superdevelop,
    contractApp, VExpr.inst, instVar, ident, tower, liftN]
  rfl

/-- One superdevelopment still leaves a typed beta-redex with a lambda argument.
This is the downward-creation case; it does not refute an input-dependent strategy. -/
theorem downwardExample_still_hasBeta : HasBeta (superdevelop downwardExample) := by
  rw [superdevelop_downwardExample]
  exact chain_succ_hasBeta 0 0

end Lean4Lean.VEnv.Strengthening.Developments
