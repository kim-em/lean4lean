import Lean4Lean.Theory.Typing.Strengthening.NormalBetaReflection

/-! A single compatible beta contraction, used to transport finite beta paths
through ordinary normal comparison without introducing eta expansions. -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Exactly one beta contraction, possibly under syntax or inside an annotation. -/
inductive BetaStep : VExpr → VExpr → Prop where
  | beta : BetaStep (.app (.lam A b) a) (b.inst a)
  | appL : BetaStep f f' → BetaStep (.app f a) (.app f' a)
  | appR : BetaStep a a' → BetaStep (.app f a) (.app f a')
  | lamL : BetaStep A A' → BetaStep (.lam A b) (.lam A' b)
  | lamR : BetaStep b b' → BetaStep (.lam A b) (.lam A b')
  | forallL : BetaStep A A' → BetaStep (.forallE A B) (.forallE A' B)
  | forallR : BetaStep B B' → BetaStep (.forallE A B) (.forallE A B')
  | proj : BetaStep m m' → BetaStep (.proj s i m) (.proj s i m')

theorem BetaStep.toBeta (R : BetaStep e e') : BetaRed e e' := by
  induction R with
  | beta => exact .beta
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

theorem BetaStep.liftN (R : BetaStep e e') (n k : Nat) :
    BetaStep (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | beta => rw [liftN_inst_hi]; exact .beta
  | appL _ ih => exact .appL (ih k)
  | appR _ ih => exact .appR (ih k)
  | lamL _ ih => exact .lamL (ih k)
  | lamR _ ih => exact .lamR (ih (k+1))
  | forallL _ ih => exact .forallL (ih k)
  | forallR _ ih => exact .forallR (ih (k+1))
  | proj _ ih => exact .proj (ih k)

/-- Induction on individual compatible contractions suffices for all finite beta
paths. The predicate may change after each contraction. -/
theorem betaRed_induct_steps {P : VExpr → Prop} (R : BetaRed e e')
    (he : P e) (hs : ∀ {a b}, BetaStep a b → P a → P b) : P e' := by
  have aux {a b : VExpr} (R : BetaRed a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, BetaStep x y → Q x → Q y) → Q b := by
    induction R with
    | refl => exact fun _ h _ => h
    | trans _ _ ih1 ih2 => exact fun Q h H => ih2 Q (ih1 Q h H) H
    | beta => exact fun _ h H => H .beta h
    | @app f f' a a' _ _ ihf iha =>
      intro Q h H
      exact iha (fun x => Q (.app f' x))
        (ihf (fun x => Q (.app x a)) h (fun R => H (.appL R))) (fun R => H (.appR R))
    | @lam A A' b b' _ _ ihA ihb =>
      intro Q h H
      exact ihb (fun x => Q (.lam A' x))
        (ihA (fun x => Q (.lam x b)) h (fun R => H (.lamL R))) (fun R => H (.lamR R))
    | @forallE A A' B B' _ _ ihA ihB =>
      intro Q h H
      exact ihB (fun x => Q (.forallE A' x))
        (ihA (fun x => Q (.forallE x B)) h (fun R => H (.forallL R))) (fun R => H (.forallR R))
    | @proj m m' s i _ ihm =>
      exact fun Q h H => ihm (fun x => Q (.proj s i x)) h (fun R => H (.proj R))
  exact aux R P he hs

end Lean4Lean.VEnv.Strengthening
