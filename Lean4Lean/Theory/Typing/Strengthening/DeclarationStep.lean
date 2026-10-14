import Lean4Lean.Theory.Typing.Strengthening.FreshDeclarationReflection
import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelClosure

/-! A single compatible beta/delta contraction, used to transport finite beta/delta paths
through ordinary normal comparison without introducing eta expansions. -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Exactly one beta/delta contraction, possibly under syntax or inside an annotation. -/
inductive ComputeStep (D : Definitions) : VExpr → VExpr → Prop where
  | delta : D.unfolds c ls rhs → ComputeStep D (.const c ls) rhs
  | beta : ComputeStep D (.app (.lam A b) a) (b.inst a)
  | appL : ComputeStep D f f' → ComputeStep D (.app f a) (.app f' a)
  | appR : ComputeStep D a a' → ComputeStep D (.app f a) (.app f a')
  | lamL : ComputeStep D A A' → ComputeStep D (.lam A b) (.lam A' b)
  | lamR : ComputeStep D b b' → ComputeStep D (.lam A b) (.lam A b')
  | forallL : ComputeStep D A A' → ComputeStep D (.forallE A B) (.forallE A' B)
  | forallR : ComputeStep D B B' → ComputeStep D (.forallE A B) (.forallE A B')
  | proj : ComputeStep D m m' → ComputeStep D (.proj s i m) (.proj s i m')

variable {D : Definitions}

theorem ComputeStep.toCompute (R : ComputeStep D e e') : Compute D e e' := by
  induction R with
  | delta H => exact .delta H
  | beta => exact .beta
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

theorem ComputeStep.liftN (R : ComputeStep D e e') (n k : Nat) :
    ComputeStep D (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | delta H =>
    have hc := (D.closed H).liftN_eq (n := n) (Nat.zero_le k)
    rw [hc]; exact .delta H
  | beta => rw [liftN_inst_hi]; exact .beta
  | appL _ ih => exact .appL (ih k)
  | appR _ ih => exact .appR (ih k)
  | lamL _ ih => exact .lamL (ih k)
  | lamR _ ih => exact .lamR (ih (k+1))
  | forallL _ ih => exact .forallL (ih k)
  | forallR _ ih => exact .forallR (ih (k+1))
  | proj _ ih => exact .proj (ih k)

/-- Induction on individual compatible contractions suffices for all finite beta/delta
paths. The predicate may change after each contraction. -/
theorem compute_induct_steps {P : VExpr → Prop} (R : Compute D e e')
    (he : P e) (hs : ∀ {a b}, ComputeStep D a b → P a → P b) : P e' := by
  have aux {a b : VExpr} (R : Compute D a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, ComputeStep D x y → Q x → Q y) → Q b := by
    induction R with
    | refl => exact fun _ h _ => h
    | trans _ _ ih1 ih2 => exact fun Q h H => ih2 Q (ih1 Q h H) H
    | delta Hd => exact fun _ h H => H (.delta Hd) h
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

end Lean4Lean.VEnv.Strengthening.PureObservation
