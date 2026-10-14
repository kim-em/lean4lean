import Lean4Lean.Theory.Typing.Strengthening.PatternProjectionTransport
import Lean4Lean.Theory.Typing.Strengthening.DeclarationStep

/-! Single compatible beta, delta, pattern and projection steps, used to transport finite paths
through ordinary normal comparison without introducing eta expansions. -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Exactly one computational contraction, possibly under syntax or inside an annotation. -/
inductive PatternStep (D : Definitions) : VExpr → VExpr → Prop where
  | pattern : Pat p r → ConcretePattern env p r → p.Matches e levels captures →
      CheckFromTyping env univs p r levels → PatternStep D e (r.1.apply levels captures)
  | projIota : env.projections s info → args.length = info.nparams + info.numFields →
      args[info.nparams + index]? = some field →
      PatternStep D (.proj s index (mkApps (.const info.ctorName ls) args)) field
  | delta : D.unfolds c ls rhs → PatternStep D (.const c ls) rhs
  | beta : PatternStep D (.app (.lam A b) a) (b.inst a)
  | appL : PatternStep D f f' → PatternStep D (.app f a) (.app f' a)
  | appR : PatternStep D a a' → PatternStep D (.app f a) (.app f a')
  | lamL : PatternStep D A A' → PatternStep D (.lam A b) (.lam A' b)
  | lamR : PatternStep D b b' → PatternStep D (.lam A b) (.lam A b')
  | forallL : PatternStep D A A' → PatternStep D (.forallE A B) (.forallE A' B)
  | forallR : PatternStep D B B' → PatternStep D (.forallE A B) (.forallE A B')
  | proj : PatternStep D m m' → PatternStep D (.proj s i m) (.proj s i m')

variable {D : Definitions}

theorem PatternStep.toCompute (R : PatternStep D e e') : PatternCompute D e e' := by
  induction R with
  | pattern hp hc hm ht => exact .pattern hp hm ht
  | projIota hi hl hg => exact .base (.projIota hi hl hg)
  | delta H => exact .base (.base (.delta H))
  | beta => exact .of_beta .beta
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

theorem PatternStep.liftN (R : PatternStep D e e') (n k : Nat) :
    PatternStep D (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | pattern hp hc hm ht =>
    rw [Pattern.RHS.liftN_apply]
    exact .pattern hp hc (Pattern.matches_liftN.mpr ⟨_, hm, fun _ => rfl⟩) ht
  | projIota hi hl hg =>
    simp only [VExpr.liftN, VExpr.liftN_mkApps]
    exact .projIota hi (by simpa using hl) (by simp [List.getElem?_map, hg])
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

/-- Embed the single beta/delta steps used by closed computation. -/
theorem PatternStep.of_computeStep (R : ComputeStep D a b) : PatternStep D a b := by
  induction R with
  | beta => exact .beta
  | delta H => exact .delta H
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lamL _ ih => exact .lamL ih
  | lamR _ ih => exact .lamR ih
  | forallL _ ih => exact .forallL ih
  | forallR _ ih => exact .forallR ih
  | proj _ ih => exact .proj ih

/-- A predicate preserved by individual pattern steps is preserved by all finite
compatible computations. Concrete registration is used only at pattern roots. -/
theorem pattern_induct_steps
    (hc : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PatternCompute D a b) {P : VExpr → Prop} (ha : P a)
    (hstep : ∀ {x y}, PatternStep D x y → P x → P y) : P b := by
  have base {a b} (R : ProjectionCompute D a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, PatternStep D x y → Q x → Q y) → Q b := by
    induction R with
    | base R => exact fun Q h H => compute_induct_steps R h (fun R => H (.of_computeStep R))
    | trans _ _ ih1 ih2 => exact fun Q h H => ih2 Q (ih1 Q h H) H
    | projIota hi hl hg => exact fun _ h H => H (.projIota hi hl hg) h
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
  have aux {a b} (R : PatternCompute D a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, PatternStep D x y → Q x → Q y) → Q b := by
    induction R with
    | base R => exact base R
    | trans _ _ ih1 ih2 => exact fun Q h H => ih2 Q (ih1 Q h H) H
    | pattern hp hm ht => exact fun _ h H => H (.pattern hp (hc hp) hm ht) h
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
  exact aux R P ha hstep

end Lean4Lean.VEnv.Strengthening.PureObservation
