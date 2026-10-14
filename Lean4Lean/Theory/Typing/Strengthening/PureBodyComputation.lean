import Lean4Lean.Theory.Typing.Strengthening.CertifiedKComputation

/-! # K computation on bodies containing only lambda-calculus syntax

For a body built from variables, applications and lambdas, every guarded K
computation erases to ordinary beta reduction after lambda annotations are
removed. Declarations, projections, patterns and K may compute inside the
annotations, but cannot introduce those operations into the body. The matching
predicate is arbitrary, so increasing certificate depth cannot evade this fact.
This is a syntactic reduction invariant, not typed reflection of erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The computational body uses only lambda calculus. Lambda annotations are
unrestricted and may contain declaration, projection, or K computations. -/
inductive PureBody : VExpr → Prop where
  | bvar : PureBody (.bvar i)
  | app : PureBody f → PureBody a → PureBody (.app f a)
  | lam : PureBody b → PureBody (.lam A b)

/-- Remove lambda-domain annotations, retaining every computational body node.
Other constructors remain explicit; the main invariant excludes them in bodies. -/
def eraseLamDomains : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .app f a => .app (eraseLamDomains f) (eraseLamDomains a)
  | .lam _ b => .lam (.sort .zero) (eraseLamDomains b)
  | .forallE A B => .forallE (eraseLamDomains A) (eraseLamDomains B)
  | .proj s i m => .proj s i (eraseLamDomains m)

/-- Erasure commutes with all binder insertions. -/
theorem eraseLamDomains_liftN (e : VExpr) :
    eraseLamDomains (e.liftN n k) = (eraseLamDomains e).liftN n k := by
  induction e generalizing k <;> simp [eraseLamDomains, liftN, *]

/-- Erasure commutes with substitution, including beta-created redexes. -/
theorem eraseLamDomains_inst (e : VExpr) :
    eraseLamDomains (e.inst x k) = (eraseLamDomains e).inst (eraseLamDomains x) k := by
  induction e generalizing k <;> simp [eraseLamDomains, inst, *]
  case bvar i =>
    simp only [instVar]
    split
    · rfl
    · split
      · exact eraseLamDomains_liftN x
      · rfl

/-- Inserting binders changes variables but does not introduce body operations. -/
theorem PureBody.liftN (H : PureBody e) : PureBody (e.liftN n k) := by
  induction H generalizing k with
  | bvar => exact .bvar
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ ih => exact .lam ih

/-- Substituting another pure body preserves the grammar. -/
theorem PureBody.inst (H : PureBody e) (Hx : PureBody x) : PureBody (e.inst x k) := by
  induction H generalizing k with
  | bvar =>
    simp only [VExpr.inst, instVar]
    split
    · exact .bvar
    · split
      · exact Hx.liftN
      · exact .bvar
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ ih => exact .lam ih

/-- Registered patterns require a constant along the function spine, which this
grammar excludes regardless of what appears inside annotations. -/
theorem PureBody.no_match (H : PureBody e) (hm : Pattern.Matches p e ls vals) : False := by
  induction hm with
  | const => cases H
  | var _ ih => cases H with | app Hf _ => exact ih Hf
  | app _ _ ih _ => cases H with | app Hf _ => exact ih Hf

/-- In particular, no constant-headed application is a pure body. -/
theorem PureBody.no_const_spine (H : PureBody (mkApps (.const c ls) args)) : False := by
  induction args using List.snoc_induction with
  | nil => cases H
  | snoc args a ih =>
    rw [mkApps_snoc] at H
    cases H with | app Hf _ => exact ih Hf

/-- A computation preserves pure bodies and acts by beta on their erasures. -/
def BodySimulation (e out : VExpr) : Prop :=
  PureBody e → PureBody out ∧ BetaRed (eraseLamDomains e) (eraseLamDomains out)

private theorem BodySimulation.refl : BodySimulation e e := fun H => ⟨H, .refl⟩

private theorem BodySimulation.trans (h1 : BodySimulation a b) (h2 : BodySimulation b c) :
    BodySimulation a c := fun H =>
  let ⟨Hb, Rb⟩ := h1 H
  let ⟨Hc, Rc⟩ := h2 Hb
  ⟨Hc, Rb.trans Rc⟩

private theorem BodySimulation.app (hf : BodySimulation f f') (ha : BodySimulation a a') :
    BodySimulation (.app f a) (.app f' a') := by
  intro H
  cases H with
  | app Hf Ha =>
    obtain ⟨Hf, Rf⟩ := hf Hf
    obtain ⟨Ha, Ra⟩ := ha Ha
    exact ⟨.app Hf Ha, .app Rf Ra⟩

private theorem BodySimulation.lam (hb : BodySimulation b b') :
    BodySimulation (.lam A b) (.lam A' b') := by
  intro H
  cases H with
  | lam Hb =>
    obtain ⟨Hb, Rb⟩ := hb Hb
    exact ⟨.lam Hb, .lam .refl Rb⟩

private theorem BodySimulation.beta : BodySimulation (.app (.lam A b) x) (b.inst x) := by
  intro H
  cases H with
  | app Hf Hx =>
    cases Hf with
    | lam Hb =>
      refine ⟨Hb.inst Hx, ?_⟩
      simpa only [eraseLamDomains, eraseLamDomains_inst] using
        (BetaRed.beta (A := .sort .zero) (b := eraseLamDomains b) (a := eraseLamDomains x))

/-- Closed delta equations can act only inside annotations of a pure body. -/
theorem PureObservation.Compute.body_simulation (R : PureObservation.Compute D e out) :
    BodySimulation e out := by
  induction R with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | beta => exact .beta
  | delta => intro H; cases H
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ _ ih => exact ih.lam
  | forallE | proj => intro H; cases H

variable [Params]

/-- Projection computation has no body redex in this grammar. -/
theorem PureObservation.ProjectionCompute.body_simulation
    (R : PureObservation.ProjectionCompute D e out) : BodySimulation e out := by
  induction R with
  | base R => exact R.body_simulation
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | projIota => intro H; cases H
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ _ ih => exact ih.lam
  | forallE | proj => intro H; cases H

/-- Pattern rules cannot introduce a constant-headed redex into a pure body. -/
theorem PureObservation.PatternCompute.body_simulation
    (R : PureObservation.PatternCompute D e out) : BodySimulation e out := by
  induction R with
  | base R => exact R.body_simulation
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | pattern _ hm _ => intro H; exact (H.no_match hm).elim
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ _ ih => exact ih.lam
  | forallE | proj => intro H; cases H

/-- Syntactic K also has no body redex here, even with unrestricted annotation
computation. No soundness assumption on the declaration collection is needed. -/
theorem CastCompute.body_simulation (R : CastCompute D e out) : BodySimulation e out := by
  induction R with
  | base R => exact R.body_simulation
  | cast => intro H; exact (PureBody.no_const_spine (args := [_, _, _, _, _, _]) H).elim
  | eqRec => intro H; exact (PureBody.no_const_spine (args := [_, _, _, _, _, _]) H).elim
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ _ ih => exact ih.lam
  | forallE | proj => intro H; cases H

/-- The result holds for every matching predicate, even one that accepts every
endpoint pair. Guard strength therefore cannot change these computational bodies. -/
theorem GuardedKCompute.body_simulation (R : GuardedKCompute D Cmp Γ e out) :
    BodySimulation e out := by
  induction R with
  | base R => exact R.body_simulation
  | eqRec => intro H; exact (PureBody.no_const_spine (args := [_, _, _, _, _, _]) H).elim
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ _ _ ih => exact ih.lam
  | forallE | proj => intro H; cases H

/-- At every finite certificate depth, a pure body has only beta behavior after
annotation erasure. This concerns body computation, not reflection of typed equality. -/
theorem CertifiedKCompute.pure_body_beta (R : CertifiedKCompute D depth Γ e out)
    (H : PureBody e) : PureBody out ∧ BetaRed (eraseLamDomains e) (eraseLamDomains out) :=
  GuardedKCompute.body_simulation R H

end Lean4Lean.VEnv.Strengthening
