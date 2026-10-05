import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorization
import Lean4Lean.Theory.Typing.AnchoredOriginalClosureMeasure

/-! A structural acceptance gate for typed inverse substitution.  The source
typing views below expose only ORIGINAL application, lambda and Pi children.
An unexpanded boundary retains its actual Strong proof; this file does not
interpret that proof or assert that every Strong proof has already been
expanded into a view.  In particular this is not a two-typing theorem.

The cut clause is connected to the actual Obs/InstFootprint implementation.
It retains the original typing of the lifted cut BEFORE reflecting its source
syntax.  Reflection of that typing, or identifying its assigned type with the
application argument's assigned type, is deliberately not assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

def AtomicSyntax : VExpr → Prop
  | .app .. | .lam .. | .forallE .. => False
  | _ => True

/-- A finite exposed part of an original typing derivation.  `boundary` is an
unexpanded original child, not a callback and not a semantic induction result.
The numerical label belongs to the separate original-closure schedule; a
full reifier must supply those labels and the corresponding access proofs. -/
inductive TypingView (env : VEnv) (U : Nat) :
    List VExpr → VExpr → VExpr → Type where
  | boundary (origin : Origin) (original : env.IsDefEqStrong U source e e A)
      (atomic : AtomicSyntax e) :
      TypingView env U source e A
  | app (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : TypingView env U source A (.sort u))
      (codomain : TypingView env U (A :: source) B (.sort v))
      (function : TypingView env U source f (.forallE A B))
      (argument : TypingView env U source a A)
      (result : TypingView env U source (B.inst a) (.sort v)) :
      TypingView env U source (.app f a) (B.inst a)
  | lam (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : TypingView env U source A (.sort u))
      (codomain : TypingView env U (A :: source) B (.sort v))
      (body : TypingView env U (A :: source) e B) :
      TypingView env U source (.lam A e) (.forallE A B)
  | pi (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : TypingView env U source A (.sort u))
      (body : TypingView env U (A :: source) B (.sort v)) :
      TypingView env U source (.forallE A B) (.sort (.imax u v))

/-- Only raw soundness is replayed here.  No synthesized proof is recursively
interpreted.  All semantic premises of the exposed rules remain children. -/
theorem TypingView.original (view : TypingView env U source e A) :
    env.IsDefEqStrong U source e e A := by
  induction view with
  | boundary _ original _ => exact original
  | app hu hv _ _ _ _ _ ihA ihB ihF ihArg ihResult =>
    exact .appDF hu hv ihA ihB ihF ihArg ihResult
  | lam hu hv _ _ _ ihA ihB ihBody =>
    exact .lamDF hu hv ihA ihB ihB ihBody ihBody
  | pi hu hv _ _ ihA ihB => exact .forallEDF hu hv ihA ihB ihB

def TypingView.origin : TypingView env U source e A → Origin
  | .boundary origin _ _ => origin
  | .app _ _ domain codomain function argument result =>
      .binder domain.origin [codomain.origin] [function.origin, argument.origin, result.origin]
  | .lam _ _ domain codomain body => .binder domain.origin [codomain.origin, body.origin] []
  | .pi _ _ domain body => .binder domain.origin [body.origin] []

/-- The syntax children visited by factorInst.  Formation-only children of an
application are intentionally absent: factorInst visits its function and
argument observations, not arbitrary assigned-type premises.  Lambda and Pi
annotations ARE source syntax and hence retain their original formations. -/
inductive Located (root : TypingView env U source e A) :
    {context : List VExpr} → {expression type : VExpr} →
      TypingView env U context expression type → Type where
  | here : Located root root
  | appFunction
      (parent : Located root (TypingView.app hu hv domain codomain function argument result)) :
      Located root function
  | appArgument
      (parent : Located root (TypingView.app hu hv domain codomain function argument result)) :
      Located root argument
  | lamDomain (parent : Located root (TypingView.lam hu hv domain codomain body)) :
      Located root domain
  | lamBody (parent : Located root (TypingView.lam hu hv domain codomain body)) :
      Located root body
  | piDomain (parent : Located root (TypingView.pi hu hv domain body)) :
      Located root domain
  | piBody (parent : Located root (TypingView.pi hu hv domain body)) :
      Located root body

theorem Located.weight_le (location : Located root selected) :
    selected.origin.weight ≤ root.origin.weight := by
  induction location with
  | here => exact Nat.le_refl _
  | appFunction parent ih | appArgument parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (Origin.binder_other (by simp))) ih
  | lamDomain parent ih | piDomain parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (Origin.binder_domain _ _ _)) ih
  | lamBody parent ih | piBody parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (Origin.binder_body (by simp))) ih

/-- Source binders retain their actual ORIGINAL domain formation closures.
The context prefix is recovered separately in FactorContext. -/
def Located.environment (location : Located root selected) (initial : List Closure) : List Closure :=
  match location with
  | .here => initial
  | .appFunction parent => parent.environment initial
  | .appArgument parent => parent.environment initial
  | .lamDomain parent => parent.environment initial
  | .lamBody (domain := domain) parent =>
      .close domain.origin (parent.environment initial) :: parent.environment initial
  | .piDomain parent => parent.environment initial
  | .piBody (domain := domain) parent =>
      .close domain.origin (parent.environment initial) :: parent.environment initial

theorem Located.cost_le (location : Located root selected) (initial : List Closure) :
    (Closure.close selected.origin (location.environment initial)).cost ≤
      (Closure.close root.origin initial).cost := by
  induction location with
  | here => exact Nat.le_refl _
  | appFunction parent ih | appArgument parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_other_cost (by simp) (parent.environment initial))) ih
  | lamDomain parent ih | piDomain parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_domain_cost _ _ _ (parent.environment initial))) ih
  | lamBody parent ih | piBody parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_body_cost (by simp) (parent.environment initial))) ih

/-- A cut carries its original context and assigned type.  `depth` records
source weakening of the removed argument; it does not alter the original
typing derivation. -/
structure CutOrigin (root : TypingView env U source e A) (argument : VExpr) where
  context : List VExpr
  expression : VExpr
  type : VExpr
  view : TypingView env U context expression type
  location : Located root view
  depth : Nat
  expression_eq : expression = argument.lift' (.skipN .refl depth)

theorem CutOrigin.original {root : TypingView env U source e A}
    (cut : CutOrigin root argument) :
    env.IsDefEqStrong U cut.context cut.expression cut.expression cut.type :=
  cut.view.original

theorem CutOrigin.weight_le (cut : CutOrigin root argument) :
    cut.view.origin.weight ≤ root.origin.weight := cut.location.weight_le

/-- In the crucial B = bvar 0 case the cut is the WHOLE original H_Ba
endpoint, rather than a strictly smaller subderivation of H_Ba. -/
def TypingView.wholeCut (view : TypingView env U source argument type) :
    CutOrigin view argument where
  context := source
  expression := argument
  type := type
  view := view
  location := .here
  depth := 0
  expression_eq := by simp

/-- The original app reserves both its instantiated-type child and argument
child.  A cut may use all of the former; their combined coherence call is
still strictly below the parent app. -/
theorem app_cut_schedule
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : TypingView env U source A (.sort u))
    (codomain : TypingView env U (A :: source) B (.sort v))
    (function : TypingView env U source f (.forallE A B))
    (argument : TypingView env U source a A)
    (result : TypingView env U source (B.inst a) (.sort v))
    (cut : CutOrigin result a) (environment : List Closure) :
    schedule .coherence
      ((Closure.close cut.view.origin (cut.location.environment environment)).cost +
        (Closure.close argument.origin environment).cost) <
      schedule .fundamental
        ((Closure.close (TypingView.app domainWF bodyWF domain codomain function argument result).origin
          environment).cost) := by
  apply schedule_strict
  have hcut := cut.location.cost_le environment
  have bound : result.origin.weight + argument.origin.weight <
      (TypingView.app domainWF bodyWF domain codomain function argument result).origin.weight := by
    simp only [TypingView.origin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  have strict : (Closure.close result.origin environment).cost +
      (Closure.close argument.origin environment).cost <
      (Closure.close (TypingView.app domainWF bodyWF domain codomain function argument result).origin
        environment).cost := by
    simpa only [Closure.cost, Nat.add_mul] using
      Nat.mul_lt_mul_of_pos_right bound (show 0 < 1 + environmentCost environment by omega)
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hcut _) strict

/-- The actual factorInst cut operation, with its original typing location
retained next to the reflected observation.  The output contains no typing
claim for `argument` at a reflected version of `cut.type`; obtaining that
claim is exactly the pending two-typing/reindexing edge. -/
theorem CutOrigin.factorCut
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {e A argument : VExpr}
    {root : TypingView env U source e A}
    (cut : CutOrigin root argument)
    {locals : List Nat} {τ σ : Subst} {demand : Profile n} {before : Footprint}
    (observation : Obs env U registry target locals τ cut.expression demand before)
    (tail : Subst.lift_l (.skipN .refl cut.depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ argumentFootprint,
      ∃ _reflected : Obs env U registry target baseLocals σ argument demand argumentFootprint,
      before = shiftFootprint cut.depth argumentFootprint ∧
      Nonempty (Obs env U registry target newLocals
        ((Subst.one argument).liftN cut.depth |>.comp τ) (.bvar cut.depth) demand
        [(cut.depth, ⟨n, demand⟩)]) ∧
      Nonempty (InstFootprint env U registry target baseLocals σ argument cut.depth
        before [(cut.depth, ⟨n, demand⟩)]) := by
  obtain ⟨footprint, ⟨reflected⟩, footprintEq⟩ :=
    observation.reflectSource _ cut.expression_eq baseLocals
  rw [tail] at reflected
  rw [← shiftFootprint_sourceLift] at footprintEq
  refine ⟨footprint, reflected, footprintEq, ⟨.var newLocals _ cut.depth demand⟩, ?_⟩
  rw [footprintEq]
  exact ⟨by simpa only [List.append_nil] using InstFootprint.cut reflected InstFootprint.nil⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
