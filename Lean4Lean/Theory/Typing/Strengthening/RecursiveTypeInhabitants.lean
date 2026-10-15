import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier
import Lean4Lean.Theory.Typing.EqTyping

/-! # Logical consequences of negative recursive universe types

A type `D ≡ D → Prop` yields a Curry diagonal for every proposition. Canonical
Eq then transports an identity function into an inhabitant of any type. This
explains why such recursive test environments cannot themselves witness a
failure of strengthening, despite obstructing restricted computation relations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace RecursiveType

/-- Any equation `D ≡ D → T` types the diagonal self-application at `T`.
The result need not be proof-relevant. -/
theorem inhabit_result
    (Hrec : env.IsDefEq univs Γ D (.forallE D T.lift) (.sort u)) :
    env.HasType univs Γ (RecursiveDomain.omegaTerm D) T := by
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody T.lift := by
    simpa only [RecursiveDomain.selfBody, inst_liftN_bvar] using HasType.app hf hv
  have hl := HasType.lam Hrec.hasType.1 hb
  have hx := Hrec.symm.defeq hl
  simpa only [RecursiveDomain.omegaTerm, RecursiveDomain.diagonal, inst_lift] using HasType.app hl hx

/-- Curry's diagonal makes every proposition inhabited in the presence of a
negative recursive universe type. No canonical-Eq or strengthening premise is
needed for this first step. -/
theorem inhabit_prop
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    ∃ p, env.HasType univs Γ p P := by
  have hD := Hrec.hasType.1
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  let b := VExpr.forallE RecursiveDomain.selfBody (P.liftN 2)
  have hP' : env.HasType univs (RecursiveDomain.selfBody :: D :: Γ) (P.liftN 2) (.sort .zero) := by
    simpa only [VExpr.lift, liftN_liftN, Nat.one_add, VExpr.liftN] using
      ((hP.weak henv (B := D)).weak henv (B := RecursiveDomain.selfBody)).hasType.1
  have hB : env.HasType univs (D :: Γ) b (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_zero).defeq (HasType.forallE hb hP')
  let f := VExpr.lam D b
  have hfun : env.HasType univs Γ f (.forallE D (.sort .zero)) := .lam hD hB
  have harg : env.HasType univs Γ f D := Hrec.symm.defeq hfun
  have hQ : env.HasType univs Γ (.app f f) (.sort .zero) := hfun.app harg
  have Hbeta := BetaRed.simAt (env := env) henv.orderedStrong henv.betaSubjectReduction
    (BetaRed.beta (A := D) (b := b) (a := f)) hΓ _ hQ
  have HQ : env.IsDefEq univs Γ (.app f f) (.forallE (.app f f) P.lift) (.sort .zero) := by
    simpa [b, f, RecursiveDomain.selfBody, VExpr.inst, instVar, inst_liftN_lo, VExpr.lift] using Hbeta
  exact ⟨_, inhabit_result HQ⟩

/-- If every proposition is inhabited, canonical equality supplies an inhabitant
of every type: cast the identity on `A` from `A → A` to `A`. This uses ordinary
Eq elimination, not equality reflection. -/
theorem inhabit_type_of_props (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hall : ∀ {P}, env.HasType univs Γ P (.sort .zero) → ∃ p, env.HasType univs Γ p P)
    (hA : env.HasType univs Γ A (.sort u)) : ∃ a, env.HasType univs Γ a A := by
  have hu : u.WF univs := (hA.isType henv hΓ).sort_inv henv.ordered
  have hF : env.HasType univs Γ (.forallE A A.lift) (.sort u) :=
    (IsDefEq.sortDF (by exact ⟨hu, hu⟩) hu VLevel.imax_self).defeq
      (HasType.forallE hA (hA.weak henv))
  have hx : env.HasType univs Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lam hA (.bvar .zero)
  obtain ⟨q, hq⟩ := hall (HasType.eqApp (w := .succ u) heq hu (HasType.sort hu) hF hA)
  exact ⟨_, HasType.typeCast henv.ordered heq hu hF hA hq hx⟩

/-- A negative recursive universe type in every context makes proposition
strengthening hold by substituting an actual inhabitant of the removed binder.
Thus these recursive test environments cannot refute canonical-Eq strengthening. -/
theorem propositionFront (heq : env.HasCanonicalEq)
    (hrec : ∀ Γ, OnCtx Γ (env.IsType univs) → env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u)) :
    PropositionFront := by
  intro Γ Q P R hΓ hQ _ _ HE
  obtain ⟨u, hQ⟩ := hQ
  obtain ⟨q, hq⟩ := inhabit_type_of_props heq hΓ (inhabit_prop hΓ (hrec Γ hΓ)) hQ
  simpa only [inst_lift] using HE.instN henv.ordered .zero hq

end RecursiveType
/-- The recursive family used in the ordinary-core paired-substitution
counterexample already satisfies proposition strengthening under canonical Eq.
Instantiate its parameter by the closed identity on Prop and use Curry's diagonal. -/
theorem RecursiveDomain.propositionFront (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) : PropositionFront := by
  let arg := VExpr.lam (.sort .zero) (.bvar 0)
  have harg (Γ) : env.HasType univs Γ arg RecursiveDomain.argType :=
    HasType.lam (HasType.sort (by trivial)) (HasType.bvar .zero)
  intro Γ Q P R hΓ hQ hP hR HE
  refine RecursiveType.propositionFront (D := .app (.const c []) arg) (u := .succ .zero) heq ?_ hΓ hQ hP hR HE
  intro Γ hΓ
  have H := IsDefEq.appDF (hδ Γ) (harg Γ)
  have HB := BetaRed.simAt (env := env) henv.orderedStrong henv.betaSubjectReduction
    (BetaRed.beta (A := RecursiveDomain.argType)
      (b := .forallE (.app (.const c []) (.bvar 0)) (.sort .zero)) (a := arg)) hΓ _ H.hasType.2
  simpa [RecursiveDomain.familyValue, VExpr.inst, instVar] using H.trans HB

omit [Params] in
/-- The actual canonical-Eq extension used to refute full-core paired
instantiation nevertheless has the proposition front, proved without that law. -/
theorem canonical_recursiveDomain_front {base : VEnv} (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
    PropositionFront := by
  letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
  intro Γ Q P R hΓ hQ hP hR HE
  exact RecursiveDomain.propositionFront
    (RecursiveDomain.extended_canonicalEq heq hfresh) (fun Γ => RecursiveDomain.equation 0 Γ)
    hΓ hQ hP hR HE

end Lean4Lean.VEnv.Strengthening
