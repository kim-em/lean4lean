import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeInhabitants
import Lean4Lean.Theory.Typing.Strengthening.RecursiveProbeTyping

/-! # Curry collapse with an inhabited function-result parameter

The recursive family retaining a proposition parameter also admits Curry's
construction as soon as that parameter is inhabited. Its front implication from
finite paired substitution is therefore not evidence that paired substitution
is the remaining difficulty in this test environment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace RecursiveType

/-- A recursive type returning `P → Prop` admits Curry's diagonal whenever
`P` has an inhabitant. The result is an inhabitant of every proposition in the
same context, without a strengthening or paired-substitution assumption. -/
theorem inhabit_prop_function
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (RecursiveProbe.result P).lift) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hp : env.HasType univs Γ p P)
    (hT : env.HasType univs Γ T (.sort .zero)) : ∃ t, env.HasType univs Γ t T := by
  have hD := Hrec.hasType.1
  have hb := RecursiveProbe.body_typed Hrec
  have hP' : env.HasType univs (D :: Γ) P.lift (.sort .zero) := hP.weak henv
  let a := VExpr.app RecursiveDomain.selfBody.lift (.bvar 0)
  have ha : env.HasType univs (P.lift :: D :: Γ) a (.sort .zero) :=
    HasType.app (hb.weak henv) (HasType.bvar .zero)
  have hT' : env.HasType univs (a :: P.lift :: D :: Γ) (T.liftN 3) (.sort .zero) := by
    simpa only [VExpr.lift, liftN_liftN, VExpr.liftN] using
      (((hT.weak henv (B := D)).weak henv (B := P.lift)).weak henv (B := a)).hasType.1
  have hn : env.HasType univs (P.lift :: D :: Γ) (.forallE a (T.liftN 3)) (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_zero).defeq (HasType.forallE ha hT')
  let b := VExpr.lam P.lift (.forallE a (T.liftN 3))
  have hB : env.HasType univs (D :: Γ) b (RecursiveProbe.result P).lift := .lam hP' hn
  let f := VExpr.lam D b
  have hfun : env.HasType univs Γ f (.forallE D (RecursiveProbe.result P).lift) := .lam hD hB
  have harg : env.HasType univs Γ f D := Hrec.symm.defeq hfun
  have hloop : env.HasType univs Γ (.app f f) (RecursiveProbe.result P) := by
    simpa only [inst_lift] using HasType.app hfun harg
  have hQ : env.HasType univs Γ (.app (.app f f) p) (.sort .zero) := hloop.app hp
  have EB : b.inst f = .lam P (.forallE (.app (VExpr.app f f).lift (.bvar 0)) (T.liftN 2)) := by
    simp [b, a, RecursiveDomain.selfBody, VExpr.inst, instVar, VExpr.lift, VExpr.liftN,
      inst_liftN_lo]
  have R₁ : BetaRed (.app (.app f f) p) (.app (b.inst f) p) := .app .beta .refl
  rw [EB] at R₁
  have R₂ := BetaRed.beta (A := P)
    (b := .forallE (.app (VExpr.app f f).lift (.bvar 0)) (T.liftN 2)) (a := p)
  have Hbeta := (R₁.trans R₂).simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hQ
  have HQ : env.IsDefEq univs Γ (.app (.app f f) p)
      (.forallE (.app (.app f f) p) T.lift) (.sort .zero) := by
    simpa [VExpr.inst, instVar, inst_liftN_lo, inst_lift] using Hbeta
  exact ⟨_, inhabit_result HQ⟩

end RecursiveType
/-- The parameter-retaining family also has the proposition front outright.
Choose an inhabited reflexive equality as its parameter, use the function-result
Curry diagonal, then substitute an inhabitant of the removed context type. -/
theorem RecursiveProbe.propositionFront (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveProbe.familyValue c)
      RecursiveProbe.familyType) : PropositionFront := by
  let P := eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
  have hP (Γ) : env.HasType univs Γ P (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial))
  have hp (Γ) : env.HasType univs Γ
      (eqReflApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero)) P :=
    HasType.eqReflApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial))
  intro Γ Q A B hΓ hQ _ _ HE
  obtain ⟨_, hQ⟩ := hQ
  have HD := RecursiveProbe.recursive hδ hΓ (hP Γ)
  obtain ⟨q, hq⟩ := RecursiveType.inhabit_type_of_props heq hΓ
    (RecursiveType.inhabit_prop_function hΓ HD (hP Γ) (hp Γ)) hQ
  simpa only [inst_lift] using HE.instN henv.ordered .zero hq

omit [Params] in
/-- The actual canonical-Eq extension used for the finite paired-law front
implication already satisfies that front without the paired law. Consequently
that implication alone is not evidence for a new irreducible obligation. -/
theorem canonical_recursiveProbe_front {base : VEnv}
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    letI := (RecursiveProbe.extended_wf hbase hfresh).params 0
    PropositionFront := by
  letI := (RecursiveProbe.extended_wf hbase hfresh).params 0
  intro Γ Q P R hΓ hQ hP hR HE
  exact RecursiveProbe.propositionFront (RecursiveProbe.extended_canonicalEq heq hfresh)
    (fun Γ => RecursiveProbe.equation 0 Γ) hΓ hQ hP hR HE

end Lean4Lean.VEnv.Strengthening
