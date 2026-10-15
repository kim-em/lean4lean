import Lean4Lean.Theory.Typing.Strengthening.RecursiveDataEnvironment
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop

/-! # Recovering the parameter of the fixed-data recursive family

Unfolding exposes `P → S` for the fixed data constant S. The recursive domain is inhabited by its diagonal,
so recovering `P` from Pi injectivity uses ordinary instantiation of that inhabitant,
not strengthening through the recursive binder.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveData
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The family application is typed independently of its defining equation. -/
theorem domain_typed (hc : env.constants c = some (declaration c d).toVConstant)
    (hP : env.HasType univs Γ P (.sort .zero)) :
    env.HasType univs Γ (domain c P) (.sort (.succ .zero)) :=
  (family_typed hc univs Γ).app hP

/-- The installed equation gives the parameterized recursive domain equation. -/
theorem recursive (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (familyValue c d) familyType)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero)) :
    env.IsDefEq univs Γ (domain c P) (unfolded c d P) (.sort (.succ .zero)) := by
  have H := IsDefEq.appDF (hδ Γ) hP
  have HB := BetaRed.simAt (env := env) henv.orderedStrong henv.betaSubjectReduction
    (BetaRed.beta (A := .sort .zero)
      (b := .forallE (domain c (.bvar 0)) (result d (.bvar 1))) (a := P)) hΓ _ H.hasType.2
  simpa [familyValue, domain, unfolded, result, VExpr.inst, instVar, VExpr.lift, liftN] using H.trans HB

/-- Self-application in a recursive-domain context has the retained function
result, which remains non-proof even when `P` itself is a proposition. -/
theorem body_typed
    (Hrec : env.IsDefEq univs Γ D (.forallE D (result d P).lift) (.sort u)) :
    env.HasType univs (D :: Γ) RecursiveDomain.selfBody (result d P).lift := by
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  simpa [RecursiveDomain.selfBody, result, VExpr.lift, liftN, VExpr.inst, instVar, inst_liftN_bvar] using HasType.app hf hv

/-- The recursive domain has an explicit inhabitant, so its binder can be
removed by substitution when reading the retained proposition parameter. -/
theorem inhabited
    (Hrec : env.IsDefEq univs Γ D (.forallE D (result d P).lift) (.sort u)) :
    env.HasType univs Γ (RecursiveDomain.diagonal D) D :=
  Hrec.symm.defeq (HasType.lam Hrec.hasType.1 (body_typed Hrec))

/-- Definitional equality of two recursive family applications implies equality
of their proposition parameters. The only binder removal substitutes the checked
diagonal inhabitant; no strengthening inverse is used. -/
theorem parameter_injective
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (familyValue c d) familyType)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : env.IsDefEqU univs Γ (domain c P) (domain c Q)) : env.IsDefEqU univs Γ P Q := by
  have HP := recursive hδ hΓ hP
  have HQ := recursive hδ hΓ hQ
  have HE := (IsDefEqU.trans henv hΓ ⟨_, HP.symm⟩ H).trans henv hΓ ⟨_, HQ⟩
  obtain ⟨_, _, Hbody⟩ := HE.forallE_inv henv hΓ
  have hΓD : OnCtx (domain c P :: Γ) (env.IsType univs) := ⟨hΓ, _, HP.hasType.1⟩
  have HB : env.IsDefEqU univs (domain c P :: Γ)
      (.forallE P.lift (.const d [])) (.forallE Q.lift (.const d [])) := ⟨_, Hbody⟩
  obtain ⟨⟨_, HD⟩, _⟩ := HB.forallE_inv henv hΓD
  simpa only [inst_lift] using IsDefEqU.instN henv.ordered .zero ⟨_, HD⟩ (inhabited HP)

end Lean4Lean.VEnv.Strengthening.RecursiveData
