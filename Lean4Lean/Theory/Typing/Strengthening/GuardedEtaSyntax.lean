import Lean4Lean.Theory.Typing.Strengthening.BidirectionalBetaBoundary
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop

/-! # A beta-stable syntax for eta-expanded recursive diagonals

Every abstraction at the recursive domain has an extra Prop binder in its body.
Beta reduction can unfold self-application indefinitely, but cannot remove this
binder from a surviving recursive-domain abstraction. This is a syntactic
invariant; the typed comparison obstruction is established separately.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Developments

def domain (c : Name) : VExpr := .const c []
def prop : VExpr := .sort .zero
def selfBody : VExpr := .app (.bvar 0) (.bvar 0)
def diagonal (c : Name) : VExpr := .lam (domain c) selfBody
def etaDiagonal (c : Name) : VExpr :=
  .lam (domain c) (.lam prop (.app selfBody.lift (.bvar 0)))
def omegaTerm (c : Name) : VExpr := .app (diagonal c) (diagonal c)
def etaOmega (c : Name) : VExpr := .app (etaDiagonal c) (etaDiagonal c)

/-- Recursive-domain lambdas retain one explicit eta binder. -/
inductive Guarded (c : Name) : VExpr → Prop where
  | var : Guarded c (.bvar i)
  | app : Guarded c f → Guarded c a → Guarded c (.app f a)
  | lamProp : Guarded c b → Guarded c (.lam prop b)
  | lamDomain : Guarded c b → Guarded c (.lam (domain c) (.lam prop b))

/-- Lifting preserves the two closed annotations and every guarding binder. -/
theorem Guarded.liftN (H : Guarded c e) : Guarded c (e.liftN n k) := by
  induction H generalizing k with
  | var => exact .var
  | app _ _ ihf iha => exact .app ihf iha
  | lamProp _ ih => exact .lamProp ih
  | lamDomain _ ih => exact .lamDomain ih

/-- Substitution preserves guards because all annotations are closed. -/
theorem Guarded.inst (H : Guarded c e) (Hx : Guarded c x) : Guarded c (e.inst x k) := by
  induction H generalizing k with
  | var =>
    simp only [VExpr.inst, instVar]
    split
    · exact .var
    · split
      · exact Hx.liftN
      · exact .var
  | app _ _ ihf iha => exact .app (ihf) (iha)
  | lamProp _ ih => exact .lamProp ih
  | lamDomain _ ih => exact .lamDomain ih

private theorem beta_lam_inv (R : BetaRed e out) (hs : e = .lam D b) :
    ∃ D' b', out = .lam D' b' ∧ BetaRed D D' ∧ BetaRed b b' := by
  induction R generalizing D b with
  | refl => exact ⟨_, _, hs, .refl, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, hs1, RD1, Rb1⟩ := ih1 hs
    obtain ⟨_, _, hs2, RD2, Rb2⟩ := ih2 hs1
    exact ⟨_, _, hs2, RD1.trans RD2, Rb1.trans Rb2⟩
  | lam RD Rb => cases hs; exact ⟨_, _, rfl, RD, Rb⟩
  | app | forallE | proj | beta => cases hs

/-- Every finite beta reduct retains the guarded-lambda syntax, regardless of how
many recursive root redexes it contracts. No normalization premise is used. -/
theorem Guarded.beta (R : BetaRed e out) (H : Guarded c e) : Guarded c out := by
  induction R with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih2 (ih1 H)
  | app _ _ ihf iha => cases H with | app Hf Ha => exact .app (ihf Hf) (iha Ha)
  | lam RD Rb _ ihb =>
    cases H with
    | lamProp Hb =>
      have hD := beta_eq_of_not_hasBeta RD (by simp [prop, HasBeta])
      subst hD
      exact .lamProp (ihb Hb)
    | lamDomain Hb =>
      have hD := beta_eq_of_not_hasBeta RD (by simp [domain, HasBeta])
      subst hD
      obtain ⟨D', b', hb, RD', _⟩ := beta_lam_inv Rb rfl
      have hD' := beta_eq_of_not_hasBeta RD' (by simp [prop, HasBeta])
      subst D'
      have HB := ihb (.lamProp Hb)
      rw [hb] at HB ⊢
      cases HB with | lamProp HB => exact .lamDomain HB
  | beta =>
    cases H with
    | app Hf Ha =>
      cases Hf with
      | lamProp Hb => exact Hb.inst Ha
      | lamDomain Hb => exact (Guarded.lamProp Hb).inst Ha
  | forallE | proj => cases H

/-- The eta-expanded self-application starts in the guarded syntax. -/
theorem etaOmega_guarded : Guarded c (etaOmega c) :=
  .app (.lamDomain (.app (.app .var .var) .var))
    (.lamDomain (.app (.app .var .var) .var))

/-- The unexpanded diagonal has no guarding eta binder. -/
theorem diagonal_not_guarded : ¬ Guarded c (diagonal c) := by
  intro H
  cases H

/-- The ordinary self-application has only itself as a finite beta reduct. -/
theorem omega_beta_eq (R : BetaRed (omegaTerm c) out) : out = omegaTerm c :=
  RecursiveDomain.omega_beta_eq (by simp [domain, HasBeta]) R

end Lean4Lean.VEnv.Strengthening.GuardedEta
