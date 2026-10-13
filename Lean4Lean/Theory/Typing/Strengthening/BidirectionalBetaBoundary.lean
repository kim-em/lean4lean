import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication
import Lean4Lean.Theory.Typing.Strengthening.DomainCertificateBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEta

/-! # Independent comparison is not closed under beta simulation

An identity applied to `f` and to its eta expansion has an independent comparison.
Reducing the left identity exposes `f`; neither beta reduct of the right side has
an independent comparison with this variable. One full eta step repairs the pair.
The example is uniformly typed in any Params environment and uses no recursion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

/-- An independently compared non-proof variable can only compare with itself. -/
theorem BiNormal.variable_inv (H : BiNormal false n Γ (.bvar i) e)
    (hn : ¬ IsProof Γ (.bvar i)) : e = .bvar i := by
  cases H with
  | refl => rfl
  | proofIrrel hP hi _ => exact (hn ⟨_, hi, hP⟩).elim

omit [Params] in
/-- An identity with beta-normal annotation and argument has exactly its source
and its argument as possible finite beta reducts. -/
theorem identity_beta_targets (hD : ¬ HasBeta D) (hx : ¬ HasBeta x)
    (R : BetaRed (.app (.lam D (.bvar 0)) x) out) :
    out = .app (.lam D (.bvar 0)) x ∨ out = x := by
  have hi : ¬ HasBeta (.lam D (.bvar 0)) := by simpa [HasBeta] using hD
  have aux {source out} (R : BetaRed source out)
      (hsrc : source = .app (.lam D (.bvar 0)) x) :
      out = .app (.lam D (.bvar 0)) x ∨ out = x := by
    induction R with
    | refl => exact .inl hsrc
    | trans R1 R2 ih1 ih2 =>
      rcases ih1 hsrc with h | h
      · exact ih2 h
      · subst h
        exact .inr (beta_eq_of_not_hasBeta R2 hx)
    | app Rf Ra _ _ =>
      cases hsrc
      rw [beta_eq_of_not_hasBeta Rf hi, beta_eq_of_not_hasBeta Ra hx]
      exact .inl rfl
    | beta =>
      cases hsrc
      exact .inr (by simp [inst, instVar_zero])
    | lam | forallE | proj => cases hsrc
  exact aux R rfl

namespace BiBetaBoundary
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

def D : VExpr := .forallE (.sort .zero) (.sort .zero)
def ctx : List VExpr := [D]
def f : VExpr := .bvar 0
def etaF : VExpr := .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
def identity : VExpr := .lam D (.bvar 0)
def left : VExpr := .app identity f
def right : VExpr := .app identity etaF

private theorem domain_typed : Γ ⊢ D : .sort (.succ .zero) := by
  have h : Γ ⊢ D : .sort (.imax (.succ .zero) (.succ .zero)) :=
    HasType.forallE (HasType.sort (l := .zero) (by trivial))
    (HasType.sort (l := .zero) (by trivial))
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (by trivial)
    (by trivial) VLevel.imax_self).defeq h

private theorem ctx_wf : OnCtx ctx (Params.env.IsType univs) := ⟨trivial, _, domain_typed⟩

private theorem f_typed : ctx ⊢ f : D := .bvar .zero

private theorem identity_typed : ctx ⊢ identity : .forallE D D.lift :=
  HasType.lam domain_typed (.bvar .zero)

private theorem eta_typed : ctx ⊢ etaF : D := (IsDefEq.eta f_typed).hasType.1

/-- The application has independent mode even though its argument comparison uses eta. -/
theorem comparison : BiNormal false 3 ctx left right := by
  have hbody : .sort .zero :: ctx ⊢ .app f.lift (.bvar 0) : .sort .zero :=
    HasType.app (f_typed.weak henv) (.bvar .zero)
  have HE : BiNormal true 2 ctx f etaF := .etaR f_typed (.refl hbody)
  exact .appDF identity_typed identity_typed f_typed eta_typed (.refl identity_typed) HE

/-- The exposed left variable has no independent comparison with any right beta
reduct, so one-sided beta simulation fails even with common endpoint typings. -/
theorem no_beta_match (R : BetaRed right out) : ¬ ∃ n, BiNormal false n ctx f out := by
  have hn : ¬ IsProof ctx f := not_isProof_function_to_sort ctx_wf f_typed
  have hD : ¬ HasBeta D := by simp [D, HasBeta]
  have hη : ¬ HasBeta etaF := by simp [etaF, HasBeta]
  have hcases := identity_beta_targets hD hη R
  rintro ⟨n, H⟩
  have he := H.variable_inv hn
  rcases hcases with rfl | rfl <;> cases he

/-- A fully typed failure of beta-only independent simulation. This is an
obstruction to that closure lemma, not to strengthening or full-reduction repair. -/
theorem beta_simulation_failure :
    OnCtx ctx (Params.env.IsType univs) ∧ (ctx ⊢ left : D) ∧ (ctx ⊢ right : D) ∧
    BiNormal false 3 ctx left right ∧ BetaRed left f ∧
    ∀ out, BetaRed right out → ¬ ∃ n, BiNormal false n ctx f out :=
  ⟨ctx_wf, HasType.app identity_typed f_typed, HasType.app identity_typed eta_typed,
    comparison, .beta, fun _ R => no_beta_match R⟩

/-- One eta expansion of the exposed left variable and one beta contraction on
the right produce the same term, giving a reflexive independent comparison. -/
theorem full_repair : FullReduction ctx f etaF ∧ FullReduction ctx right etaF ∧
    BiNormal false 0 ctx etaF etaF :=
  ⟨.tail .rfl (.funEta f_typed), .tail .rfl (.core (.beta .rfl .rfl)), .refl eta_typed⟩

end BiBetaBoundary
end Lean4Lean.VEnv.Strengthening
