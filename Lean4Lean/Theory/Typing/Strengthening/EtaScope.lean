import Lean4Lean.Theory.Typing.Strengthening.DomainJoin
import Lean4Lean.Theory.Typing.Strengthening.DevelopmentRounds

/-! # Scope and typing in eta repair

A typed eta expansion can introduce the unused binder into its annotation. This
is an explicit scope failure for arbitrary full reducts, not a strengthening
counterexample. Conversely, eta expansion is harmless below when its two endpoints
already have the same typing below.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- A same-type eta expansion is already justified in the smaller context by its
endpoint typings. No chosen function typing from the larger context is required. -/
theorem eta_of_endpoint_typings (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : T) (hη : Γ ⊢ .lam A (.app f.lift (.bvar 0)) : T) :
    Γ ⊢ f ≡ .lam A (.app f.lift (.bvar 0)) : T := by
  obtain ⟨B, hPi, _⟩ := hη.lam_inv_forallE henv hΓ
  have hfPi := hf.defeqU_r henv hΓ hPi.symm
  exact hPi.defeqDF henv hΓ (IsDefEq.eta hfPi).symm

/-- Lower a full eta step whose target is syntactically a lift and typed below at
the source's type. The hypotheses deliberately include that target typing: ambient
subject reduction alone does not provide it. -/
theorem eta_lift_descend (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : T) (hg : Γ ⊢ g : T)
    (shape : g.lift' ρ = .lam A (.app (f.lift' ρ).lift (.bvar 0))) : Γ ⊢ f ≡ g : T := by
  obtain ⟨A₀, b, rfl, rfl, hb⟩ := lift'_eq_lam shape
  have hb' : b = .app f.lift (.bvar 0) := by
    apply lift'_inj.1
    rw [← hb]
    simp [lift', lift_lift'_cons]
  subst b
  exact eta_of_endpoint_typings hΓ hf hg

namespace EtaScope
/-- This domain is convertible to Prop but explicitly mentions the new binder. -/
def capturedDomain (Q : VExpr) : VExpr :=
  .app (.lam Q.lift (.sort .zero)) (.bvar 0)
def expanded (Q : VExpr) : VExpr :=
  .lam (capturedDomain Q) (.app (ident 0).lift.lift (.bvar 0))

/-- The identity can be eta-expanded using the captured annotation in any new
well-typed binder, including one with no inhabitant supplied below. -/
theorem captured_step :
    FullStep (Q :: Γ) (ident 0).lift (expanded Q) := by
  have hvar : Q :: Γ ⊢ .bvar 0 : Q.lift := .bvar .zero
  have hA : Q :: Γ ⊢ capturedDomain Q ≡ .sort .zero : .sort (.succ .zero) :=
    .beta (HasType.sort (by trivial)) hvar
  have hf : Q :: Γ ⊢ (ident 0).lift : .forallE (.sort .zero) (.sort .zero) := by
    have h : Q :: Γ ⊢ (ident 0).lift : (tower 1).lift :=
      (ident_typed Params.env univs Γ 0).weak henv
    simpa only [tower, lift, liftN] using h
  have hTy : Q :: Γ ⊢ .forallE (.sort .zero) (.sort .zero) ≡
      .forallE (capturedDomain Q) (.sort .zero) : .sort (.imax (.succ .zero) (.succ .zero)) :=
    .forallEDF hA.symm (HasType.sort (by trivial))
  exact .funEta (hTy.defeq hf)

omit [Params] in
/-- The generated annotation prevents the eta target from being a lift. -/
theorem captured_not_lift : ¬ (expanded Q).Skips 1 0 := by
  simp [skips_iff, expanded, capturedDomain, Skips']

/-- Beta reduction cleans this particular annotation and eta body, returning to
the original lifted identity. The scope failure is repairable in this example. -/
theorem captured_cleanup : FullReduction (Q :: Γ) (expanded Q) (ident 0).lift := by
  have hB : ParRed (capturedDomain Q :: Q :: Γ)
      (.app (ident 0).lift.lift (.bvar 0)) (.bvar 0) := by
    have h : ParRed (capturedDomain Q :: Q :: Γ)
        (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) ((.bvar 0 : VExpr).inst (.bvar 0)) :=
      .beta .rfl .rfl
    simpa [ident, tower, lift, liftN, inst, instVar] using h
  have hD' : ParRed (Q :: Γ) (capturedDomain Q) (.sort .zero) := .beta .rfl .rfl
  simpa [expanded, ident, tower, lift, liftN, liftVar] using
    (show FullReduction (Q :: Γ) (.lam (capturedDomain Q) (.app (ident 0).lift.lift (.bvar 0)))
      (.lam (.sort .zero) (.bvar 0)) from .tail .rfl (.core (.lam hD' hB)))

/-- A well-formed extension in which a full step from a lifted, typed identity
introduces the new variable, and a finite cleanup removes it again. -/
theorem scope_failure_and_cleanup (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hQ : Γ ⊢ Q : .sort u) :
    OnCtx (Q :: Γ) (Params.env.IsType univs) ∧
    FullStep (Q :: Γ) (ident 0).lift (expanded Q) ∧
    ¬ (expanded Q).Skips 1 0 ∧
    FullReduction (Q :: Γ) (expanded Q) (ident 0).lift :=
  ⟨⟨hΓ, _, hQ⟩, captured_step, captured_not_lift, captured_cleanup⟩

end EtaScope
end Lean4Lean.VEnv.Strengthening
