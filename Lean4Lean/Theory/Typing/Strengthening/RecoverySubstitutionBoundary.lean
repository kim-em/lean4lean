import Lean4Lean.Theory.Typing.Strengthening.TypeRecovery
import Lean4Lean.Theory.Typing.Strengthening.EtaScope

/-! # Exact type recovery is not closed under arbitrary typed substitution

A variable recovers its declared type. That declaration can contain an irrelevant
binder in a beta-redex annotation. Substituting a closed identity at this valid
type leaves a chosen output type which cannot be recovered: scope reflection
would remove the binder from syntax that explicitly contains it.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaScope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
open PureObservation (Definitions)
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- A valid function type whose domain still contains the newly added variable. -/
def capturedPi (Q : VExpr) : VExpr := .forallE (capturedDomain Q) (.sort .zero)

/-- Ordinary typing can choose this convertible, syntactically captured type
for the lifted identity. Exact recovery is intentionally more restrictive. -/
theorem identity_at_captured_pi : Q :: Γ ⊢ (ident 0).lift : capturedPi Q := by
  have hvar : Q :: Γ ⊢ .bvar 0 : Q.lift := .bvar .zero
  have hA : Q :: Γ ⊢ capturedDomain Q ≡ .sort .zero : .sort (.succ .zero) :=
    .beta (HasType.sort (by trivial)) hvar
  have hf : Q :: Γ ⊢ (ident 0).lift : .forallE (.sort .zero) (.sort .zero) := by
    have h : Q :: Γ ⊢ (ident 0).lift : (tower 1).lift :=
      (ident_typed Params.env univs Γ 0).weak henv
    simpa only [tower, lift, liftN] using h
  have hTy : Q :: Γ ⊢ .forallE (.sort .zero) (.sort .zero) ≡ capturedPi Q :
      .sort (.imax (.succ .zero) (.succ .zero)) :=
    .forallEDF hA.symm (HasType.sort (by trivial))
  exact hTy.defeq hf

omit [Params] in
/-- The chosen Pi type cannot be the weakening of any smaller expression. -/
theorem captured_pi_not_scoped : ¬ (capturedPi Q).Skips 1 0 := by
  simp [skips_iff, capturedPi, capturedDomain, Skips']

/-- No finite recovery certificate can infer this captured type for the lifted
identity, although the ordinary typing above is valid. -/
theorem identity_captured_not_recovered (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hQ : Γ ⊢ Q : .sort u) :
    ¬ TypeRecovery D depth (Q :: Γ) (ident 0).lift (capturedPi Q) := by
  intro R
  rw [lift_eq_lift'] at R
  obtain ⟨T, hT, _⟩ := R.descend heq hs (Ctx.Lift'.skip .refl) hΓ
    ⟨hΓ, _, hQ⟩ ⟨_, ident_typed env univs Γ 0⟩
  apply captured_pi_not_scoped (Q := Q)
  rw [hT, ← lift_eq_lift']
  exact .liftN

/-- A fully typed one-variable substitution counterexample. The source variable
has a recovery certificate, and the substitution has the correct declared type,
but retaining the exact substituted output type is impossible. This does not
refute re-synthesizing a different convertible output type after substitution. -/
theorem exact_recovery_substitution_failure (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hQ : Γ ⊢ Q : .sort u) :
    OnCtx (capturedPi Q :: Q :: Γ) (env.IsType univs) ∧
    (Q :: Γ ⊢ (ident 0).lift : capturedPi Q) ∧
    Ctx.InstN (Q :: Γ) (ident 0).lift (capturedPi Q) 0 (capturedPi Q :: Q :: Γ) (Q :: Γ) ∧
    TypeRecovery D depth (capturedPi Q :: Q :: Γ) (.bvar 0) (capturedPi Q).lift ∧
    ¬ TypeRecovery D depth (Q :: Γ) ((.bvar 0 : VExpr).inst (ident 0).lift)
      ((capturedPi Q).lift.inst (ident 0).lift) := by
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf : Q :: Γ ⊢ (ident 0).lift : capturedPi Q := identity_at_captured_pi
  refine ⟨⟨hΓQ, hf.isType henv hΓQ⟩, hf, .zero, .bvar .zero, ?_⟩
  simpa only [inst, instVar_zero, liftN_zero, inst_lift] using
    (identity_captured_not_recovered (depth := depth) heq hs hΓ hQ)


/-- Re-synthesizing the ordinary Pi type succeeds for the substituted term. -/
theorem substituted_identity_plain_recovery :
    TypeRecovery D depth (Q :: Γ) (ident 0).lift (tower 1) :=
  .lam (.bvar .zero)

/-- The old captured type computes to the newly synthesized one. This concrete
repair changes the selected output type, which exact substitution preservation
was incorrectly required to retain. -/
theorem captured_pi_computes_plain :
    CertifiedKCompute D depth (Q :: Γ) (capturedPi Q) (tower 1) :=
  .forallE (.base (.base (.base (.base .beta)))) (.base .refl)

end Lean4Lean.VEnv.Strengthening.EtaScope
