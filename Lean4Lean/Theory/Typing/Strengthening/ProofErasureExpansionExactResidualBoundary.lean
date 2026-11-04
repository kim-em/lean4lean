import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTransparentExpansionResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverySubstitutionBoundary

/-! # Common native carriers cannot give exact expansion residuals

A bound variable admits native identity expansion at its captured declared type.
Substituting a closed identity retains that annotation in the exact output, but
contracting first loses it. The assigned type beta-computes to a common native
carrier, so even that stronger alignment cannot repair exact instantiation.
The two endpoints do have a beta common reduct.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeIdentityResidualBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape Developments EtaScope
open ErasedRecoverySubstitutionBoundary (captured captured_erasure captured_beta_plain)
open private ProofShape.liftN_lam_inv ProofShape.liftN_app_inv ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay

/-- The closed ordinary identity is the head-beta contractum. -/
def short : ProofShape := .lam (.sort .zero) (.bvar 0)
/-- The exact substituted expansion retains a fresh proposition in its type. -/
def long : ProofShape := .app (.lam captured (.bvar 0)) short
/-- Expanding the bound variable uses its lifted declaration as annotation. -/
def expandedBody : ProofShape := .app (.lam (captured.liftN 1) (.bvar 0)) (.bvar 0)

/-- Substitution into the expanded body produces the captured identity wrapper. -/
theorem expandedBody_inst : expandedBody.inst short = long := by
  simp only [expandedBody, long, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one, ProofShape.subst,
    ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.lift, ProofShape.Subst.cons]

/-- Its captured annotation disappears in a single beta contraction. -/
theorem long_beta_short : ProofShape.BetaRed long short := by
  simpa only [long, ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
    (ProofShape.BetaRed.beta (A := captured) (b := .bvar 0) (a := short))

/-- No lower raw term lifts to the captured expansion output. -/
theorem long_not_lift (e : ProofShape) : e.liftN 1 ≠ long := by
  intro E
  obtain ⟨_, _, _, EF, _⟩ := ProofShape.liftN_app_inv E
  obtain ⟨_, _, _, EA, _⟩ := ProofShape.liftN_lam_inv EF
  obtain ⟨_, _, _, ED, _⟩ := ProofShape.liftN_forallE_inv EA
  obtain ⟨_, x, _, _, EX⟩ := ProofShape.liftN_app_inv ED
  cases x <;> simp [ProofShape.liftN, liftVar] at EX

variable [Params]

private theorem short_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (ident 0) = short := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hn := not_isProof_function_to_sort hΓ (ident_typed env univs Γ 0)
  have hx : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  change proofErase Γ (.lam (.sort .zero) (.bvar 0)) = short
  change ¬ IsProof Γ (.lam (.sort .zero) (.bvar 0)) at hn
  simp only [proofErase, if_neg hn, if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .zero) (by trivial))),
    if_neg (not_isProof_of_sort hΓS hx), short]

/-- No source-typed descending relation can reproduce the exact expansion
from its beta contractum, independently of guard depth or canonical Eq. -/
theorem short_not_compute_long (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedCompute Step (proofEraseCtx (.sort .zero :: Γ)) short long := by
  intro R
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  obtain ⟨e, _, E⟩ := proofErase_scoped_compute_descend hstep hΓ hΓS Ctx.LiftN.one
    (ident_typed env univs Γ 0) rfl
    (by simpa [short_erasure hΓ, short, ProofShape.liftN, liftVar] using R)
  exact long_not_lift _ E

/-- Native identity expansion of the variable is already a stage-one step;
its guard uses only the declaration lookup, with no conversions. -/
theorem variable_expand :
    ErasedExpansionStage D 1 (captured :: Δ) (.bvar 0) expandedBody :=
  .inr (.inr (.inr (.intro (ScopedTypeRecovery.bvar))))

/-- A typed argument has a beta-only common native carrier with its assigned
type, yet exact substitution of a stage-one identity expansion is impossible
in every source-typed descending target relation. The failed endpoint still
beta-contracts to the instantiated source. This rules out replacing exact
native images by common carriers while keeping an exact directed conclusion. -/
theorem common_native_exact_instantiation_failure
    (hstep : ErasedScopedPrimitiveDescent Target)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ A x b B out native,
      OnCtx (A :: Δ) (env.IsType univs) ∧ env.HasType univs Δ x A ∧
      env.HasType univs (A :: Δ) b B ∧
      ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Δ) (proofErase Δ x) native ∧
      ProofShape.BetaRed (proofErase Δ A) native ∧
      ScopedCompute (ErasedExpansionStage D 1) (proofEraseCtx (A :: Δ))
        (proofErase (A :: Δ) b) out ∧
      (¬ ScopedCompute Target (proofEraseCtx Δ) (proofErase Δ (b.inst x))
        (out.inst (proofErase Δ x))) ∧
      ProofShape.BetaRed (out.inst (proofErase Δ x)) (proofErase Δ (b.inst x)) := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hx : env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) :=
    identity_at_captured_pi
  have hΓC : OnCtx (capturedPi (.sort .zero) :: .sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓS, hx.isType henv hΓS⟩
  have hb : env.HasType univs (capturedPi (.sort .zero) :: .sort .zero :: Γ)
      (.bvar 0) (capturedPi (.sort .zero)).lift := .bvar .zero
  have hn := not_isProof_function_to_sort hΓC
    (A := (capturedDomain (.sort .zero)).lift) (u := .zero) hb
  have EX : proofErase (.sort .zero :: Γ) (ident 0).lift = short := by
    simpa only [ident, tower, VExpr.lift, VExpr.liftN, liftVar, Nat.zero_lt_succ,
      ↓reduceIte, Nat.zero_add] using short_erasure hΓS
  refine ⟨.sort .zero :: Γ, capturedPi (.sort .zero), (ident 0).lift, .bvar 0, _,
    expandedBody, .forallE (.sort .zero) (.sort .zero), hΓC, hx, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [EX]
    exact .lam (.bvar)
  · rw [captured_erasure hΓ]
    exact captured_beta_plain
  · rw [proofEraseCtx, captured_erasure hΓ,
      show proofErase _ (.bvar 0) = .bvar 0 from if_neg hn]
    exact .base variable_expand
  · simp only [VExpr.inst, instVar_zero, EX, expandedBody_inst]
    exact short_not_compute_long hstep hΓ
  · simpa only [VExpr.inst, instVar_zero, EX, expandedBody_inst] using long_beta_short

/-- The counterexample persists in the entire controlled expansion union,
even in a canonical-Eq environment and with sound definitions. -/
theorem expansion_union_exact_instantiation_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ A x b B out native,
      OnCtx (A :: Δ) (env.IsType univs) ∧ env.HasType univs Δ x A ∧
      env.HasType univs (A :: Δ) b B ∧
      ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Δ) (proofErase Δ x) native ∧
      ProofShape.BetaRed (proofErase Δ A) native ∧
      ScopedCompute (ErasedExpansionStage D 1) (proofEraseCtx (A :: Δ))
        (proofErase (A :: Δ) b) out ∧
      (¬ ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Δ) (proofErase Δ (b.inst x))
        (out.inst (proofErase Δ x))) ∧
      ProofShape.BetaRed (out.inst (proofErase Δ x)) (proofErase Δ (b.inst x)) :=
  common_native_exact_instantiation_failure (erased_expansion_union_descent heq hs) hΓ

end Lean4Lean.VEnv.Strengthening.NativeIdentityResidualBoundary
