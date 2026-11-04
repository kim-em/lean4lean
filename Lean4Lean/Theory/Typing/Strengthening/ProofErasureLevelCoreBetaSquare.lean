import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation

/-! # Head beta against mixed ordinary, universe and expansion computation

A mixed path from a retained lambda has a level-core lambda common reduct.
Its body path substitutes freely. Thus a whole computed function and an
arbitrarily expanded argument meet the original beta contractum without any
native recovery hypothesis on either the original or computed argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Level-core primitives cannot consume a lambda head. Every finite path from
a lambda therefore has separate annotation and body paths in the same core. -/
theorem ProofShape.Compute.level_core_lam_inv
    (R : ProofShape.Compute (ErasedLevelCore D) (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ ProofShape.Compute (ErasedLevelCore D) A A' ∧
      ProofShape.Compute (ErasedLevelCore D) b b' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | base H =>
    rcases H with H | H
    · exact (E ▸ erased_iota_primitive_head H).elim
    · cases E; cases H
  | beta H =>
    cases E
    obtain ⟨A', b', HE, HA, HB⟩ := H.lam_inv
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨A₁, b₁, rfl, HA, HB⟩ := ih1 E
    obtain ⟨A₂, b₂, HE, RA, RB⟩ := ih2 rfl
    exact ⟨_, _, HE, HA.trans RA, HB.trans RB⟩
  | lam RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | forallE => cases E

/-- A whole mixed path from a retained lambda has a level-core lambda readout
with ordinary/level histories for both original components. No body history
or native coverage premise is supplied by the caller. -/
theorem proofErase_level_core_expansion_lambda_readout
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF) :
    ∃ X y, ProofShape.Compute (ErasedLevelCore D) outF (.lam X y) ∧
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ A) X ∧
      ProofShape.Compute (ErasedLevelCore D) (proofErase (A :: Γ) b) y := by
  have EE : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  obtain ⟨shared, RL, RF'⟩ := proofErase_level_core_expansion_join hs hlevels hcon hc hr
    hΓ (HasType.lam hA hb) (EE ▸ RF)
  rw [EE] at RL
  obtain ⟨X, y, rfl, RX, RY⟩ := RL.level_core_lam_inv
  exact ⟨X, y, RF', RX, RY⟩

/-- Head beta commutes with whole mixed function computation and arbitrary
full-union argument computation, up to a common residual. Neither argument
needs a native certificate; the right residual uses only ordinary/level steps. -/
theorem proofErase_level_core_expansion_function_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ProofShape.Compute (ErasedLevelCore D) (.app outF outX) shared := by
  obtain ⟨X, y, RF', _, RB⟩ := proofErase_level_core_expansion_lambda_readout
    hs hlevels hcon hc hr hΓ hA hb hn RF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have RXB := proofErase_expansion_compute_inst_argument heq hs hΓA hb hx RX
  have RB' : ProofShape.Compute (ErasedLevelCore D)
      ((proofErase (A :: Γ) b).inst outX) (y.inst outX) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RB.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one outX)
  refine ⟨y.inst outX, (RXB.mono (fun H => ⟨stage, H⟩)).trans (RB'.scoped ?_),
    (ProofShape.Compute.app RF' .refl).trans (.beta .beta)⟩
  intro Δ a b H
  exact .base (erased_level_core_expansion_into_union (.inl H))

namespace StoredCore
/-- Concrete stored definitions discharge all confluence/compatibility premises
of the whole-function beta square. Native guards may use the full expanded
union, and the argument may use any of its singleton stages. -/
theorem level_expansion_function_beta_square (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv))) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedExpansionUnion (Definitions.ofEnv env univs henv))
      (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedExpansionUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ProofShape.Compute (ErasedLevelCore (Definitions.ofEnv env univs henv)) (.app outF outX) shared :=
  proofErase_level_core_expansion_function_beta_square heq (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓ hA hb hx hn RF RX
end StoredCore
end Lean4Lean.VEnv.Strengthening
