import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinSubstitution

/-! # Native recovery across contexts related by computation

Exact native outputs need not survive context change. On pure syntax, native
recovery can instead retain a raw join to its old output. The target recovery
uses only beta conversions, even when the source used controlled expansions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape
variable [Params]

/-- Pure native recovery transports through joined context lookups, with a
joined output. The target primitive relation is arbitrary: only beta conversion
is used. In particular, no target guarded computation needs to be reproduced. -/
theorem ScopedTypeRecovery.joined_context
    (hpure : ∀ {Δ a b}, Step Δ a b → PureContext Δ → PureLambda a → PureLambda b)
    (hjoin : ∀ {Δ a b}, Step Δ a b → PureLambda a → BetaLevelJoin a b)
    (R : ScopedTypeRecovery Step Δ e A) (HΔ : PureContext Δ) (HE : PureLambda e)
    (W : BetaLevelContext Δ' Δ) :
    ∃ A', ScopedTypeRecovery Step' Δ' e A' ∧ BetaLevelJoin A' A := by
  induction R generalizing Δ' with
  | bvar => exact ⟨_, .bvar, W.oracle⟩
  | sort hw => exact ⟨_, .sort hw, .refl⟩
  | const | proj => exact HE.elim
  | lam _ ih =>
    obtain ⟨B', R', H⟩ := ih (HΔ.cons HE.1) HE.2 (W.cons .refl)
    exact ⟨_, .lam R', .forallE .refl H⟩
  | app _ ih =>
    obtain ⟨T', R', H⟩ := ih HΔ HE.1 W
    obtain ⟨X, Y, RT, _, HY⟩ := H.pi_exposure
    exact ⟨_, ScopedTypeRecovery.app (R'.convert (.beta RT)), HY.inst_pair .refl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨T', RA, HA⟩ := ihA HΔ HE.1 W
    obtain ⟨u', RU, HU⟩ := HA.sort_exposure
    obtain ⟨S', RB, HB⟩ := ihB (HΔ.cons HE.1) HE.2 (W.cons .refl)
    obtain ⟨v', RV, HV⟩ := HB.sort_exposure
    exact ⟨_, .forallE (RA.convert (.beta RU)) (RB.convert (.beta RV)),
      .variant (.sort (VLevel.imax_congr HU HV))⟩
  | convert R RC ih =>
    obtain ⟨T', R', H⟩ := ih HΔ HE W
    exact ⟨_, R', H.trans (RC.pure_join hpure hjoin HΔ (R.pure_context hpure HΔ HE))⟩

end ProofShape
variable [Params]

/-- Expanded finite-stage recovery on pure syntax transports to beta-only
recovery in any joined context. Neither the output nor target context must be
pure; their relation to the source is recorded by the raw join. -/
theorem erased_expansion_stage_native_joined_context
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) Δ e A)
    (HΔ : PureContext Δ) (HE : PureLambda e) (W : BetaLevelContext Δ' Δ) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ' e A' ∧ BetaLevelJoin A' A :=
  R.joined_context (erased_expansion_stage_pure_root stage)
    (erased_expansion_stage_pure_root_join stage) HΔ HE W

/-- Arbitrary expanded union recovery has the same beta-only context transport. -/
theorem erased_expansion_union_native_joined_context
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ e A)
    (HΔ : PureContext Δ) (HE : PureLambda e) (W : BetaLevelContext Δ' Δ) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ' e A' ∧ BetaLevelJoin A' A :=
  R.joined_context (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root stage R)
    (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root_join stage R) HΔ HE W

/-- Pure expanded native evidence can be replaced by beta-only native evidence
in the same context, retaining a raw join to its former output. -/
theorem erased_expansion_union_native_beta_basis
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ e A)
    (HΔ : PureContext Δ) (HE : PureLambda e) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ e A' ∧ BetaLevelJoin A' A :=
  erased_expansion_union_native_joined_context R HΔ HE .refl

end Lean4Lean.VEnv.Strengthening
