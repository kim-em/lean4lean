import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidValueReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidValueInjectivity

/-! # Computational rigid injectivity from the proved value observer

At universe-ending dependent telescope assignments, rigid argument histories
are now derived rather than assumed. Type-fork joining remains an explicit
premise. The proof uses beta cleanup twice and transports the first vector's
histories along the second cleanup's component beta paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

private theorem rigid_spine_arguments
    (E : ProofShape.mkApps (.const c ls) args = ProofShape.mkApps (.const c' ls') args') : args = args' := by
  induction args using List.snoc_induction generalizing args' with
  | nil =>
    cases args' using List.snoc_induction with
    | nil => rfl
    | snoc args' a => rw [ProofShape.mkApps_snoc] at E; cases E
  | snoc args a ih =>
    cases args' using List.snoc_induction with
    | nil => rw [ProofShape.mkApps_snoc] at E; cases E
    | snoc args' a' =>
      rw [ProofShape.mkApps_snoc, ProofShape.mkApps_snoc] at E
      obtain ⟨Ef, rfl⟩ := ProofShape.app.inj E
      exact congrArg (· ++ [a]) (ih Ef)

variable [Params] {D : PureObservation.Definitions}

/-- Beta cleanup of a raw argument vector appends to every value history. -/
theorem ScopedValueChain.forall₂_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : List.Forall₂ (ScopedValueChain D Δ) original args)
    (R : List.Forall₂ ProofShape.BetaRed args outputs) :
    List.Forall₂ (ScopedValueChain D Δ) original outputs := by
  induction H generalizing outputs with
  | nil => cases R; exact .nil
  | cons H HT ih =>
    cases R with
    | cons R RT => exact .cons (H.compute heq hs (.beta R)) (ih RT)

/-- Rigid type spines at universe-ending telescope assignments have pairwise
computational argument equalities. All argument histories are supplied by the
proved observer; the only joining premise is TypeForkJoin. -/
theorem TypedComputationEq.rigid_spine_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : env.HasType univs Γ (.const c ls) T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (hf' : env.HasType univs Γ (.const c ls') T')
    (HT' : DemandProfile.SortTelescope args'.length T')
    (HW' : InstForallsC env univs Γ T' args' result')
    (ht : env.HasType univs Γ (VExpr.mkApps (.const c ls) args) (.sort u))
    (H : TypedComputationEq D Γ (VExpr.mkApps (.const c ls) args)
      (VExpr.mkApps (.const c ls') args') A) :
    List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args' := by
  obtain ⟨hls, HA⟩ := H.defeq.toU.rigidApp_inv henv hΓ hc ht
  have H := H.at_source_type hΓ ht
  obtain ⟨shared, RL, RR⟩ := H.type_join heq hs HF hΓ
  obtain ⟨levels, outputs, RB, HL⟩ :=
    ValueDemandProfile.static_structure_rigid_value_readout heq hs hc hD hΓ hf HT HW RL
  obtain ⟨levels', outputs', RB', HR⟩ :=
    ValueDemandProfile.static_structure_rigid_value_readout heq hs hc hD hΓ hf' HT' HW'
      (RR.trans (.beta RB))
  obtain ⟨next, EN, RN⟩ := RB'.const_spine
  have EArgs := rigid_spine_arguments EN
  rw [← EArgs] at RN
  exact ⟨hls, scoped_value_histories_reify heq hs hΓ HA (ScopedValueChain.forall₂_beta heq hs HL RN) HR⟩

end Lean4Lean.VEnv.Strengthening
