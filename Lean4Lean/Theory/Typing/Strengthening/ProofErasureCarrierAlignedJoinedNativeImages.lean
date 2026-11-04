import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedBetaNativeRenaming

/-! # Native substitution with joined image types

Exact selected types are unnecessary for substitution on the pure source
fragment. Images carry beta-only native evidence whose output is joined to the
substituted context lookup. The substituted recovery keeps the same guarantee.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape
variable [Params]

/-- Every raw variable image has beta-only native evidence joined to its
substituted lookup type. Images and target contexts need not be pure. -/
def JoinedNativeImages (Δ Δ' : List ProofShape) (τ : Subst) : Prop :=
  ∀ i, ∃ T, ScopedTypeRecovery (fun _ _ _ => False) Δ' (τ i) T ∧
    BetaLevelJoin T ((contextOracle Δ i).subst τ)

/-- Joined native images extend under arbitrary displayed binders. Exact
beta-only weakening preserves each older image and lifts its join certificate. -/
theorem JoinedNativeImages.cons (H : JoinedNativeImages Δ Δ' τ) :
    JoinedNativeImages (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro i
  cases i with
  | zero =>
    refine ⟨(A.subst τ).liftN 1, .bvar, ?_⟩
    simp only [contextOracle, TypeOracle.cons, lift_subst_lift]
    exact .refl
  | succ i =>
    obtain ⟨T, R, HT⟩ := H i
    refine ⟨T.liftN 1, R.beta_weak, ?_⟩
    simpa only [contextOracle, TypeOracle.cons, lift_subst_lift] using HT.liftN (n := 1) (k := 0)

/-- A single joined native argument gives a joined raw instantiation map. -/
theorem JoinedNativeImages.inst
    (R : ScopedTypeRecovery (fun _ _ _ => False) Δ p T) (H : BetaLevelJoin T A) :
    JoinedNativeImages (A :: Δ) Δ (Subst.one p) := by
  intro i
  cases i with
  | zero =>
    refine ⟨T, R, ?_⟩
    simpa only [contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id, Subst.cons] using H
  | succ i =>
    refine ⟨contextOracle Δ i, .bvar, ?_⟩
    simp only [contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id]
    exact .refl

/-- Pure native recovery substitutes through joined native images. All target
conversions are beta paths; source primitive computations survive as raw joins
of output types instead of needing exact target replay. -/
theorem ScopedTypeRecovery.joined_subst
    (hpure : ∀ {Δ a b}, Step Δ a b → PureContext Δ → PureLambda a → PureLambda b)
    (hjoin : ∀ {Δ a b}, Step Δ a b → PureLambda a → BetaLevelJoin a b)
    (R : ScopedTypeRecovery Step Δ e A) (HΔ : PureContext Δ) (HE : PureLambda e)
    (W : JoinedNativeImages Δ Δ' τ) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ' (e.subst τ) A' ∧
      BetaLevelJoin A' (A.subst τ) := by
  induction R generalizing Δ' τ with
  | bvar => exact W _
  | sort hw => exact ⟨_, .sort hw, .refl⟩
  | const | proj => exact HE.elim
  | lam _ ih =>
    obtain ⟨B', R', H⟩ := ih (HΔ.cons HE.1) HE.2 W.cons
    exact ⟨_, .lam R', .forallE .refl H⟩
  | app _ ih =>
    obtain ⟨T', R', H⟩ := ih HΔ HE.1 W
    obtain ⟨X, Y, RT, _, HY⟩ := H.pi_exposure
    refine ⟨_, ScopedTypeRecovery.app (R'.convert (.beta RT)), ?_⟩
    rw [subst_inst]
    exact HY.inst_pair .refl
  | forallE _ _ ihA ihB =>
    obtain ⟨T', RA, HA⟩ := ihA HΔ HE.1 W
    obtain ⟨u', RU, HU⟩ := HA.sort_exposure
    obtain ⟨S', RB, HB⟩ := ihB (HΔ.cons HE.1) HE.2 W.cons
    obtain ⟨v', RV, HV⟩ := HB.sort_exposure
    exact ⟨_, .forallE (RA.convert (.beta RU)) (RB.convert (.beta RV)),
      .variant (.sort (VLevel.imax_congr HU HV))⟩
  | convert R RC ih =>
    obtain ⟨T', R', H⟩ := ih HΔ HE W
    exact ⟨_, R', H.trans (RC.pure_join hpure hjoin HΔ (R.pure_context hpure HΔ HE)).subst⟩

end ProofShape
variable [Params]

/-- Joined images substitute every finite expanded recovery on a pure source
in a pure context, without restrictions on the image syntax or target context. -/
theorem erased_expansion_stage_native_joined_subst
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) Δ e A)
    (HΔ : PureContext Δ) (HE : PureLambda e) (W : JoinedNativeImages Δ Δ' τ) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ' (e.subst τ) A' ∧
      BetaLevelJoin A' (A.subst τ) :=
  R.joined_subst (erased_expansion_stage_pure_root stage)
    (erased_expansion_stage_pure_root_join stage) HΔ HE W

/-- The same joined-image transport holds for arbitrary expanded union recovery. -/
theorem erased_expansion_union_native_joined_subst
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ e A)
    (HΔ : PureContext Δ) (HE : PureLambda e) (W : JoinedNativeImages Δ Δ' τ) :
    ∃ A', ScopedTypeRecovery (fun _ _ _ => False) Δ' (e.subst τ) A' ∧
      BetaLevelJoin A' (A.subst τ) :=
  R.joined_subst (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root stage R)
    (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root_join stage R) HΔ HE W

/-- A beta-only native argument joined to the source annotation instantiates
expanded union recovery, retaining a joined dependent result type. -/
theorem erased_expansion_union_native_joined_inst
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (A :: Δ) e B)
    (HΔ : PureContext Δ) (HA : PureLambda A) (HE : PureLambda e)
    (RP : ScopedTypeRecovery (fun _ _ _ => False) Δ p T) (HT : BetaLevelJoin T A) :
    ∃ B', ScopedTypeRecovery (fun _ _ _ => False) Δ (e.inst p) B' ∧ BetaLevelJoin B' (B.inst p) := by
  simpa only [inst_eq_subst, Subst.liftN] using
    erased_expansion_union_native_joined_subst R (HΔ.cons HA) HE (JoinedNativeImages.inst RP HT)

end Lean4Lean.VEnv.Strengthening
