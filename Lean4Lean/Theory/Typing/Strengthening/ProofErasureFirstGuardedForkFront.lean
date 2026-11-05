import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFullIdentityEtaPeak
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # First guarded beta/eta residuals already test the proposition front

The identity instances below are equivalent to general type-conversion joining,
even though their eta guards use stage zero and their source branches use stage
one. Hence guard depth alone does not reduce the ordinary conversion cost in the
source typing. All sufficiency results here are conditional; none proves joining.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The still-open full residual join for only the explicit identity-beta/eta
peaks of FullIdentityEtaPeak. Arbitrary ordinary conversion enters solely through
the typing of their source. This is not asserted to be a smaller sufficient gap. -/
def FirstIdentityEtaResidualJoin (D : Definitions) : Prop :=
  ∀ {Γ A B u}, OnCtx Γ (env.IsType univs) → env.IsDefEq univs Γ A B (.sort u) →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.lam (proofErase Γ A) (.sort .zero)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (identityEtaTarget Γ A B u) shared

/-- Joining only those identity peaks already joins every ordinary equation
between types. Full residual computation does not weaken this consequence. -/
theorem FirstIdentityEtaResidualJoin.type_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FirstIdentityEtaResidualJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) shared :=
  (identity_eta_full_conversion_peak heq hs hΓ HAB).2.2.2.2.mp (H hΓ HAB)

/-- Exact equivalence with ordinary type-conversion joining. Restricting the
peak syntax and guard depth therefore does not remove that open obligation. -/
theorem first_identity_eta_residual_iff_type_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    FirstIdentityEtaResidualJoin D ↔
      ∀ {Γ A B u}, OnCtx Γ (env.IsType univs) → env.IsDefEq univs Γ A B (.sort u) →
        ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ A) shared ∧
          ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ B) shared := by
  constructor
  · exact fun H => H.type_conversion heq hs
  · intro H Γ A B u hΓ HAB
    exact (identity_eta_full_conversion_peak heq hs hΓ HAB).2.2.2.2.mpr (H hΓ HAB)

/-- The restricted first-guarded identity peak obligation implies proposition
strengthening. Descending its induced domain joins removes the fresh binder;
this is a conditional implication, not a proof of the premise. -/
theorem FirstIdentityEtaResidualJoin.propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FirstIdentityEtaResidualJoin D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  obtain ⟨shared, RP, RR⟩ := H.type_conversion heq hs hΓ' (HE.of_l henv hΓ' hP')
  rw [proofErase_liftN hΓ hΓ' Ctx.LiftN.one hP] at RP
  rw [proofErase_liftN hΓ hΓ' Ctx.LiftN.one hR] at RR
  obtain ⟨P', HP, EP⟩ := proofErase_scoped_compute_descend
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hΓ' Ctx.LiftN.one hP rfl RP
  obtain ⟨R', HR, ER⟩ := proofErase_scoped_compute_descend
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hΓ' Ctx.LiftN.one hR rfl RR
  have EE := ProofShape.liftN_inj.mp (EP.trans ER.symm)
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ HP.hasType.2 HR.hasType.2 EE).1
    (IsDefEqU.refl ⟨_, HasType.sort (l := .zero) (by trivial)⟩)
  exact (HP.trans (((HC.defeq hΓ).of_l henv hΓ HP.hasType.2).trans HR.symm)).toU

/-- A proposed first-stage confluence obligation with unrestricted full-union
residuals. Sources have arbitrary ordinary typings; they are not restricted to
sort-typed sources. The next theorem exposes the conversion cost of that scope. -/
def FirstGuardedTypedForkJoin (D : Definitions) : Prop :=
  ∀ {Γ e T left right}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ e) left →
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ e) right →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared

/-- First-stage typed forks include every explicit identity peak. The beta
branch uses no primitive, and the eta branch uses exactly one first-stage root. -/
theorem FirstGuardedTypedForkJoin.identity_peaks
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FirstGuardedTypedForkJoin D) : FirstIdentityEtaResidualJoin D := by
  intro Γ A B u hΓ HAB
  obtain ⟨ht, RB, RE, _, _⟩ := identity_eta_full_conversion_peak heq hs hΓ HAB
  exact H hΓ ht (.beta RB) (.base (.inr (.inr (.inr (.inr (.inl RE))))))

/-- Even allowing arbitrary guard depth in the residuals, joining all typed
forks at stage one already suffices for the original proposition front. A
stage-only induction must therefore solve this cost in its first guarded case. -/
theorem FirstGuardedTypedForkJoin.propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FirstGuardedTypedForkJoin D) : PropositionFront :=
  FirstIdentityEtaResidualJoin.propositionFront heq hs (H.identity_peaks heq hs)

/-- The actual environment collection discharges the soundness interface.
Only canonical Eq and the explicitly open first-stage joining premise remain. -/
theorem environment_first_guarded_forks_propositionFront
    (heq : env.HasCanonicalEq) (H : FirstGuardedTypedForkJoin EnvironmentCore.definitions) :
    PropositionFront := H.propositionFront heq EnvironmentCore.sound

end Lean4Lean.VEnv.Strengthening
