import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrimitiveCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbeExpansionBarrier

/-! # A typed guarded occurrence is necessary to expose an Eq carrier

The first primitive outside core plus controlled beta expansion has a strictly
earlier guard stage. The complete prefix, actual occurrence context and suffix
are retained. This does not assert that the occurrence's indices are descendants
of the original probe indices; establishing that ancestry is still necessary
before using the cut to descend an original proposition equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Outside core and the two controlled beta expansions, a finite full-stage
root is one of the four remaining guarded families at a strictly earlier stage.
The recovery bound of the excluded fragment can be larger than the root stage. -/
theorem static_stage_outside_core_expansion
    (hn : n ≤ bound)
    (H : ErasedStaticStructureEtaExpansionStage D n Δ a b)
    (HN : ¬ ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D bound) Δ a b) :
    ∃ k, k < n ∧
      (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ a b) := by
  induction n with
  | zero =>
    rcases H with H | H
    · exact (HN (.inl H)).elim
    · exact (HN (.inr (.inl H))).elim
  | succ n ih =>
    rcases H with H | H | H | H | H | H
    · obtain ⟨k, hk, H⟩ := ih (by omega) H
      exact ⟨k, by omega, H⟩
    · exact ⟨n, by omega, .inl H⟩
    · exact ⟨n, by omega, .inr (.inl H)⟩
    · exact (HN (.inr (.inr (H.mono
        (fun R => erased_static_structure_eta_expansion_stage_mono (show n ≤ bound by omega) R))))).elim
    · exact ⟨n, by omega, .inr (.inr (.inl H))⟩
    · exact ⟨n, by omega, .inr (.inr (.inr H))⟩

/-- Exposing a type-valued Eq recursor requires an actual typed nontransparent
primitive occurrence. Everything before it can be chosen in the core/constant/
native-identity fragment, and the full original suffix still reaches the same
exposed carrier. Its singleton, Eq-prefix or eta guard has strictly lower stage.
The hole can lie inside an argument or binder; no head-ancestry claim is made. -/
theorem pi_inert_eq_rec_exposure_guarded_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) out) (HE : CarrierExposure out) :
    ∃ Θ left right, ∃ C : ScopedHole (proofEraseCtx Γ) Θ,
      ∃ k, k < n ∧
        ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
          (proofErase Γ (eqRecApp v w α a M m b p)) (C.plug left) ∧
        ScopedCompute (ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n))
          (proofEraseCtx Γ) (proofErase Γ (eqRecApp v w α a M m b p)) (C.plug left) ∧
        TypedSource Θ left ∧ PiInertStage D n Θ left right ∧
        ¬ ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n) Θ left right ∧
        (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Θ left right ∨
         ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D k) Θ left right ∨
         NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ left right ∨
         NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ left right) ∧
        ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (C.plug right) out := by
  have hr : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D n) :=
    erased_static_structure_eta_expansion_stage_descent heq hs n
  have hTarget : ErasedScopedPrimitiveDescent (fun Δ a b => PiInertStage D n Δ a b ∧
      ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n) Δ a b) := by
    intro Γ Γ' count offset e T out hΓ hΓ' W ht R
    exact erased_level_core_expansion_descent hs hr hΓ hΓ' W ht R.2
  rcases R.typed_fragment_or_cut
    (Target := fun Δ a b => PiInertStage D n Δ a b ∧
      ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n) Δ a b)
    hTarget ⟨Γ, _, _, hΓ, rfl, ht, rfl⟩ with
    RP | ⟨Θ, left, right, C, RP, HT, H, HN, RT⟩
  · exact (eq_rec_core_expansion_no_carrier_exposure heq hs hl hcon hc hr
      hreg hoff hRec hRigid hΓ ht (RP.mono (fun H => H.2)) HE).elim
  · have HN' : ¬ ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n)
        Θ left right := fun Hmixed => HN ⟨H, Hmixed⟩
    obtain ⟨k, hk, HG⟩ := static_stage_outside_core_expansion (Nat.le_refl n) H.1 HN'
    exact ⟨Θ, left, right, C, k, hk, RP.mono (fun H => H.1), RP.mono (fun H => H.2),
      HT, H, HN', HG, RT⟩

end Lean4Lean.VEnv.Strengthening
