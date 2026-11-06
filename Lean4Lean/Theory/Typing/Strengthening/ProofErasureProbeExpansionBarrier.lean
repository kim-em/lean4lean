import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionReadoutBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe

/-! # Controlled beta expansion cannot expose a proof-major Eq carrier

A changed literal head is not enough: constant expansion changes it for free.
An exposed structural carrier is stronger. Core confluence removes arbitrary
interleaved constant and native identity expansions, and ordinary Eq-spine
inversion then excludes structural exposure, independently of index equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params] {D : Definitions}

/-- Structural checking shapes persist under level-core computation. The
non-unfolding premise protects every registered structure family. -/
theorem ProofShape.CarrierExposure.level_core_compute
    (heq : env.HasCanonicalEq)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : CarrierExposure A) (R : Compute (ErasedLevelCore D) A B) : CarrierExposure B := by
  cases H with
  | record hi hx hp =>
    rename_i family info ls ps
    have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) family := by
      intro Δ ls args out H
      exact erased_level_recovered_stage_spine_levels heq (henv.projectionRigid hi)
        (hRigid (henv.projectionRigid hi)) 0 (Δ := Δ) H
    obtain ⟨ls', ps', rfl, _, Hps⟩ := (R.scoped (Δ := []) (fun H => .base H)).const_spine_levels @hroot
    exact .record hi hx (Hps.length_eq.symm.trans hp)
  | function =>
    obtain ⟨A', B', rfl, _, _⟩ := R.pi_parts (fun H => erased_level_core_no_pi H)
    exact .function

/-- A type-valued Eq recursor cannot join an exposed structural carrier in
the level core. Its erased major stays a proof marker, so ordinary reduction
retains Eq.rec even when the indices are definitionally equal. -/
theorem eq_rec_no_level_core_carrier_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u))
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ (eqRecApp v w α a M m b p)) out) :
    ¬ CarrierExposure out := by
  intro HE
  obtain ⟨shared, RL, RR⟩ := HJ
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht RL
  have HM := HE.level_core_compute heq hRigid (RR.trans RT)
  obtain ⟨_, hw, hα, ha, _, _, hb, hp⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have Ep : proofErase Γ p = .proof := proofErase_eq_proof.2
    ⟨_, hp, HasType.eqApp heq hw hα ha hb⟩
  have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht
    (not_isProof_of_sort hΓ ht)
  change proofErase Γ (eqRecApp v w α a M m b p) = _ at ES
  simp only [List.map_cons, List.map_nil, Ep] at ES
  rw [ES] at RM
  obtain ⟨α', a', M', m', b', rfl, _⟩ := RM.eqRec_proof_core_inv hreg hoff hRec
  exact carrier_exposure_ne_eqRec heq HM rfl

/-- Arbitrarily many controlled beta expansions, with arbitrary descending
native recovery guards, cannot expose a type-valued Eq recursor. This excludes
a whole computation fragment, not just the first visible head change. -/
theorem eq_rec_core_expansion_no_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u))
    (R : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) out) : ¬ CarrierExposure out :=
  eq_rec_no_level_core_carrier_join heq hs hl hcon hreg hoff hRec hRigid hΓ ht
    (proofErase_level_core_expansion_join hs hl hcon hc hr hΓ ht R)

/-- Even the unrestricted expanded stage zero cannot expose the carrier of a
type-valued Eq recursor. Universe changes and constant wrappers are included. -/
theorem eq_rec_stage_zero_no_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) out) : ¬ CarrierExposure out := by
  apply eq_rec_core_expansion_no_carrier_exposure
    (Recovery := fun _ => ErasedLevelCore D) heq hs hl hcon hc
    (fun hΓ hΓ' W ht R => erased_level_core_descent hs hΓ hΓ' W ht R)
    hreg hoff hRec hRigid hΓ ht
  exact R.mono (fun H => by
    rcases H with H | H
    · exact .inl H
    · exact .inr (.inl H))

/-- At stage zero a type-valued Eq carrier cannot justify comparison of
distinct variables, including via any sequence of carrier/endpoint reductions. -/
theorem eq_rec_pi_inert_zero_guard_bvar_injective
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u))
    (H : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (.bvar i) (.bvar j)) : i = j := by
  rcases H.checked_or_exposed with H | ⟨C, R, HE, _⟩
  · exact H.pi_inert_bvar_injective
  · exact (eq_rec_stage_zero_no_carrier_exposure heq hs hl hcon hc hreg hoff hRec hRigid
      hΓ ht (R.mono (fun H => H.1)) HE).elim

end Lean4Lean.VEnv.Strengthening
