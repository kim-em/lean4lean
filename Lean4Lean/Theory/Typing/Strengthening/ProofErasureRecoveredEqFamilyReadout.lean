import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixGuardReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent

/-! # Descend the generated Eq family before decoding its endpoints

A recovered comparison may expand Eq heads. Instead of inverting that raw
comparison, remove the fresh proof major using its typed family endpoints and
then apply semantic rigid-family injectivity in the lower context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
variable [Params]

/-- A general singleton at five supplied Eq arguments exposes its generated
family comparison for any guard relation. No syntactic Eq-head preservation
is required; the fresh proof-major context is retained exactly. -/
theorem proofErase_singleton_eq_five_family_readout
    (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : SingletonPrimitiveWith Cmp (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b)) out) :
    Cmp (proofEraseCtx (eqApp w α a b :: Γ))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift a.lift))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift b.lift)) := by
  generalize Es : proofErase Γ (eqRecBeforeMajor v w α a M m b) = source at H
  cases H with
  | intro V ha hcalc HG =>
    have hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b) := by
      intro hp
      have E := congrArg constHead (Es.symm.trans (proofErase_eq_proof.2 hp))
      simp only [constHead_mkApps, constHead] at E
      cases E
    have HE := proofErase_const_spine hΓ (args := [α,a,M,m,b]) ht hnp
    obtain ⟨hn, hl, hargs⟩ := ProofShape.const_spine_inj (HE.symm.trans Es)
    rw [← hargs] at hcalc HG
    exact V.eq_five_family_guard heq hn.symm hl.symm hΓ ht hcalc HG

/-- A recovered singleton on an actual five-argument Eq prefix proves equality
of its indices in the same context. The family certificate first descends out
of its generated proof-major binder; rigidity is used only afterwards. This
works for arbitrary carriers and guard computations, including head expansion. -/
theorem proofErase_recovered_singleton_eq_five_reflect
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : SingletonPrimitiveWith (fun Δ => CarrierRecoveredCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ (eqRecBeforeMajor v w α a M m b)) out) :
    env.IsDefEq univs Γ a b α := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hP := HasType.eqApp heq hw hα ha ha
  have hQ := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have HG := proofErase_singleton_eq_five_family_readout heq hΓ ht H
  have HG' : CarrierRecoveredCompare Step (proofEraseCtx (eqApp w α a b :: Γ)) true
      ((proofErase Γ (eqApp w α a a)).liftN 1)
      ((proofErase Γ (eqApp w α a b)).liftN 1) := by
    rw [← proofErase_liftN hΓ hΓE Ctx.LiftN.one hP,
      ← proofErase_liftN hΓ hΓE Ctx.LiftN.one hQ]
    exact HG
  have HF := (proofErase_carrier_recovered_compare_descend hstep hΓ hΓE
    Ctx.LiftN.one rfl hP hQ HG').1 ⟨_, HasType.sort (by trivial)⟩
  change env.IsDefEqU univs Γ (VExpr.mkApps (.const ``Eq [w]) [α,a,a])
    (VExpr.mkApps (.const ``Eq [w]) [α,a,b]) at HF
  obtain ⟨_, HA⟩ := HF.rigidApp_inv henv hΓ (heq.rigid henv) hP
  cases HA with | cons _ HA =>
    cases HA with | cons _ HA =>
      cases HA with | cons hab _ => exact hab.of_l henv hΓ ha

/-- At a source typed below an unused block, an upper recovered singleton
retains a lower singleton root and therefore forces lower endpoint equality.
The exact lower root is reconstructed before its family guard is decoded;
no endpoint certificate completeness is assumed. -/
theorem proofErase_recovered_singleton_eq_five_descend
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      ((proofErase Γ (eqRecBeforeMajor v w α a M m b)).liftN count offset) out) :
    env.IsDefEq univs Γ a b α := by
  obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep
    hΓ hΓ' W ht H
  exact proofErase_recovered_singleton_eq_five_reflect heq hstep.descent hΓ ht HL.2

/-- Arbitrary computation of all five arguments before the selected singleton
still forces equality of the original lower indices. The entire typed lower
prefix is reconstructed first; component paths then relate its indices and
carrier to the original ones. Neither literal-sort preservation nor Eq-head
inertness is assumed. -/
theorem proofErase_recovered_singleton_eq_computed_five_descend
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) args)
    (RL : ScopedCompute Source (proofEraseCtx Γ')
      (.const ``Eq.rec [v,w]) (.const ``Eq.rec [v',w']))
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) args) out) :
    env.IsDefEq univs Γ a b α := by
  simp only [List.map_cons, List.map_nil] at HA
  cases HA with | cons Rα HA =>
    cases HA with | cons Ra HA =>
      cases HA with | cons RM HA =>
        cases HA with | cons Rm HA =>
          cases HA with | cons Rb HA =>
            cases HA
            rename_i rα ra rM rm rb
            have R : ScopedCompute Source (proofEraseCtx Γ')
                ((proofErase Γ (eqRecBeforeMajor v w α a M m b)).liftN count offset)
                (ProofShape.eqRecBeforeMajor v' w' rα ra rM rm rb) := by
              rw [eqRecBeforeMajor, proofErase_const_spine hΓ (args := [α,a,M,m,b]) ht hn]
              simp only [List.map_cons, List.map_nil, ProofShape.mkApps, ProofShape.liftN]
              exact .app (.app (.app (.app (.app RL Rα) Ra) RM) Rm) Rb
            obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ' W ht rfl R
            obtain ⟨αraw, araw, Mraw, mraw, braw, Er, Eα, Ea, EM, Em, Eb⟩ :=
              ProofShape.liftN_eqRecBeforeMajor_inv Ee'
            obtain ⟨α', a', M', m', b', rfl, Eα', Ea', EM', Em', Eb'⟩ :=
              proofErase_eqRecBeforeMajor_inv Er
            obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
            obtain ⟨_, _, hα', ha', _, _, hb'⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, HE.hasType.2⟩
            rw [← Eα, ← Eα'] at Rα
            rw [← Ea, ← Ea'] at Ra
            rw [← Eb, ← Eb'] at Rb
            have HC : env.IsDefEqU univs Γ α α' :=
              (proofErase_joint_compare_descend (mode := false) hsource hΓ hΓ' W rfl hα hα'
                (.compute Rα .refl (.leaf .refl))).2 rfl
                (not_isProof_of_sort hΓ hα) (not_isProof_of_sort hΓ hα')
            have HA : env.IsDefEqU univs Γ a a' :=
              (proofErase_joint_compare_descend (mode := true) hsource hΓ hΓ' W rfl ha ha'
                (.compute Ra .refl (.leaf .refl))).1 HC
            have HB : env.IsDefEqU univs Γ b b' :=
              (proofErase_joint_compare_descend (mode := true) hsource hΓ hΓ' W rfl hb hb'
                (.compute Rb .refl (.leaf .refl))).1 HC
            change CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
              (ProofShape.eqRecBeforeMajor v' w' rα ra rM rm rb) out at H
            have HL := proofErase_recovered_singleton_eq_five_descend heq hstep hΓ hΓ' W
              HE.hasType.2 (Ee'.symm ▸ H)
            exact ((HA.trans henv hΓ HL.toU).trans henv hΓ HB.symm).of_l henv hΓ ha

end Lean4Lean.VEnv.Strengthening
