import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqPrefixCompletion

/-! # Read lower indices from any computed recovered singleton prefix

Reconstruct the complete typed five-argument source, descend the selected
partial-prefix root, and use fresh completion to read its original indices.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem nonproof_spine_head
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps f args)) : ¬ IsProof Γ f := by
  induction args using List.snoc_induction generalizing T with
  | nil => exact hn
  | snoc args a ih =>
    rw [VExpr.mkApps_snoc] at ht hn
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact ih hf (not_isProof_fn hΓ hf ha hn)

/-- A singleton at any lifted prefix of a typed lower five-argument Eq term
forces its original lower endpoint equation. The selected root descends before
its missing arguments are supplied. -/
theorem proofErase_recovered_singleton_eq_prefix_descend
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (Eargs : pre ++ pending = [α,a,M,m,b])
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w])
        ((pre.map (proofErase Γ)).map (·.liftN count offset))) out) :
    env.IsDefEq univs Γ a b α := by
  have hall : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) pending) T := by
    rw [← VExpr.mkApps_append, Eargs]; exact ht
  have hnall : ¬ IsProof Γ (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) pending) := by
    rw [← VExpr.mkApps_append, Eargs]; exact hn
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, hall⟩
  have Ep := proofErase_const_spine hΓ hp (nonproof_spine_head hΓ hall hnall)
  have H' : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre)).liftN count offset) out := by
    rw [Ep, ProofShape.liftN_mkApps]; exact H
  obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep hΓ hΓ' W hp H'
  rw [Ep] at HL
  exact proofErase_recovered_singleton_eq_prefix_reflect heq hstep.descent hΓ ht Eargs HL.2

/-- All component paths of a typed lower Eq prefix suffice to read the lower
endpoint equation from a recovered singleton at any computed initial segment.
The carrier, indices, motive, minor and universe head may all compute. -/
theorem proofErase_recovered_singleton_eq_computed_prefix_descend
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
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (args.take arity)) out) :
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
            have H' : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
                (ProofShape.mkApps (.const ``Eq.rec [v',w'])
                  ((([α',a',M',m',b'].take arity).map (proofErase Γ)).map (·.liftN count offset))) out := by
              simpa only [List.map_take, List.map_cons, List.map_nil, Eα', Ea', EM', Em', Eb',
                Eα, Ea, EM, Em, Eb] using H
            have HL := proofErase_recovered_singleton_eq_prefix_descend heq hstep hΓ hΓ' W
              HE.hasType.2 (fun hp => hn ((isProof_congr hΓ HE).2 hp))
              (List.take_append_drop arity [α',a',M',m',b']) H'
            exact ((HA.trans henv hΓ HL.toU).trans henv hΓ HB.symm).of_l henv hΓ ha

end Lean4Lean.VEnv.Strengthening
