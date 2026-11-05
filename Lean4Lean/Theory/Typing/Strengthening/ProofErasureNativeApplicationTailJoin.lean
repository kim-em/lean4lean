import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroNativeCoherence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeControlResultTypes

/-! # Joining selected application types through arbitrary base conversion tails

Core joining of selected Pis gives a codomain join at a shared argument. Both
original argument computations and final native conversion tails may differ.
Actual selected result-type representatives justify each composition of joins.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- A level-core join of Pis retains a join of their codomains after the same
raw argument is substituted, independently of their written domains. -/
theorem level_core_pi_inst_join
    (H : ComputeJoin (ErasedLevelCore D) (.forallE A B) (.forallE C E)) :
    ComputeJoin (ErasedLevelCore D) (B.inst p) (E.inst p) := by
  obtain ⟨shared, HL, HR⟩ := H
  obtain ⟨X, Y, rfl, _, HB⟩ := HL.pi_parts (fun H => erased_level_core_no_pi H)
  obtain ⟨X', Y', H, _, HE⟩ := HR.pi_parts (fun H => erased_level_core_no_pi H)
  cases H
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
    (ComputeJoin.subst (fun H => erased_level_core_subst H)
      (σ := ProofShape.Subst.one p) ⟨Y, HB, HE⟩)

/-- A natively selected Pi codomain instantiated at an actual argument is the
exact erasure of a typed type. This remains true when the application is a proof
and therefore its whole-term erasure would hide the application syntax. -/
theorem stage_zero_native_result_type_realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T)) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y)) :
    ∃ P v, env.HasType univs Γ P (.sort v) ∧ proofErase Γ P = Y.inst (proofErase Γ p) := by
  obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ hf RF
  obtain ⟨A, B, rfl, _, _, EB⟩ := erase_forallE_inv EP
  obtain ⟨⟨u, hA⟩, v, hB⟩ := (hfP.isType henv hΓ).forallE_inv henv
  have hpA := argument_at_displayed_domain hΓ hf hfP hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  refine ⟨B.inst p, v, ?_, ?_⟩
  · exact hB.instN henv.ordered Ctx.InstN.zero hpA
  · rw [proofErase_instN hΓA hpA Ctx.InstN.zero hB, EB]

/-- A core join of selected Pis and a common typed argument reduct suffice to
join independently converted application result types. Final tails are arbitrary
stage-zero computations; no forward transport of an arbitrary check is assumed. -/
theorem stage_zero_native_application_tails_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HJ : ComputeJoin (ErasedLevelCore D) (.forallE X Y) (.forallE Z W))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ p))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (Y.inst (proofErase Γ x)) outL)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (W.inst (proofErase Γ y)) outR) :
    ComputeJoin (ErasedLevelCore D) outL outR := by
  have hcl : TypedCoreConfluence (ErasedLevelCore D) := proofErase_level_core_confluent hs hl hcon hc
  obtain ⟨L, uL, hL, EL⟩ := stage_zero_native_result_type_realize heq hs hΓ hf hx RF
  obtain ⟨R, uR, hR, ER⟩ := stage_zero_native_result_type_realize heq hs hΓ hg hy RG
  obtain ⟨LP, uLP, hLP, ELP⟩ := stage_zero_native_result_type_realize heq hs hΓ hf hp RF
  obtain ⟨RP, uRP, hRP, ERP⟩ := stage_zero_native_result_type_realize heq hs hΓ hg hp RG
  have LX := stage_zero_native_result_argument_compute heq hs hΓ hf hx RF RX
  have RY' := stage_zero_native_result_argument_compute heq hs hΓ hg hy RG RY
  have JL := stage_zero_compute_level_join heq hs hl hcon hc hΓ hL (EL ▸ LX)
  have JR := stage_zero_compute_level_join heq hs hl hcon hc hΓ hR (ER ▸ RY')
  have JP := level_core_pi_inst_join (p := proofErase Γ p) HJ
  have JL' := stage_zero_compute_level_join heq hs hl hcon hc hΓ hL (EL ▸ RL)
  have JR' := stage_zero_compute_level_join heq hs hl hcon hc hΓ hR (ER ▸ RR)
  rw [← ELP] at JL JP
  rw [← ERP] at JP JR
  exact ((JL'.symm.trans_typed hcl hΓ hL JL).trans_typed hcl hΓ hLP JP).trans_typed
    hcl hΓ hRP (JR.symm.trans_typed hcl hΓ hR JR')

/-- Two complete native recoveries of applications of the same actual function
join when their arguments compute to a shared typed argument. The recovered Pis,
result types and final conversion tails may all differ independently. -/
theorem stage_zero_same_function_native_application_outputs_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C) (hp : env.HasType univs Γ p C)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ p))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f y)) outR) :
    ComputeJoin (ErasedLevelCore D) outL outR := by
  have hnL : ¬ IsProof Γ (.app f x) := fun H => RL.ne_proof (proofErase_eq_proof.2 H)
  have hnR : ¬ IsProof Γ (.app f y) := fun H => RR.ne_proof (proofErase_eq_proof.2 H)
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hnL] at RL
  rw [show proofErase Γ (.app f y) = .app _ _ from if_neg hnR] at RR
  obtain ⟨X, Y, RF, RL⟩ := RL.app_origin
  obtain ⟨Z, W, RG, RR⟩ := RR.app_origin
  have HJ := stage_zero_native_outputs_join heq hs hl hcon hD hc hΓ hf RF RG
  exact stage_zero_native_application_tails_join heq hs hl hcon hc hΓ hf hf hx hy hp RF RG HJ RX RY RL RR

end Lean4Lean.VEnv.Strengthening
