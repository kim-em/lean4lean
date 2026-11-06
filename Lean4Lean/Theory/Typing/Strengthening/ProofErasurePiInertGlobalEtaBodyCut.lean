import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertContinuationFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializationFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaBodyCut

/-! # Eq exposure reaches a non-level root inside a minimum eta body

Minimize over all finite stages, read every outer singleton directly, and
bypass administrative and proof-argument eta cases. The retained native eta
must itself contain a non-level cut on its original constant-headed body.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
open private singleton_spine_readout
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaBodyCut
variable [Params]

/-- The original lower equation holds, or an original-prefix eta of arity at
most four contains a non-level body-spine cut. The whole path has minimum
primitive count among all finite stages; every prefix and suffix is retained.
The outer and body decompositions have exact costs, and the body path is
globally minimal with smaller count (via `CountedEtaBodySpineCut.smaller_minimum`).
The body and its application continuation are jointly minimal with variable
body endpoint; identity and constant expansion are excluded at the selected
inner root, with its typing and the actual argument's context substitution retained.
Both singleton forms read the original lower equation. The remaining inner
root is native function eta. Eliminating this nested eta through the retained
application continuation remains open. `CountedEtaBodySpineCut.nested_eta_cut`
supplies a smaller body/continuation minimum in both the consumed and retained
lambda cases. `CountedEtaBodySpineCut.nested_eta_frames` retains concrete typed
application and annotated lambda frames ending at this same original output.
For a retained component-only body, `pi_inert_native_retained_eta_later_body_cut`
extracts a smaller body/suffix minimum from the actual later path to an exposed
output. If the short function remains constant-headed, that body has a typed
non-level root. `CountedLaterEtaBodyCut.eq_guarded` classifies the later short
Eq root as singleton or native eta while retaining the same cut.
`CountedLaterEtaBodyCut.read_singleton` reads both singleton guards through a
retained source-to-target Eq specialization, leaving the same native eta cut.
Its `read_singleton_of_origin` variant obtains the later Pi assignment from
the retained typed eta origin, without requiring renewed native recovery.
Supplying that specialization throughout arbitrary mixed frames and eliminating
the remaining eta recursively remain open. `EqPrefixSpecializationAt.compute_inst` transports a retained
specialization through the two endpoint histories when the actual argument's
agreement with the chosen target binder image has been established.
`EqPrefixSpecializationAt.eta_compute_inst` derives that agreement when the
prefix and its next actual argument share the retained target completion.
`EqPrefixSpecializationAt.eta_compute_spine_inst` also retains the independently
computed remaining source arguments, the whole spine's assigned type and exact
erasure. `compute_annotation` preserves the chosen specialization across a
computed retained annotation. `CountedLaterEtaBodyCut.eq_or_eta_of_completion`
then derives short-prefix inputs from that whole completion and reads its
singleton cases. `EqSpecializationFrame` records actual endpoint substitution
and semantic agreement of the target assignments. Its witnesses compose, lift
under retained binders and arise from context conversion or computed argument
supply (`eta_supply_frame`). `eq_or_eta_after_frame` reads the later cut after
such a composed frame. Deriving agreeing frames throughout the actual arbitrary
mixed continuation, and closing the remaining eta recursion, are still open. -/
theorem pi_inert_eq_exposure_eq_or_global_eta_spine_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (Eargs : args = (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    env.IsDefEq univs Γ a b α ∨
    (∃ stage cost ls pre pending A B u k cp ct,
      ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out ∧
      (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out → cost ≤ j) ∧
      cp+1+ct = cost ∧ List.Forall₂ (· ≈ ·) [v,w] ls ∧ pre.length ≤ 4 ∧
      List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedComputeCount (PiInertStage D stage) cp (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      k < stage ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B) ∧
      DomainSort (proofEraseCtx Γ') A u ∧
      ScopedComputeCount (PiInertStage D stage) ct (proofEraseCtx Γ')
        (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1)
          (etaArgument u))) pending) out ∧
      CountedEtaBodySpineCut D stage (proofEraseCtx Γ') ``Eq.rec ls pre A u pending out ct
        (EqEtaRemainingRoot D)) := by
  classical
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eargs' : args = [(proofErase Γ α).liftN count offset,
      (proofErase Γ a).liftN count offset, (proofErase Γ M).liftN count offset,
      (proofErase Γ m).liftN count offset, (proofErase Γ b).liftN count offset, .proof] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using Eargs
  obtain ⟨initialCost, RC₀⟩ := R.count
  obtain ⟨stage, cost, RC, hminAll⟩ := RC₀.minimal_across_stages
  have hmin := hminAll stage
  rcases RC.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args', EO, _, _⟩ | ⟨ls, pre, pending, target, cp, ct, hcost, HL, HA, RP, H, HN, RT⟩
  · exact ((carrier_exposure_ne_eqRec heq HE) (by rw [EO, constHead_mkApps]; rfl)).elim
  · have hcostExact : cp+1+ct = cost := by
      have RT' := ((ScopedComputeCount.base H).mkApps ScopedArgumentsCount.refl).trans RT
      rw [← ProofShape.mkApps_append] at RT'
      have HM := hmin (cp+1+ct) (by
        simpa only [Nat.add_zero, ← Nat.add_assoc] using RP.trans RT')
      omega
    have HA6 := Eargs' ▸ HA
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D stage) (ErasedStaticStructureEtaExpansionStage D stage) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage
    by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target
    · have HG := HQ.spine_component_guard (HA6.imp (fun _ _ R => R.mono pi_inert_stage_embed))
      have HGl := proofErase_computed_joint_carrier_certificate_descend hd hΓ hΓ' W ha hb HG
      exact .inl (proofErase_computed_joint_carrier_reflect hd.descent hΓ ha hb HGl)
    · have HC : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
        rintro (HC | HC)
        · exact pi_inert_eq_prefix_no_core_root hreg hoff hRec HA6 HC
        · exact HN HC
      have hp : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs stage)
      have HTsrc : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
        obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HT
        exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
      have HS := HT.compute hp RP.forget
      rw [ProofShape.mkApps_append] at HS
      have HTpre := RP.forget.spine_cut_source_typed hp HTsrc
      have hbypass : ∀ {Recovery},
          (ConstantExpansion (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∨
           NativeIdentityExpansion Recovery (proofEraseCtx Γ')
             (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) → False := by
        intro Recovery HX
        obtain ⟨j, hj, RB⟩ := pi_inert_expansion_prefix_count_bypass heq hs HTpre HX RT HE
        have HM := hmin _ (RP.trans (by simpa only [ProofShape.mkApps_append] using RB))
        omega
      rcases static_other_spine_root H.1 HC HQ
          (fun H => HS.no_masked_structure_spine hd.descent H) with HC | ⟨k, hk, HG | HI | Heta⟩
      · exact (hbypass (Recovery := ErasedStaticStructureEtaExpansionStage D stage) (.inl HC)).elim
      · exact .inl (singleton_spine_readout heq hs hΓ hΓ' W ht hn Eargs HL HA HG)
      · exact (hbypass (.inr HI)).elim
      · have HTwhole : TypedSource (proofEraseCtx Γ')
            (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending) := by
          obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HS
          exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
        have hnotProof : ∀ rest, pending ≠ .proof :: rest := by
          intro rest EP
          obtain ⟨j, hj, RB⟩ := pi_inert_proof_eta_spine_count_eliminate heq hs
            (erased_static_structure_eta_expansion_stage_descent heq hs k)
            (EP ▸ HTwhole) Heta (EP ▸ RT) HE
          have HM := hmin _ (RP.trans (by simpa only [EP, ProofShape.mkApps_append] using RB))
          omega
        cases Heta with
        | intro RN SD =>
          have HB := globally_minimal_pi_inert_eta_body_spine_cut heq hs
            (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RN SD
            (by simpa only [ProofShape.mkApps_append] using RP) H RT hcost hminAll HE
          have hpending : 0 < pending.length := by
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, RX, _⟩ := HB
            cases RX with | cons => simp
          have hlength := HA.length_eq
          rw [Eargs'] at hlength
          simp only [List.length_cons, List.length_nil, List.length_append] at hlength
          have hshort : pre.length ≤ 4 := by
            by_contra hlong
            have hfive : pre.length = 5 := by omega
            have Hdrop : (pre ++ pending).drop 5 = pending := by
              rw [← hfive, List.drop_left]
            have HD : List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ'))
                [.proof] pending := by
              simpa only [List.drop_succ_cons, List.drop_zero, Hdrop] using
                Lean4Lean.List.forall₂_drop HA6 5
            cases HD with | cons HP HD =>
              cases HD
              exact hnotProof [] (by rw [HP.pi_inert_proof_fixed])
          rcases CountedEtaBodySpineCut.read_singleton heq hs hΓ hΓ' W ht hn HL
              (by simpa only [Eargs] using HA) hshort HTpre RN SD
              (HB.eq_guarded heq hs hreg hoff hRec hshort) with Hlower | HB'
          · exact .inl Hlower
          · exact .inr ⟨stage, cost, ls, pre, pending, _, _, _, k, cp, ct,
              RC, hminAll, hcostExact, HL, hshort, HA, RP, HTpre, hk, RN, SD, RT, HB'⟩

end Lean4Lean.VEnv.Strengthening
