import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaBodyResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaCut

/-! # Probe exposure forces genuine computation inside an eta body

The minimum-count original-spine cut excludes administrative expansions and
all singleton cases. A surviving eta must consume an argument, and its body
before that beta is not reachable from its original body by beta alone.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
open private singleton_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaCut
variable [Params]

private theorem singleton_spine_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (Eargs : args = (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HL : List.Forall₂ (· ≈ ·) [v,w] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')) args (pre ++ pending))
    (HG : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k)
      (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) :
    env.IsDefEq univs Γ a b α := by
  have hlen := HG.2.eq_rec_arity_le heq
  have HA5 := Lean4Lean.List.forall₂_take HA 5
  rw [Eargs] at HA5
  have HA5 : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) ((pre ++ pending).take 5) := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero] using HA5
  have HW := singleton_const_levels_wf HG.2
  cases HL with | cons Hv HL =>
    cases HL with | cons Hw HL =>
      cases HL
      have RL : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ')
          (.const ``Eq.rec [v,w]) (.const ``Eq.rec [_,_]) :=
        .base (erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n)
          (show ErasedStaticStructureEtaExpansionStage D 0 _ _ _ from .inl (.inr (.const (.cons Hv (.cons Hw .nil)) HW))))
      have HP : ((pre ++ pending).take 5).take pre.length = pre := by
        rw [List.take_take, Nat.min_eq_left hlen, List.take_left]
      exact proofErase_recovered_singleton_eq_computed_prefix_descend heq
        (erased_static_structure_eta_expansion_stage_descent heq hs n)
        (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
        hΓ hΓ' W ht hn (HA5.imp (fun _ _ R => R.mono pi_inert_stage_embed)) RL (HP.symm ▸ HG)

/-- A typed-lower probe exposure gives the original lower equation, or a
proper original-prefix eta whose first consuming beta follows genuine body
computation beyond beta. All original component paths, whole prefix, exact
lambda/argument paths and post-beta tail are retained. The remaining gap is
readout through this non-beta body work; no eta-bypass closure is assumed. -/
theorem pi_inert_eq_exposure_eq_or_nonbeta_eta_body_cut
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
    (∃ ls pre pending A body A' body' x' xs' k cf ca cs,
      List.Forall₂ (· ≈ ·) [v,w] ls ∧ pre.length ≤ 5 ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      k < n ∧ NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.lam A body) ∧
      ScopedComputeCount (PiInertStage D n) cf (proofEraseCtx Γ') (.lam A body) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Γ') ca pending (x' :: xs') ∧
      ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Γ')
        (ProofShape.mkApps (body'.inst x') xs') out ∧
      ¬ ProofShape.BetaRed body body' ∧ 0 < cf) := by
  classical
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eargs' : args = [(proofErase Γ α).liftN count offset,
      (proofErase Γ a).liftN count offset, (proofErase Γ M).liftN count offset,
      (proofErase Γ m).liftN count offset, (proofErase Γ b).liftN count offset, .proof] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using Eargs
  obtain ⟨cost, RC, hmin⟩ := R.minimal_count
  rcases RC.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args', EO, _, _⟩ | ⟨ls, pre, pending, target, cp, ct, hcost, HL, HA, RP, H, HN, RT⟩
  · exact ((carrier_exposure_ne_eqRec heq HE) (by rw [EO, constHead_mkApps]; rfl)).elim
  · have HA6 := Eargs' ▸ HA
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D n) (ErasedStaticStructureEtaExpansionStage D n) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs n
    by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target
    · have HG := HQ.spine_component_guard (HA6.imp (fun _ _ R => R.mono pi_inert_stage_embed))
      have HGl := proofErase_computed_joint_carrier_certificate_descend hd hΓ hΓ' W ha hb HG
      exact .inl (proofErase_computed_joint_carrier_reflect hd.descent hΓ ha hb HGl)
    · have HC : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
        rintro (HC | HC)
        · exact pi_inert_eq_prefix_no_core_root hreg hoff hRec HA6 HC
        · exact HN HC
      have hp : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
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
      · exact (hbypass (Recovery := ErasedStaticStructureEtaExpansionStage D n) (.inl HC)).elim
      · exact .inl (singleton_spine_readout heq hs hΓ hΓ' W ht hn Eargs HL HA HG)
      · exact (hbypass (.inr HI)).elim
      · have HTwhole : TypedSource (proofEraseCtx Γ')
            (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending) := by
          obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HS
          exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
        cases Heta with
        | intro RN SD =>
          obtain ⟨A', body', x', xs', cf, ca, cs, _, RF, RX, RS, Hbody, hpos⟩ :=
            minimal_pi_inert_eta_cut_nonbeta_body heq hs
              (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole
              (.intro RN SD) (by simpa only [ProofShape.mkApps_append] using RP) RT hcost hmin HE
          have hpending : 0 < pending.length := by
            cases RX with | cons => simp
          have hlength := HA.length_eq
          rw [Eargs'] at hlength
          simp only [List.length_cons, List.length_nil, List.length_append] at hlength
          exact .inr ⟨ls, pre, pending, _, _, A', body', x', xs', k, cf, ca, cs,
            HL, by omega, HA, RP.forget, HTpre, hk, .intro RN SD, RF, RX, RS, Hbody, hpos⟩

end Lean4Lean.VEnv.Strengthening
