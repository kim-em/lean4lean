import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqFamilyReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalSpineCut

/-! # Remove complete singleton guards from a minimum-count probe cut

When the five-argument prefix originates below the block, recovered-family
readout removes the complete singleton alternative even after component and
universe computation. Only shorter singleton prefixes and function eta remain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

private theorem singleton_const_levels_wf
    (H : SingletonPrimitiveWith Cmp Δ (ProofShape.mkApps (.const c ls) args) out) :
    ∀ l ∈ ls, l.WF univs := by
  generalize ES : ProofShape.mkApps (.const c ls) args = source at H
  cases H with
  | intro V _ _ _ =>
    obtain ⟨_, HL, _⟩ := ProofShape.const_spine_inj ES
    exact HL.symm ▸ V.levels_wf

/-- With a typed lower five-argument probe prefix, minimum-count exposure
forces lower endpoint equality or an original-spine cut at a singleton with
fewer than five arguments or a native function eta. All component origins,
source typing and both computation segments are retained. Shorter singleton
guards and function eta are still unresolved; no sufficiency claim is made. -/
theorem pi_inert_eq_exposure_eq_or_short_guarded_cut
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
    (∃ ls pre pending target,
      List.Forall₂ (· ≈ ·) [v,w] ls ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      PiInertStage D n (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
      (∃ k, k < n ∧
        ((pre.length < 5 ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k)
          (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) ∨
         NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k)
          (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target)) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ') (ProofShape.mkApps target pending) out) := by
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eargs' : args = [(proofErase Γ α).liftN count offset,
      (proofErase Γ a).liftN count offset, (proofErase Γ M).liftN count offset,
      (proofErase Γ m).liftN count offset, (proofErase Γ b).liftN count offset, .proof] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using Eargs
  rcases pi_inert_eq_exposure_readout_or_guarded_spine_cut heq hs hreg hoff hRec
      hΓ hΓ' W ha hb Eargs' HT R HE with HH |
      ⟨ls, pre, pending, target, HL, HA, RP, HP, HS, ⟨k, hk, HG⟩, RT⟩
  · exact .inl HH.2
  · rcases HG with HG | HG
    · have hlen := HG.2.eq_rec_arity_le heq
      by_cases hfive : pre.length = 5
      · have HA5 := Lean4Lean.List.forall₂_take HA 5
        rw [Eargs, ← hfive, List.take_left] at HA5
        rw [hfive] at HA5
        have HA5 : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
            (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) pre := by
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
            exact .inl (proofErase_recovered_singleton_eq_computed_five_descend heq
              (erased_static_structure_eta_expansion_stage_descent heq hs n)
              (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
              hΓ hΓ' W ht hn (HA5.imp (fun _ _ R => R.mono pi_inert_stage_embed)) RL HG)
      · exact .inr ⟨ls, pre, pending, target, HL, HA, RP, HP, HS,
          ⟨k, hk, .inl ⟨by omega, HG⟩⟩, RT⟩
    · exact .inr ⟨ls, pre, pending, target, HL, HA, RP, HP, HS, ⟨k, hk, .inr HG⟩, RT⟩

end Lean4Lean.VEnv.Strengthening
