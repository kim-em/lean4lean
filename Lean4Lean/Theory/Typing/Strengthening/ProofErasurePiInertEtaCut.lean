import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalSpineCut

/-! # Only native function eta remains at a guarded Eq exposure cut

Fresh completion reads any general singleton prefix, including all shorter
arities. A typed lower five-argument origin therefore leaves only native
function eta after the minimum-count original-spine cut.
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
forces lower endpoint equality or an earlier native function-eta root on the
original spine. All component origins, source typing and both computation
segments are retained. The eta case is unresolved; this is not yet a smaller
sufficient obligation for PropositionFront. -/
theorem pi_inert_eq_exposure_eq_or_native_eta_cut
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
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k)
          (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) ∧
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
      have HA5 := Lean4Lean.List.forall₂_take HA 5
      rw [Eargs] at HA5
      have HA5 : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
          (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset))
          ((pre ++ pending).take 5) := by
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
          exact .inl (proofErase_recovered_singleton_eq_computed_prefix_descend heq
            (erased_static_structure_eta_expansion_stage_descent heq hs n)
            (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
            hΓ hΓ' W ht hn (HA5.imp (fun _ _ R => R.mono pi_inert_stage_embed)) RL (HP.symm ▸ HG))
    · exact .inr ⟨ls, pre, pending, target, HL, HA, RP, HP, HS, ⟨k, hk, HG⟩, RT⟩

end Lean4Lean.VEnv.Strengthening
