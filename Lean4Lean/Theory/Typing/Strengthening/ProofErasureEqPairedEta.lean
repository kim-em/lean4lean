import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmbeddedCompletion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqDelayedSupply

/-! # Keep a chosen supply frame through nested eta opening

Nested eta uses the same next target argument on both sides of an already
linked actual frame. Its domain may depend on the binder consumed by that
frame. The target typing of the new image is derived from the completion,
so no new argument-image agreement or domain independence is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Opening another eta binder preserves a chosen actual supply frame.
The completion itself types the next target image; the same image extends
both target assignments. The outgoing domain is the actual substituted
incoming domain, including any dependence on consumed older variables. -/
theorem EqPrefixSpecializationAt.eta_frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B)) :
    EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
      (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
    EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
      (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
    EqPrefixSpecializationAt (A.subst ρ :: Γ') Δ v w v' w' original
      ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (·.subst ρ.lift)) (σ'.cons y) rest ∧
    env.HasType univs (A.subst ρ :: Γ')
      (VExpr.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (·.subst ρ.lift))) (B.subst ρ.lift) ∧
    (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (·.subst ρ.lift)).map
      (proofErase (A.subst ρ :: Γ'))) =
      ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map (·.subst τ.lift) := by
  have Hfresh := H.eta hΔ ht hA hf
  have hy : env.HasType univs Δ y (A.subst σ) := by
    have HS := Hfresh.1
    cases HS with
    | cons _ _ hy => exact hy.hasType.1
  have Wfresh := W.under_binder hΔ hA hy
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    have Hbody := hfw.app (HasType.bvar (Lookup.zero (ty := A)))
    simpa only [VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN, VExpr.mkApps_append,
      VExpr.mkApps_cons, VExpr.mkApps_nil, VExpr.inst_liftN_bvar] using Hbody
  obtain ⟨Hout, htout, Eout⟩ := Hfresh.frame hΔ Wfresh hb
  exact ⟨Hfresh, Wfresh, Hout, htout, Eout⟩

/-- A chosen specialization at an actual non-proof prefix yields the existing
constructed-embedding invariant in that exact scope. No fresh target witness
is selected; the stored assignment is used in the base completion. -/
theorem EqPrefixSpecializationAt.embedding
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :
    EqTargetPrefixEmbedding Δ v w original (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) := by
  apply EqTargetPrefixCompletion.embedding
  apply EqTargetPrefixCompletion.of_completion
  apply IteratedAmbientEqCompletion.base
  refine ⟨Γ, Γ, 0, 0, v', w', pre, F, H.1.wf, H.1.wf, Ctx.LiftN.zero [], rfl,
    hf, hn, H.forget, ?_⟩
  simpa only [ProofShape.liftN_zero] using proofErase_const_spine H.1.wf hf hn

/-- The paired invariant gives completion after its actual frame at the exact
raw substituted spine. The raw map is retained, and non-proof status after
substitution follows from the source erasure rather than being assumed. -/
theorem EqPrefixSpecializationAt.embedding_after_frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :
    EqTargetPrefixEmbedding Δ v w original (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map (·.subst τ))) := by
  obtain ⟨Hout, hfout, Eout⟩ := H.frame hΔ W hf
  have hnout : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ))) := by
    intro hp
    apply hn ((isProof_subst W.target.wf W.actual hf).1 ?_)
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  simpa only [Eout] using Hout.embedding hfout hnout

/-- Open a dependent eta binder and compute its actual body components before
following the old frame beneath that binder. Both chosen specializations survive,
as does the same paired frame. The existing embedding invariant is recovered at
the exact substituted raw endpoint. Only components are computed here: a new
non-level head cut still needs the recursive minimum-descent argument. -/
theorem EqPrefixSpecializationAt.eta_compute_frame
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx (A :: Γ)))
      ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))) raw) :
    ∃ pre' : List VExpr,
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v'' w'' original pre' (σ.cons y) rest ∧
      EqPrefixSpecializationAt (A.subst ρ :: Γ') Δ v w v'' w'' original
        (pre'.map (·.subst ρ.lift)) (σ'.cons y) rest ∧
      env.HasType univs (A.subst ρ :: Γ')
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ.lift))) (B.subst ρ.lift) ∧
      pre'.map (proofErase (A :: Γ)) = raw ∧
      (pre'.map (·.subst ρ.lift)).map (proofErase (A.subst ρ :: Γ')) = raw.map (·.subst τ.lift) ∧
      EqTargetPrefixEmbedding Δ v w original (proofEraseCtx (A.subst ρ :: Γ'))
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.subst τ.lift))) := by
  obtain ⟨Hfresh, Wfresh, _, _, _⟩ := H.eta_frame hΔ W ht hA hf
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have EE : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body H.1.wf hA hf hn
  rw [← EE] at EB
  have hnb : ¬ IsProof (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  obtain ⟨pre', HP, EP, HE⟩ := Hfresh.compute hstep Hfresh.1.wf Hfresh.1.wf
    (Ctx.LiftN.zero []) hΔ hb HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using HA)
  have EP' : pre'.map (proofErase (A :: Γ)) = raw := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP
  have hn' : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') := by
    intro hp
    exact hnb ((isProof_congr Hfresh.1.wf HE).2 hp)
  obtain ⟨Hout, htout, Eout⟩ := HP.frame hΔ Wfresh HE.hasType.2
  refine ⟨pre', Wfresh, HP, Hout, htout, EP', ?_, ?_⟩
  · simpa only [EP'] using Eout
  · simpa only [EP'] using HP.embedding_after_frame hΔ Wfresh HE.hasType.2 hn'

/-- Shared actual supply seeds a linked consumption frame, and a subsequent
eta opening retains that frame beneath its new dependent binder. The outer
argument is reified from its actual computation, not equated with an arbitrary
chosen image. Only the semantic source realization is handled here; carrying
this pair through ambient insertions and the full minimum descent remains open. -/
theorem EqPrefixSpecializationAt.supplied_nested_eta_frame
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (RX : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ x) rawX)
    (Etail : rest.map (·.subst σ) ++ pending = y :: remaining)
    (hC : env.HasType univs (A :: Γ) C (.sort z))
    (hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) (.forallE C E)) :
    ∃ x', env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX ∧
      EqSpecializationFrame (C :: A :: Γ) (C.inst x' :: Γ) Δ
        ((σ.cons (x.subst σ)).cons y) (σ.cons y)
        (VExpr.Subst.one x').lift (ProofShape.Subst.one rawX).lift ∧
      EqPrefixSpecializationAt (C.inst x' :: Γ) Δ v w v' w' original
        (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map VExpr.lift ++ [VExpr.bvar 0]).map
          (·.subst (VExpr.Subst.one x').lift)) (σ.cons y) remaining := by
  obtain ⟨Hfresh, x', HX, EX, W⟩ := H.eta_supply_frame hsource hΔ ht hwhole hA hf RX
  rw [Etail] at Hfresh
  obtain ⟨_, Wfresh, Hout, _, _⟩ := Hfresh.eta_frame hΔ W ht hC hb
  exact ⟨x', HX, EX, by simpa only [VExpr.inst_eq, VExpr.Subst.one] using Wfresh,
    by simpa only [VExpr.inst_eq, VExpr.Subst.one] using Hout⟩

end Lean4Lean.VEnv.Strengthening
