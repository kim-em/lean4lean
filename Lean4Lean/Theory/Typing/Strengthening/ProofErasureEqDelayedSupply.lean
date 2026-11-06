import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializationFrames

/-! # Preserve a chosen eta supply across a later frame and computation

The incoming binder image remains the original supplied argument's target
specialization. Actual annotation and argument computations in the later scope
produce both the retained binder frame and its matching consumption frame.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An agreeing outer frame, actual annotation computation and actual argument
computation derive the retained and consumed binder frames with the original
chosen image. Their composite retains the exact raw endpoint substitution.
No new equality between the chosen image and computed argument is assumed. -/
theorem EqSpecializationFrame.computed_binder_supply
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (RA : ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' (A.subst ρ)) rawA)
    (RX : ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' (x.subst ρ)) rawX) :
    ∃ A' x', env.IsDefEq univs Γ' (A.subst ρ) A' (.sort u) ∧ proofErase Γ' A' = rawA ∧
      env.IsDefEq univs Γ' (x.subst ρ) x' (A.subst ρ) ∧ proofErase Γ' x' = rawX ∧
      EqSpecializationFrame (A :: Γ) (A' :: Γ') Δ
        (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift ∧
      EqSpecializationFrame (A' :: Γ') Γ' Δ (σ'.cons (x.subst σ)) σ'
        (VExpr.Subst.one x') (ProofShape.Subst.one rawX) ∧
      EqSpecializationFrame (A :: Γ) Γ' Δ (σ.cons (x.subst σ)) σ'
        (ρ.lift.comp (VExpr.Subst.one x')) (τ.lift.comp (ProofShape.Subst.one rawX)) := by
  have hAρ := hA.subst henv.orderedStrong H.actual H.target.wf
  have hxρ := hx.subst henv.orderedStrong H.actual H.target.wf
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep H.target.wf hAρ rfl rfl RA
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hstep H.target.wf hxρ rfl rfl RX
  have hy := hx.subst henv.orderedStrong H.agree.left hΔ
  have Hlift := H.under_binder hΔ hA hy
  have C : IsDefEqCtx env univs [] (A.subst ρ :: Γ') (A' :: Γ') := .succ (.refl H.target.wf) HA
  have Hconvert := EqSpecializationFrame.of_conversion hΔ Hlift.target C
  have Hretained : EqSpecializationFrame (A :: Γ) (A' :: Γ') Δ
      (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift := by
    have Eρ : ρ.lift.comp VExpr.Subst.id = ρ.lift := by
      funext i
      exact VExpr.subst_id
    have Eτ : τ.lift.comp ProofShape.Subst.id = τ.lift := by
      funext i
      exact ProofShape.subst_id _
    simpa only [Eρ, Eτ] using Hlift.compose hΔ Hconvert
  have HXtarget := HX.subst henv.orderedStrong H.target hΔ
  have Hxy := (H.term hΔ hx).trans_r henv hΔ HXtarget
  have Hxy' : env.IsDefEq univs Δ (x.subst σ) (x'.subst σ') (A'.subst σ') :=
    .defeqDF (HA.subst henv.orderedStrong H.target hΔ) Hxy
  have Hconsume : EqSpecializationFrame (A' :: Γ') Γ' Δ (σ'.cons (x.subst σ)) σ'
      (VExpr.Subst.one x') (ProofShape.Subst.one rawX) := by
    simpa only [EX] using EqSpecializationFrame.inst H.target HA.hasType.2
      (HA.defeq HX.hasType.2) Hxy'
  exact ⟨A', x', HA, EA, HX, EX, Hretained, Hconsume, Hretained.compose hΔ Hconsume⟩

/-- Compute components in their actual source scope, then follow an agreeing
frame while retaining the same chosen target assignment and pending vector.
The new erased vector is the literal substitution of the computed endpoint;
no primitive computation is transported through that substitution. -/
theorem EqPrefixSpecializationAt.compute_then_frame
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (pre.map (proofErase Γ)) raw) :
    ∃ pre' : List VExpr, EqPrefixSpecializationAt Γ' Δ v w v'' w'' original
        (pre'.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      pre'.map (proofErase Γ) = raw ∧
      (pre'.map (·.subst ρ)).map (proofErase Γ') = raw.map (·.subst τ) := by
  obtain ⟨pre', HP, EP, HE⟩ := H.compute hstep H.1.wf H.1.wf (Ctx.LiftN.zero []) hΔ hf HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using HA)
  have EP' : pre'.map (proofErase Γ) = raw := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP
  obtain ⟨HP', hf', ER⟩ := HP.frame hΔ W HE.hasType.2
  exact ⟨pre', HP', hf', EP', by simpa only [EP'] using ER⟩

/-- A shared actual supply opens eta, crosses an agreeing outer frame,
computes the displayed annotation and body components in the later scope,
and consumes the independently computed original argument. The body keeps its
original chosen target image throughout. The result derives post-beta target
completion and exact erased arguments, retaining both actual binder frames.
The agreeing outer frame must come from earlier ancestry; raw interpretation
alone is not asserted to supply it. -/
theorem EqPrefixSpecializationAt.eta_delayed_compute_inst
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (RA : ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' (A.subst ρ)) rawA)
    (RX : ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' (x.subst ρ)) rawX)
    (HB : List.Forall₂ (ScopedCompute BodyStep (rawA :: proofEraseCtx Γ'))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map (·.subst τ.lift)) rawPre) :
    ∃ (A' x' : VExpr) (pre' : List VExpr),
      env.IsDefEq univs Γ' (A.subst ρ) A' (.sort u) ∧ proofErase Γ' A' = rawA ∧
      env.IsDefEq univs Γ' (x.subst ρ) x' (A.subst ρ) ∧ proofErase Γ' x' = rawX ∧
      EqSpecializationFrame (A :: Γ) (A' :: Γ') Δ
        (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift ∧
      EqSpecializationFrame (A' :: Γ') Γ' Δ (σ'.cons (x.subst σ)) σ'
        (VExpr.Subst.one x') (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original
        (pre'.map (·.inst x')) σ' (rest.map (·.subst σ) ++ pending) ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x')))
        ((B.subst ρ.lift).inst x') ∧
      pre'.map (proofErase (A' :: Γ')) = rawPre ∧
      (pre'.map (·.inst x')).map (proofErase Γ') = rawPre.map (·.inst rawX) := by
  obtain ⟨Hfresh, x₀, HX₀, _, _⟩ := H.eta_supply_frame hstep hΔ ht hwhole hA hf
    (ScopedCompute.refl (Step := Step) (e := proofErase Γ x))
  have hx := HX₀.hasType.1
  obtain ⟨A', x', HA, EA, HX, EX, Hretained, Hconsume, _⟩ :=
    W.computed_binder_supply hstep hΔ hA hx RA RX
  have hfw : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have EE : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [.bvar 0])) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  obtain ⟨HPafter, hbafter, EPafter⟩ := Hfresh.frame hΔ Hretained hb
  have HCafter : env.IsDefEqU univs (A' :: Γ') (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) := by
    obtain ⟨_, HC⟩ := HC
    simpa only [VExpr.subst] using (HC.subst henv.orderedStrong Hretained.actual Hretained.target.wf).toU
  have HBafter : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A' :: Γ')))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (·.subst ρ.lift)).map (proofErase (A' :: Γ'))) rawPre := by
    simpa only [EPafter, proofEraseCtx, EA] using HB
  obtain ⟨pre', HPfinal, hfinal, Epre, Efinal⟩ :=
    HPafter.compute_then_frame hbody hΔ Hconsume hbafter HCafter HBafter
  refine ⟨A', x', pre', HA, EA, HX, EX, Hretained, Hconsume, ?_, ?_, Epre, ?_⟩
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using HPfinal
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using hfinal
  · simpa only [VExpr.inst_eq, VExpr.Subst.one, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using Efinal

end Lean4Lean.VEnv.Strengthening
