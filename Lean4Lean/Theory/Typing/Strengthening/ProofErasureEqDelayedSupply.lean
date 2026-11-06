import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializationFrames

/-! # Preserve a chosen eta supply across a later frame and computation

The incoming binder image remains the original supplied argument's target
specialization. Actual annotation and argument computations in the later scope
produce both the retained binder frame and its matching consumption frame.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private args_subst
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixSpecialization
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
      (pre'.map (·.subst ρ)).map (proofErase Γ') = raw.map (·.subst τ) ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨pre', HP, EP, HE⟩ := H.compute hstep H.1.wf H.1.wf (Ctx.LiftN.zero []) hΔ hf HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using HA)
  have EP' : pre'.map (proofErase Γ) = raw := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP
  obtain ⟨HP', hf', ER⟩ := HP.frame hΔ W HE.hasType.2
  exact ⟨pre', HP', hf', EP', by simpa only [EP'] using ER, HE⟩

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
      (pre'.map (·.inst x')).map (proofErase Γ') = rawPre.map (·.inst rawX) ∧
      env.IsDefEqU univs Γ'
        (.app ((VExpr.mkApps (.const ``Eq.rec [v',w']) pre).subst ρ) (x.subst ρ))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) := by
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
  obtain ⟨pre', HPfinal, hfinal, Epre, Efinal, HEbody⟩ :=
    HPafter.compute_then_frame hbody hΔ Hconsume hbafter HCafter HBafter
  refine ⟨A', x', pre', HA, EA, HX, EX, Hretained, Hconsume, ?_, ?_, Epre, ?_, ?_⟩
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using HPfinal
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using hfinal
  · simpa only [VExpr.inst_eq, VExpr.Subst.one, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using Efinal
  · have EBefore : VExpr.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (·.subst ρ.lift)) =
        .app ((VExpr.mkApps (.const ``Eq.rec [v',w']) pre).subst ρ).lift (.bvar 0) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst, VExpr.lift_subst_lift,
        VExpr.Subst.lift, VExpr.Subst.cons] using congrArg (fun e => e.subst ρ.lift) EE
    have HI := (HEbody.instN henv (HA.defeq HX.hasType.2) Ctx.InstN.zero).toU
    rw [EBefore] at HI
    have HI' : env.IsDefEqU univs Γ'
        (.app ((VExpr.mkApps (.const ``Eq.rec [v',w']) pre).subst ρ) x')
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) := by
      simpa only [VExpr.inst_eq, VExpr.subst_mkApps, VExpr.subst,
        VExpr.lift_subst_cons, VExpr.Subst.cons, VExpr.subst_id] using HI
    exact (IsDefEq.appDF (hf.subst henv.orderedStrong W.actual W.target.wf) HX).toU.trans henv W.target.wf HI'

/-- Restore an actual source tail whose specialization agrees with the
pending target tail. The original chosen substitution and final pending
vector are unchanged; only the agreeing tail moves back into the source. -/
theorem EqPrefixSpecializationAt.append_pending_agree
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (targetTail ++ pending))
    (HR : List.Forall₂ (env.IsDefEqU univs Δ) targetTail (rest.map (·.subst σ))) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ rest) σ pending := by
  have Hrefl := (H.2.2.flip.imp (fun _ _ h => IsDefEqU.symm h)).trans
    (fun _ _ _ h k => h.trans henv hΔ k) H.2.2
  obtain ⟨Hpre, Htail⟩ := List.forall₂_append_split Hrefl rfl
  obtain ⟨_, Hpending⟩ := List.forall₂_append_split Htail rfl
  refine ⟨H.1, H.2.1, ?_⟩
  have HH := H.2.2.trans (fun _ _ _ h k => h.trans henv hΔ k)
    (Hpre.append' (HR.append' Hpending))
  simpa only [List.map_append, List.append_assoc] using HH

/-- Delayed eta consumption retains the entire independently computed actual
supply. Semantic prefix equality restores whole-application typing before the
remaining arguments are reified. Their original target images agree through
the outer frame and their actual computations, so they can be returned from
the pending vector to the source spine without changing the chosen assignment.
An agreeing outer frame is still required; arbitrary context interpretation
alone does not prove the initial agreement. -/
theorem EqPrefixSpecializationAt.eta_delayed_compute_spine_inst
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
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map (·.subst τ.lift)) rawPre)
    (RXS : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      ((rest.map (proofErase Γ)).map (·.subst τ)) rawRest) :
    ∃ (A' x' : VExpr) (pre' rest' : List VExpr),
      env.IsDefEq univs Γ' (A.subst ρ) A' (.sort u) ∧ proofErase Γ' A' = rawA ∧
      env.IsDefEq univs Γ' (x.subst ρ) x' (A.subst ρ) ∧ proofErase Γ' x' = rawX ∧
      EqSpecializationFrame (A :: Γ) (A' :: Γ') Δ
        (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift ∧
      EqSpecializationFrame (A' :: Γ') Γ' Δ (σ'.cons (x.subst σ)) σ'
        (VExpr.Subst.one x') (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original
        (pre'.map (·.inst x') ++ rest') σ' pending ∧
      env.IsDefEq univs Γ'
        (VExpr.mkApps (.const ``Eq.rec [v',w']) ((pre ++ x :: rest).map (·.subst ρ)))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x') ++ rest')) (F.subst ρ) ∧
      pre'.map (proofErase (A' :: Γ')) = rawPre ∧ rest'.map (proofErase Γ') = rawRest ∧
      (pre'.map (·.inst x') ++ rest').map (proofErase Γ') = rawPre.map (·.inst rawX) ++ rawRest := by
  obtain ⟨A', x', pre', HA, EA, HX, EX, Hretained, Hconsume, HP, hprefix, EP, EI, Hhead⟩ :=
    H.eta_delayed_compute_inst hstep hbody hΔ W ht hwhole hA hf HC RA RX HB
  have hrest : ∀ e ∈ rest, VExpr.WF env univs Γ e := by
    intro e he
    exact (mkApps_arguments_wf henv H.1.wf ⟨_, hwhole⟩).2 e
      (List.mem_append_right pre (List.mem_cons_of_mem x he))
  have Erest : (rest.map (·.subst ρ)).map (proofErase Γ') =
      (rest.map (proofErase Γ)).map (·.subst τ) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, heT⟩ := hrest e he
    exact proofErase_subst_with W.target.wf W.actual heT W.erase
  have hsplit : env.HasType univs Γ'
      (VExpr.mkApps (.app ((VExpr.mkApps (.const ``Eq.rec [v',w']) pre).subst ρ) (x.subst ρ))
        (rest.map (·.subst ρ))) (F.subst ρ) := by
    simpa only [VExpr.subst_mkApps, VExpr.subst, List.map_append, List.map_cons,
      VExpr.mkApps_append, VExpr.mkApps_cons] using hwhole.subst henv.orderedStrong W.actual W.target.wf
  obtain ⟨rest', HR, ER, HE⟩ := proofErase_scoped_spine_arguments_descend hstep
    W.target.wf W.target.wf (Ctx.LiftN.zero []) Hhead hsplit
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id, Erest] using RXS)
  have ER' : rest'.map (proofErase Γ') = rawRest := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using ER
  have HframeRest : List.Forall₂ (env.IsDefEqU univs Δ)
      (rest.map (·.subst σ)) ((rest.map (·.subst ρ)).map (·.subst σ')) := by
    apply List.forall₂_of_getElem (by simp only [List.length_map])
    intro i hi hi'
    have hi₀ : i < rest.length := by simpa only [List.length_map] using hi
    obtain ⟨Te, heT⟩ := hrest rest[i] (List.getElem_mem hi₀)
    simpa only [List.getElem_map] using (W.term hΔ heT).toU
  have HRtarget := HframeRest.trans (fun _ _ _ h k => h.trans henv hΔ k)
    (args_subst hΔ W.target HR)
  refine ⟨A', x', pre', rest', HA, EA, HX, EX, Hretained, Hconsume,
    HP.append_pending_agree hΔ HRtarget, ?_, EP, ER', ?_⟩
  · simpa only [VExpr.subst_mkApps, VExpr.subst, List.map_append, List.map_cons,
      VExpr.mkApps_append, VExpr.mkApps_cons] using HE
  · rw [List.map_append, EI, ER']

end Lean4Lean.VEnv.Strengthening
