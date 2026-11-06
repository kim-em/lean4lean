import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixSpecialization

/-! # Preserve the Eq target completion when a binder is consumed

The chosen target image of the binder must agree with the specialized actual
argument. Paired ordinary substitution then identifies every prefix component
before and after instantiation. Computation is first reified in its own scope;
neither raw guarded paths nor native recovery certificates are substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Consume a binder while retaining the chosen target completion. The
actual argument must specialize to the stored binder image. This equality is
an explicit ancestry requirement, not a consequence of arbitrary typed
substitution. The instantiated source retains its actual assigned type. -/
theorem EqPrefixSpecializationAt.inst
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending)
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hx : env.HasType univs Γ x A)
    (Hxy : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ)) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.map (·.inst x)) σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.inst x))) (F.inst x) := by
  obtain ⟨WS, HC, HA⟩ := H
  cases WS with
  | cons WS hA _ =>
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨WS.wf, _, hA⟩
    have Wxy : Ctx.SubstEq env univs Δ (σ.cons y) (σ.cons (x.subst σ)) (A :: Γ) :=
      .cons WS hA Hxy
    have HP : List.Forall₂ (env.IsDefEqU univs Δ)
        (pre.map (·.subst (σ.cons y))) ((pre.map (·.inst x)).map (·.subst σ)) := by
      apply List.forall₂_of_getElem (by simp only [List.length_map])
      intro i hi hi'
      have hi₀ : i < pre.length := by simpa only [List.length_map] using hi
      obtain ⟨Te, he⟩ := (mkApps_arguments_wf henv hΓA ⟨_, hf⟩).2 pre[i]
        (List.getElem_mem hi₀)
      have HE := IsDefEq.substDF henv.orderedStrong hΓA hΔ Wxy he
      simpa only [List.getElem_map, VExpr.subst_inst, VExpr.inst_lift_cons] using HE.toU
    have Hreverse : List.Forall₂ (env.IsDefEqU univs Δ)
        (pre.map (·.subst (σ.cons y)) ++ pending) original :=
      HA.flip.imp (fun _ _ H => IsDefEqU.symm H)
    have Hrefl := Hreverse.trans (fun _ _ _ H K => H.trans henv hΔ K) HA
    have Hpending : List.Forall₂ (env.IsDefEqU univs Δ) pending pending := by
      simpa only [List.drop_left] using
        Lean4Lean.List.forall₂_drop Hrefl (pre.map (·.subst (σ.cons y))).length
    refine ⟨⟨WS, HC, HA.trans (fun _ _ _ H K => H.trans henv hΔ K) (HP.append' Hpending)⟩, ?_⟩
    simpa only [VExpr.inst_eq, VExpr.subst_mkApps, VExpr.subst] using hf.instN henv Ctx.InstN.zero hx

/-- Reify a computed argument before consuming the binder. Its semantic
equality preserves agreement with the chosen target image, so the same
target completion survives with the exact computed erased argument. -/
theorem EqPrefixSpecializationAt.inst_compute
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending)
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hx : env.HasType univs Γ x A)
    (Hxy : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ))
    (RX : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ x) rawX) :
    ∃ x', env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX ∧
      (pre.map (·.inst x')).map (proofErase Γ) =
        (pre.map (proofErase (A :: Γ))).map (·.inst rawX) ∧
      EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.map (·.inst x')) σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.inst x'))) (F.inst x') := by
  have WS := H.1
  cases WS with
  | cons WS hA _ =>
    obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hsource WS.wf hx rfl rfl RX
    have Hxy' := Hxy.trans (HX.subst henv.orderedStrong WS hΔ)
    obtain ⟨HS, hf'⟩ := H.inst hΔ hf HX.hasType.2 Hxy'
    refine ⟨x', HX, EX, ?_, HS, hf'⟩
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨WS.wf, _, hA⟩
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓA ⟨_, hf⟩).2 e he
    simpa only [EX, Function.comp_def] using proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero ht

/-- Compute the prefix components in the binder scope and the actual
argument in the outer scope, then instantiate only their exact endpoints.
The chosen target substitution survives both histories. The result supplies
the exact raw argument vector needed by a later Eq-root readout, without
transporting either guarded computation through substitution. Agreement with
the stored target image remains an explicit argument-ancestry requirement. -/
theorem EqPrefixSpecializationAt.compute_inst
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending)
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A :: Γ)))
      (pre.map (proofErase (A :: Γ))) rawPre)
    (hx : env.HasType univs Γ x A)
    (Hxy : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ))
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ) (proofErase Γ x) rawX) :
    ∃ pre' x', env.IsDefEq univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      pre'.map (proofErase (A :: Γ)) = rawPre ∧
      env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original (pre'.map (·.inst x')) σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) (F.inst x') ∧
      (pre'.map (·.inst x')).map (proofErase Γ) = rawPre.map (·.inst rawX) := by
  have hΓA := H.1.wf
  obtain ⟨pre', HS, EP, HE⟩ := H.compute hbody hΓA hΓA (Ctx.LiftN.zero []) hΔ hf HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using HA)
  have EP' : pre'.map (proofErase (A :: Γ)) = rawPre := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP
  obtain ⟨x', HX, EX, EI, HI, hf'⟩ := HS.inst_compute harg hΔ HE.hasType.2 hx Hxy RX
  exact ⟨pre', x', HE, EP', HX, EX, HI, hf', by simpa only [EP'] using EI⟩

/-- When the specialization tracks the prefix and its actual next argument
together, taking the prefix chooses that argument's specialized value for the
eta binder. After independent body-component and argument computations, beta
consumption therefore preserves the target completion without an additional
target-image equality premise. This is the actual supply/eta/consume case;
arbitrary unrelated application substitutions are not covered. -/
theorem EqPrefixSpecializationAt.eta_compute_inst
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A :: Γ)))
      ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))) rawPre)
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ) (proofErase Γ x) rawX) :
    ∃ (pre' : List VExpr) (x' : VExpr), EqPrefixSpecializationAt Γ Δ v w v'' w'' original
        (pre'.map (·.inst x')) σ (rest.map (·.subst σ) ++ pending) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) (B.inst x') ∧
      (pre'.map (·.inst x')).map (proofErase Γ) = rawPre.map (·.inst rawX) ∧
      env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX := by
  have HP : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      ((x.subst σ) :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  have HEta := HP.eta hΔ ht hA hf
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
  obtain ⟨pre', x', _, _, HX, EX, HS, hf', EI⟩ := HEta.compute_inst hbody harg hΔ hb HC HA hx
    (hx.subst henv.orderedStrong H.1 hΔ) RX
  exact ⟨pre', x', HS, hf', EI, HX, EX⟩

end Lean4Lean.VEnv.Strengthening
