import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaSingleton

/-! # Retain the computed source tail across eta consumption

A source spine and its target completion remain related after the eta body,
consumed argument and remaining arguments compute independently. Keeping the
actual remaining source arguments permits the next consumption to use the
same supply invariant, rather than forgetting them into target-only pending
terms. Arbitrary intervening retained frames still require integration.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- Move an explicitly represented source tail from the target completion
back into the source spine. Both the chosen substitution and the residual
target completion are unchanged. -/
theorem EqPrefixSpecializationAt.append_pending
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      (rest.map (·.subst σ) ++ pending)) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ rest) σ pending := by
  obtain ⟨WS, HC, HA⟩ := H
  exact ⟨WS, HC, by simpa only [List.map_append, List.append_assoc] using HA⟩

/-- Consume a fresh eta binder while preserving the entire tracked source
spine, including its independently computed remaining arguments. The target
binder image is derived from the shared completion. The result retains the
whole spine's original assigned type and its exact raw instantiated vector,
so another split/eta/consume step can use the same invariant. Only ordinary
semantic equalities cross the binder; raw guarded paths stay in their scopes. -/
theorem EqPrefixSpecializationAt.eta_compute_spine_inst
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A :: Γ)))
      ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))) rawPre)
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ) (proofErase Γ x) rawX)
    (RXS : List.Forall₂ (ScopedCompute ArgStep (proofEraseCtx Γ))
      (rest.map (proofErase Γ)) rawRest) :
    ∃ (pre' rest' : List VExpr) (x' : VExpr),
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original
        (pre'.map (·.inst x') ++ rest') σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x') ++ rest')) F ∧
      (pre'.map (·.inst x') ++ rest').map (proofErase Γ) =
        rawPre.map (·.inst rawX) ++ rawRest ∧
      pre'.map (proofErase (A :: Γ)) = rawPre ∧
      rest'.map (proofErase Γ) = rawRest ∧
      env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX := by
  have hΓ := H.1.wf
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x) rest) F := by
    simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using hwhole
  obtain ⟨Tx, hfx⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
  have hfx : env.HasType univs Γ
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x) Tx := hfx
  obtain ⟨_, _, hf₀, hx₀⟩ := hfx.app_inv henv hΓ
  have hx := argument_at_displayed_domain hΓ hf₀ hf hx₀
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
  obtain ⟨pre', x', HEbody, EP, HX, EX, HS, hf', EI⟩ := HEta.compute_inst hbody harg hΔ hb HC HA hx
    (hx.subst henv.orderedStrong H.1 hΔ) RX
  have HEinst : env.IsDefEqU univs Γ
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x')
      (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) := by
    have HI := (HEbody.instN henv HX.hasType.2 Ctx.InstN.zero).toU
    rw [EE] at HI
    simpa only [VExpr.inst_eq, VExpr.subst_mkApps, VExpr.subst,
      VExpr.lift_subst_cons, VExpr.Subst.cons, VExpr.subst_id] using HI
  have HEhead := (IsDefEq.appDF hf HX).toU.trans henv hΓ HEinst
  obtain ⟨rest', HR, ER, HE⟩ := proofErase_scoped_spine_arguments_descend harg
    hΓ hΓ (Ctx.LiftN.zero []) HEhead hsplit
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using RXS)
  have ER' : rest'.map (proofErase Γ) = rawRest := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using ER
  have HRpre : List.Forall₂ (env.IsDefEqU univs Γ) (pre'.map (·.inst x')) (pre'.map (·.inst x')) :=
    List.Forall₂.rfl (mkApps_arguments_wf henv hΓ ⟨_, hf'⟩).2
  have Hhead : env.IsDefEqU univs Γ (.const ``Eq.rec [v'',w'']) (.const ``Eq.rec [v'',w'']) :=
    VExpr.WF.of_mkApps henv hΓ ⟨_, hf'⟩
  refine ⟨pre', rest', x', HS.append_pending.congr hΔ Hhead (HRpre.append' HR), ?_, ?_, EP, ER', HX, EX⟩
  · simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using HE
  · rw [List.map_append, EI, ER']

/-- Ordinary context conversion preserves the chosen target substitution,
head equality and all argument ancestry. This changes the source realization,
not the target equation, and makes no claim about guarded computation paths. -/
theorem EqPrefixSpecializationAt.source_convert
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ')
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending) :
    EqPrefixSpecializationAt Γ' Δ v w v' w' original pre σ pending :=
  ⟨substEq_source_convert hΔ W H.1, H.2⟩

/-- A computed retained-lambda annotation changes the source binder while
preserving its already chosen target image and the actual source argument
vector. The new source typing and unchanged component erasures are supplied
by ordinary context conversion. Guarded paths in the old context are not
transported to the new one. -/
theorem EqPrefixSpecializationAt.compute_annotation
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre σ pending)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (RD : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ A) rawA) :
    ∃ A', env.IsDefEq univs Γ A A' (.sort u) ∧ proofErase Γ A' = rawA ∧
      EqPrefixSpecializationAt (A' :: Γ) Δ v w v' w' original pre σ pending ∧
      env.HasType univs (A' :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      pre.map (proofErase (A' :: Γ)) = pre.map (proofErase (A :: Γ)) := by
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hsource hΓ hA rfl rfl RD
  have W : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  refine ⟨A', HA, EA, H.source_convert hΔ W, hf.defeqDFC henv W, ?_⟩
  apply List.map_congr_left
  intro e he
  obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓA ⟨_, hf⟩).2 e he
  exact (proofErase_defeqCtx hΓA W ht).symm

/-- A selected short prefix of the retained whole source completion can
immediately feed the later cut classifier and singleton readout. Prefix typing,
nonproof status and target specialization are derived from the whole spine;
the current eta domain is supplied by its retained typed origin. The result
keeps the same cut if its selected root is native eta. -/
theorem CountedLaterEtaBodyCut.eq_or_eta_of_completion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] full σ pending)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) full) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) full))
    (hlen : arity ≤ 4)
    (HO : TypedEtaOrigin (proofEraseCtx Γ) rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((full.map (proofErase Γ)).take arity)) u)
    (H : CountedLaterEtaBodyCut D n (proofEraseCtx Γ) rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((full.map (proofErase Γ)).take arity))
      u args out ct cost)
    (HE : CarrierExposure out) :
    env.IsDefEq univs Δ a b α ∨
      CountedLaterEtaBodyCut D n (proofEraseCtx Γ) rawA
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((full.map (proofErase Γ)).take arity))
        u args out ct cost (EqEtaRemainingRoot D) := by
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) (full.take arity)) (full.drop arity)) F := by
    rw [← VExpr.mkApps_append, List.take_append_drop]
    exact hf
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
  have hp : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (full.take arity)) Tp := hp
  have hnp := nonproof_spine_head hΓ hsplit (by
    simpa only [← VExpr.mkApps_append, List.take_append_drop] using hn)
  have HG := H.eq_guarded heq hs hreg hoff hRec (by
    simp only [List.length_take, List.length_map]; omega) HE
  have HP' := (HP.take arity).forget
  rw [← List.map_take] at HO HG ⊢
  exact HG.read_singleton_of_origin heq hs hΓ hΔ HP' ht hp hnp
    (by simp only [List.length_take]; omega) HO

end Lean4Lean.VEnv.Strengthening
