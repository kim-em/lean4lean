import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaRoot

/-! # Read singleton roots in a later eta body

A retained semantic Eq specialization connects the later source prefix to the
original target equation. Read singleton guards in their actual body context
before specializing the resulting semantic equality. Native eta remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private computed_prefix_length
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaComputed
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- Read a specialized singleton in a fresh body using an arbitrary retained
Eq completion. Arity forces four source arguments; the fresh fifth argument
is interpreted by the completion only after guard certificate descent. -/
theorem EqPrefixSpecialization.read_computed_fresh_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hlen : pre.length ≤ 4)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (proofEraseCtx (A :: Γ)))
      ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u]) (bodyPre ++ bodyPending))
    (HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
      (proofEraseCtx (A :: Γ)) (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target) :
    env.IsDefEq univs Δ a b α := by
  have hbodyLen := computed_prefix_length HQ
  have hv := HA.length_eq
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hv
  have hfour : pre.length = 4 := by omega
  obtain ⟨α', a', M', minor', rfl⟩ : ∃ α' a' M' minor', pre = [α',a',M',minor'] := by
    cases pre with | nil => simp at hfour | cons x xs =>
    cases xs with | nil => simp at hfour | cons y ys =>
    cases ys with | nil => simp at hfour | cons z zs =>
    cases zs with | nil => simp at hfour | cons q qs =>
    cases qs with
    | nil => exact ⟨_, _, _, _, rfl⟩
    | cons r rs => simp at hfour
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) [α',a',M',minor']).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hb : env.HasType univs (A :: Γ)
      (eqRecBeforeMajor v' w' α'.lift a'.lift M'.lift minor'.lift (.bvar 0)) B := by
    simpa only [eqRecBeforeMajor, VExpr.mkApps, VExpr.lift, VExpr.liftN,
      List.foldl_cons, List.foldl_nil, VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have HF : EqPrefixSpecialization (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
      [α'.lift,a'.lift,M'.lift,minor'.lift,.bvar 0] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      H.eta hΔ ht hA hf (by change 4 < 5; decide)
  have Epre : ([α',a',M',minor'].map VExpr.lift).map (proofErase (A :: Γ)) =
      ([α',a',M',minor'].map (proofErase Γ)).map (·.liftN 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 e he
    exact proofErase_liftN hΓ hΓA Ctx.LiftN.one ht
  have HA' := HA.imp (fun _ _ R => R.mono (fun H =>
    erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left bodyStage rootStage) H.1))
  have HQ' := HQ.mono (erased_static_structure_eta_expansion_stage_mono (Nat.le_max_right bodyStage rootStage))
  apply HF.read_computed_guard heq
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs (max bodyStage rootStage))
    hΓA hΓA (Ctx.LiftN.zero []) hΔ ht hb (rest := []) (pending := bodyPending) ?_ HQ'
  rw [← Epre] at HA'
  simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id,
    List.append_nil, List.map_cons, List.map_nil, proofErase_fresh_argument hΓ hA,
    List.cons_append, List.nil_append] using HA'

/-- Either singleton form in a later fresh body proves the original target
Eq equation through the retained specialization. Ordinary source typing is
sufficient here; native recovery need not survive the earlier instantiation. -/
theorem EqPrefixSpecialization.read_later_fresh_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : pre.length ≤ 4)
    (HL : List.Forall₂ (· ≈ ·) [v',w'] bodyLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (proofEraseCtx (A :: Γ)))
      ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u]) (bodyPre ++ bodyPending))
    (HT : TypedSource (proofEraseCtx (A :: Γ)) (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre))
    (HG : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (proofEraseCtx (A :: Γ)) (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target ∨
      ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (proofEraseCtx (A :: Γ)) (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) target) :
    env.IsDefEq univs Δ a b α := by
  rcases HG with HG | HQ
  · obtain ⟨v₂, w₂, rfl⟩ : ∃ v₂ w₂, bodyLs = [v₂,w₂] := by
      cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
    have RL : ScopedCompute (ErasedStaticStructureEtaExpansionStage D bodyStage)
        (proofEraseCtx (A :: Γ)) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v₂,w₂]) :=
      .base (erased_static_structure_eta_expansion_stage_mono (Nat.zero_le bodyStage)
        (show ErasedStaticStructureEtaExpansionStage D 0 _ _ _ from
          .inl (.inr (.const HL (typed_const_levels_wf HT)))))
    apply H.read_fresh_singleton heq
      (erased_static_structure_eta_expansion_stage_descent heq hs bodyStage)
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs rootStage)
      hΓ hΓ (Ctx.LiftN.zero []) hΔ ht hA hf hn (by omega)
      (raw := bodyPre ++ bodyPending) (arity := bodyPre.length)
    · simpa only [List.length_nil, VExpr.liftN_zero, ProofShape.liftN_zero, List.map_id_fun', id]
        using HA.imp (fun _ _ R => R.mono pi_inert_stage_embed)
    · simpa only [List.length_nil, VExpr.liftN_zero] using RL
    · simpa only [List.length_nil, VExpr.liftN_zero, List.take_left] using HG
  · exact H.read_computed_fresh_guard heq hs hΓ hΔ ht hA hf hlen HA HQ

/-- Read the two singleton alternatives at the already selected later body
root. The remaining native eta alternative retains every root witness,
component history, count, prefix and suffix. -/
theorem CountedNonlevelSpineRoot.read_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : pre.length ≤ 4)
    (H : CountedNonlevelSpineRoot D n (proofEraseCtx (A :: Γ)) ``Eq.rec [v',w']
      ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u]) body' cb (EqEtaGuardedRoot D)) :
    env.IsDefEq univs Δ a b α ∨
      CountedNonlevelSpineRoot D n (proofEraseCtx (A :: Γ)) ``Eq.rec [v',w']
        ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u]) body' cb (EqEtaRemainingRoot D) := by
  obtain ⟨ls', bodyPre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT, HG⟩ := H
  rcases HG with HQ | ⟨k, hk, HG | HE⟩
  · exact .inl (HP.read_later_fresh_singleton heq hs hΓ hΔ ht hA hf hn hlen HL HA HT (.inr HQ))
  · exact .inl (HP.read_later_fresh_singleton heq hs hΓ hΔ ht hA hf hn hlen HL HA HT (.inl HG))
  · exact .inr ⟨ls', bodyPre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT, k, hk, HE⟩

/-- With the retained source-to-target Eq specialization, both singleton
forms in the later body cut prove the original equation. Otherwise the same
cut has only a native eta root. This does not yet supply specialization
ancestry through an arbitrary stack of retained continuation frames. -/
theorem CountedLaterEtaBodyCut.read_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : pre.length ≤ 4)
    (H : CountedLaterEtaBodyCut D n (proofEraseCtx Γ) (proofErase Γ A)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))
      u args out ct cost (EqEtaGuardedRoot D)) :
    env.IsDefEq univs Δ a b α ∨
      CountedLaterEtaBodyCut D n (proofEraseCtx Γ) (proofErase Γ A)
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))
        u args out ct cost (EqEtaRemainingRoot D) := by
  obtain ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
    RD, RB, RX, RS, HT, WI, HM, HR⟩ := H
  rcases (HR _ _ _ rfl).read_singleton heq hs hΓ hΔ HP ht hA hf hn hlen with HE | Hroot
  · exact .inl HE
  · right
    refine ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
      RD, RB, RX, RS, HT, WI, HM, ?_⟩
    intro c ls pre' Ef
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj Ef
    exact Hroot

/-- The retained typed eta origin supplies the actual domain and Pi
assignment needed by singleton readout, including after endpoint substitution.
The source prefix needs only its existing ordinary typing and nonproof status.
No renewed native recovery premise is imposed on the later scope. -/
theorem CountedLaterEtaBodyCut.read_singleton_of_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : pre.length ≤ 4)
    (HO : TypedEtaOrigin (proofEraseCtx Γ) rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) u)
    (H : CountedLaterEtaBodyCut D n (proofEraseCtx Γ) rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))
      u args out ct cost (EqEtaGuardedRoot D)) :
    env.IsDefEq univs Δ a b α ∨
      CountedLaterEtaBodyCut D n (proofEraseCtx Γ) rawA
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))
        u args out ct cost (EqEtaRemainingRoot D) := by
  obtain ⟨A, g, B, hA, hg, hng, EA, Eg⟩ := HO.realize hΓ
  have Ef := proofErase_const_spine hΓ hf hn
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg hf (Eg.trans Ef.symm)).2 hng
  have hfPi := ((HE.defeq hΓ).of_l henv hΓ hg).hasType.2
  subst rawA
  exact H.read_singleton heq hs hΓ hΔ HP ht hA hfPi hn hlen

end Lean4Lean.VEnv.Strengthening
