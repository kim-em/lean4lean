import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadCompletion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton

/-! # Construct completion ancestry along component and eta histories

Component histories are reified below ambient unused binders. A recovered eta
domain then opens the exact actual fresh-body context and consumes one chosen
target argument. Arbitrary wrapper histories, and eta at a completed five-slot
prefix, are not covered by these two preservation steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Reify a component history and select any prefix while preserving its
original target completion. The actual source realization and ambient unused
binders are retained; the new head levels need their usual well-formedness. -/
theorem EqHeadCompletion.compute_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqHeadCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HL : List.Forall₂ (· ≈ ·) ls ls') (HW : ∀ l ∈ ls', l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Ξ) args args') (arity : Nat) :
    EqHeadCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls') (args'.take arity)) := by
  obtain ⟨Γ, Γ', count, offset, v₀, w₀, pre, F, hΓ, hΓ', W, rfl, hf, hn, HP, E⟩ := H
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN] at E
  obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj E
  obtain ⟨v₁, w₁, rfl⟩ : ∃ v₁ w₁, ls' = [v₁,w₁] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  have HW₀ := typed_const_levels_wf
    (show TypedSource (proofEraseCtx Γ) (ProofShape.mkApps (.const ``Eq.rec [v₀,w₀]) (pre.map (proofErase Γ))) from
      ⟨Γ, _, F, hΓ, rfl, hf, proofErase_const_spine hΓ hf hn⟩)
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v₀,w₀]) (.const ``Eq.rec [v₁,w₁]) :=
    ⟨_, .constDF heq.2.2.1 HW₀ HW (by rfl) HL⟩
  obtain ⟨pre', HP', EP, HE⟩ := HP.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) hΓ hΓ' W hΔ hf HC HA
  have hnew := HE.hasType.2
  have hnnew := fun hp => hn ((isProof_congr hΓ HE).2 hp)
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v₁,w₁]) (pre'.take arity)) (pre'.drop arity)) F := by
    rw [← VExpr.mkApps_append, List.take_append_drop]
    exact hnew
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
  have hnp := nonproof_spine_head hΓ hsplit (by
    simpa only [← VExpr.mkApps_append, List.take_append_drop] using hnnew)
  refine ⟨Γ, Γ', count, offset, v₁, w₁, pre'.take arity, Tp,
    hΓ, hΓ', W, rfl, hp, hnp, HP'.take arity, ?_⟩
  rw [proofErase_const_spine hΓ hp hnp, ProofShape.liftN_mkApps]
  simp only [ProofShape.liftN, List.map_take, EP]

/-- Open an actual recovered eta binder while a target argument remains.
The new source typing, nonproof status, context erasure and completion are
all derived. The exact raw domain from the computation is preserved. -/
theorem EqHeadCompletion.eta
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqHeadCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length < original.length)
    (RN : ScopedTypeRecovery Guard Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u) :
    EqHeadCompletion Δ v w original (rawA :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  obtain ⟨Γ, Γ', count, offset, v₀, w₀, pre, F, hΓ, hΓ', W, rfl, hf, hn, HP, E⟩ := H
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ' W hf (E.symm ▸ RN)
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hA := (EA ▸ SD).descend hΓ hΓ' W hA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
  have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA]
  have Ehead := E
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN] at Ehead
  obtain ⟨_, Els, Eargs⟩ := ProofShape.const_spine_inj Ehead
  have hshort : pre.length < original.length := by
    have HL := congrArg List.length Eargs
    simp only [List.length_map] at HL
    omega
  let fresh := pre.map VExpr.lift ++ [VExpr.bvar 0]
  have Efresh : VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) fresh =
      .app (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) pre).lift (.bvar 0) := by
    simp only [fresh, VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hfw : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hfPi.weak henv
  have hb : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) fresh) B := by
    rw [Efresh]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body hΓ hA hfPi hn
  rw [← Efresh] at EB
  have hnb : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) fresh) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  refine ⟨A :: Γ, A.liftN count offset :: Γ', count, offset+1, v₀, w₀, fresh, B,
    hΓA, hΓA', W.succ, Ectx, hb, hnb, HP.eta hΔ ht hA hfPi hshort, ?_⟩
  rw [EB, ProofShape.liftN, etaArgument_liftN]
  rw [← ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _), E]

/-- The original component history supplies a completing realization for the
selected short outer prefix. This initializes ancestry from the original
five actual arguments, while leaving the extra raw proof marker unrepresented. -/
theorem eq_head_completion_of_probe_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (HL : List.Forall₂ (· ≈ ·) [v,w] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      ((([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof]) (pre ++ pending))
    (hlen : pre.length ≤ 5)
    (HT : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre)) :
    EqHeadCompletion Γ v w [α,a,M,minor,b] (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) := by
  have H : EqHeadCompletion Γ v w [α,a,M,minor,b] (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w])
        (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset))) := by
    refine ⟨Γ, Γ', count, offset, v, w, [α,a,M,minor,b], T,
      hΓ, hΓ', W, rfl, ht, hn, EqPrefixSpecialization.of_typed hΓ ht, ?_⟩
    rw [proofErase_const_spine hΓ ht hn, ProofShape.liftN_mkApps]
    rfl
  have HA5 := Lean4Lean.List.forall₂_take HA 5
  have HA5 : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
      (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ((pre ++ pending).take 5) := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero] using HA5
  have HP := H.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA5 pre.length
  simpa only [List.take_take, Nat.min_eq_left hlen, List.take_left] using HP

/-- Reify the actual selected body-prefix history, adding target completion
at that same root. All count, path, scope, typing and minimum witnesses are
retained. The fresh-body completion is constructed by `EqHeadCompletion.eta`. -/
theorem CountedEtaBodySpineCut.complete_root
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqHeadCompletion Γ v w original (A :: Δ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)))
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct Root) :
    CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct
      (fun m Ξ source target => Root m Ξ source target ∧ EqHeadCompletion Γ v w original Ξ source) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩ := H
  have HP' : EqHeadCompletion Γ v w original (A :: Δ)
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u])) := by
    simpa only [ProofShape.mkApps_append, ProofShape.mkApps, List.foldl_cons, List.foldl_nil,
      ProofShape.liftN_mkApps, ProofShape.liftN] using HP
  have Hcompletion := HP'.compute_components heq hs hΓ HLbody (typed_const_levels_wf HTR) HAbody bodyPre.length
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG, ?_⟩
  simpa only [List.take_left] using Hcompletion

/-- Forget only the added root completion, recovering the original cut with
all its actual witnesses. This permits the existing continuation construction. -/
theorem CountedEtaBodySpineCut.forget_completion
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (H : CountedEtaBodySpineCut D n Δ c ls pre A u args out ct
      (fun m Ξ source target => Root m Ξ source target ∧ EqHeadCompletion Γ v w original Ξ source)) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args out ct Root := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG, _⟩ := H
  exact ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, HAbody, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩

/-- At a completed five-argument Eq prefix, the recovered eta domain is a
proposition. Its fresh argument is therefore literally the erased proof
marker, even when native recovery selected a converted domain. -/
theorem EqHeadCompletion.full_eta_argument
    (heq : env.HasCanonicalEq) (hguard : ErasedScopedPrimitiveDescent Guard)
    (H : EqHeadCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5)
    (RN : ScopedTypeRecovery Guard Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u) : etaArgument u = .proof := by
  obtain ⟨Γ, Γ', count, offset, v₀, w₀, pre, F, hΓ, hΓ', W, rfl, hf, hn, _, E⟩ := H
  have Ehead := E
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN] at Ehead
  obtain ⟨_, _, Eargs⟩ := ProofShape.const_spine_inj Ehead
  have hfive : pre.length = 5 := by
    have HL := congrArg List.length Eargs
    simp only [List.length_map] at HL
    omega
  obtain ⟨α', a', M', minor', b', rfl⟩ :
      ∃ α' a' M' minor' b', pre = [α',a',M',minor',b'] := by
    cases pre with | nil => simp at hfive | cons x xs =>
    cases xs with | nil => simp at hfive | cons y ys =>
    cases ys with | nil => simp at hfive | cons z zs =>
    cases zs with | nil => simp at hfive | cons q qs =>
    cases qs with | nil => simp at hfive | cons r rs =>
    cases rs with
    | nil => exact ⟨_, _, _, _, _, rfl⟩
    | cons s ss => simp at hfive
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ' W hf (E.symm ▸ RN)
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have hfCanon := eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  obtain ⟨⟨_, HD⟩, _⟩ := (hfCanon.uniqU henv hΓ hfPi).forallE_inv henv hΓ
  have hA : env.HasType univs Γ A (.sort .zero) :=
    (HasType.eqApp heq hw hα ha hb).defeqU_l henv hΓ HD.toU
  have hAu := (EA ▸ SD).descend hΓ hΓ' W hA
  exact if_pos ((hAu.uniqU henv hΓ hA).sort_inv henv hΓ)

/-- Preserve completion ancestry while constructing the actual smaller typed
continuation under the next eta binder. If fewer than five arguments have
been supplied, its fresh source has a derived completion. Otherwise the
selected prefix is exactly complete at arity five, and that prefix's original
completion is retained. The new sixth argument needs separate proof-major
handling; this theorem does not assign it a target inhabitant. The actual
inner recovery and domain-sort witnesses are retained for subsequent readout. -/
theorem CountedEtaBodySpineCut.nested_eta_completed_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (HRouter : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct
      (fun rootStage Ξ source target => EqEtaRemainingRoot D rootStage Ξ source target ∧
        EqHeadCompletion Γ v w [α,a,M,minor,b] Ξ source))
    (hcost : cp+1+ct ≤ cost) :
    ∃ innerA innerU bodyLs bodyPre smaller, smaller < cost ∧
      PiInertTypedContinuationMinimum D Δ out (innerA :: A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) smaller ∧
      (EqHeadCompletion Γ v w [α,a,M,minor,b] (innerA :: A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) ∨
        bodyPre.length = 5 ∧ etaArgument innerU = .proof ∧
          EqHeadCompletion Γ v w [α,a,M,minor,b] (A :: Δ)
          (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre)) ∧
      ∃ innerStage innerB,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
          (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) (.forallE innerA innerB) ∧
        DomainSort (A :: Δ) innerA innerU := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, _, _, _, RP, HR, _, RT, _, HM, _, _, WI, _, ⟨k, _, HEta⟩, HP⟩ := H
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have HTwhole : TypedSource (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls') bodyPre) bodyPending) := by
    simpa only [ProofShape.mkApps_append] using HTbody.pi_inert_compute heq hs RP.forget
  have HTbody' := HTwhole.pi_inert_compute heq hs
    ((((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).trans RT).forget)
  have HTlong := HT.pi_inert_compute heq hs
    (((ScopedComputeCount.base HRouter).mkApps (ScopedArgumentsCount.refl (args := args))).forget)
  have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs')) (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  have HTnext := HTlong.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
  have HTout := HTnext.pi_inert_compute heq hs RS.forget
  have HK : PiInertTypedContinuationRun D Δ out (A :: Δ)
      (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs'
        (fun e k => e = out ∧ k = 0)) body' cs := by
    have RS' : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') out := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    simpa only [Nat.add_zero] using
      PiInertTypedContinuationRun.application HTbody' WI HTnext' RS' (.terminal HTout)
  cases HEta with
  | @intro innerA innerB innerU RNinner SDinner =>
    obtain ⟨smaller, hsmall, Htyped⟩ := pi_inert_eta_typed_continuation_frames heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RNinner SDinner
      (by simpa only [ProofShape.mkApps_append] using RP) HR RT HK
      (cost := cb+cs) (by omega) (by
        rintro later j endpoint suffixCost RJ ⟨suffixStage, suffixCount, endpoint', tailCost, hsum, RK, rfl, rfl⟩
        have HH := HM later suffixStage j suffixCount endpoint RJ
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RK)
        omega)
    refine ⟨innerA, innerU, ls', bodyPre, smaller, by omega, Htyped, ?_, k, innerB, RNinner, SDinner⟩
    by_cases hshort : bodyPre.length < 5
    · exact .inl (HP.eta (erased_static_structure_eta_expansion_stage_descent heq hs k)
        hΓ ht (by simpa only [List.length_cons, List.length_nil] using hshort) RNinner SDinner)
    · obtain ⟨levels, sourceArgs, EE, hlen⟩ := HP.arity
      obtain ⟨_, _, rfl⟩ := ProofShape.const_spine_inj EE
      simp only [List.length_cons, List.length_nil] at hlen
      have hfive : bodyPre.length = 5 := by omega
      exact .inr ⟨hfive, HP.full_eta_argument heq
        (erased_static_structure_eta_expansion_stage_descent heq hs k) hfive RNinner SDinner, HP⟩


end Lean4Lean.VEnv.Strengthening
