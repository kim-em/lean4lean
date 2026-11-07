import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIteratedAmbient

/-! # Compute Eq components through successive unused insertions

Reify component endpoints below each inserted block and retain their lower
computation certificates. The completion at the lower scope can then advance,
and the same actual insertion restores the exact upper prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
variable [Params]

/-- Component paths whose endpoints are displayed lifts descend to those
exact lower erased endpoints. Certificate descent supplies the lower paths;
injectivity of raw lifting identifies their outputs with the chosen actual
representatives. No semantic strengthening or guarded substitution is used. -/
theorem erased_components_certificate_below {args args' : List VExpr}
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (HT : ∀ e ∈ args, VExpr.WF env univs Γ e)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      ((args.map (proofErase Γ)).map (·.liftN count offset))
      ((args'.map (proofErase Γ)).map (·.liftN count offset))) :
    List.Forall₂ (ScopedCompute Target (proofEraseCtx Γ))
      (args.map (proofErase Γ)) (args'.map (proofErase Γ)) := by
  induction args generalizing args' with
  | nil =>
    cases args' with
    | nil => exact .nil
    | cons => cases HA
  | cons e args ih =>
    cases args' with
    | nil => cases HA
    | cons e' args' =>
      cases HA with
      | cons R HA =>
        obtain ⟨T, he⟩ := HT e (by simp)
        obtain ⟨f, HE, RF, EF⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W he rfl R
        have E : proofErase Γ f = proofErase Γ e' := ProofShape.liftN_inj.1 EF
        exact .cons (E ▸ RF) (ih (fun e he => HT e (by simp [he])) HA)

/-- Component computation, universe conversion and prefix selection preserve
completion through any finite sequence of unused binder insertions. Each
inserted block is removed from actual endpoints and their raw certificates,
then restored after advancing the lower completion. Arbitrary wrapper-body
computation is not asserted to be a component history. -/
theorem IteratedAmbientEqCompletion.compute_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : IteratedAmbientEqCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HL : List.Forall₂ (· ≈ ·) ls ls') (HW : ∀ l ∈ ls', l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Ξ) args args') (arity : Nat) :
    IteratedAmbientEqCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls') (args'.take arity)) := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec ls) args = source at H
  induction H generalizing ls args ls' args' with
  | base H => exact .base ((ES.symm ▸ H).compute_components heq hs hΔ HL HW HA arity)
  | @insert Γ Γ' count offset f T hΓ hΓ' W hf H ih =>
    obtain ⟨raw, Eraw, Eargs⟩ := ProofShape.liftN_const_spine_inv ES.symm
    obtain ⟨actual, rfl, Eactual⟩ := proofErase_const_spine_inv Eraw
    obtain ⟨Tc, hc⟩ := VExpr.WF.of_mkApps henv hΓ (show VExpr.WF env univs Γ _ from ⟨_, hf⟩)
    obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
    have HC : env.IsDefEqU univs Γ (.const ``Eq.rec ls) (.const ``Eq.rec ls') :=
      ⟨_, .constDF hci hw HW hl HL⟩
    have HA' : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ'))
        ((actual.map (proofErase Γ)).map (·.liftN count offset)) args' := by
      simpa only [Eargs, Eactual] using HA
    obtain ⟨actual', HP, EP, HE⟩ := proofErase_scoped_spine_arguments_descend
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hΓ' W HC hf HA'
    have HA₀ := erased_components_certificate_below (pi_inert_stage_certificate_descent heq hs n)
      hΓ hΓ' W (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 (EP ▸ HA')
    have Hlower := ih HL HW HA₀ (by simpa only [Eactual] using Eraw.symm)
    have hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec ls) actual) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (Eraw.symm.trans (proofErase_eq_proof.2 hp))
    have hn' := fun hp => hn ((isProof_congr hΓ HE).2 hp)
    have hsplit : env.HasType univs Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec ls') (actual'.take arity)) (actual'.drop arity)) T := by
      rw [← VExpr.mkApps_append, List.take_append_drop]
      exact HE.hasType.2
    obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
    have hnp := nonproof_spine_head hΓ hsplit (by
      simpa only [← VExpr.mkApps_append, List.take_append_drop] using hn')
    have Epre := proofErase_const_spine hΓ hp hnp
    have Hbase : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const ``Eq.rec ls') (actual'.take arity))) := by
      simpa only [Epre, List.map_take] using Hlower
    have Hup := IteratedAmbientEqCompletion.insert hΓ hΓ' W hp Hbase
    simpa only [Epre, ProofShape.liftN_mkApps, ProofShape.liftN, List.map_take, EP] using Hup

/-- Opening a recovered eta binder preserves iterated completion while a
target argument remains. Recovery certificates descend through each unused
insertion; the lower eta step chooses its target argument before the same
insertion is restored under the new binder. No ambient type is inhabited. -/
theorem IteratedAmbientEqCompletion.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : IteratedAmbientEqCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length < original.length)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u) :
    IteratedAmbientEqCompletion Δ v w original (rawA :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec ls) args = source at H
  induction H generalizing ls args rawA rawB u with
  | base H =>
    have HH := (ES.symm ▸ H).eta
      (erased_static_structure_eta_expansion_stage_descent heq hs stage) hΔ ht hlen RN SD
    exact .base (ES ▸ HH)
  | @insert Γ Γ' count offset f F₀ hΓ hΓ' W hf H ih =>
    obtain ⟨raw, Eraw, Eargs⟩ := ProofShape.liftN_const_spine_inv ES.symm
    obtain ⟨F, hfF, RN₀, EF⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage)
      hΓ hΓ' W hf rfl (ES ▸ RN)
    obtain ⟨_, _, EF₀, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A, B, rfl, _, ED, EC⟩ := erase_forallE_inv EF₀
    have EA' : (proofErase Γ A).liftN count offset = rawA := by simpa only [← ED] using EA
    rw [EF₀, ← ED, ← EC] at RN₀
    obtain ⟨_, hPi⟩ := hfF.isType henv hΓ
    obtain ⟨⟨_, hA₀⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA' ▸ SD).descend hΓ hΓ' W hA₀
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
      ⟨hΓ', u, hA.weakN henv W⟩
    have SD₀ := DomainSort.of_typed hΓ hA
    have hlen₀ : raw.length < original.length := by
      simpa only [Eargs, List.length_map] using hlen
    have Hlow := ih hlen₀ (Eraw ▸ RN₀) SD₀ Eraw.symm
    have hn : ¬ IsProof Γ f := by
      intro hp
      exact ProofShape.const_spine_ne_proof (Eraw.symm.trans (proofErase_eq_proof.2 hp))
    have Ebody := proofErase_eta_body hΓ hA hfF hn
    have hfw : env.HasType univs (A :: Γ) f.lift (.forallE A.lift (B.liftN 1 1)) := hfF.weak henv
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
      simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
    have Hbody : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) (.app f.lift (.bvar 0))) := by
      simpa only [proofEraseCtx, Ebody, Eraw] using Hlow
    have Hup := IteratedAmbientEqCompletion.insert hΓA hΓA' W.succ hb Hbody
    have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
      rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA']
    rw [Ebody, ProofShape.liftN, etaArgument_liftN,
      ← ProofShape.liftN_comm (proofErase Γ f) count 1 offset 0 (Nat.zero_le _)] at Hup
    simpa only [Ectx, ← ES] using Hup

/-- Reify the actual selected body-prefix history, adding target completion
at that same root. All count, path, scope, typing and minimum witnesses are
retained. The fresh-body completion is constructed by `IteratedAmbientEqCompletion.eta`. -/
theorem CountedEtaBodySpineCut.complete_iterated_root
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Γ v w original (A :: Δ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)))
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct Root) :
    CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct
      (fun m Ξ source target => Root m Ξ source target ∧ IteratedAmbientEqCompletion Γ v w original Ξ source) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, ⟨HAbody, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩ := H
  have HP' : IteratedAmbientEqCompletion Γ v w original (A :: Δ)
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u])) := by
    simpa only [ProofShape.mkApps_append, ProofShape.mkApps, List.foldl_cons, List.foldl_nil,
      ProofShape.liftN_mkApps, ProofShape.liftN] using HP
  have Hcompletion := HP'.compute_components heq hs hΓ HLbody (typed_const_levels_wf HTR) HAbody bodyPre.length
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HLbody, ⟨HAbody, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG, ?_⟩
  simpa only [List.take_left] using Hcompletion


end Lean4Lean.VEnv.Strengthening
