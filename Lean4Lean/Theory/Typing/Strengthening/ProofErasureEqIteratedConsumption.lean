import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIteratedAmbientHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAmbientConsumption

/-! # Consume eta binders through successive unused insertions

Retain the recovery, body, argument and tail certificates below every actual
insertion. Consumption then takes place below that insertion, and semantic
instantiation identifies the exact raw endpoint when it is restored.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private map_split_consumed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAmbientConsumption
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- Consume a recovered fresh eta binder after component computations, retaining
completion through any finite sequence of unused ambient insertions. The lower
body and argument certificates remain in their own contexts. Their actual
semantic endpoints identify the final instantiated spine; no native recovery
certificate is substituted across the consumed binder. Arbitrary intervening
wrapper bodies are not claimed to be component histories. -/
theorem IteratedAmbientEqCompletion.consume_eta_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : IteratedAmbientEqCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u)
    (HL : List.Forall₂ (· ≈ ·) ls bodyLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: Ξ))
      (pre.map (·.liftN 1) ++ [etaArgument u]) rawBody)
    (HTbody : TypedSource (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec bodyLs) rawBody))
    (RX : ScopedCompute (PiInertStage D argStage) Ξ x rawX)
    (RXS : List.Forall₂ (ScopedCompute (PiInertStage D argStage) Ξ) rest rawRest) :
    IteratedAmbientEqCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec bodyLs) (rawBody.map (·.inst rawX) ++ rawRest)) := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest) = source at H
  induction H generalizing ls pre x rest rawA rawB u bodyLs rawBody rawX rawRest with
  | base H => exact .base ((ES.symm ▸ H).consume_eta_components heq hs hΔ ht RN SD HL HA HTbody RX RXS)
  | @insert Γ Γ' count offset f F hΓ hΓ' W hf H ih =>
    obtain ⟨raw, Eraw, Eargs⟩ := ProofShape.liftN_const_spine_inv ES.symm
    obtain ⟨actual, rfl, Eactual⟩ := proofErase_const_spine_inv Eraw
    have Eargs' : (actual.map fun e => (proofErase Γ e).liftN count offset) = pre ++ x :: rest := by
      simpa only [Eactual, List.map_map, Function.comp_def] using Eargs.symm
    obtain ⟨pre₀, x₀, rest₀, rfl, EP, EX, ER⟩ := map_split_consumed Eargs'
    have hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec ls) (pre₀ ++ x₀ :: rest₀)) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (Eraw.symm.trans (proofErase_eq_proof.2 hp))
    have hsplit : env.HasType univs Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec ls) pre₀) (x₀ :: rest₀)) F := by
      simpa only [VExpr.mkApps_append] using hf
    obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
    have hnp := nonproof_spine_head hΓ hsplit (by simpa only [VExpr.mkApps_append] using hn)
    have Epre : (proofErase Γ (VExpr.mkApps (.const ``Eq.rec ls) pre₀)).liftN count offset =
        ProofShape.mkApps (.const ``Eq.rec ls) pre := by
      rw [proofErase_const_spine hΓ hfp hnp, ProofShape.liftN_mkApps, ProofShape.liftN]
      simpa only [List.map_map, Function.comp_def] using congrArg (ProofShape.mkApps (.const ``Eq.rec ls)) EP
    obtain ⟨Fpi, hfPi, RN₀, EF⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs guardStage)
      hΓ hΓ' W hfp rfl (Epre.symm ▸ RN)
    obtain ⟨_, _, EF₀, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A, B, rfl, _, ED, EC⟩ := erase_forallE_inv EF₀
    have EA' : (proofErase Γ A).liftN count offset = rawA := by simpa only [← ED] using EA
    rw [EF₀, ← ED, ← EC, proofErase_const_spine hΓ hfp hnp] at RN₀
    obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
    obtain ⟨⟨_, hA₀⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA' ▸ SD).descend hΓ hΓ' W hA₀
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
      ⟨hΓ', u, hA.weakN henv W⟩
    have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
      rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA']
    obtain ⟨Tc, hc⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hfp⟩
    obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
    have HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec ls) (.const ``Eq.rec bodyLs) :=
      ⟨_, .constDF hci hw (typed_const_levels_wf HTbody) hl HL⟩
    have EPbody : (pre₀.map fun e => (proofErase (A :: Γ) e.lift).liftN count (offset+1)) =
        pre.map (·.liftN 1) := by
      rw [← EP, List.map_map]
      apply List.map_congr_left
      intro e he
      obtain ⟨Te, he⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hfp⟩).2 e he
      rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one he]
      exact (ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _)).symm
    have Efresh : (proofErase (A :: Γ) (.bvar 0)).liftN count (offset+1) = etaArgument u := by
      rw [proofErase_fresh_argument hΓ hA, etaArgument_liftN]
    have HAbody : List.Forall₂
        (ScopedCompute (PiInertStage D bodyStage) (proofEraseCtx (A.liftN count offset :: Γ')))
        (((pre₀.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) rawBody := by
      simpa only [Ectx, List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        EPbody, Efresh] using HA
    have hfw : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec ls) pre₀).lift
        (.forallE A.lift (B.liftN 1 1)) := hfPi.weak henv
    have EE : VExpr.mkApps (.const ``Eq.rec ls) (pre₀.map VExpr.lift ++ [VExpr.bvar 0]) =
        .app (VExpr.mkApps (.const ``Eq.rec ls) pre₀).lift (.bvar 0) := by
      simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
        VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
    have hb : env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec ls) (pre₀.map VExpr.lift ++ [VExpr.bvar 0])) B := by
      rw [EE]
      simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
    obtain ⟨body₀, _, EBody, HEbody⟩ := proofErase_scoped_spine_arguments_descend
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs bodyStage))
      hΓA hΓA' W.succ HC hb HAbody
    have HA₀ := erased_components_certificate_below (pi_inert_stage_certificate_descent heq hs bodyStage)
      hΓA hΓA' W.succ (mkApps_arguments_wf henv hΓA ⟨_, hb⟩).2 (EBody ▸ HAbody)
    have EbodySource : proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec ls) (pre₀.map VExpr.lift ++ [VExpr.bvar 0])) =
        ProofShape.mkApps (.const ``Eq.rec ls) ((pre₀.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u]) := by
      rw [EE, proofErase_eta_body hΓ hA hfPi hnp, proofErase_const_spine hΓ hfp hnp]
      simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
        ProofShape.mkApps]
    have hnbody : ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec ls) (pre₀.map VExpr.lift ++ [VExpr.bvar 0])) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (EbodySource.symm.trans (proofErase_eq_proof.2 hp))
    have hnbody' := fun hp => hnbody ((isProof_congr hΓA HEbody).2 hp)
    have HTbody₀ : TypedSource (proofEraseCtx (A :: Γ))
        (ProofShape.mkApps (.const ``Eq.rec bodyLs) (body₀.map (proofErase (A :: Γ)))) :=
      ⟨_, _, _, hΓA, rfl, HEbody.hasType.2, proofErase_const_spine hΓA HEbody.hasType.2 hnbody'⟩
    have Eargsbody : (pre₀.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ)) =
        (pre₀.map (proofErase Γ)).map (·.liftN 1) ++ [etaArgument u] := by
      rw [List.map_append, List.map_cons, List.map_nil, proofErase_fresh_argument hΓ hA]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro e he
      obtain ⟨Te, he⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hfp⟩).2 e he
      exact proofErase_liftN hΓ hΓA Ctx.LiftN.one he
    have hsplit' : env.HasType univs Γ
        (VExpr.mkApps (.app (VExpr.mkApps (.const ``Eq.rec ls) pre₀) x₀) rest₀) F := hsplit
    obtain ⟨Tx, hfx⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit'⟩
    have hfx : env.HasType univs Γ (.app (VExpr.mkApps (.const ``Eq.rec ls) pre₀) x₀) Tx := hfx
    obtain ⟨_, _, hf₀, hx₀⟩ := hfx.app_inv henv hΓ
    have hx := argument_at_displayed_domain hΓ hf₀ hfPi hx₀
    obtain ⟨x₁, HX, RX₀, EX₁⟩ := proofErase_scoped_compute_certificate_descend
      (pi_inert_stage_certificate_descent heq hs argStage) hΓ hΓ' W hx rfl (EX ▸ RX)
    have HEinst : env.IsDefEqU univs Γ
        (.app (VExpr.mkApps (.const ``Eq.rec ls) pre₀) x₁)
        (VExpr.mkApps (.const ``Eq.rec bodyLs) (body₀.map (·.inst x₁))) := by
      have HI := (HEbody.instN henv HX.hasType.2 Ctx.InstN.zero).toU
      rw [EE] at HI
      simpa only [VExpr.inst_eq, VExpr.subst_mkApps, VExpr.subst,
        VExpr.lift_subst_cons, VExpr.Subst.cons, VExpr.subst_id] using HI
    have HEhead := (IsDefEq.appDF hfPi HX).toU.trans henv hΓ HEinst
    have RXS' : List.Forall₂ (ScopedCompute (PiInertStage D argStage) (proofEraseCtx Γ'))
        ((rest₀.map (proofErase Γ)).map (·.liftN count offset)) rawRest := by
      simpa only [List.map_map] using ER ▸ RXS
    obtain ⟨rest₁, _, ER₁, HE⟩ := proofErase_scoped_spine_arguments_descend
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs argStage))
      hΓ hΓ' W HEhead hsplit' RXS'
    have RXS₀ := erased_components_certificate_below (pi_inert_stage_certificate_descent heq hs argStage)
      hΓ hΓ' W (mkApps_arguments_wf henv hΓ ⟨_, hsplit'⟩).2 (ER₁ ▸ RXS')
    have HP₀ := ih RN₀ (DomainSort.of_typed hΓ hA) HL
      (by simpa only [proofEraseCtx, Eargsbody] using HA₀)
      (by simpa only [proofEraseCtx] using HTbody₀) RX₀ RXS₀
      (by simpa only [Eactual, List.map_append, List.map_cons] using Eraw.symm)
    have HE' : env.IsDefEq univs Γ
        (VExpr.mkApps (.const ``Eq.rec ls) (pre₀ ++ x₀ :: rest₀))
        (VExpr.mkApps (.const ``Eq.rec bodyLs) (body₀.map (·.inst x₁) ++ rest₁)) F := by
      simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using HE
    have hn' := fun hp => hn ((isProof_congr hΓ HE').2 hp)
    have EInst : (body₀.map (·.inst x₁)).map (proofErase Γ) =
        (body₀.map (proofErase (A :: Γ))).map (·.inst (proofErase Γ x₁)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro e he
      obtain ⟨Te, he⟩ := (mkApps_arguments_wf henv hΓA ⟨_, HEbody.hasType.2⟩).2 e he
      exact proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero he
    have EOut := proofErase_const_spine hΓ HE'.hasType.2 hn'
    have HPactual : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const ``Eq.rec bodyLs) (body₀.map (·.inst x₁) ++ rest₁))) := by
      simpa only [EOut, List.map_append, EInst] using HP₀
    have Hup := IteratedAmbientEqCompletion.insert hΓ hΓ' W HE'.hasType.2 HPactual
    have EInstLift : ((body₀.map (·.inst x₁)).map (proofErase Γ)).map (·.liftN count offset) =
        rawBody.map (·.inst rawX) := by
      rw [EInst, ← EBody, ← EX₁]
      simp only [List.map_map]
      apply List.map_congr_left
      intro e he
      exact ProofShape.liftN_instN _ _ count offset 0
    simpa only [EOut, ProofShape.liftN_mkApps, ProofShape.liftN,
      List.map_append, EInstLift, ER₁] using Hup

/-- Any finite concrete history of these forms preserves completion to the
same original vector. Any finite sequence of unused ambient insertions remains in the completion witness;
no unrelated typed context substitution is admitted as an ancestry step. -/
theorem EqSpineConsumptionHistory.iterated_completion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqSpineConsumptionHistory D original.length Ξ source Θ out)
    (HP : IteratedAmbientEqCompletion Δ v w original Ξ source) :
    IteratedAmbientEqCompletion Δ v w original Θ out := by
  induction H with
  | refl => exact HP
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ HP)
  | components HL HW HA => exact HP.compute_components heq hs hΔ HL HW HA _
  | eta hlen RN SD =>
    exact HP.eta heq hs hΔ ht hlen RN SD
  | consume RN SD HL HA HT RX RXS =>
    exact HP.consume_eta_components heq hs hΔ ht RN SD HL HA HT RX RXS

/-- A selected head loss after any such finite ancestry history reads the
original equation, including repeated consumption after unused
insertions at different depths. The open coverage question is whether the concrete history leading
to the global selected root can always be represented by this relation or
by a sound extension for the remaining wrapper cases. -/
theorem EqSpineConsumptionHistory.read_iterated_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqSpineConsumptionHistory D 5 Ξ source Θ root)
    (HP : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HR : PiInertStage D n Θ root target) (HN : ¬ WrappedConstHead ``Eq.rec target) :
    env.IsDefEq univs Δ a b α :=
  (H.iterated_completion heq hs hΔ ht HP).read_loss heq hs hreg hoff hD hΔ ht HR HN

end Lean4Lean.VEnv.Strengthening
