import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadCompletionHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpineInstantiation

/-! # Preserve Eq argument ancestry through consumption below ambient binders

Body and argument computations remain in their original scopes. Their actual
endpoints descend below the unused block before semantic instantiation. This
retains the exact raw consumed spine and the original target completion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- Compute a completed prefix under a fresh binder and ambient unused block,
then consume the independently computed actual argument. Only actual terms
and equalities descend and instantiate. Both raw endpoints retain the block;
no guarded path or recovery certificate is substituted. -/
theorem EqPrefixSpecializationAt.compute_inst_below
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending)
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A.liftN count offset :: Γ')))
      ((pre.map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) rawPre)
    (hx : env.HasType univs Γ x A)
    (Hxy : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ))
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ') ((proofErase Γ x).liftN count offset) rawX) :
    ∃ pre' x', env.IsDefEq univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      ((pre'.map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) = rawPre ∧
      env.IsDefEq univs Γ x x' A ∧ (proofErase Γ x').liftN count offset = rawX ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original (pre'.map (·.inst x')) σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) (F.inst x') ∧
      (((pre'.map (·.inst x')).map (proofErase Γ)).map (·.liftN count offset)) =
        rawPre.map (·.inst rawX) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
    ⟨hΓ', u, hA.weakN henv W⟩
  obtain ⟨pre', HS, EP, HE⟩ := H.compute hbody hΓA hΓA' W.succ hΔ hf HC HA
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend harg hΓ hΓ' W hx rfl RX
  have Hxy' := Hxy.trans (HX.subst henv.orderedStrong (show Ctx.SubstEq env univs Δ σ σ Γ from by
    have WS := H.1
    cases WS with | cons WS _ _ => exact WS) hΔ)
  obtain ⟨HI, hf'⟩ := HS.inst hΔ HE.hasType.2 HX.hasType.2 Hxy'
  refine ⟨pre', x', HE, EP, HX, EX, HI, hf', ?_⟩
  rw [← EP, ← EX]
  simp only [List.map_map]
  apply List.map_congr_left
  intro e he
  obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓA ⟨_, HE.hasType.2⟩).2 e he
  simp only [Function.comp_def]
  rw [proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero ht]
  exact ProofShape.liftN_instN _ _ count offset 0

/-- Consume a fresh eta binder while preserving the entire tracked source
spine, including its independently computed remaining arguments. All three
histories may lie below an ambient unused block. The target binder image is derived from the shared completion. The result retains the
whole spine's original assigned type and its exact raw instantiated vector,
so another split/eta/consume step can use the same invariant. Only ordinary
semantic equalities cross the binder; raw guarded paths stay in their scopes. -/
theorem EqPrefixSpecializationAt.eta_compute_spine_inst_below
    (hbody : ErasedScopedPrimitiveDescent BodyStep)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (A.liftN count offset :: Γ')))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) rawPre)
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ') ((proofErase Γ x).liftN count offset) rawX)
    (RXS : List.Forall₂ (ScopedCompute ArgStep (proofEraseCtx Γ'))
      ((rest.map (proofErase Γ)).map (·.liftN count offset)) rawRest) :
    ∃ (pre' rest' : List VExpr) (x' : VExpr),
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original
        (pre'.map (·.inst x') ++ rest') σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x') ++ rest')) F ∧
      ((pre'.map (·.inst x') ++ rest').map (proofErase Γ)).map (·.liftN count offset) =
        rawPre.map (·.inst rawX) ++ rawRest ∧
      (pre'.map (proofErase (A :: Γ))).map (·.liftN count (offset+1)) = rawPre ∧
      (rest'.map (proofErase Γ)).map (·.liftN count offset) = rawRest ∧
      env.IsDefEq univs Γ x x' A ∧ (proofErase Γ x').liftN count offset = rawX := by
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
  obtain ⟨pre', x', HEbody, EP, HX, EX, HS, hf', EI⟩ := HEta.compute_inst_below hbody harg hΓ hΓ' W hΔ hA hb HC HA hx
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
    hΓ hΓ' W HEhead hsplit RXS
  have ER' : (rest'.map (proofErase Γ)).map (·.liftN count offset) = rawRest := ER
  have HRpre : List.Forall₂ (env.IsDefEqU univs Γ) (pre'.map (·.inst x')) (pre'.map (·.inst x')) :=
    List.Forall₂.rfl (mkApps_arguments_wf henv hΓ ⟨_, hf'⟩).2
  have Hhead : env.IsDefEqU univs Γ (.const ``Eq.rec [v'',w'']) (.const ``Eq.rec [v'',w'']) :=
    VExpr.WF.of_mkApps henv hΓ ⟨_, hf'⟩
  refine ⟨pre', rest', x', HS.append_pending.congr hΔ Hhead (HRpre.append' HR), ?_, ?_, EP, ER', HX, EX⟩
  · simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using HE
  · rw [List.map_append, List.map_append, EI, ER']

omit [Params] in
private theorem map_split_consumed {f : α → β}
    (E : actual.map f = pre ++ x :: rest) :
    ∃ pre₀ x₀ rest₀, actual = pre₀ ++ x₀ :: rest₀ ∧
      pre₀.map f = pre ∧ f x₀ = x ∧ rest₀.map f = rest := by
  induction pre generalizing actual with
  | nil =>
    cases actual with
    | nil => simp at E
    | cons a actual =>
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at E
      exact ⟨[], a, actual, rfl, rfl, E⟩
  | cons a pre ih =>
    cases actual with
    | nil => simp at E
    | cons b actual =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at E
      obtain ⟨pre₀, x₀, rest₀, rfl, EP, EX, ER⟩ := ih E.2
      exact ⟨b :: pre₀, x₀, rest₀, rfl, by simp only [List.map_cons, E.1, EP], EX, ER⟩

/-- The raw completion invariant survives an actual eta/body/argument/beta
consumption below its ambient unused binders. The consumed argument and tail
are taken from the same completed source spine, so target agreement is derived.
This covers component histories in the fresh body; arbitrary intervening
wrapped bodies still require a stronger invariant over the whole execution. -/
theorem EqHeadCompletion.consume_eta_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqHeadCompletion Δ v w original Ξ
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
    EqHeadCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec bodyLs) (rawBody.map (·.inst rawX) ++ rawRest)) := by
  obtain ⟨Γ, Γ', count, offset, v₀, w₀, actual, F, hΓ, hΓ', W, rfl, hf, hn, HP, E⟩ := H
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN] at E
  obtain ⟨_, rfl, Eargs⟩ := ProofShape.const_spine_inj E
  simp only [List.map_map] at Eargs
  obtain ⟨pre₀, x₀, rest₀, rfl, EP, EX, ER⟩ := map_split_consumed Eargs
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) pre₀) (x₀ :: rest₀)) F := by
    simpa only [VExpr.mkApps_append] using hf
  obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
  have hnp := nonproof_spine_head hΓ hsplit (by simpa only [VExpr.mkApps_append] using hn)
  have Epre : (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v₀,w₀]) pre₀)).liftN count offset =
      ProofShape.mkApps (.const ``Eq.rec [v₀,w₀]) pre := by
    rw [proofErase_const_spine hΓ hfp hnp, ProofShape.liftN_mkApps, ProofShape.liftN]
    simpa only [List.map_map] using congrArg (ProofShape.mkApps (.const ``Eq.rec [v₀,w₀])) EP
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    hΓ hΓ' W hfp (Epre.symm ▸ RN)
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨_, hA₀⟩, _, _⟩ := hPi.forallE_inv henv
  have hA := (EA ▸ SD).descend hΓ hΓ' W hA₀
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA]
  obtain ⟨v₁, w₁, rfl⟩ : ∃ v₁ w₁, bodyLs = [v₁,w₁] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  have HW := typed_const_levels_wf HTbody
  have HW₀ := typed_const_levels_wf (show TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v₀,w₀]) (pre₀.map (proofErase Γ))) from
    ⟨Γ, _, Fp, hΓ, rfl, hfp, proofErase_const_spine hΓ hfp hnp⟩)
  have HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v₀,w₀]) (.const ``Eq.rec [v₁,w₁]) :=
    ⟨_, .constDF heq.2.2.1 HW₀ HW (by rfl) HL⟩
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
  obtain ⟨σ, pending, HP⟩ := HP
  obtain ⟨pre', rest', x', HP', HE, EI, _, _, _, _⟩ := HP.eta_compute_spine_inst_below
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs bodyStage))
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs argStage))
    hΓ' W hΔ ht hf hA hfPi HC HAbody
    (by simpa only [Function.comp_def] using EX ▸ RX)
    (by simpa only [List.map_map, Function.comp_def] using ER ▸ RXS)
  have hn' := fun hp => hn ((isProof_congr hΓ HE).2 hp)
  refine ⟨Γ, Γ', count, offset, v₁, w₁, pre'.map (·.inst x') ++ rest', F,
    hΓ, hΓ', W, rfl, HE.hasType.2, hn', HP'.forget, ?_⟩
  rw [proofErase_const_spine hΓ HE.hasType.2 hn', ProofShape.liftN_mkApps, ProofShape.liftN, EI]

/-- Concrete head-spine ancestry through component computation, opening a
fresh eta binder while a target slot remains, and consuming an eta binder
with its actual source argument and tail. Constructors retain the original
scopes and raw histories; they never assume target-image agreement.
Coverage of arbitrary retained-lambda and identity-wrapper histories, and
fresh eta beyond the target vector, remains to be established separately. -/
inductive EqSpineConsumptionHistory (D : Definitions) (slots : Nat) :
    List ProofShape → ProofShape → List ProofShape → ProofShape → Prop where
  | refl : EqSpineConsumptionHistory D slots Ξ e Ξ e
  | trans : EqSpineConsumptionHistory D slots Ξ e Θ mid →
      EqSpineConsumptionHistory D slots Θ mid Ω out →
      EqSpineConsumptionHistory D slots Ξ e Ω out
  | components : List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls', l.WF univs) →
      List.Forall₂ (ScopedCompute (PiInertStage D n) Ξ) args args' →
      EqSpineConsumptionHistory D slots Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args)
        Ξ (ProofShape.mkApps (.const ``Eq.rec ls') (args'.take arity))
  | eta : args.length < slots →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B) →
      DomainSort Ξ A u →
      EqSpineConsumptionHistory D slots Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args)
        (A :: Ξ) (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u))
  | consume :
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
        (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B) →
      DomainSort Ξ A u → List.Forall₂ (· ≈ ·) ls bodyLs →
      List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A :: Ξ))
        (pre.map (·.liftN 1) ++ [etaArgument u]) rawBody →
      TypedSource (A :: Ξ) (ProofShape.mkApps (.const ``Eq.rec bodyLs) rawBody) →
      ScopedCompute (PiInertStage D argStage) Ξ x rawX →
      List.Forall₂ (ScopedCompute (PiInertStage D argStage) Ξ) rest rawRest →
      EqSpineConsumptionHistory D slots Ξ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest))
        Ξ (ProofShape.mkApps (.const ``Eq.rec bodyLs) (rawBody.map (·.inst rawX) ++ rawRest))

/-- Any finite concrete history of these forms preserves completion to the
same original vector. Unused ambient binders remain in the completion witness;
no unrelated typed context substitution is admitted as an ancestry step. -/
theorem EqSpineConsumptionHistory.completion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqSpineConsumptionHistory D original.length Ξ source Θ out)
    (HP : EqHeadCompletion Δ v w original Ξ source) :
    EqHeadCompletion Δ v w original Θ out := by
  induction H with
  | refl => exact HP
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ HP)
  | components HL HW HA => exact HP.compute_components heq hs hΔ HL HW HA _
  | eta hlen RN SD =>
    exact HP.eta (erased_static_structure_eta_expansion_stage_descent heq hs _) hΔ ht hlen RN SD
  | consume RN SD HL HA HT RX RXS =>
    exact HP.consume_eta_components heq hs hΔ ht RN SD HL HA HT RX RXS

/-- A selected head loss after any such finite ancestry history reads the
original equation, including repeated consumption under ambient unused
binders. The open coverage question is whether the concrete history leading
to the global selected root can always be represented by this relation or
by a sound extension for the remaining wrapper cases. -/
theorem EqSpineConsumptionHistory.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqSpineConsumptionHistory D 5 Ξ source Θ root)
    (HP : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HR : PiInertStage D n Θ root target) (HN : ¬ WrappedConstHead ``Eq.rec target) :
    env.IsDefEq univs Δ a b α :=
  (H.completion heq hs hΔ ht HP).read_loss heq hs hreg hoff hD hΔ ht HR HN

end Lean4Lean.VEnv.Strengthening
