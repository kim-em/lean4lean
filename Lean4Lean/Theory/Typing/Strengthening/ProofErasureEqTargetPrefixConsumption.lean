import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefix

/-! # Consume eta beyond the target prefix

A supplied argument inside the target prefix uses the existing completed
consumption theorem after truncating the tail. Beyond the target length, the
completed prefix is independent of the fresh binder. Descending its component
certificates proves that its computed endpoint is still a literal lift, so
instantiating any raw argument removes that unused binder exactly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
variable [Params]

/-- Compute a completed prefix under an unused fresh binder, then instantiate
any raw argument. The component endpoints are reified below that binder and
retain lower computation certificates. Their exact lifted images make the
instantiated vector independent of the argument, without any target inhabitant
or substitution of guarded computations. -/
theorem IteratedAmbientEqCompletion.compute_lifted_components_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (SD : DomainSort Ξ A u)
    (HL : List.Forall₂ (· ≈ ·) ls ls') (HW : ∀ l ∈ ls', l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (A :: Ξ)) (args.map (·.liftN 1)) rawArgs)
    (x : ProofShape) :
    IteratedAmbientEqCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls') (rawArgs.map (·.inst x))) := by
  obtain ⟨Γ, f, F, hΓ, rfl, hf, Ef⟩ := HP.typed
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ef
  obtain ⟨A₀, hA, EA⟩ := SD.realize hΓ
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨Tc, hc⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hf⟩
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec ls) (.const ``Eq.rec ls') :=
    ⟨_, .constDF hci hw HW hl HL⟩
  have HA' : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx (A₀ :: Γ)))
      ((actual.map (proofErase Γ)).map (·.liftN 1)) rawArgs := by
    simpa only [proofEraseCtx, EA, ← Eargs] using HA
  obtain ⟨actual', _, EP, _⟩ := proofErase_scoped_spine_arguments_descend
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ hΓA Ctx.LiftN.one HC hf HA'
  have HA₀ := erased_components_certificate_below (pi_inert_stage_certificate_descent heq hs n)
    hΓ hΓA Ctx.LiftN.one (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 (EP ▸ HA')
  have HP₀ := HP.compute_components heq hs hΔ HL HW (Eargs.symm ▸ HA₀) (actual'.map (proofErase Γ)).length
  have EI : rawArgs.map (·.inst x) = actual'.map (proofErase Γ) := by
    rw [← EP, List.map_map]
    simp only [Function.comp_def, ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact List.map_id' _
  simpa only [List.take_length, EI] using HP₀

/-- Eta consumption preserves completion up to the target length without
restricting the number of actual source arguments. If the consumed argument
belongs to the target prefix, truncate the remaining tail and use completed
consumption. Otherwise descend the already completed, unused lifted prefix;
its exact component endpoints make instantiation independent of the supplied
argument. All body and argument computations stay in their original scopes. -/
theorem EqTargetPrefixCompletion.consume_eta_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Ξ A u)
    (HL : List.Forall₂ (· ≈ ·) ls bodyLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A :: Ξ))
      (pre.map (·.liftN 1) ++ [etaArgument u]) rawBody)
    (HTbody : TypedSource (A :: Ξ) (ProofShape.mkApps (.const ``Eq.rec bodyLs) rawBody))
    (RX : ScopedCompute (PiInertStage D argStage) Ξ x rawX)
    (RXS : List.Forall₂ (ScopedCompute (PiInertStage D argStage) Ξ) rest rawRest) :
    EqTargetPrefixCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec bodyLs) (rawBody.map (·.inst rawX) ++ rawRest)) := by
  have hbody : rawBody.length = pre.length+1 := by
    have HH := HA.length_eq
    simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using HH.symm
  refine ⟨bodyLs, rawBody.map (·.inst rawX) ++ rawRest, rfl, ?_⟩
  by_cases hlen : pre.length < original.length
  · have Epre : (pre ++ x :: rest).take original.length =
        pre ++ x :: rest.take (original.length-pre.length-1) := by
      rw [List.take_append, List.take_of_length_le (Nat.le_of_lt hlen), List.take_cons (by omega)]
    have HP : IteratedAmbientEqCompletion Δ v w original Ξ
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest.take (original.length-pre.length-1))) := by
      simpa only [Epre] using H.prefix
    have HH := HP.consume_eta_components heq hs hΔ ht RN SD HL HA HTbody RX
      (Lean4Lean.List.forall₂_take RXS (original.length-pre.length-1))
    have hbody' : (rawBody.map (·.inst rawX)).length ≤ original.length := by
      simp only [List.length_map, hbody]
      omega
    simpa only [List.take_append, List.take_of_length_le hbody', List.length_map, hbody,
      Nat.sub_add_eq] using HH
  · have hlen : original.length ≤ pre.length := by omega
    have HP : IteratedAmbientEqCompletion Δ v w original Ξ
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre.take original.length)) := by
      simpa only [List.take_append_of_le_length hlen] using H.prefix
    have hmap : original.length ≤ (pre.map (·.liftN 1)).length := by simpa only [List.length_map] using hlen
    have HA₀ : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A :: Ξ))
        ((pre.take original.length).map (·.liftN 1)) (rawBody.take original.length) := by
      simpa only [List.take_append_of_le_length hmap, List.map_take] using
        Lean4Lean.List.forall₂_take HA original.length
    have HH := HP.compute_lifted_components_inst heq hs hΔ SD HL (typed_const_levels_wf HTbody) HA₀ rawX
    have hbody' : original.length ≤ (rawBody.map (·.inst rawX)).length := by
      simp only [List.length_map, hbody]
      omega
    simpa only [List.take_append_of_le_length hbody', List.map_take] using HH


/-- Every finite concrete spine history preserves bounded-prefix completion.
Its eta arity bound may be unrelated to the target length: opening and consuming
beyond the target vector are both covered. This is closure of the recorded
component/eta/consumption history, not yet coverage of arbitrary wrapper bodies. -/
theorem EqSpineConsumptionHistory.target_prefix_completion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqSpineConsumptionHistory D slots Ξ source Θ out)
    (HP : EqTargetPrefixCompletion Δ v w original Ξ source) :
    EqTargetPrefixCompletion Δ v w original Θ out := by
  induction H with
  | refl => exact HP
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ HP)
  | components HL HW HA => exact HP.compute_components heq hs hΔ HL HW HA _
  | eta _ RN SD => exact HP.eta heq hs hΔ ht RN SD
  | consume RN SD HL HA HT RX RXS =>
    exact HP.consume_eta_components heq hs hΔ ht RN SD HL HA HT RX RXS

/-- A typed nonstructural head loss after a finite spine history reads the
original equation even when eta and consumption have passed the target-vector
length. Actual root typing and structure exclusion supply the short root bound;
no completion of the intervening extra arguments is assumed. -/
theorem EqSpineConsumptionHistory.read_target_prefix_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqSpineConsumptionHistory D slots Ξ source Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HP : EqTargetPrefixCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HT : TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Δ a b α :=
  (H.target_prefix_completion heq hs hΔ ht HP).read_loss heq hs hreg hoff hRec hΔ ht HT HR HN Hstruct

end Lean4Lean.VEnv.Strengthening
