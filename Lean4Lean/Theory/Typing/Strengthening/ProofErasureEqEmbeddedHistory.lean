import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmbeddedCompletion

/-! # Histories retaining constructed reverse embeddings

Keep the insertion construction through component and eta execution, retained
annotation changes, and proof-valued endpoint maps at arbitrary depth.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private native_eta_body_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixExecution
variable [Params]

/-- Component computations and prefix selection preserve reverse-renaming
completion. Every component certificate is renamed at its original stage. -/
theorem EqTargetPrefixEmbedding.compute_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixEmbedding Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HL : List.Forall₂ (· ≈ ·) ls ls') (HW : ∀ l ∈ ls', l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Ξ) args args') (arity : Nat) :
    EqTargetPrefixEmbedding Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls') (args'.take arity)) := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP
  have HA' : List.Forall₂ (ScopedCompute (PiInertStage D n) Θ)
      (args.map (·.subst κ)) (args'.map (·.subst κ)) :=
    List.forall₂_map_both (fun _ _ H => H.rename (pi_inert_stage_rename heq hs n) WK.renaming) HA
  refine ⟨Θ, κ, WK, ?_⟩
  simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_take] using
    HP.compute_components heq hs hΔ HL HW HA' arity

/-- Opening native eta preserves the reverse-renaming witness at every arity.
The exact renaming extends under the recovered annotation; no extra source
argument needs a target image. -/
theorem EqTargetPrefixEmbedding.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixEmbedding Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B))
    (SD : DomainSort Ξ A u) :
    EqTargetPrefixEmbedding Δ v w original (A :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  have RN' := RN.rename (erased_static_structure_eta_expansion_stage_rename heq hs guardStage) WK.renaming
  have SD' := ContextSubstitution.sort WK.renaming.interpretation SD
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP RN'
  refine ⟨A.subst κ :: Θ, κ.lift, WK.binder, ?_⟩
  simpa only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst,
    ProofShape.subst_mkApps] using HP.eta heq hs hΔ ht RN' SD'

/-- The actual supplied eta argument and remaining tail preserve the reverse
renaming through consumption, including beyond the target prefix. Body and
argument computations are renamed in their own scopes; their literal
instantiation is the renamed actual endpoint. -/
theorem EqTargetPrefixEmbedding.consume_eta_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixEmbedding Δ v w original Ξ
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
    EqTargetPrefixEmbedding Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec bodyLs) (rawBody.map (·.inst rawX) ++ rawRest)) := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  have RN' := RN.rename (erased_static_structure_eta_expansion_stage_rename heq hs guardStage) WK.renaming
  have SD' := ContextSubstitution.sort WK.renaming.interpretation SD
  have HAmap : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A.subst κ :: Θ))
      ((pre.map (·.liftN 1) ++ [etaArgument u]).map (·.subst κ.lift)) (rawBody.map (·.subst κ.lift)) :=
    List.forall₂_map_both (fun _ _ H => H.rename (pi_inert_stage_rename heq hs bodyStage) WK.renaming.cons) HA
  have HA' : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A.subst κ :: Θ))
      ((pre.map (·.subst κ)).map (·.liftN 1) ++ [etaArgument u]) (rawBody.map (·.subst κ.lift)) := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.map_map,
      Function.comp_def, ProofShape.lift_subst_lift, etaArgument_subst] using
      HAmap
  have HT' := HTbody.subst WK.renaming.cons.interpretation
  have RX' := RX.rename (pi_inert_stage_rename heq hs argStage) WK.renaming
  have RXS' : List.Forall₂ (ScopedCompute (PiInertStage D argStage) Θ)
      (rest.map (·.subst κ)) (rawRest.map (·.subst κ)) :=
    List.forall₂_map_both (fun _ _ H => H.rename (pi_inert_stage_rename heq hs argStage) WK.renaming) RXS
  simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append,
    List.map_cons] at HP RN' HT'
  refine ⟨Θ, κ, WK, ?_⟩
  simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append,
    List.map_map, Function.comp_def, ProofShape.subst_inst] using
    HP.consume_eta_components heq hs hΔ ht RN' SD' HL HA' HT' RX' RXS'

/-- Every finite recorded component/eta/consumption history now preserves
reverse-renaming completion, including after an earlier proof endpoint.
Arbitrary endpoint scope moves are handled by the separate constructed
embedding transport theorem; non-proof consumed domains remain open. -/
theorem EqSpineConsumptionHistory.target_prefix_embedding
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqSpineConsumptionHistory D slots Ξ source Θ out)
    (HP : EqTargetPrefixEmbedding Δ v w original Ξ source) :
    EqTargetPrefixEmbedding Δ v w original Θ out := by
  induction H with
  | refl => exact HP
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ HP)
  | components HL HW HA => exact HP.compute_components heq hs hΔ HL HW HA _
  | eta _ RN SD => exact HP.eta heq hs hΔ ht RN SD
  | consume RN SD HL HA HT RX RXS =>
    exact HP.consume_eta_components heq hs hΔ ht RN SD HL HA HT RX RXS


/-- The actual first non-level Eq-spine root, with bounded reverse-renaming completion derived
from its preceding component history, up to the target length. This retains the original path endpoints,
root stage, pending arguments and count bound. The reverse-renaming witness for the full supplied
spine is also retained, so actual eta consumption can use its argument ancestry.
Following arbitrary enclosing wrapper execution remains a separate obligation. -/
def EmbeddedTargetPrefixEqSpineCut (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (n : Nat) (Δ : List ProofShape)
    (source endpoint : ProofShape) (budget : Nat) : Prop :=
  ∃ ls pre pending target cp ct, cp+1+ct ≤ budget ∧
    ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
    PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ¬ LevelPrimitive univs (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) endpoint ∧
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending))

/-- A counted computation from an actually typed Eq spine either preserves bounded completion
at its exact endpoint or encounters a prefix-completed non-level root on that same
path. Completion at the root is obtained by reifying its actual component
history, not assumed from root typing. -/
theorem EqTargetPrefixEmbedding.counted_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HTsource : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint) :
    (∃ ls' args', endpoint = ProofShape.mkApps (.const ``Eq.rec ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args' ∧
      EqTargetPrefixEmbedding Γ v w original Δ endpoint) ∨
    EmbeddedTargetPrefixEqSpineCut D Γ v w original n Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint cost := by
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls', args', EO, HL, HA⟩ | ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, HR, HN, RT⟩
  · have HT := EO ▸ HTsource.pi_inert_compute heq hs R.forget
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA args'.length
    exact .inl ⟨ls', args', EO, HL, HA, by simpa only [List.take_length, ← EO] using HH⟩
  · have HT := RP.forget.spine_cut_source_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) HTsource
    have HH := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA pre.length
    have Hfull := HP.compute_components heq hs hΓ HL (typed_const_levels_wf HT) HA (pre ++ pending).length
    exact .inr ⟨ls', pre, pending, target, cp, ct, hc, RP, HR, HN, RT,
      (by simpa only [List.take_left] using HH), (by simpa only [List.take_length] using Hfull)⟩

/-- Taking a prefix of a completed source keeps the exact current scope.
This is the zero-step case of actual component preservation. -/
theorem EqTargetPrefixEmbedding.take_prefix {D : Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending))) :
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) := by
  have HH := HP.compute_components heq hs hΓ (.rfl (fun _ _ => by rfl))
    (by
      obtain ⟨Θ, κ, _, HP⟩ := HP
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP
      exact typed_const_levels_wf HP.prefix.typed)
    (show List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) (pre ++ pending) (pre ++ pending) from
      .rfl (fun _ _ => .refl)) pre.length
  simpa only [List.take_left] using HH

/-- The actual first-beta execution either preserves reverse-renaming
completion and the full supplied arity at the consumed endpoint, or identifies
its original-scope body cut carrying the same invariant. The body component history is derived from
execution; no additional target-image agreement is assumed. -/
theorem EqTargetPrefixEmbedding.consumed_eta_spine_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body'))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) (x' :: rest')) :
    ∃ cd cb bodyStage, cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      ((∃ nextLs nextArgs,
          ProofShape.mkApps (body'.inst x') rest' = ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs ∧
          nextArgs.length = pre.length + 1 + rest.length ∧
          EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec nextLs) nextArgs)) ∨
        EmbeddedTargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  have HPpre := HP.take_prefix heq hs hΓ
  have HPbody := HPpre.eta heq hs hΓ ht RN SD
  have HTpre : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) :=
    typed_spine_head (by simpa only [ProofShape.mkApps_append] using HTwhole)
  have HTfresh := native_eta_body_typed
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) HTpre RN SD
  obtain ⟨cd, cb, bodyStage, hc, RD, RB⟩ := pi_inert_native_eta_count_body_readout heq hs
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    HTpre (.intro RN SD) RF
  refine ⟨cd, cb, bodyStage, hc, RD, RB, ?_⟩
  have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
      ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
      ProofShape.mkApps]
  rcases (ES ▸ HPbody).counted_spine_or_cut heq hs hΓ (ES ▸ HTfresh) (ES ▸ RB) with
    ⟨bodyLs, rawBody, EO, HL, HA, _⟩ | Hcut
  · have HTbody := EO ▸ HTfresh.pi_inert_compute heq hs RB.forget
    cases RX with
    | cons RX RXS =>
      have Hnext := HP.consume_eta_components heq hs hΓ ht RN SD HL HA HTbody RX.forget RXS.forget
      refine .inl ⟨bodyLs, rawBody.map (·.inst x') ++ rest', ?_, ?_, Hnext⟩
      · simp only [EO, ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
          ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append]
      · have HB := HA.length_eq
        have HX := RXS.forget.length_eq
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at HB ⊢
        omega
  · exact .inr (ES.symm ▸ Hcut)

/-- The actual first-beta execution either preserves reverse-renaming
completion at the consumed endpoint or identifies its original-scope body
cut carrying the same invariant. The body component history is derived from
execution; no additional target-image agreement is assumed. -/
theorem EqTargetPrefixEmbedding.consumed_eta_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (HTwhole : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ x :: rest)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u))) (.lam A' body'))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca (x :: rest) (x' :: rest')) :
    ∃ cd cb bodyStage, cd+cb = cf ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      ScopedComputeCount (PiInertStage D bodyStage) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' ∧
      (EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (body'.inst x') rest') ∨
        EmbeddedTargetPrefixEqSpineCut D Γ v w original bodyStage (A :: Δ)
          (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u)) body' cb) := by
  obtain ⟨cd, cb, bodyStage, hc, RD, RB, Hnext | Hcut⟩ :=
    HP.consumed_eta_spine_execution heq hs hΓ ht HTwhole RN SD RF RX
  · obtain ⟨nextLs, nextArgs, ES, _, HPnext⟩ := Hnext
    exact ⟨cd, cb, bodyStage, hc, RD, RB, .inl (ES.symm ▸ HPnext)⟩
  · exact ⟨cd, cb, bodyStage, hc, RD, RB, .inr Hcut⟩


/-- Positive singleton guards read the target through reverse renaming even
when their output retains an Eq head. Their guards transport at the same
stage before the established completion readout is applied. -/
theorem EqTargetPrefixEmbedding.read_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hrename : ∀ {Ξ Θ a b κ}, Step Ξ a b → ContextRenaming Ξ Θ κ →
      Step Θ (a.subst κ) (b.subst κ))
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixEmbedding Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HG : CarrierRecoveredSingletonPrimitive Step Ξ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
      ComputedJointPrefixPrimitive Step Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Δ a b α :=
  HP.forget.read_guard heq hstep hrename hΔ ht HG


end Lean4Lean.VEnv.Strengthening
