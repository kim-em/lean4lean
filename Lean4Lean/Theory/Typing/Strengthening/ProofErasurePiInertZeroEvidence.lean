import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPrefixEvidence

/-! # Raw stage-zero computations retain complete histories

Stage zero has ordinary core steps and constant beta expansions. Typed core
confluence joins every such path, so its certificate can be reconstructed after
arbitrary typed substitution. This also certifies computation inside arbitrary
typed consumers, independently of the source head. Positive-stage guarded paths
are not covered by this argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- A core join supplies directed interpreted computation at any requested
stage. The target need not be a forward reduct of the source: confluence joins
each fresh source residual with the retained common-output path. -/
theorem PiInertInterpret.of_core_join
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (H : ComputeJoin (ErasedLevelCore D) a b) :
    PiInertInterpret D stage .compute Δ a b := by
  refine ⟨HB, ?_⟩
  intro out R
  obtain ⟨shared, RA, RB⟩ := H
  obtain ⟨Γ, e, T, hΓ, _, ht, Ee⟩ := HA
  obtain ⟨joined, RL, RR⟩ := hc hΓ ht (Ee ▸ R) (Ee ▸ RA)
  exact ⟨joined, RL.in_pi_inert_stage, RB.trans RR⟩

/-- Both branches of an ordinary-core join substitute directly. Typed source
transport therefore gives all future interpretations without assuming any
substitution theorem for guarded computation. -/
theorem PiInertEvidence.of_core_join
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (H : ComputeJoin (ErasedLevelCore D) a b) :
    PiInertEvidence D stage .compute Δ a b :=
  ⟨PiInertInterpret.of_core_join hc HA HB H,
    fun W => PiInertInterpret.of_core_join hc (HA.subst W) (HB.subst W)
      (H.subst (fun R => erased_level_core_subst R))⟩

/-- Every raw stage-zero path from an actual typed source has an ordinary
level-core join. Expansion roots return by beta; only typed core confluence is
needed, with no separate universe-factorization or pattern assumptions. -/
theorem ProofShape.ScopedCompute.pi_inert_zero_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ a)
    (R : ScopedCompute (PiInertStage D 0) Δ a b) :
    ComputeJoin (ErasedLevelCore D) a b := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  apply proofErase_scoped_compute_core_join
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hc
    (R := R.mono (fun H => pi_inert_stage_embed H))
    (hΓ := hΓ) (ht := ht) (EΓ := EΓ) (Ee := Ee)
  intro Γ e T Δ a b H _ _ _ _
  rcases H with H | H
  · exact .of_compute (.base H)
  · exact (ComputeJoin.of_compute (.beta H.beta_back)).symm

/-- A raw stage-zero path produces a complete computation certificate, even
when its output is only raw syntax. All future substitutions and independent
core residuals are reconstructed from its join at any requested output stage. -/
theorem PiInertEvidence.stage_zero
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ a)
    (R : ScopedCompute (PiInertStage D 0) Δ a b) :
    PiInertEvidence D stage .compute Δ a b := by
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs 0
      hΓ hΓ' W ht HR.1
  have HB : TypedSource Δ b := by
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hdsc hΓ ht EΓ Ee R
    exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩
  exact .of_core_join hc HT HB (R.pi_inert_zero_core_join heq hs hc HT)

/-- Raw stage-zero computation survives arbitrary actual typed consumers.
Core joins instantiate the consumer at their shared raw argument; no head
restriction or previously supplied hereditary certificate is needed. -/
theorem pi_inert_zero_consumer_evidence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs (A :: Γ) t T)
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst a)) (proofErase Γ (t.inst b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, ha.isType henv hΓ⟩
  obtain ⟨shared, RA, RB⟩ := R.pi_inert_zero_core_join heq hs hc ⟨Γ, a, A, hΓ, rfl, ha, rfl⟩
  apply PiInertEvidence.of_core_join hc
    ⟨Γ, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero ha, rfl⟩
    ⟨Γ, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero hb, rfl⟩
  rw [proofErase_instN hΓA ha Ctx.InstN.zero ht, proofErase_instN hΓA hb Ctx.InstN.zero ht]
  exact ⟨_, RA.inst_argument level_lift _, RB.inst_argument level_lift _⟩

/-- The unit-framed lambda terminal consumes a raw stage-zero function prefix
at any head. Its application receives a complete carrier history at any chosen
stage, for every actual argument and arbitrary raw carrier endpoints. The path
recovers the required Pi typing from any original assigned source type. -/
theorem pi_inert_zero_unit_application_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F)
    (hd : env.HasType univs (C :: Γ) d (.sort u)) (hy : env.HasType univs Γ y C)
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (.lam C d)))
    (HF : RigidSortFrames family (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app f y)) a b := by
  obtain ⟨w, hC⟩ := hy.isType henv hΓ
  have htarget := HasType.lam hC hd
  have hnf : ¬ IsProof Γ f := by
    intro hp
    have HR := R
    rw [proofErase_eq_proof.2 hp] at HR
    exact (not_isProof_function_to_sort hΓ htarget) (proofErase_eq_proof.1 HR.pi_inert_proof_fixed)
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs 0
      hΓ hΓ' W ht HR.1
  have HCmp : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ (.lam C d)) := .compute R .refl (.leaf .refl)
  have HE := (proofErase_computed_joint_compare_reflect hdsc hΓ hf htarget HCmp).2 rfl hnf
    (not_isProof_function_to_sort hΓ htarget)
  have hfPi := (HE.of_r henv hΓ htarget).hasType.1
  have hsourceApp := hfPi.app hy
  have htargetApp := htarget.app hy
  have J := R.pi_inert_zero_core_join heq hs hc ⟨Γ, f, _, hΓ, rfl, hf, rfl⟩
  have EJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ (.app f y))
      (proofErase Γ (.app (.lam C d) y)) := by
    rw [show proofErase Γ (.app f y) = .app (proofErase Γ f) (proofErase Γ y)
        from if_neg (not_isProof_of_sort hΓ hsourceApp),
      show proofErase Γ (.app (.lam C d) y) =
        .app (proofErase Γ (.lam C d)) (proofErase Γ y)
        from if_neg (not_isProof_of_sort hΓ htargetApp)]
    exact J.app .refl
  exact PiInertCarrierHistory.carrier_prefix
    (PiInertEvidence.of_core_join hc ⟨Γ, _, _, hΓ, rfl, hsourceApp, rfl⟩
      ⟨Γ, _, _, hΓ, rfl, htargetApp, rfl⟩ EJ)
    (HF.unit_application_history hs hc hi hp hx hfields hD hΓ hd hy)

end Lean4Lean.VEnv.Strengthening
