import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification

/-! # Continuing reified type telescopes across argument supply

An already reified type telescope supports another whole type computation.
Supplying an ordinarily typed argument preserves the matching lambda telescope
and native family guard, so another type-history segment can run afterward.
The source checkpoints are literal typed telescopes. This does not normalize
arbitrary native recovery derivations to those checkpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A reified telescope can restart after any whole type computation. The
family expression may already be a raw partial application. Its existing lambda
path and exact guard use the same source domains; no generic-application shape
of the source body or native evidence for earlier arguments is required. -/
theorem static_structure_reified_telescope_continue
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapForalls (proofEraseDomains Γ ds) (.sort u)))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapLams (proofEraseDomains Γ ds) (proofErase (ds.reverse ++ Γ) B)))
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) out) :
    ∃ rawDs body, ds.length = rawDs.length ∧
      BetaRed out (ProofShape.wrapForalls rawDs body) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
        (ProofShape.wrapLams rawDs body) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
        (ProofShape.wrapForalls rawDs (.sort u)) := by
  obtain ⟨rawDs, body, RD, RB, Rβ⟩ := static_structure_pi_telescope_origin heq hs hΓ hT RT
  exact ⟨rawDs, body, by simpa only [proofEraseDomains_length] using RD.length_eq, Rβ,
    RF.trans (RD.wrapLams (proofEraseDomains_context ▸ RB)), RN.convert (RD.wrapForalls .refl)⟩

/-- Supply of one ordinarily typed argument preserves both sides of a reified
telescope and derives the residual type's ordinary formation. The remaining
dependent domains are instantiated together. The family expression may be raw,
and the argument has no native premise. The universe guard is well formed. -/
theorem static_structure_reified_telescope_supply
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (hT : env.IsType univs Γ (VExpr.wrapForalls (A :: ds) B))
    (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapForalls (proofEraseDomains Γ (A :: ds)) (.sort u)))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapLams (proofEraseDomains Γ (A :: ds)) (proofErase ((A :: ds).reverse ++ Γ) B))) :
    let tail := VExpr.instDomains ds x 0
    let body := B.inst x ds.length
    env.IsType univs Γ (VExpr.wrapForalls tail body) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app f (proofErase Γ x)) (ProofShape.wrapForalls (proofEraseDomains Γ tail) (.sort u)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app f (proofErase Γ x))
        (ProofShape.wrapLams (proofEraseDomains Γ tail) (proofErase (tail.reverse ++ Γ) body)) := by
  dsimp only
  obtain ⟨v, hT⟩ := hT
  obtain ⟨⟨w, hA⟩, z, hRest⟩ := hT.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  obtain ⟨hctx, q, hB⟩ := IsType.wrapForalls_inv henv hΓ ⟨v, hT⟩
  have hctx' : OnCtx (ds.reverse ++ A :: Γ) (env.IsType univs) := by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
  have hB' : env.HasType univs (ds.reverse ++ A :: Γ) B (.sort q) := by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hB
  have hRestI := hRest.instN henv.ordered Ctx.InstN.zero hx
  change env.HasType univs Γ ((VExpr.wrapForalls ds B).inst x) (.sort z) at hRestI
  simp only [VExpr.wrapForalls_inst, Nat.zero_add] at hRestI
  have hLI := (IsDefEq.etaOpen_wrapLams hΓ hctx hB).hasType.1
  have hLRI := (IsDefEq.etaOpen_wrapLams hΓA hctx' hB').hasType.1
  have hApp := HasType.app hLI hx
  change env.HasType univs Γ (.app (VExpr.wrapLams (A :: ds) B) x)
    ((VExpr.wrapForalls ds (.sort q)).inst x) at hApp
  simp only [VExpr.wrapForalls_inst, VExpr.inst] at hApp
  have RB := proofErase_beta_forward hΓ hApp
    (VExpr.BetaRed.beta (A := A) (b := VExpr.wrapLams ds B) (a := x))
  have hnApp : ¬ IsProof Γ (.app (VExpr.wrapLams (A :: ds) B) x) := by
    apply not_isProof_telescope_to_sort hΓ
    exact hApp
  rw [show proofErase Γ (.app (VExpr.wrapLams (A :: ds) B) x) =
    .app (proofErase Γ (VExpr.wrapLams (A :: ds) B)) (proofErase Γ x) from if_neg hnApp,
    proofErase_wrapLams_nonproof hctx (not_isProof_telescope_to_sort hΓ hLI)] at RB
  simp only [VExpr.wrapLams_inst, Nat.zero_add] at RB
  have hBodyI := hLRI.instN henv.ordered Ctx.InstN.zero hx
  simp only [VExpr.wrapLams_inst, VExpr.wrapForalls_inst, Nat.zero_add, VExpr.inst] at hBodyI
  have hTailCtx := (hBodyI.etaOpen_wf henv.ordered hΓ).1
  have hTargetEq := proofErase_wrapLams_nonproof hTailCtx
    (not_isProof_telescope_to_sort hΓ hBodyI)
  rw [hTargetEq] at RB
  have hGuardBody : env.IsType univs (A :: Γ) (VExpr.wrapForalls ds (.sort u)) := by
    obtain ⟨r, H⟩ := VExpr.wrapForalls_defeq hctx' (HasType.sort hu)
    exact ⟨r, H.hasType.1⟩
  have EGuard := proofErase_wrapForalls_type hΓA hGuardBody
  rw [show proofErase (ds.reverse ++ A :: Γ) (.sort u) = .sort u from
    if_neg (not_isProof_of_sort hctx' (HasType.sort hu))] at EGuard
  have RNG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f (proofErase Γ x))
      ((proofErase (A :: Γ) (VExpr.wrapForalls ds (.sort u))).inst (proofErase Γ x)) := by
    rw [EGuard]
    exact ScopedTypeRecovery.app RN
  obtain ⟨r, hGuardBody⟩ := hGuardBody
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero hGuardBody, VExpr.wrapForalls_inst] at RNG
  simp only [VExpr.inst] at RNG
  have hGuardI := hGuardBody.instN henv.ordered Ctx.InstN.zero hx
  simp only [VExpr.wrapForalls_inst, VExpr.inst] at hGuardI
  rw [proofErase_wrapForalls_type hΓ ⟨r, hGuardI⟩,
    show proofErase ((VExpr.instDomains ds x 0).reverse ++ Γ) (.sort u) = .sort u from
      if_neg (not_isProof_of_sort hTailCtx (HasType.sort hu))] at RNG
  exact ⟨⟨z, hRestI⟩, RNG, (ScopedCompute.app RF .refl).trans (.beta RB)⟩

/-- A new whole-type computation may run after an actual argument was supplied
to a reified prefix. The residual family guard and lambda history are derived,
not requested again. The intermediate checkpoint is the literal instantiated
source telescope; general opaque recovery outputs still need a normalization
argument before this theorem applies to every native recovery derivation. -/
theorem static_structure_reified_telescope_supply_continue
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (hT : env.IsType univs Γ (VExpr.wrapForalls (A :: ds) B))
    (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapForalls (proofEraseDomains Γ (A :: ds)) (.sort u)))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (ProofShape.wrapLams (proofEraseDomains Γ (A :: ds)) (proofErase ((A :: ds).reverse ++ Γ) B)))
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ ((VExpr.wrapForalls ds B).inst x)) out) :
    ∃ rawDs body, ds.length = rawDs.length ∧
      BetaRed out (ProofShape.wrapForalls rawDs body) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app f (proofErase Γ x)) (ProofShape.wrapLams rawDs body) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app f (proofErase Γ x)) (ProofShape.wrapForalls rawDs (.sort u)) := by
  obtain ⟨hTI, RNI, RFI⟩ := static_structure_reified_telescope_supply hΓ hu hT hx RN RF
  simp only [VExpr.wrapForalls_inst, Nat.zero_add] at RT
  obtain ⟨rawDs, body, hlen, Rβ, RC, RN'⟩ :=
    static_structure_reified_telescope_continue heq hs hΓ hTI RNI RFI RT
  exact ⟨rawDs, body, by simpa only [VExpr.instDomains_length] using hlen, Rβ, RC, RN'⟩

end Lean4Lean.VEnv.Strengthening
