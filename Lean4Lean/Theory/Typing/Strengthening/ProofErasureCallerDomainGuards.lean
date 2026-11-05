import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerArgumentHistories
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHistoricalCallerBodies

/-! # Caller transformations with only the selected native domain

Generic argument transformations never inspect the caller's selected native
codomain. Requiring that codomain to equal its ordinary assigned codomain is
unnecessary. The historical body square consequently needs a native Pi with
the original argument domain, while its codomain may be arbitrary raw syntax.
The domain requirement remains; no general recovery-preservation law is proved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- The selected native domain suffices to run a generic argument computation
through a retained call. Its selected codomain is arbitrary and need not be the
erasure of the ordinary caller's assigned codomain. The supplied argument has
ordinary typing only. -/
theorem static_structure_domain_guarded_caller_generic_argument
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE (proofErase Γ A) selected))
    (RG : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.bvar 0)) generic) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (.app (proofErase Γ f) (generic.inst (proofErase Γ x))) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have RG' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofErase Γ A :: proofEraseCtx Γ) (etaArgument u) generic := by
    simpa only [proofEraseCtx, proofErase_fresh_argument hΓ hA] using RG
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn]
  exact static_structure_caller_generic_argument_raw RN (DomainSort.of_typed hΓ hA) RG'

/-- Simultaneous annotation replacement only needs the selected native
argument domain. The caller's ordinary dependent result type is retained for
typing and erasure, but no recovery at that result type is required. -/
theorem static_structure_domain_guarded_caller_telescope_annotations
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (VExpr.wrapForalls ds T) C))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE (proofErase Γ (VExpr.wrapForalls ds T)) selected))
    (hx : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f (VExpr.wrapLams written b)))
      (proofErase Γ (.app f (VExpr.wrapLams ds b))) := by
  have HE := telescope_annotations_defeq hΓ hx hlen
  have HC := IsDefEq.appDF hf HE
  classical
  by_cases hp : IsProof Γ (.app f (VExpr.wrapLams written b))
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
    exact .refl
  have hp' := mt (isProof_congr hΓ HC).2 hp
  obtain ⟨u, hT⟩ := hx.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg := generic_eta_telescope_typing hΓ hT
  have RG := static_structure_generic_eta_telescope heq hs hΓ hT
  have RC := static_structure_domain_guarded_caller_generic_argument hΓ hx hp RN RG
  have RB := proofErase_beta_forward hΓ (hg.instN henv.ordered Ctx.InstN.zero hx)
    (EtaTelescope.generic_inst_reannotate_beta hlen b)
  rw [proofErase_instN hΓT hx Ctx.InstN.zero hg] at RB
  rw [show proofErase Γ (.app f (VExpr.wrapLams ds b)) = .app _ _ from if_neg hp']
  exact RC.trans (.beta (.app .refl RB))

/-- Arbitrary old-context body computation commutes with reannotation when
only the old argument telescope is recovered exactly. The native codomain can
be unrelated raw syntax. A forward argument-type history derives the new domain
guard with that same selected codomain, and actual type equality is obtained
by replay. The old written domain is still required; this does not supply it
for a computed caller automatically or prove general type-fork joining. -/
theorem static_structure_domain_guarded_caller_body_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (written.reverse ++ Γ) (env.IsType univs))
    (hb : env.HasType univs (written.reverse ++ Γ) b T)
    (hT' : env.IsType univs Γ (VExpr.wrapForalls ds T'))
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls written T)) (proofErase Γ (VExpr.wrapForalls ds T')))
    (hlen : written.length = ds.length)
    (hf : env.HasType univs Γ f (.forallE (VExpr.wrapForalls written T) C))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f)
      (.forallE (proofErase Γ (VExpr.wrapForalls written T)) selected))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (written.reverse ++ Γ))
      (proofErase (written.reverse ++ Γ) b) out) :
    ∃ b', env.IsDefEq univs (written.reverse ++ Γ) b b' T ∧
      proofErase (written.reverse ++ Γ) b' = out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams written b)))
        (proofErase Γ (.app f (VExpr.wrapLams ds b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams written b)))
        (proofErase Γ (.app f (VExpr.wrapLams written b'))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams ds b)))
        (proofErase Γ (.app f (VExpr.wrapLams ds b'))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams written b')))
        (proofErase Γ (.app f (VExpr.wrapLams ds b'))) := by
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hctx hb rfl rfl RB
  have HL := HB.etaOpen_wrapLams hΓ hctx
  have RL := proofErase_scoped_compute_wrapLams_eq hΓ hctx HB (EB ▸ RB)
  obtain ⟨v, hT⟩ := HL.isType henv hΓ
  obtain ⟨S, HS, ES⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RT
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ HS.hasType.2 hT'.choose_spec ES).2
    (not_isProof_of_sort hΓ HS.hasType.2)
  have HT := HS.transU_l henv hΓ (HE.defeq hΓ)
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, _, hC⟩ := hPi.forallE_inv henv
  have hf' := (IsDefEq.forallEDF HT hC).defeq hf
  have RF' := RF.convert (ScopedCompute.forallE RT ScopedCompute.refl)
  have hx := HT.defeq HL.hasType.1
  have hx' := HT.defeq HL.hasType.2
  have RA := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf' RF' hx hlen
  have RA' := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf' RF' hx' hlen
  have hBack := HT.symm.defeq (telescope_annotations_defeq hΓ hx hlen).hasType.2
  have RBack := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf RF
    hBack hlen.symm
  have RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f (VExpr.wrapLams written b)))
      (proofErase Γ (.app f (VExpr.wrapLams written b'))) := by
    have HC := IsDefEq.appDF hf HL
    classical
    by_cases hp : IsProof Γ (.app f (VExpr.wrapLams written b))
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
      exact .refl
    have hp' := mt (isProof_congr hΓ HC).2 hp
    rw [show proofErase Γ (.app f (VExpr.wrapLams written b)) = .app _ _ from if_neg hp,
      show proofErase Γ (.app f (VExpr.wrapLams written b')) = .app _ _ from if_neg hp']
    exact .app .refl RL
  exact ⟨b', HB, EB, RA, RC, RBack.trans (RC.trans RA'), RA'⟩

end Lean4Lean.VEnv.Strengthening
