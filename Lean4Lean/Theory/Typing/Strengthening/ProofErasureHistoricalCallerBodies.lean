import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeCallerTelescopes

/-! # Running body histories through a caller's earlier telescope guard

A caller retains its original native guard when a forward type history gives
it another one. This permits a reannotated argument to return through the old
telescope, run its body history there, and acquire the new annotations again.
The resulting square operates after administrative beta has cancelled the
written prefix. It does not move a guard through a computation of the caller.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A forward domain history converts both an ordinary caller type and its
exact native guard. The dependent codomain is unchanged as syntax; its erased
representation agrees across the actual binder conversion. The old guard is
still available at the same caller. No reverse domain computation is used. -/
theorem proofErase_native_caller_domain_history
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (.forallE A B)))
    (RA : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ f (.forallE C B) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (proofErase Γ (.forallE C B)) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, v, hB⟩ := hPi.forallE_inv henv
  have H := IsDefEq.forallEDF HAC hB
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have EC := proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) hB
  refine ⟨H.defeq hf, ?_⟩
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ H.hasType.1)] at RN
  rw [show proofErase Γ (.forallE C B) = .forallE (proofErase Γ C) (proofErase (C :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ H.hasType.2), ← EC]
  exact RN.convert (.forallE RA .refl)

/-- A forward change of the caller's assigned argument telescope commutes with
an arbitrary body history under the old written telescope. Four forward paths
form a square whose target has both the new annotations and the computed body.
The difficult side starts after reannotation has already beta-cancelled the old
prefix: the caller's historical guard restores that prefix before computation.
Only the original caller has a native premise. Formation of the new assigned
type is given; its equality to the old type, the new guard, and the computed
body's typings are derived. Neither argument needs recovery.
This covers a fixed caller and a directed history of its argument type, not
arbitrary caller computations or arbitrary type-context forks. -/
theorem static_structure_historical_caller_body_square
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
      (proofErase Γ (.forallE (VExpr.wrapForalls written T) C)))
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
  obtain ⟨hf', RF'⟩ := proofErase_native_caller_domain_history hΓ HT hf RF RT
  have hx := HT.defeq HL.hasType.1
  have hx' := HT.defeq HL.hasType.2
  have RA := static_structure_native_caller_telescope_annotations heq hs hΓ hf' (fun _ => RF') hx hlen
  have RA' := static_structure_native_caller_telescope_annotations heq hs hΓ hf' (fun _ => RF') hx' hlen
  have hBack := HT.symm.defeq (telescope_annotations_defeq hΓ hx hlen).hasType.2
  have RBack := static_structure_native_caller_telescope_annotations heq hs hΓ hf (fun _ => RF)
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
