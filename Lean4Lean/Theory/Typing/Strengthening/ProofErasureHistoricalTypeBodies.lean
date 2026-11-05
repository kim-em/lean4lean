import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInstantiationBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerDomainGuards
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification

/-! # Type-valued body histories across one changed telescope binder

The open single type-instantiation joining law transports a type history below
an arbitrary unchanged dependent prefix. One Pi packages that whole prefix;
readout extracts its body join in the new context. No sequence of intermediate
joins is composed, and no type-fork confluence premise is added.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
private theorem unchanged_telescope (ds : List ProofShape) (Δ : List ProofShape) :
    ScopedTelescopeCompute Step Δ ds ds := by
  induction ds generalizing Δ with
  | nil => exact .nil
  | cons A ds ih => exact .cons .refl (ih (A :: Δ))

/-- The single type-instantiation joining premise transports a type history
across a changed binder below any unchanged dependent prefix. The old binder
types need only ordinary equality, not forward computation. One whole Pi join
and telescope readout suffice; joining is never assumed transitive. This does
not change several independent binders or handle arbitrary data-valued bodies. -/
theorem TypeInstantiationJoin.type_compute_context_conversion_prefix
    {pre : List VExpr}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hctx : OnCtx (pre.reverse ++ A :: Γ) (env.IsType univs))
    (hB : env.HasType univs (pre.reverse ++ A :: Γ) B (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pre.reverse ++ A :: Γ)) (proofErase (pre.reverse ++ A :: Γ) B) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx (pre.reverse ++ C :: Γ)) (proofErase (pre.reverse ++ C :: Γ) B) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx (pre.reverse ++ C :: Γ)) out shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.2⟩
  have WC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  obtain ⟨w, hPi⟩ := VExpr.wrapForalls_defeq hctx hB
  have hPiC := hPi.hasType.1.defeqDFC henv WC
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (VExpr.wrapForalls pre B))
      (ProofShape.wrapForalls (proofEraseDomains (A :: Γ) pre) out) := by
    rw [proofErase_wrapForalls_type hΓA ⟨w, hPi.hasType.1⟩]
    exact (unchanged_telescope _ _).wrapForalls (proofEraseDomains_context ▸ RB)
  obtain ⟨B', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hctx hB rfl rfl RB
  obtain ⟨w', hPi'⟩ := VExpr.wrapForalls_defeq hctx HB'.hasType.2
  have hPiC' := hPi'.hasType.1.defeqDFC henv WC
  have EP : proofErase (C :: Γ) (VExpr.wrapForalls pre B') =
      ProofShape.wrapForalls (proofEraseDomains (A :: Γ) pre) out := by
    rw [← proofErase_defeqCtx hΓA WC hPi'.hasType.1,
      proofErase_wrapForalls_type hΓA ⟨w', hPi'.hasType.1⟩, EB']
  obtain ⟨joint, RL, RR⟩ := HJ.type_compute_context_conversion heq hs hΓ HAC hPi.hasType.1 RP
  rw [← EP] at RR
  obtain ⟨rawDs, body, RD, RBL, Rβ⟩ := static_structure_pi_telescope_origin
    heq hs hΓC ⟨w, hPiC⟩ RL
  obtain ⟨_, RBR⟩ := static_structure_pi_telescope_components heq hs hΓC ⟨w', hPiC'⟩
    (by simpa only [proofEraseDomains_length] using RD.length_eq) (RR.trans (.beta Rβ))
  have WFull := hPi.toU.wrapForalls_context henv hΓ WC (domains' := pre) rfl
  have EB'C : proofErase (pre.reverse ++ C :: Γ) B' = out :=
    (proofErase_defeqCtx hctx WFull HB'.hasType.2).symm.trans EB'
  rw [EB'C] at RBR
  exact ⟨body, RBL, RBR⟩

/-- Assuming the still-open type-instantiation joining law, a type-valued body
history commutes with changing one binder below any unchanged dependent prefix.
Only the caller's new domain is recovered; the old written domain need not be
recoverable and the domains need only ordinary equality. This is not transport
of arbitrary data bodies or of several independently changed binders. -/
theorem static_structure_new_domain_caller_type_body_square
    {pre : List VExpr}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hctx : OnCtx (pre.reverse ++ A :: Γ) (env.IsType univs))
    (hB : env.HasType univs (pre.reverse ++ A :: Γ) B (.sort v))
    (hf : env.HasType univs Γ f
      (.forallE (VExpr.wrapForalls (C :: pre) (.sort v)) R))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f)
      (.forallE (proofErase Γ (VExpr.wrapForalls (C :: pre) (.sort v))) selected))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pre.reverse ++ A :: Γ)) (proofErase (pre.reverse ++ A :: Γ) B) out) :
    ∃ B', env.IsDefEq univs (pre.reverse ++ A :: Γ) B B' (.sort v) ∧
      proofErase (pre.reverse ++ A :: Γ) B' = out ∧ ∃ shared,
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B)))
        (proofErase Γ (.app f (VExpr.wrapLams (C :: pre) B))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B)))
        (proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B'))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams (C :: pre) B))) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B'))) shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have hctxA : OnCtx ((A :: pre).reverse ++ Γ) (env.IsType univs) := by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
  obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hctx hB rfl rfl RB
  have HBfull : env.IsDefEq univs ((A :: pre).reverse ++ Γ) B B' (.sort v) := by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using HB
  have HL := HBfull.etaOpen_wrapLams hΓ hctxA
  have hrest := HasType.wrapLams_of hctx hB
  have HT := IsDefEq.forallEDF HAC (hrest.isType henv hΓA).choose_spec
  have hx := HT.defeq HL.hasType.1
  have hx' := HT.defeq HL.hasType.2
  have hlen : (A :: pre).length = (C :: pre).length := rfl
  have HA := telescope_annotations_defeq hΓ hx hlen
  have HA' := telescope_annotations_defeq hΓ hx' hlen
  have RA := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf RN hx hlen
  have RA' := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf RN hx' hlen
  have HC := IsDefEq.appDF hf (IsDefEq.defeqDF HT HL)
  have HCA := IsDefEq.appDF hf HA
  have HCA' := IsDefEq.appDF hf HA'
  have RL := proofErase_scoped_compute_wrapLams_eq hΓ hctxA HBfull (by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, EB] using RB)
  have hctxC := (HA.hasType.2.wrapLams_inv henv hΓ).1
  have WC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  obtain ⟨w, hPi⟩ := VExpr.wrapForalls_defeq hctx hB
  have WFull := hPi.toU.wrapForalls_context henv hΓ WC (domains' := pre) rfl
  have EB'C : proofErase (pre.reverse ++ C :: Γ) B' = out :=
    (proofErase_defeqCtx hctx WFull HB.hasType.2).symm.trans EB
  obtain ⟨body, RBL, RBR⟩ := HJ.type_compute_context_conversion_prefix heq hs hΓ HAC hctx hB RB
  have LL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapLams (C :: pre) B))
      (ProofShape.wrapLams (proofEraseDomains Γ (C :: pre)) body) := by
    rw [proofErase_wrapLams_nonproof hctxC (not_isProof_telescope_to_sort hΓ HA.hasType.2)]
    apply (unchanged_telescope _ _).wrapLams
    rw [← proofEraseDomains_context]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using RBL
  have LR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapLams (C :: pre) B'))
      (ProofShape.wrapLams (proofEraseDomains Γ (C :: pre)) body) := by
    rw [proofErase_wrapLams_nonproof hctxC (not_isProof_telescope_to_sort hΓ HA'.hasType.2)]
    apply (unchanged_telescope _ _).wrapLams
    rw [← proofEraseDomains_context]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, EB'C] using RBR
  classical
  by_cases hp : IsProof Γ (.app f (VExpr.wrapLams (A :: pre) B))
  · refine ⟨B', HB, EB, .proof, RA, ?_, ?_, ?_⟩
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
      exact .refl
    · rw [proofErase_eq_proof.2 ((isProof_congr hΓ HCA).1 hp)]
      exact .refl
    · rw [proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
      exact .refl
  have hpB' := mt (isProof_congr hΓ HC).2 hp
  have hpC := mt (isProof_congr hΓ HCA).2 hp
  have hpC' := mt (isProof_congr hΓ HCA').2 hpB'
  refine ⟨B', HB, EB, .app (proofErase Γ f)
    (ProofShape.wrapLams (proofEraseDomains Γ (C :: pre)) body), RA, ?_, ?_, RA'.trans ?_⟩
  · rw [show proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B)) = .app _ _ from if_neg hp,
      show proofErase Γ (.app f (VExpr.wrapLams (A :: pre) B')) = .app _ _ from if_neg hpB']
    exact .app .refl RL
  · rw [show proofErase Γ (.app f (VExpr.wrapLams (C :: pre) B)) = .app _ _ from if_neg hpC]
    exact .app .refl LL
  · rw [show proofErase Γ (.app f (VExpr.wrapLams (C :: pre) B')) = .app _ _ from if_neg hpC']
    exact .app .refl LR

end Lean4Lean.VEnv.Strengthening
