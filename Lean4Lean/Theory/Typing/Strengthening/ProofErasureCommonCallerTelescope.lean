import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerDomainGuards
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification

/-! # Reannotating arguments at a caller's changed native domain

Common type output exposes a new native argument telescope. Its annotation
paths come from the old assigned telescope, so the branch that already changed
the argument's annotations can follow those paths without recovering the old
domain at the computed caller. The branch retaining the written annotations
uses the computed caller's new domain guard. Common output is still explicit.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A literal erased Pi prefix comes from a literal actual prefix of the same
length. All erased domains and the final body's context are retained exactly.
This is syntax inversion, not exposure of an arbitrary computed type. -/
theorem proofErase_wrapForalls_inverse
    (E : proofErase Γ T = ProofShape.wrapForalls rawDs body) :
    ∃ ds B, T = VExpr.wrapForalls ds B ∧ proofEraseDomains Γ ds = rawDs ∧
      proofErase (ds.reverse ++ Γ) B = body := by
  induction rawDs generalizing Γ T with
  | nil => exact ⟨[], T, rfl, rfl, E⟩
  | cons X rawDs ih =>
    obtain ⟨A, C, rfl, _, EA, EC⟩ := erase_forallE_inv E
    obtain ⟨ds, B, rfl, ED, EB⟩ := ih EC
    refine ⟨A :: ds, B, rfl, ?_, ?_⟩
    · simp only [proofEraseDomains, EA, ED]
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using EB

/-- A whole assigned-type computation between literal telescopes computes
the annotations of any lambda with the old domains. Actual type equality and
agreement of the body's erasure in the two dependent contexts are derived.
The body is unchanged, and no native guard for this lambda is used. -/
theorem static_structure_computed_telescope_reannotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ (VExpr.wrapLams ds b) (VExpr.wrapForalls ds T))
    (hT' : env.IsType univs Γ (VExpr.wrapForalls es T'))
    (hlen : ds.length = es.length)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds T)) (proofErase Γ (VExpr.wrapForalls es T'))) :
    env.IsDefEqU univs Γ (VExpr.wrapForalls ds T) (VExpr.wrapForalls es T') ∧
      env.IsDefEq univs Γ (VExpr.wrapLams ds b) (VExpr.wrapLams es b)
        (VExpr.wrapForalls es T') ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapLams ds b)) (proofErase Γ (VExpr.wrapLams es b)) := by
  obtain ⟨v, hT⟩ := hx.isType henv hΓ
  obtain ⟨S, HS, ES⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RT
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ HS.hasType.2 hT'.choose_spec ES).2
    (not_isProof_of_sort hΓ HS.hasType.2)
  have HT := HS.transU_l henv hΓ (HE.defeq hΓ)
  have HX := telescope_annotations_defeq hΓ (HT.defeq hx) hlen
  refine ⟨HT.toU, HX, ?_⟩
  classical
  by_cases hp : IsProof Γ (VExpr.wrapLams ds b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HX).1 hp)]
    exact .refl
  have hp' := mt (isProof_congr hΓ HX).2 hp
  obtain ⟨hctx, hb⟩ := hx.wrapLams_inv henv hΓ
  have hctx' := (HX.hasType.2.wrapLams_inv henv hΓ).1
  have HC := HT.toU.wrapForalls_context henv hΓ IsDefEqCtx.zero hlen
  have EB := proofErase_defeqCtx hctx HC hb
  have RP := RT
  rw [proofErase_wrapForalls_type hΓ hT'] at RP
  obtain ⟨RD, _⟩ := static_structure_pi_telescope_components heq hs hΓ ⟨v, hT⟩
    (by simpa only [proofEraseDomains_length] using hlen) RP
  rw [proofErase_wrapLams_nonproof hctx hp, proofErase_wrapLams_nonproof hctx' hp', ← EB]
  exact RD.wrapLams .refl

/-- A common native output for a caller and its old assigned Pi exposes a new
actual argument telescope. Every annotation is allowed to change. The source
argument type computes to the new one, and the caller recovers its domain;
the selected codomain is retained as arbitrary raw syntax. No exact old-domain
recovery at the caller, type-fork joining, or native argument premise is used. -/
theorem static_structure_common_caller_telescope_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsType univs Γ (.forallE (VExpr.wrapForalls ds T) C))
    (hg : env.HasType univs Γ g U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ g) common)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (VExpr.wrapForalls ds T) C)) common) :
    ∃ es T' C' selected, ds.length = es.length ∧
      env.HasType univs Γ g (.forallE (VExpr.wrapForalls es T') C') ∧
      env.IsType univs Γ (VExpr.wrapForalls es T') ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ g) (.forallE (proofErase Γ (VExpr.wrapForalls es T')) selected) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ds T)) (proofErase Γ (VExpr.wrapForalls es T')) := by
  obtain ⟨v, hF⟩ := hF
  obtain ⟨⟨u, hA⟩, w, hC⟩ := hF.forallE_inv henv
  rw [show proofErase Γ (.forallE (VExpr.wrapForalls ds T) C) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hF)] at RT
  obtain ⟨X, Y, ⟨_, _, _, _, _, _, RA, _⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hC RT
  obtain ⟨rawDs, body, RD, _, Rclean⟩ := static_structure_pi_telescope_origin heq hs hΓ ⟨u, hA⟩ RA
  have RN' := (RN.convert (.beta Rβ)).convert (.forallE (.beta Rclean) .refl)
  obtain ⟨F', hg', EF'⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hg RN'
  obtain ⟨A', C', rfl, _, EA', _⟩ := erase_forallE_inv EF'
  obtain ⟨es, T', rfl, ED, _⟩ := proofErase_wrapForalls_inverse EA'
  obtain ⟨_, hF'⟩ := hg'.isType henv hΓ
  have hT' := (IsType.forallE_inv henv.ordered ⟨_, hF'⟩).1
  refine ⟨es, T', C', Y, ?_, hg', hT', ?_, ?_⟩
  · have HL := RD.length_eq
    simpa only [← ED, proofEraseDomains_length] using HL
  · rwa [← EA'] at RN'
  · rw [EA']
    exact RA.trans (.beta Rclean)

/-- Caller computation commutes with simultaneous argument reannotation once
the old assigned caller type and a selected native output of the computed
caller have a common computation output. All four square edges are forward.
The final telescope is derived and may differ from both earlier annotations;
the computed caller need not recover the old domain. The argument body stays
unchanged, and no individual domain joins or argument recovery are assumed.
Constructing the common type output for arbitrary caller histories, and
combining this square with old-context body histories, remain open. -/
theorem static_structure_common_caller_reannotation_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (VExpr.wrapForalls ds T) C))
    (hx : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length)
    (RNold : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE (proofErase Γ (VExpr.wrapForalls ds T)) selectedOld))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) pivot)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      pivot common)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (VExpr.wrapForalls ds T) C)) common) :
    ∃ g es, env.IsDefEq univs Γ f g (.forallE (VExpr.wrapForalls ds T) C) ∧
      proofErase Γ g = pivot ∧ ds.length = es.length ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams written b)))
        (proofErase Γ (.app f (VExpr.wrapLams ds b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams written b)))
        (proofErase Γ (.app g (VExpr.wrapLams written b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams ds b)))
        (proofErase Γ (.app g (VExpr.wrapLams es b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app g (VExpr.wrapLams written b)))
        (proofErase Γ (.app g (VExpr.wrapLams es b))) := by
  obtain ⟨g, HE, EG⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hf rfl rfl RF
  rw [← EG] at RN RF
  obtain ⟨es, T', C', selected, hlen', hg', hT', RN', RT'⟩ :=
    static_structure_common_caller_telescope_guard heq hs hΓ (hf.isType henv hΓ) HE.hasType.2 RN RT
  have hxa := (telescope_annotations_defeq hΓ hx hlen).hasType.2
  obtain ⟨HT, HA, RA⟩ := static_structure_computed_telescope_reannotation
    heq hs hΓ hxa hT' hlen' RT'
  have Rshort := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ
    hg' RN' (hx.defeqU_r henv hΓ HT) (hlen.trans hlen')
  have Rroot := static_structure_domain_guarded_caller_telescope_annotations heq hs hΓ hf RNold hx hlen
  have Rfun {x} (hx : env.HasType univs Γ x (VExpr.wrapForalls ds T)) :
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
    have Hcall := IsDefEq.appDF HE hx
    classical
    by_cases hp : IsProof Γ (.app f x)
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ Hcall).1 hp)]
      exact .refl
    have hp' := mt (isProof_congr hΓ Hcall).2 hp
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp']
    exact .app RF .refl
  have Rarg : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app g (VExpr.wrapLams ds b)))
      (proofErase Γ (.app g (VExpr.wrapLams es b))) := by
    have Hcall := IsDefEq.appDF hg' HA
    classical
    by_cases hp : IsProof Γ (.app g (VExpr.wrapLams ds b))
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ Hcall).1 hp)]
      exact .refl
    have hp' := mt (isProof_congr hΓ Hcall).2 hp
    rw [show proofErase Γ (.app g (VExpr.wrapLams ds b)) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g (VExpr.wrapLams es b)) = .app _ _ from if_neg hp']
    exact .app .refl RA
  exact ⟨g, es, HE, EG, hlen', Rroot, Rfun hx, (Rfun hxa).trans Rarg, Rshort⟩

end Lean4Lean.VEnv.Strengthening
