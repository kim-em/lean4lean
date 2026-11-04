import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerCanonicalArgument

/-! # Joining neutral families through canonical caller telescopes

Head-and-arity readout followed by caller canonicalization gives a common target
for all computations from a saturated neutral family. This includes retained
proof-only structure parameters, without separate computations or native recovery
of the supplied arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every computation from a saturated neutral type application reaches the
same canonical application when its declared telescope canonicalizes. Lookup
supplies the caller's exact native type; supplied arguments need only typing. -/
theorem static_structure_neutral_canonical_telescope_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HL : Lookup Γ i T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (HC : CallerCanonicalTelescope D (proofEraseCtx Γ) (proofErase Γ T) args.length cs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (ProofShape.mkApps (.bvar i) cs) := by
  have hf : env.HasType univs Γ (.bvar i) T := .bvar HL
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  have hn := (DemandProfile.Fits.of_sortTelescope hΓ hT HT).not_isProof
    hΓ (DemandProfile.spineDemand_valid args.length).visible hf
  have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ HL hn ScopedCompute.refl
  rw [EF] at RN
  obtain ⟨rawArgs, hlen, RB⟩ := DemandProfile.static_structure_neutral_telescope_head_readout
    heq hs hΓ hf HT HW R
  exact (ScopedCompute.beta RB).trans (HC.compute RN hlen)

/-- Arbitrary computational forks from a saturated neutral family with a
canonical caller telescope join at its fixed canonical argument vector. -/
theorem static_structure_neutral_canonical_telescope_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HL : Lookup Γ i T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (HC : CallerCanonicalTelescope D (proofEraseCtx Γ) (proofErase Γ T) args.length cs)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (ProofShape.mkApps (.bvar i) cs) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (ProofShape.mkApps (.bvar i) cs) :=
  ⟨static_structure_neutral_canonical_telescope_readout heq hs hΓ HL HT HW HC RL,
    static_structure_neutral_canonical_telescope_readout heq hs hΓ HL HT HW HC RR⟩

/-- A common native certificate against a canonicalizable neutral family
recovers the canonical assigned type. Its original supplied arguments may have
no exact native certificates and need not individually compute to canonical ones. -/
theorem static_structure_neutral_canonical_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HL : Lookup Γ i T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (HC : CallerCanonicalTelescope D (proofEraseCtx Γ) (proofErase Γ T) args.length cs)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) shared) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      e (ProofShape.mkApps (.bvar i) cs) :=
  RN.convert (static_structure_neutral_canonical_telescope_readout heq hs hΓ HL HT HW HC RC)

/-- Concrete retained-data case: every computation of F x reaches F applied
to the masked constructor when F's declared domain is a positive proof-only
structure. The domain may have arbitrary open parameters and dependent proof
fields. No normalization or native recovery of x is assumed. -/
theorem static_structure_neutral_proof_structure_canonical_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls) (hp : params.length = info.nparams)
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) params) (.sort u)) (hu : ¬ u ≈ .zero)
    (HL : Lookup Γ i (.forallE (VExpr.mkApps (.const family ls) params) (.sort v)))
    (hx : env.HasType univs Γ x (VExpr.mkApps (.const family ls) params))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar i) x)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.bvar i) (ProofShape.mkApps (.const info.ctorName ls)
        (params.map (proofErase Γ) ++ List.replicate info.numFields .proof))) := by
  have hf : env.HasType univs Γ (.bvar i)
      (.forallE (VExpr.mkApps (.const family ls) params) (.sort v)) := .bvar HL
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  obtain ⟨_, w, hV⟩ := hT.forallE_inv henv
  have hΓS : OnCtx (VExpr.mkApps (.const family ls) params :: Γ) (env.IsType univs) := ⟨hΓ, u, hS⟩
  have ES := proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)
  have ET : proofErase Γ (.forallE (VExpr.mkApps (.const family ls) params) (.sort v)) =
      .forallE (ProofShape.mkApps (.const family ls) (params.map (proofErase Γ))) (.sort v) := by
    rw [show proofErase Γ (.forallE (VExpr.mkApps (.const family ls) params) (.sort v)) =
        .forallE _ _ from if_neg (not_isProof_of_sort hΓ hT), ES]
    rw [show proofErase (VExpr.mkApps (.const family ls) params :: Γ) (.sort v) = .sort v from
      if_neg (not_isProof_of_sort hΓS hV)]
  have SD := DomainSort.of_typed hΓ hS
  rw [ES] at SD
  refine static_structure_neutral_canonical_telescope_readout
    (args := [x]) (cs := [ProofShape.mkApps (.const info.ctorName ls)
      (params.map (proofErase Γ) ++ List.replicate info.numFields ProofShape.proof)])
    heq hs hΓ HL (.forallE .sort) (.cons hx .nil) ?_ R
  rw [ET]
  exact CallerCanonicalTelescope.proof_structure hi hindices HF (by simpa using hp) SD hu .nil

end Lean4Lean.VEnv.Strengthening
