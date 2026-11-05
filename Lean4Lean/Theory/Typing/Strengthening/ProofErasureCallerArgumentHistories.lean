import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerCanonicalArgument
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares

/-! # Generic caller transformations after domain and argument computation

The caller's original native Pi permits a computation of its generic argument
to run before any raw argument is supplied. Backward binder transport lets that
generic history use a computed domain. Typed replay then runs an independent
actual-argument computation through its resulting template. The resulting
square needs no native certificate at the computed argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The caller reifies an arbitrary generic-argument computation at any raw
argument. The generic output may depend on its binder. Neither the raw supplied
argument nor its instantiated generic output needs typing or native recovery.
The caller's selected Pi and the sort of its domain are explicit guards. -/
theorem static_structure_caller_generic_argument_raw
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f (.forallE A B))
    (SD : DomainSort Δ A u)
    (RG : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ)
      (etaArgument u) generic) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x)
      (.app f (generic.inst x)) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.lam A (.app (f.liftN 1) (etaArgument u))) :=
    .base (erased_static_structure_eta_expansion_union_eta (.intro RN SD))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RG)) .refl).trans
  have RB := BetaRed.beta (A := A) (b := .app (f.liftN 1) generic) (a := x)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.subst, ProofShape.Subst.one, ProofShape.lift_subst_cons,
    ProofShape.subst_id] using RB)

/-- A caller transformation commutes with arbitrary argument computation,
even when its generic history was developed under a computed binder. All four
sides are forward paths to the same raw result. The initial caller alone needs
exact native recovery; the original and computed arguments do not. This does
not transport the caller's guard through changes to the caller itself or strip
arbitrary computations after beta has simplified the instantiated template. -/
theorem static_structure_caller_changed_domain_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (.forallE A B)))
    (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ (.app f x))
    (RG : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) (.bvar 0)) generic)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f x))
        (.app (proofErase Γ f) (generic.inst (proofErase Γ x))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app (proofErase Γ f) (generic.inst (proofErase Γ x)))
        (.app (proofErase Γ f) (generic.inst image)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (.app (proofErase Γ f) image) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app (proofErase Γ f) image) (.app (proofErase Γ f) (generic.inst image)) := by
  have hA := HAC.hasType.1
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hvC : env.HasType univs (C :: Γ) (.bvar 0) C.lift := .bvar .zero
  have RGA := proofErase_static_structure_union_compute_backward_context
    heq hs hΓ HAC RA hvC RG
  have hvA : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  obtain ⟨g, HG, EG⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hvA rfl rfl RGA
  have RI := proofErase_static_structure_compute_inst_argument heq hs hΓA HG.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HG.hasType.2, EG] at RI
  have RGO : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofErase Γ A :: proofEraseCtx Γ) (etaArgument u) generic := by
    simpa only [proofEraseCtx, proofErase_fresh_argument hΓ hA] using RGA
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ hPi)] at RN
  have SD := DomainSort.of_typed hΓ hA
  have R₁ := static_structure_caller_generic_argument_raw RN SD RGO (x := proofErase Γ x)
  have R₂ := static_structure_caller_generic_argument_raw RN SD RGO (x := image)
  rw [show proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) from if_neg hn]
  exact ⟨R₁, .app .refl RI, .app .refl RX, R₂⟩

end Lean4Lean.VEnv.Strengthening
