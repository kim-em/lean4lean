import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFamilyConsumer

/-! # Inferred checking with recursively certified lambda domains

The domain certificate may relate nonjoining types. It constructs actual type
conversion and inferred lambda checks at all future beta/substitution residuals.
Applying the reannotated lambdas to joined arguments also retains inferred
checking, including the beta steps that discard the written annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A recursive common comparison reflects equality at an actual shared type.
It supplies the conversion used to move a lambda body between domain contexts. -/
theorem RecursiveFamilyCast.reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    env.IsDefEq univs Γ a b T :=
  proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ ha hb
    (.carrierChecked (H.future heq hs hregistry).base)

/-- Same-body lambda reannotation requires only a recursive domain comparison,
not an endpoint computation join. The result checks in inferred mode after
arbitrary independent beta paths and interpreted substitutions. Proof-valued
lambdas are included, and the new lambda's common Pi typing is constructed. -/
theorem recursive_lambda_annotation_future
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (HA : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ false) (proofEraseCtx Γ)
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam C b)) := by
  have HAC := HA.reflect heq hs hregistry hΓ hA hC
  have HL := IsDefEq.lamDF HAC hb
  refine ⟨HL.hasType.2, ?_⟩
  by_cases hp : IsProof Γ (.lam A b)
  · apply proofErase_beta_join_family_mode hΓ HL.hasType.1 HL.hasType.2
      (shared := proofErase Γ (.lam A b)) .refl
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact .refl
  have hpc : ¬ IsProof Γ (.lam C b) := fun H => hp ((isProof_congr hΓ HL).2 H)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EB := proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) hb
  rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hp,
    show proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b)
      from if_neg hpc, ← EB]
  exact BetaStableFamily.lam_sorted (DomainSort.of_typed hΓ hA) (DomainSort.of_typed hΓ hC)
    (HA.future heq hs hregistry) (proofErase_beta_join_family_mode hΓA hb hb .refl .refl)

/-- Applying independently annotated lambdas to recursively joined arguments
retains inferred future checking. The written domains need not join, and the
body may duplicate or apply its argument. This does not assert closure for
arbitrary consumers of a nonjoining lambda pair. -/
theorem recursive_lambda_annotation_apply_future
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HA : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C))
    (RX : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ false) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam C b) y)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨hc, _⟩ := recursive_lambda_annotation_future heq hs hregistry hΓ hA hC hb HA
  have RCX := RX.certified heq hs hregistry
  have RCY := RY.certified heq hs hregistry
  have RB := proofErase_certified_compute_inst_argument heq hs hΓA hb hx RCX
  have RC := proofErase_certified_compute_inst_argument heq hs hΓA hb hy RCY
  have HI := proofErase_certified_join_family_mode (mode := false) heq hs hΓ
    (hb.instN henv Ctx.InstN.zero hx) (hb.instN henv Ctx.InstN.zero hy) RB RC
  have hleft := HasType.app (HasType.lam hA hb) hx
  have hright := HasType.app hc hy
  exact HI.certified_prefixes_mode heq hs hΓ hleft hright
    (.beta (proofErase_beta_forward hΓ hleft .beta))
    (.beta (proofErase_beta_forward hΓ hright .beta))

/-- Every requested residual of the reannotated lambda application has an
actual finite stage in inferred mode; no uniform bound over future paths is
asserted. -/
theorem recursive_lambda_annotation_apply_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HA : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C))
    (RX : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ y) shared)
    (PL : ProofShape.BetaRed (proofErase Γ (.app (.lam A b) x)) left)
    (PR : ProofShape.BetaRed (proofErase Γ (.app (.lam C b) y)) right) :
    ∃ n, JointCompare (ErasedJointStage D n) (proofEraseCtx Γ) false left right :=
  ((recursive_lambda_annotation_apply_future heq hs hregistry hΓ hA hC hb hx hy HA RX RY).1 PL PR).finite_stage
    erased_joint_stage_mono

end Lean4Lean.VEnv.Strengthening
