import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDemandSpineReadout

/-! # Neutral type-head exposure along dependent telescopes

The head has a telescope ending in a universe. Parameter domains and supplied
arguments are unrestricted. Full enriched computation retains the head and
arity; it may compute the retained arguments instead of returning them.
-/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- A literal dependent telescope ending in a universe, with arbitrary domains. -/
inductive SortTelescope : Nat → VExpr → Prop where
  | sort : SortTelescope 0 (.sort u)
  | forallE : SortTelescope n B → SortTelescope (n+1) (.forallE A B)

variable [Params]

/-- Every typed universe-ending telescope has the profile that ignores its
parameter domains. Those domains may depend on preceding parameters. -/
theorem Fits.of_sortTelescope (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ T (.sort u)) (H : SortTelescope n T) :
    Fits Γ T (spineProfile n) := by
  induction H generalizing Γ u with
  | sort => exact ⟨⟨_, ht⟩, _, ht.toU⟩
  | forallE H ih =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    exact ⟨⟨_, ht⟩, _, _, ht.toU, ⟨v, hA⟩, ih hΓA hB⟩

/-- Applying a typed telescope discharges the ignored demands one by one.
Only ordinary argument typing is used, including at proof and data parameters. -/
theorem Obs.telescope (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (HP : Fits Γ T (spineProfile args.length))
    (HW : InstForallsC env univs Γ T args result)
    (H : Obs (proofEraseCtx Γ) S (proofErase Γ f)
      (spineProfile args.length) (spineDemand args.length)) :
    Obs (proofEraseCtx Γ) S (proofErase Γ (VExpr.mkApps f args)) .sort .pi := by
  induction HW generalizing f with
  | nil => exact H
  | @cons a A args result B ha HW ih =>
    obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
    obtain ⟨u, hA⟩ := HA.isType
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
    have HPI : Fits Γ (B.inst a) (spineProfile args.length) := by
      simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
    have hfa := HasType.app hf ha
    have E : proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a) :=
      if_neg (HPI.not_isProof hΓ (spineDemand_valid args.length).visible hfa)
    have HT : Typing (proofEraseCtx Γ) (.app (proofErase Γ f) (proofErase Γ a))
        (spineProfile args.length) := ⟨Γ, _, _, hΓ, rfl, hfa, HPI, E⟩
    have HO : Obs (proofEraseCtx Γ) S (proofErase Γ (.app f a))
        (spineProfile args.length) (spineDemand args.length) := by
      rw [E]
      exact .app (keys := []) HT H (by simp)
    exact ih hfa HPI HO

/-- A full computation from a saturated neutral type application exposes the
same variable head with exactly the original number of arguments. Its dependent
parameter telescope may contain arbitrary types and proofs. The exposed argument
vector is deliberately not asserted equal to the original one. -/
theorem static_structure_neutral_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T)
    (HP : Fits Γ T (spineProfile args.length))
    (HW : InstForallsC env univs Γ T args result)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) out) :
    ∃ args', args'.length = args.length ∧ BetaRed out (ProofShape.mkApps (.bvar i) args') := by
  have E : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (HP.not_isProof hΓ (spineDemand_valid args.length).visible hf)
  have HT : Typing (proofEraseCtx Γ) (.bvar i) (spineProfile args.length) :=
    ⟨Γ, _, _, hΓ, rfl, hf, HP, E⟩
  let S : Sets := fun j p o => j = i ∧ p = spineProfile args.length ∧ o = spineDemand args.length
  have HS : S.Typed (proofEraseCtx Γ) := by
    intro j p o hj
    obtain ⟨rfl, rfl, rfl⟩ := hj
    exact HT
  have H : Obs (proofEraseCtx Γ) S (proofErase Γ (.bvar i))
      (spineProfile args.length) (spineDemand args.length) := by
    rw [E]
    exact .var HT (spineDemand_valid args.length) ⟨rfl, rfl, rfl⟩
  have HO := (H.telescope hΓ hf HP HW).static_structure_union heq hs R HS
  exact HO.head_readout (fun _ _ _ hj => ⟨hj.1, hj.2.2⟩)

/-- A literal universe-ending telescope supplies the profile in neutral-head
readout directly. No parameter native recovery or image coverage is needed. -/
theorem static_structure_neutral_telescope_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T) (HS : SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) out) :
    ∃ args', args'.length = args.length ∧ BetaRed out (ProofShape.mkApps (.bvar i) args') := by
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  exact static_structure_neutral_head_readout heq hs hΓ hf (Fits.of_sortTelescope hΓ hT HS) HW R

/-- Common native evidence against a saturated neutral type exposes a native
certificate with the same variable head and arity. Beta cleanup alone reaches
that certificate; changed parameters remain explicit in its selected spine. -/
theorem static_structure_common_neutral_native_head
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T) (HS : SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) shared) :
    ∃ args', args'.length = args.length ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        e (ProofShape.mkApps (.bvar i) args') := by
  obtain ⟨args', hlen, RB⟩ := static_structure_neutral_telescope_head_readout heq hs hΓ hf HS HW RC
  exact ⟨args', hlen, RN.convert (.beta RB)⟩

end Lean4Lean.VEnv.Strengthening.DemandProfile
