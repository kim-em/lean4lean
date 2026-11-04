import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeBetaResidual

/-! # Common native application from one type beta join

The function's assigned Pi path provides a codomain history. Joining its
instantiation beta fork aligns the selected native result with the assigned
result. The supplied argument requires ordinary typing only.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Common native application needs no native argument evidence if the
codomain's type-valued instantiation fork joins. This theorem leaves that one
joining law explicit and makes no assertion of common-native coverage. -/
theorem static_structure_common_application_of_type_beta_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (HJ : ∀ {out}, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) out →
      ∃ joined, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) joined ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) joined)
    (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) shared) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv henv
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RC
  obtain ⟨X, Y, ⟨A', B', _, _, _, _, _, RB⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RC
  have RF := RN.convert (.beta Rβ)
  obtain ⟨out, RX, RY⟩ := HJ RB
  refine ⟨out, ?_, RX⟩
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn]
  exact (ScopedTypeRecovery.app RF).convert RY

/-- The universal type-instantiation joining obligation discharges the
single codomain residual needed by the preceding application theorem. -/
theorem TypeInstantiationJoin.common_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) shared) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  exact static_structure_common_application_of_type_beta_join heq hs hΓ hf
    (HJ hΓ hA hB hx) hn RN RC

/-- The same application result expressed as the conditional common-native
argument interface. The function needs common evidence only when the result
is retained; ordinary proof applications discharge the interface vacuously. -/
theorem TypeInstantiationJoin.common_argument_app
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (HF : CommonNativeArgument D Γ f (.forallE A B)) :
    CommonNativeArgument D Γ (.app f x) (B.inst x) := by
  intro hn
  have hnf := not_isProof_fn hΓ hf hx hn
  obtain ⟨shared, RN, RC⟩ := HF hnf
  exact HJ.common_application heq hs hΓ hf hx hn RN RC

/-- Common native evidence propagates through a dependent literal telescope
under the type beta joining law. Every supplied argument needs ordinary typing
only; no native argument witnesses are added along the spine. -/
theorem TypeInstantiationJoin.common_argument_spine
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (HW : InstForallsC env univs Γ T args result)
    (HF : CommonNativeArgument D Γ f T) :
    CommonNativeArgument D Γ (VExpr.mkApps f args) result := by
  induction HW generalizing f with
  | nil => exact HF
  | cons hx _ ih =>
    exact ih (HasType.app hf hx) (TypeInstantiationJoin.common_argument_app heq hs HJ hΓ hf hx HF)

/-- The existing open forward-binder obligation resolves the full application
case with an arbitrary typed argument. This removes the previously required
exact native argument from that conditional application reduction; it does not
prove the forward-binder obligation itself. -/
theorem NativeForwardBinder.common_argument_app
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HB : NativeForwardBinder D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (HF : CommonNativeArgument D Γ f (.forallE A B)) :
    CommonNativeArgument D Γ (.app f x) (B.inst x) :=
  TypeInstantiationJoin.common_argument_app heq hs
    (HB.type_instantiation_join heq hs) hΓ hf hx HF

end Lean4Lean.VEnv.Strengthening
