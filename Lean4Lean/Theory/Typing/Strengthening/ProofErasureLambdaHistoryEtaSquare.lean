import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaFunctionResidual

/-! # Eta peaks along a computed lambda history

The native eta branch and an arbitrary further function computation have the
same body after finite beta readout. Both annotations have forward histories
from the original written domain. Confluence at that single typed domain is
therefore enough to join the entire peak, even when the current function is a
computed control program. No original-body history or global confluence is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Native eta at any point in a lambda's computation history joins every
further function computation if forks at the original written domain join.
The local domain-fork premise is explicit and remains unproved in general.
Neither body readout with an original-body history nor exact native recovery
of control arguments is required by this reduction. -/
theorem computed_lambda_eta_square_of_domain_forks
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (joinA : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hf : env.HasType univs Γ f T)
    (R₀ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ f))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) out)
    (RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) expanded shared := by
  cases RE with
  | intro RN SD =>
    obtain ⟨C, _, d, _, RC, Rβ⟩ :=
      proofErase_static_structure_lambda_domain_readout heq hs hΓ hA hb hn (R₀.trans RF)
    have RX := proofErase_static_structure_computed_lambda_native_domain heq hs hΓ hA hb hn R₀ RN
    obtain ⟨sharedA, JC, JX⟩ := joinA RC RX
    have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
        ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
      intro Δ Δ' a b τ ⟨stage, R⟩ W
      exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage R W⟩
    obtain ⟨RL, RR⟩ := proofErase_native_eta_function_lambda_square
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_eta_expansion_union_descent heq hs)
      hrename hΓ hf RN SD (RF.trans (.beta Rβ)) JC JX
    exact ⟨.lam sharedA d, (ScopedCompute.beta Rβ).trans RL, RR⟩

/-- At the original literal lambda, the same local premise joins arbitrary
whole-function computation with native eta. The body can compute arbitrarily;
confluence is requested only at the initial annotation, a proper syntactic
subterm of the initial function. This is a local peak reduction, not a global
well-founded confluence induction or a smaller sufficient strengthening claim. -/
theorem literal_lambda_eta_square_of_domain_forks
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (joinA : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out)
    (RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) expanded shared :=
  computed_lambda_eta_square_of_domain_forks heq hs hΓ hA hb hn joinA (HasType.lam hA hb) .refl RF RE

/-- At any computed descendant of a retained lambda, every primitive root
step is either a beta-reversible control expansion or native function eta.
Opaque singleton/Eq/definition roots and structure eta cannot occur there.
This statement classifies primitive roots only, not compatible beta steps. -/
theorem computed_lambda_primitive_expansion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b)) (hf : env.HasType univs Γ f T)
    (R₀ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ f))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) (proofErase Γ f) expanded) :
    ProofShape.BetaRed expanded (proofErase Γ f) ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) expanded := by
  have H : LambdaDomainObservation.Obs D Γ (proofErase Γ A) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ (.lam A b)) .pi := by
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact .payload ⟨A, u, hA, ProofShape.liftN_zero _, .refl⟩
  have HO := H.compute heq hs hΓ R₀ hΓ (Ctx.LiftN.zero []) (HasType.lam hA hb) rfl rfl
    (fun _ _ h => h.elim)
  obtain ⟨stage, RP⟩ := RP
  generalize EE : proofErase Γ f = raw at RP HO ⊢
  induction stage with
  | zero =>
    rcases RP with (RP | RP) | RP
    · exact (HO.not_primitiveHead (erased_iota_primitive_head RP)).elim
    · cases RP with
      | sort => exact HO.not_sort.elim
      | const => exact (HO.not_primitiveHead trivial).elim
    · cases RP
      exact .inl (constantExpansion_beta _)
  | succ stage ih =>
    rcases RP with RP | RP | RP | RP | RP | RP
    · exact ih RP
    · exact (HO.not_primitiveHead RP.2.head).elim
    · exact (HO.not_primitiveHead RP.head).elim
    · cases RP with
      | intro _ =>
        exact .inl (by
          simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
            ProofShape.liftN_zero] using
            (ProofShape.BetaRed.beta (b := .bvar 0) (a := raw)))
    · exact .inr (RP.mono (fun H => ⟨stage, H⟩))
    · exact (HO.no_structure heq hs hΓ hΓ (Ctx.LiftN.zero []) hf rfl EE
        (fun _ _ h => h.elim) (RP.mono (fun H => ⟨stage, H⟩))).elim

/-- Every primitive-root versus arbitrary-computation peak along a lambda
history reduces to forks at the initial domain. Beta-root peaks and peaks inside
arbitrary contexts remain separate; this is not full local or global confluence. -/
theorem computed_lambda_primitive_square_of_domain_forks
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (joinA : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hf : env.HasType univs Γ f T)
    (R₀ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ f))
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) out)
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) (proofErase Γ f) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) expanded shared := by
  rcases computed_lambda_primitive_expansion heq hs hΓ hA hb hn hf R₀ RP with Rβ | RE
  · exact ⟨out, .refl, (ScopedCompute.beta Rβ).trans RF⟩
  · exact computed_lambda_eta_square_of_domain_forks heq hs hΓ hA hb hn joinA hf R₀ RF RE

end Lean4Lean.VEnv.Strengthening
