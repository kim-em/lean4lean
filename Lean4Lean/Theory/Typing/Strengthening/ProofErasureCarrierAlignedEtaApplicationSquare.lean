import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaBetaSquares

/-! # Eta-body application squares without native argument images

Expanding the function before computing its body avoids transporting a body
certificate by substitution. The existing eta rule supplies the binder, and
the final beta contraction supplies the exact substituted output. Thus the
argument needs no native recovery, even at a captured assigned domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {k n m : Nat}

/-- Native eta expansion exposes the binder before body computation. At the
cost of the one eta-expansion stage, the applied short source reaches the
exact computed beta contractum without any recovery premise for its argument.
The argument and body computations may have independent finite bounds. -/
theorem native_eta_application_body_square
    (RF : ScopedTypeRecovery (ErasedEtaExpansionStage D k) Δ f (.forallE A B))
    (S : DomainSort Δ A u)
    (RB : ScopedCompute (ErasedEtaExpansionStage D n) (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) outB)
    (RX : ScopedCompute (ErasedEtaExpansionStage D m) Δ x outX) :
    ScopedCompute (ErasedEtaExpansionStage D (max (k + 1) (max n m))) Δ
      (.app f x) (outB.inst outX) ∧
      ∀ X, ProofShape.BetaRed (.app (.lam X outB) outX) (outB.inst outX) := by
  have RE : ErasedEtaExpansionStage D (k + 1) Δ f
      (.lam A (.app (f.liftN 1) (etaArgument u))) :=
    .inr (.inr (.inr (.inr (.intro RF S))))
  have RE' := erased_eta_expansion_stage_mono (Nat.le_max_left (k + 1) (max n m)) RE
  have RB' := RB.mono (Step' := ErasedEtaExpansionStage D (max (k + 1) (max n m)))
    (fun H => erased_eta_expansion_stage_mono (by omega) H)
  have RX' := RX.mono (Step' := ErasedEtaExpansionStage D (max (k + 1) (max n m)))
    (fun H => erased_eta_expansion_stage_mono (by omega) H)
  refine ⟨?_, fun _ => .beta⟩
  exact (ScopedCompute.app (.base RE') RX').trans
    ((ScopedCompute.app (.lam .refl RB') .refl).trans (.beta .beta))

/-- The same eta-body square closes over the full union directly. No finite
bound or native image is selected for the argument. -/
theorem native_eta_union_application_body_square
    (RF : ScopedTypeRecovery (ErasedEtaExpansionUnion D) Δ f (.forallE A B))
    (S : DomainSort Δ A u)
    (RB : ScopedCompute (ErasedEtaExpansionUnion D) (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) outB)
    (RX : ScopedCompute (ErasedEtaExpansionUnion D) Δ x outX) :
    ScopedCompute (ErasedEtaExpansionUnion D) Δ (.app f x) (outB.inst outX) := by
  have RE := erased_eta_expansion_union_eta (D := D) (NativeEtaExpansion.intro RF S)
  exact (ScopedCompute.app (.base RE) RX).trans
    ((ScopedCompute.app (.lam .refl RB) .refl).trans (.beta .beta))

/-- At an actual type-valued application, the raw square starts at the exact
erasure of that application. Its recovered domain may differ from the assigned
domain, and the actual argument still needs no native recovery certificate. -/
theorem proofErase_native_eta_type_application_square
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app f x) (.sort v))
    (RF : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B))
    (S : DomainSort (proofEraseCtx Γ) A u)
    (RB : ScopedCompute (ErasedEtaExpansionStage D n) (A :: proofEraseCtx Γ)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) outB)
    (RX : ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ)
      (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionStage D (max (k + 1) (max n m))) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (outB.inst outX) := by
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg (not_isProof_of_sort hΓ ht)]
  exact (native_eta_application_body_square RF S RB RX).1

end Lean4Lean.VEnv.Strengthening
