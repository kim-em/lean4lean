import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport

/-! # Native-output transfer under binders and function eta

Exact certificate descent removes fresh binders from the source recovery.
Transfer at the original scope and renaming then recover the same output from
the lifted pivot. The pivot may be raw and need not recover its ordinary type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Transfer of body outputs lifts through a common written lambda domain.
The resulting Pi and all its subsequent conversions remain exactly the same. -/
theorem NativeOutputTransfer.lam
    (H : NativeOutputTransfer Step (A :: Δ) b c) :
    NativeOutputTransfer Step Δ (.lam A b) (.lam A c) := by
  intro out RN
  generalize E : ProofShape.lam A b = source at RN
  induction RN with
  | lam RB => cases E; exact .lam (H _ RB)
  | convert _ RC ih => exact (ih H E).convert RC
  | bvar | sort | const | app | forallE | proj => cases E

/-- Exact source-certificate descent makes native-output transfer stable under
arbitrary typed binder insertion. Only the source needs an ordinary witness;
the target can be any raw shape having the transferred native outputs. -/
theorem NativeOutputTransfer.liftN
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (HT : WrapperTypeWitness Γ source T)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source pivot) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ') (source.liftN n k) (pivot.liftN n k) := by
  obtain ⟨e, A, ht, rfl, _⟩ := HT
  intro out RN
  obtain ⟨B, _, RB, EB⟩ := proofErase_scoped_recovery_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓ' W ht rfl RN
  have RP := H _ RB
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨stage, R⟩ WR
    exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage R WR⟩
  have RL := RP.rename hrename (ContextRenaming.of_liftN hΓ hΓ' W)
  simpa only [subst_bvar_liftN, EB] using RL

/-- A typed raw domain permits one fresh binder without selecting any ordinary
representative for the pivot. The source and all native outputs are lifted. -/
theorem NativeOutputTransfer.under_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source pivot) (SD : DomainSort (proofEraseCtx Γ) C u) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D)
      (C :: proofEraseCtx Γ) (source.liftN 1) (pivot.liftN 1) := by
  obtain ⟨A, hA, EA⟩ := SD.realize hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  simpa only [proofEraseCtx, EA] using H.liftN heq hs hΓ hΓA Ctx.LiftN.one HT

/-- Native-output transfer survives the function-eta frame, including erased
proof arguments. It transfers every later native output of the whole lambda,
not just the Pi type that licensed the original expansion. -/
theorem NativeOutputTransfer.eta_frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source pivot) (SD : DomainSort (proofEraseCtx Γ) C u) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam C (.app (source.liftN 1) (etaArgument u)))
      (.lam C (.app (pivot.liftN 1) (etaArgument u))) :=
  (NativeOutputTransfer.app (H.under_domain heq hs hΓ HT SD) (etaArgument u)).lam

end Lean4Lean.VEnv.Strengthening
