import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryNativePivot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation

/-! # One historical pivot for every surrounding application spine

Native recovery of an application uses its function certificate, without an
argument certificate. Hence simultaneous transfer of all native outputs lifts
through an arbitrary spine, even when its arguments have lost native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every native output of the source is also available at the target. This is
an exact transfer of outputs, not an assertion of a computation between terms. -/
def NativeOutputTransfer (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (source target : ProofShape) : Prop :=
  ∀ out, ScopedTypeRecovery Step Δ source out → ScopedTypeRecovery Step Δ target out

/-- Transfer of all function outputs suffices under the same raw argument.
No certificate or typing of the argument is required. -/
theorem NativeOutputTransfer.app (H : NativeOutputTransfer Step Δ f g) (a : ProofShape) :
    NativeOutputTransfer Step Δ (.app f a) (.app g a) := by
  intro out RN
  obtain ⟨A, B, RF, RT⟩ := RN.app_origin
  exact (ScopedTypeRecovery.app (H _ RF)).convert RT

/-- Exact native output transfer is closed under any application spine. -/
theorem NativeOutputTransfer.mkApps (H : NativeOutputTransfer Step Δ f g) (args : List ProofShape) :
    NativeOutputTransfer Step Δ (ProofShape.mkApps f args) (ProofShape.mkApps g args) := by
  induction args using List.snoc_induction with
  | nil => exact H
  | snoc args a ih => simpa only [ProofShape.mkApps_snoc] using ih.app a

/-- The same typed pivot works for all raw application spines and every native
output selected there. Before and after paths lift with the spine. In particular,
the pivot is chosen independently of both the spine and the selected output. -/
theorem CutComponentHistory.spine_pivot_uniform
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    ∃ pivot, env.HasType univs Γ pivot (B.inst x) ∧ ∀ args,
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ (b.inst x)) args) (ProofShape.mkApps (proofErase Γ pivot) args) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ pivot) args) (ProofShape.mkApps (s.2.1.inst s.2.2) args) ∧
      NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps s.redex args) (ProofShape.mkApps (proofErase Γ pivot) args) := by
  obtain ⟨pivot, ht, RL, RR, HN⟩ := H.native_pivot_uniform heq hs hΓ hn HR
  exact ⟨pivot, ht, fun args => ⟨RL.mkApps (List.Forall₂.rfl (fun _ _ => .refl)),
    RR.mkApps (List.Forall₂.rfl (fun _ _ => .refl)), NativeOutputTransfer.mkApps HN args⟩⟩

end Lean4Lean.VEnv.Strengthening
