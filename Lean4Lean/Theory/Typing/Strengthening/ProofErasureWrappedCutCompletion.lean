import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutDevelopment

/-! # Eta component developments and unrestricted tails after discharge

Eta frames admit recursive marked developments, changed domains and independently
computed fresh arguments. Once the marked leaf has contracted, source and pivot
coincide through every remaining frame, so the whole term may compute freely.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- A completed state contains no uncontracted marked leaf. Unmarked beta
redexes and arbitrary control computations may still remain in its syntax. -/
def WrappedCut.Finished : WrappedCut → Prop
  | .cut .. => False
  | .done .. => True
  | .constant s | .identity _ s | .eta _ _ s => s.Finished

/-- Discharging the marked leaf makes both sides literally identical, even
under eta frames whose domains and fresh arguments have independently evolved. -/
theorem WrappedCut.Finished.pivot_eq [Params] {s : WrappedCut} (H : s.Finished) : s.source = s.pivot Γ x := by
  induction s with
  | cut => exact H.elim
  | done => rfl
  | constant s ih => exact congrArg constantExpansion (ih H)
  | identity A s ih => exact congrArg (ProofShape.app (.lam A (.bvar 0))) (ih H)
  | eta A argument s ih =>
    exact congrArg (fun e : ProofShape => ProofShape.lam A (.app (e.liftN 1) argument)) (ih H)

variable [Params] {D : PureObservation.Definitions}

/-- A completed state admits any full-union whole-term continuation. The
continuation may change or remove all remaining control frames. -/
theorem WrappedCut.Finished.continue {s : WrappedCut}
    (H : s.Finished)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source out) :
    WrappedCutStep D Γ A b x u B s (.done out) :=
  .synchronized_compute H.pivot_eq R

/-- An eta guard may be followed by any recursive marked development of its
function, arbitrary computation of its domain, and arbitrary computation of its
fresh argument under the new domain. No second native guard is required. -/
theorem wrapped_cut_eta_components
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      s.source (.forallE C E)) (SD : DomainSort (proofEraseCtx Γ) C v)
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B) s t)
    (RD : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) C C')
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (C' :: proofEraseCtx Γ)
      (etaArgument v) argument) :
    ReflTransGen (WrappedCutStep D Γ A b x u B) s (.eta C' argument t) := by
  have RE : ReflTransGen (WrappedCutStep D Γ A b x u B)
      (.eta C (etaArgument v) s) (.eta C (etaArgument v) t) := by
    induction R with
    | rfl => exact .rfl
    | tail _ R ih => exact .tail ih (.eta_inner R)
  have R₀ : ReflTransGen (WrappedCutStep D Γ A b x u B) s (.eta C (etaArgument v) s) :=
    .tail .rfl (.eta_expand RN SD)
  exact ((R₀.trans RE).tail (.eta_annotation RD)).tail (.eta_argument RX)

/-- After a finite marked development has discharged the cut, every full-union
continuation is reached directly from the original contractum. This covers
arbitrary computation of residual eta bodies and wrapper control functions once
the mark has disappeared; no normalization of those terms is asserted. -/
theorem native_cut_finished_development
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B)
      (.cut (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) b) t)
    (H : t.Finished)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) t.source out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out := by
  obtain ⟨_, _, RP⟩ := wrapped_cut_steps_simulate heq hs hΓ hn HR R
    (.cut (CutPivotHistory.refl hA hb hx))
  exact RP.trans (H.pivot_eq ▸ RC)

end Lean4Lean.VEnv.Strengthening
