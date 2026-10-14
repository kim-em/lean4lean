import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedProjectionSupport

/-! # Projection closure of arbitrary scoped comparison

All compatible and computational cases are visible to induction. Function eta
is excluded at a typed projection major, and recursive structure eta is consumed
by ordinary field selection at the source-derived family and index.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Any scoped major certificate projects at common original major and field
types. Recursive structure guards use their smaller field certificate; finite
paths replay and project without requiring general comparison transitivity. -/
theorem proofErase_scoped_project_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hta : env.HasType univs Γ (.proj s i a) T) (htb : env.HasType univs Γ (.proj s i b) T)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  generalize EΔ : proofEraseCtx Γ = Δ at H
  generalize Ea : proofErase Γ a = sa at H
  generalize Eb : proofErase Γ b = sb at H
  induction H generalizing a b A T with
  | leaf H =>
    cases H with
    | refl =>
      rw [← EΔ]
      exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf .refl)
    | sort H =>
      rw [← EΔ]
      exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.sort H))
    | const H =>
      rw [← EΔ]
      exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.const H))
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ hta (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ htb (Eb.trans E)).elim
  | app Hf Hx =>
    rw [← EΔ]
    exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .app Hf Hx)
  | proj H =>
    rw [← EΔ]
    exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .proj H)
  | forallE HD HB =>
    rw [← EΔ]
    exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallE HD HB)
  | forallSorted SA SA' HD SB SB' HB =>
    rw [← EΔ]
    exact proofErase_scoped_project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallSorted SA SA' HD SB SB' HB)
  | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
    exact (proofErase_projection_not_lam hΓ hta Ea).elim
  | etaBodyR => exact (proofErase_projection_not_lam hΓ htb Eb).elim
  | structFields hi hx hp hf hadm HF =>
    obtain ⟨ES, hidx⟩ := proofErase_projection_constructor_family hΓ hta hi hx hp hf Ea
    subst s
    rw [← EΔ]
    exact proofErase_scoped_structure_project hstep hprim hΓ ha hb hta hi hx hp hf hadm Ea
      (by simpa only [EΔ, Eb] using HF) hidx
  | compute Ra Rb _ ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ha EΔ
      (by simpa only [ProofShape.liftN_zero, Ea] using Ra)
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hb EΔ
      (by simpa only [ProofShape.liftN_zero, Eb] using Rb)
    simp only [ProofShape.liftN_zero] at EA EB
    have hta' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).of_l henv hΓ ht) T hta).hasType.2
    have htb' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ b b' from ⟨_, HB⟩).of_l henv hΓ ht) T htb).hasType.2
    exact .compute
      (proofErase_scoped_compute_project hΓ HA hta (by rwa [Ea, EA]))
      (proofErase_scoped_compute_project hΓ HB htb (by rwa [Eb, EB]))
      (ih HA.hasType.2 HB.hasType.2 hta' htb' EΔ EA EB)
  | symm _ ih => exact .symm (ih hb ha htb hta EΔ Eb Ea)

/-- A single original projection typing suffices. Scoped reflection constructs
the second projection's common field type before applying projection closure. -/
theorem proofErase_scoped_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_scoped_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  exact proofErase_scoped_project_typed hstep hprim hΓ ha hb ht HP.hasType.2 H

/-- Arbitrary scoped certificates project at every finite contextual prefix
stage without increasing the stage bound. -/
theorem proofErase_scoped_prefix_project
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) :=
  proofErase_scoped_project (erased_scoped_prefix_stage_descent heq hs stage)
    (fun H => .base (erased_scoped_prefix_stage_core stage (.inl (.inl H)))) hΓ ha hb ht H

end Lean4Lean.VEnv.Strengthening
