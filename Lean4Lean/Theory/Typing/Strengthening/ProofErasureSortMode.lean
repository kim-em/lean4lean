import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK

/-! # Inferred comparison of sort-typed erasures

Common-mode head eta cannot apply to a sort-typed original: a lambda has a Pi
type, and a saturated structure constructor has its registered rigid family.
Typed replay preserves these exclusions through computation. Consequently the
two erased comparison modes coincide on independently sort-typed endpoints.
This is a mode-conversion theorem, not certificate completeness or transitivity.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A term with a sort type cannot retain a lambda at the root of its erasure. -/
theorem proofErase_sort_not_lam (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.sort u)) : proofErase Γ e ≠ .lam A b := by
  intro H
  obtain ⟨D, body, rfl, _, _, _⟩ := erase_lam_inv H
  obtain ⟨⟨_, hD⟩, _, hb⟩ := ht.lam_inv henv hΓ
  exact (ht.uniqU henv hΓ (HasType.lam hD hb)).sort_forallE_inv henv hΓ

/-- A saturated registered structure constructor cannot be a sort-typed term.
This excludes a structure-eta head certificate regardless of its other endpoint. -/
theorem proofErase_sort_not_structure_eta (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.sort u)) :
    ¬ ProofShape.StructureEtaHead (proofErase Γ e) m := by
  intro H
  generalize Ee : proofErase Γ e = er at H
  cases H with
  | intro hi hx hp hf _ _ =>
    obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ee
    have hlen := congrArg List.length Hargs
    simp only [List.length_append, List.length_map, hp, hf] at hlen
    have hnat := structure_constructor_family hΓ hi hx hlen.symm ht
    have HE := ht.uniqU henv hΓ hnat
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ (HasType.sort ((ht.isType henv hΓ).sort_inv henv)))

/-- Both comparison modes give an inferred-mode certificate when each endpoint
has a sort typing. The sorts need not be assumed equal. Computation intermediates
are replayed at their original sort types; no normalization is used. -/
theorem proofErase_compare_sort_infer (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ProofShape.Compare Step mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compare Step false (proofErase Γ a) (proofErase Γ b) := by
  generalize Ea : proofErase Γ a = sa at H
  generalize Eb : proofErase Γ b = sb at H
  suffices ProofShape.Compare Step false sa sb by simpa only [Ea, Eb] using this
  induction H generalizing a b u v with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA HB => exact (proofErase_sort_not_lam hΓ ha Ea).elim
  | forallE HA HB => exact .forallE HA HB
  | etaL H =>
    obtain ⟨_, _, HE, _⟩ := H.shape
    exact (proofErase_sort_not_lam hΓ ha (Ea.trans HE)).elim
  | etaR H =>
    obtain ⟨_, _, HE, _⟩ := H.shape
    exact (proofErase_sort_not_lam hΓ hb (Eb.trans HE)).elim
  | structL H => exact (proofErase_sort_not_structure_eta hΓ ha (Ea ▸ H)).elim
  | structR H => exact (proofErase_sort_not_structure_eta hΓ hb (Eb ▸ H)).elim
  | etaLams HD H => exact (proofErase_sort_not_lam hΓ ha Ea).elim
  | compute Ra Rb HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W ha
      (by simpa only [ProofShape.liftN_zero, Ea] using Ra)
    obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hb
      (by simpa only [ProofShape.liftN_zero, Eb] using Rb)
    simp only [ProofShape.liftN_zero] at EA EB
    exact .compute Ra Rb (ih HA.hasType.2 HB.hasType.2 EA EB)

/-- Sort-typed certificates have interchangeable modes at every finite recursive
K stage, without increasing the stage bound. -/
theorem proofErase_compared_K_sort_modes (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v)) :
    ProofShape.Compare (ErasedComparedKStage D stage) true (proofErase Γ a) (proofErase Γ b) ↔
    ProofShape.Compare (ErasedComparedKStage D stage) false (proofErase Γ a) (proofErase Γ b) :=
  ⟨proofErase_compare_sort_infer (erased_compared_K_stage_descent heq hs stage) hΓ ha hb,
    ProofShape.Compare.common⟩

end Lean4Lean.VEnv.Strengthening
