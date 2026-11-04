import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSubstitution

/-! # Typed terminal images for recovery transport

A type, or a value at a rigid type having no projections, cannot be used as a
function or as a structure projection major. Recovery transport can therefore
stop at such images without recovering their assigned type syntactically.
No termination, canonical-form, or native-recovery premise is imposed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Typed images which cannot occur at either elimination position inspected
by native recovery. `data` excludes projection-bearing types explicitly. -/
inductive TerminalImage (Γ : List VExpr) (e : VExpr) : Prop
  | type : env.HasType univs Γ e (.sort u) → TerminalImage Γ e
  | data : env.HasType univs Γ e (VExpr.mkApps (.const c ls) args) →
      env.Rigid c → (∀ info, ¬ env.projections c info) → TerminalImage Γ e

/-- Actual typed substitution preserves a terminal image. -/
theorem TerminalImage.subst (H : TerminalImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    TerminalImage Γ₀ (e.subst σ) := by
  cases H with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | data h hr hn =>
    have hh := h.subst henv.orderedStrong W hΓ₀
    simp only [VExpr.subst_mkApps, VExpr.subst_const] at hh
    exact .data hh hr hn

/-- Replaying a source computation backwards retains terminal-image typing. -/
theorem TerminalImage.back (H : TerminalImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    TerminalImage Γ e := by
  cases H with
  | type h => exact .type (HE.toU.of_r henv hΓ h).hasType.1
  | data h hr hn => exact .data (HE.toU.of_r henv hΓ h).hasType.1 hr hn

/-- A terminal image cannot have a Pi type, even by conversion. -/
theorem TerminalImage.not_function (H : TerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  cases H with
  | type h => exact (h.uniqU henv hΓ hf).sort_forallE_inv henv hΓ
  | data h hr _ =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ hr
      ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)

/-- A terminal image cannot have any registered projection type. Rigid-head
injectivity forces a competing projection owner to be the excluded owner. -/
theorem TerminalImage.not_structure (H : TerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args)) : False := by
  cases H with
  | type h =>
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      ((h.uniqU henv hΓ ht).typeChain henv hΓ
        (HasType.sort (h.isType henv hΓ |>.choose_spec.sort_inv henv)))
  | data h hr hn =>
    obtain ⟨_, hC⟩ := h.isType henv hΓ
    obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ hr (henv.projectionRigid hi)
      ((h.uniqU henv hΓ ht).typeChain henv hΓ hC)
    subst E
    exact hn _ hi

end Lean4Lean.VEnv.Strengthening
