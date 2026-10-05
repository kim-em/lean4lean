import Lean4Lean.Theory.Typing.NativeCaptureTransport

namespace Lean4Lean.VEnv
open VExpr

/-- Rename every stored conversion edge into an actual extended context.
The edge's universe is unchanged; no component inversion is required. -/
theorem TypeConversion.weak'
    (henv : env.Ordered) (W : Ctx.Lift' ρ Γ Δ)
    (H : TypeConversion env U Γ A B) :
    TypeConversion env U Δ (A.lift' ρ) (B.lift' ρ) := by
  induction H with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (by simpa only [VExpr.lift'] using edge.weak' henv W)

/-- Move a codomain conversion to a domain connected by an explicit path.
Every edge retains its own universe; no sort or Pi injectivity is used. -/
theorem TypeConversion.changeDomain
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U Γ B (.sort v))
    (domains : TypeConversion env U Γ A B)
    (codomains : TypeConversion env U (B :: Γ) C D) :
    TypeConversion env U (A :: Γ) C D := by
  have domains' : TypeConversion env U (A :: Γ) A.lift B.lift := by
    clear hB codomains
    induction domains with
    | refl => exact .refl
    | tail _ edge ih => exact .tail ih (by simpa only [VExpr.liftN] using edge.weak henv)
  have W : Ctx.SubstEq env U (A :: Γ) Subst.id Subst.id (B :: Γ) := by
    refine .cons ((Ctx.SubstEq.id henv hΓ).skip henv) hB ?_
    have h := domains'.cast (show env.HasType U (A :: Γ) (.bvar 0) A.lift from .bvar .zero)
    change env.IsDefEq U (A :: Γ) (.bvar 0) (.bvar 0) (B.subst Subst.id.tail)
    rw [show B.subst Subst.id.tail = B.lift from by rw [← lift_subst, subst_id]]
    exact h
  induction codomains with
  | refl => exact .refl
  | tail _ edge ih =>
    have ht : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
    exact .tail ih (by simpa only [subst_id, subst_sort] using (edge.subst henv W ht))

/-- Dependent composition after two exposures have the same middle Pi
display. Aligning that middle display is a separate trace obligation. -/
theorem TypeConversion.composePi
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hA₁ : env.HasType U Γ A₁ (.sort u₁)) (hA₂ : env.HasType U Γ A₂ (.sort u₂))
    (domains₁₂ : TypeConversion env U Γ A₁ A₂)
    (domains₂₃ : TypeConversion env U Γ A₂ A₃)
    (codomains₁₂ : TypeConversion env U (A₁ :: Γ) B₁ B₂)
    (codomains₂₃ : TypeConversion env U (A₂ :: Γ) B₂ B₃) :
    TypeConversion env U Γ A₁ A₃ ∧
      TypeConversion env U (A₁ :: Γ) B₁ B₃ := by
  exact ⟨domains₁₂.trans domains₂₃,
    codomains₁₂.trans (changeDomain henv hΓ hA₁ hA₂ domains₁₂ codomains₂₃)⟩

end Lean4Lean.VEnv
