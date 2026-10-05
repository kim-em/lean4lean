import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.ProjectionDesugaring
import Lean4Lean.Theory.Inductive.RawShape

/-! Structural translation retains constructor skeletons even when different
projection witnesses select syntactically different case programs. -/

namespace Lean4Lean
open Lean

theorem ProjectionDesugaring.rawShape
    (H1 : ProjectionDesugaring env U Γ name index major target)
    (H2 : ProjectionDesugaring env' U' Γ' name' index' major' target') :
    VExpr.RawShapeRel target target' := by
  obtain ⟨_, _, _, rfl⟩ := H1.target_lamApp
  obtain ⟨_, _, _, rfl⟩ := H2.target_lamApp
  exact .lamApp

/-- Projection expansions have opaque heads for constructor skeletons. -/
theorem TrProj.rawShape (H1 : TrProj (env := env) (U := U) Γ name index major target)
    (H2 : TrProj (env := env') (U := U') Γ' name' index' major' target') :
    VExpr.RawShapeRel target target' := by
  rw [H1.target_eq, H2.target_eq]
  exact .proj

inductive TrExprS.RawShapeDecl : VLocalDecl → VLocalDecl → Prop
  | vlam : RawShapeDecl (.vlam ty) (.vlam ty')
  | vlet : VExpr.RawShapeRel val val' → RawShapeDecl (.vlet ty val) (.vlet ty' val')

inductive TrExprS.RawShapeCtx : VLCtx → VLCtx → Prop
  | base : RawShapeCtx Δ Δ
  | cons : RawShapeCtx Δ₁ Δ₂ → RawShapeDecl d₁ d₂ →
      RawShapeCtx ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem TrExprS.RawShapeCtx.find?_rel (hΔ : RawShapeCtx Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    VExpr.RawShapeRel e₁ e₂ := by
  induction hΔ generalizing v e₁ e₂ A₁ A₂ with
  | base => cases H1.symm.trans H2; exact .refl _
  | @cons _ _ _ _ ofv _ hd ih =>
    revert H1 H2
    simp [VLCtx.find?]
    split
    · rintro ⟨⟩ ⟨⟩
      cases hd with
      | vlam => exact .bvar
      | vlet h => exact h
    · simp
      rintro _ _ h1 rfl rfl _ _ h2 rfl rfl
      have h := ih h1 h2
      cases hd <;> exact h.liftN

theorem TrExprS.IsUniqueCtx.rawShape (H : IsUniqueCtx Δ₁ Δ₂) : RawShapeCtx Δ₁ Δ₂ := by
  induction H with
  | base => exact .base
  | cons _ hd ih =>
    cases hd with
    | vlam => exact .cons ih .vlam
    | vlet => exact .cons ih (.vlet (.refl _))

/-- Two translations agree on their constructor skeleton. The context
relation permits different translated values in preceding let declarations. -/
theorem TrExprS.rawShape (hΔ : RawShapeCtx Δ₁ Δ₂)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) :
    VExpr.RawShapeRel e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_rel ‹_› ‹_›
  | fvar => exact hΔ.find?_rel ‹_› ‹_›
  | sort => exact .sort
  | const _ h => cases h.symm.trans ‹_›; exact .const
  | app _ _ _ _ ih1 ih2 => exact .app (ih1 hΔ ‹_›) (ih2 hΔ ‹_›)
  | lam => exact .lam
  | forallE _ _ _ _ _ ih => exact .forallE (ih (hΔ.cons .vlam) ‹_›)
  | letE _ _ _ _ _ ih1 ih2 =>
    exact ih2 (hΔ.cons (.vlet (ih1 hΔ ‹_›))) ‹_›
  | lit _ _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ hp => exact hp.rawShape ‹_›

end Lean4Lean
