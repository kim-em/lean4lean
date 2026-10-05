import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

/-- Primitive projections make translation deterministic for every source
expression, including headers containing projections.  Local declaration
values must agree; their typing certificates need not be identical. -/
theorem TrExprS.identity'
    (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (left : TrExprS env Us Δ₁ expression first)
    (right : TrExprS env Us Δ₂ expression second) : first = second := by
  induction left generalizing Δ₂ second with cases right
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const _ h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ _ _ ih1 ih2 =>
    cases ih1 hΔ ‹_›
    cases ih2 hΔ ‹_›
    rfl
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 =>
    cases ih1 hΔ ‹_›
    cases ih2 (hΔ.cons .vlam) ‹_›
    rfl
  | letE _ _ _ _ _ ih1 ih2 =>
    cases ih1 hΔ ‹_›
    cases ih2 (hΔ.cons .vlet) ‹_›
    rfl
  | lit _ _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ _ ih =>
    cases ih hΔ ‹_›
    exact TrProj.target_eq ‹_› |>.trans (TrProj.target_eq ‹_›).symm

theorem TrExprS.identity
    (left : TrExprS env Us Δ expression first)
    (right : TrExprS env Us Δ expression second) : first = second :=
  left.identity' .base right

end Lean4Lean
