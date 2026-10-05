import Lean4Lean.Theory.Typing.AnchoredProfileViews
import Lean4Lean.Theory.Typing.AnchoredViewInterpretation

/-! Closed semantic maps for finite paired profile transformations. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {source target : Profile n}

theorem ProfileView.codeMap (view : ProfileView env U registry Γ source target)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (view.mapType profile) :=
  view.codeMapWith (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h) h

theorem ProfileView.termMap (view : ProfileView env U registry Γ source target)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (htyped : source.HasType profile)
    (h : Related env U registry Γ left right type source profile) :
    Related env U registry Γ left right type target (view.mapType profile) :=
  view.termMapWith henv hscoped hΓ (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun {_ _} v {_ _ _ _} h => v.termMap henv hscoped hΓ h) htyped h

end Lean4Lean.AnchoredSemantics
