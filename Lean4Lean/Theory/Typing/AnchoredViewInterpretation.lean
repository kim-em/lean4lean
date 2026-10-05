import Lean4Lean.Theory.Typing.AnchoredFunctionView
import Lean4Lean.Theory.Typing.AnchoredReanchor
import Lean4Lean.Theory.Typing.AnchoredFunctionInputTerm
import Lean4Lean.Theory.Typing.AnchoredProfileViews

/-! Interpret concrete hereditary views. Recursive output/padding cases
decrease rank; composition follows proper subviews at the same rank. No
semantic producer is stored in a view or supplied by the public caller. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {n : Nat} {a b : Atom n}
    (view : AtomView env U registry Γ a b) :
    (∀ left right profile, TypeRelated env U registry Γ left right profile →
      TypeRelated env U registry Γ left right (view.mapType profile)) ∧
    (∀ left right type profile, OnCtx Γ (env.IsType U) →
      Related env U registry Γ left right type (.singleton a) profile →
      Related env U registry Γ left right type (.singleton b) (view.mapType profile)) := by
  match n, a, b, view with
  | _, _, _, .refl atom => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | _ + 1, _, _, .reanchor seed =>
    exact ⟨fun _ _ _ h => TypeRelated.reanchor henv hscoped seed h,
      fun _ _ _ _ _ h => Related.reanchor henv hscoped seed h⟩
  | _ + 1, _, _, .domainRekey path typed formation bridge =>
    exact ⟨fun _ _ _ h => TypeRelated.domainRekey henv path typed formation bridge h,
      fun _ _ _ _ _ h => Related.domainRekey henv path typed formation bridge h⟩
  | k + 1, _, _, .input forward backward =>
    have code : ∀ {Δ : List VExpr} {p q : Profile k}
        (v : ProfileView env U registry Δ p q) {l r : VExpr} {d : Profile k},
        TypeRelated env U registry Δ l r d →
          TypeRelated env U registry Δ l r (v.mapType d) := by
      intro Δ p q v l r d h
      exact v.codeMapWith (fun av _ _ _ h => (interpret henv hscoped av).1 _ _ _ h) h
    have term : ∀ {Δ : List VExpr}, OnCtx Δ (env.IsType U) →
        ∀ {p q : Profile k} (v : ProfileView env U registry Δ p q)
        {l r A : VExpr} {d : Profile k}, p.HasType d →
        Related env U registry Δ l r A p d →
          Related env U registry Δ l r A q (v.mapType d) := by
      intro Δ hΔ p q v l r A d ht h
      exact v.termMapWith henv hscoped hΔ
        (fun av _ _ _ h => (interpret henv hscoped av).1 _ _ _ h)
        (fun av _ _ _ _ h => (interpret henv hscoped av).2 _ _ _ _ hΔ h) ht h
    exact ⟨fun _ _ _ h => TypeRelated.inputView henv code term forward backward h,
      fun _ _ _ _ _ h => Related.inputView henv code term forward backward h⟩
  | _ + 2, _, _, .commutePadFn key output =>
    exact ⟨fun _ _ _ h => (h.down henv).rankShift henv,
      fun _ _ _ _ hΓ h => Related.commute_pad_fn henv hΓ h⟩
  | _ + 2, _, _, .uncommutePadFn key output =>
    exact ⟨fun _ _ _ h => (h.unshift henv key).pad henv,
      fun _ _ _ _ _ h => Related.uncommute_pad_fn henv h⟩
  | _ + 1, _, _, .fn key child =>
    constructor
    · intro left right profile h
      exact TypeRelated.outputView henv hscoped
        (fun v _ _ _ h => (interpret henv hscoped v).1 _ _ _ h) child h
    · intro left right type profile hΓ h
      exact Related.outputView henv hscoped
        (fun v _ _ _ h => (interpret henv hscoped v).1 _ _ _ h)
        (fun v _ _ _ _ hΔ h => (interpret henv hscoped v).2 _ _ _ _ hΔ h)
        hΓ child h
  | _ + 1, _, _, .pad child =>
    constructor
    · intro left right profile h
      exact TypeRelated.pad henv
        ((interpret henv hscoped child).1 _ _ _ (h.down henv))
    · intro left right type profile hΓ h
      change Related env U registry Γ left right type (Profile.singleton _).pad profile at h
      exact Related.pad henv
        ((interpret henv hscoped child).2 _ _ _ _ hΓ (Related.unpad henv hΓ h))
  | _, _, _, .trans first second =>
    constructor
    · intro left right profile h
      exact (interpret henv hscoped second).1 _ _ _
        ((interpret henv hscoped first).1 _ _ _ h)
    · intro left right type profile hΓ h
      exact (interpret henv hscoped second).2 _ _ _ _ hΓ
        ((interpret henv hscoped first).2 _ _ _ _ hΓ h)
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

theorem AtomView.codeMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {a b : Atom n} (view : AtomView env U registry Γ a b)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (view.mapType profile) :=
  (interpret henv hscoped view).1 _ _ _ h

theorem AtomView.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {a b : Atom n} (view : AtomView env U registry Γ a b)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : Related env U registry Γ left right type (.singleton a) profile) :
    Related env U registry Γ left right type (.singleton b) (view.mapType profile) :=
  (interpret henv hscoped view).2 _ _ _ _ hΓ h

end Lean4Lean.AnchoredSemantics
