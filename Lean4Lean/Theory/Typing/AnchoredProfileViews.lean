import Lean4Lean.Theory.Typing.AnchoredViewTyping
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction

/-! Interpret a finite paired profile view using the actual atomic views it
contains. These are internal rank-induction helpers: the input-view consumer
uses them one rank below its function atom. Closed wrappers live with the
completed atomic interpreter, so no interpreter is imported here. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}

theorem ProfileView.codeMapWith {source target : Profile n}
    (view : ProfileView env U registry Γ source target)
    (code : ∀ {a b : Atom n} (v : AtomView env U registry Γ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Γ left right profile →
      TypeRelated env U registry Γ left right (v.mapType profile))
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (view.mapType profile) := by
  match source, target, view with
  | _, _, .nil => exact h
  | _, _, .cons head tail =>
    apply TypeRelated.of_singletons
    intro atom hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (code head h).singleton hm
    · exact (codeMapWith tail code h).singleton hm
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

/-- The support is computed once from the paired syntax. Each atomic result
is retagged at that support using the retained actual type capability. -/
theorem ProfileView.termMapWith {source target : Profile n}
    (view : ProfileView env U registry Γ source target)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (code : ∀ {a b : Atom n} (v : AtomView env U registry Γ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Γ left right profile →
      TypeRelated env U registry Γ left right (v.mapType profile))
    (term : ∀ {a b : Atom n} (v : AtomView env U registry Γ a b)
      {left right type : VExpr} {profile : Profile n},
      Related env U registry Γ left right type (.singleton a) profile →
      Related env U registry Γ left right type (.singleton b) (v.mapType profile))
    (htyped : source.HasType profile)
    (h : Related env U registry Γ left right type source profile) :
    Related env U registry Γ left right type target (view.mapType profile) := by
  match source, target, view with
  | _, _, .nil => exact h
  | _, _, @ProfileView.cons _ _ _ _ _ a b source target head tail =>
    have hc := (ProfileView.cons head tail).codeMapWith code
      (h.typeCode henv hscoped hΓ (by intro he; cases he))
    have ht := (ProfileView.cons head tail).mapType_typed htyped
    have hh := term head (h.singleton_of_mem List.mem_cons_self)
    have htail : Related env U registry Γ left right type source profile := by
      apply Related.of_singletons
      intro atom hm
      exact h.singleton_of_mem (List.mem_cons_of_mem _ hm)
    have htail := termMapWith tail henv hscoped hΓ code term (ProfileView.typed_tail htyped) htail
    apply Related.of_singletons
    intro atom hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Related.retag henv (ht.singleton_of_mem List.mem_cons_self) hc hh
    · exact Related.retag henv (ht.singleton_of_mem (List.mem_cons_of_mem _ hm)) hc
        (htail.singleton_of_mem hm)
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSemantics
