import Lean4Lean.Theory.Typing.AnchoredFunctionHeadBeta
import Lean4Lean.Theory.Typing.AnchoredRecordBeta

/-! Closed head-beta expansion of term observations. Raw equalities come from
the actual typed beta redexes; the semantic recursion decreases demand rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem sort_cover {type : Profile (n + 1)}
    (h : (Profile.sort relevant).HasType type) :
    ∃ r, (AtomData.sort r : Atom (n + 1)) ∈ type.atoms := by
  obtain ⟨cover, hm, ht⟩ := h.2.2 _ (List.mem_singleton_self _)
  cases cover with
  | sort r => exact ⟨r, hm⟩
  | fn | pi | pad | family | ctor | record => contradiction

private theorem pi_cover {type : Profile (n + 1)}
    (h : (Profile.pi A B domain rows).HasType type) :
    ∃ r, (AtomData.sort r : Atom (n + 1)) ∈ type.atoms := by
  obtain ⟨cover, hm, ht⟩ := h.2.2 _ (List.mem_singleton_self _)
  cases cover with
  | sort r => exact ⟨r, hm⟩
  | fn | pi | pad | family | ctor | record => contradiction

private theorem family_cover {type : Profile (n + 1)} {demand : FamilyData (Profile n)}
    (h : (Profile.singleton (n := n + 1) (.family demand)).HasType type) :
    ∃ r, (AtomData.sort r : Atom (n + 1)) ∈ type.atoms := by
  obtain ⟨cover, hm, ht⟩ := h.2.2 _ (List.mem_singleton_self _)
  cases cover with
  | sort r => exact ⟨r, hm⟩
  | fn | pi | pad | family | ctor | record => contradiction

private theorem TypeRelated.sort_member_path (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) {support : Profile (n + 1)}
    (H : TypeRelated env U registry Γ type type support)
    (hm : (AtomData.sort relevant : Atom (n + 1)) ∈ support.atoms) :
    ∃ level, TypeConversion env U Γ type (.sort level) := by
  have hc := H Γ .refl (.refl hΓ) (.sort relevant)
    (by simpa only [Profile.rename_refl] using hm)
  simp only [lift'_refl] at hc
  exact SortRelated.path henv hc

theorem Related.headBeta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {value support : Profile n}
    {Γ : List VExpr} {leftExpanded rightExpanded left right type : VExpr}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : Related env U registry Γ left right type value support) :
    Related env U registry Γ leftExpanded rightExpanded type value support := by
  induction n generalizing Γ leftExpanded rightExpanded left right type with
  | zero =>
    intro requested hm Δ ρ future
    rcases H requested hm Δ ρ future with empty | ⟨Ω, τ, insertion, typed, code, terms⟩
    · exact .inl empty
    have hl' := (hl.lift ρ).lift τ
    have hr' := (hr.lift ρ).lift τ
    have cl' := (cl.weak' henv future.weakening).weak' henv insertion.weakening
    have cr' := (cr.weak' henv future.weakening).weak' henv insertion.weakening
    have hΩ := insertion.targetWF henv
    obtain ⟨cover, hcover, _⟩ := typed ((requested.rename ρ).rename τ) (by
      rw [Profile.rename_singleton, Profile.rename_singleton]
      exact List.mem_singleton_self _)
    have hsort := code Ω .refl (.refl hΩ) cover
      (by simpa only [Profile.rename_refl] using hcover)
    simp only [lift'_refl] at hsort
    obtain ⟨level, path⟩ := SortRelated.path henv hsort
    change TypeRelated env U registry Ω ((left.lift' ρ).lift' τ)
      ((right.lift' ρ).lift' τ) ((Profile.singleton requested).rename ρ |>.rename τ) at terms
    exact .inr ⟨Ω, τ, insertion, typed, code,
      TypeRelated.headBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) terms⟩
  | succ n ih =>
    intro requested hm Δ ρ future
    rcases H requested hm Δ ρ future with empty | ⟨Ω, τ, insertion, typed, code, terms⟩
    · exact .inl empty
    have hl' := (hl.lift ρ).lift τ
    have hr' := (hr.lift ρ).lift τ
    have cl' := (cl.weak' henv future.weakening).weak' henv insertion.weakening
    have cr' := (cr.weak' henv future.weakening).weak' henv insertion.weakening
    have hΩ := insertion.targetWF henv
    refine .inr ⟨Ω, τ, insertion, typed, code, ?_⟩
    intro atom ha
    have ht := typed.singleton_of_mem ha
    have hv := terms atom ha
    cases atom with
    | fn key output =>
      exact FunctionBehavior.headBeta henv (fun Γ le re l r A p d hl hr cl cr h =>
        ih hl hr cl cr h) hl' hr' cl' cr' hv
    | pad lower => exact ih hl' hr' cl' cr' hv
    | sort relevant =>
      change TypeRelated env U registry Ω ((left.lift' ρ).lift' τ)
        ((right.lift' ρ).lift' τ) (.sort (n := n + 1) relevant) at hv
      obtain ⟨r, hm⟩ := sort_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.headBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv
    | ctor demand => exact RankedData.ConstructorRelation.headBeta henv hl' hr' cl' cr' hv
    | record demand =>
      exact RankedData.RecordRelation.headBeta henv (fun Γ le re l r A p d hl hr cl cr h =>
        ih hl hr cl cr h) hl' hr' cl' cr' hv
    | family demand =>
      change TypeRelated env U registry Ω ((left.lift' ρ).lift' τ)
        ((right.lift' ρ).lift' τ) (.singleton (n := n + 1) (.family demand)) at hv
      obtain ⟨r, hm⟩ := family_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.headBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv
    | pi A B domain rows =>
      change TypeRelated env U registry Ω ((left.lift' ρ).lift' τ)
        ((right.lift' ρ).lift' τ) (.pi A B domain rows) at hv
      obtain ⟨r, hm⟩ := pi_cover ht
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv hΩ code hm
      exact TypeRelated.headBeta henv hl' hr' (.single (path.cast cl'))
        (.single (path.cast cr')) hv

end Lean4Lean.AnchoredSemantics
