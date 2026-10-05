import Lean4Lean.Theory.Typing.AnchoredRankLawData
import Lean4Lean.Theory.Typing.AnchoredPiTransitivity
import Lean4Lean.Theory.Typing.AnchoredCoreFuture
import Lean4Lean.Theory.Typing.AnchoredFunctionTransitivity
import Lean4Lean.Theory.Typing.AnchoredDataValueLaws

/-! Successor steps for the joint code/term rank induction. Every data
argument operation is taken from the completed preceding rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem FunctionBehavior.symm
    (lowerSymm : ∀ Γ l r A (p d : Profile n),
      Related env U registry Γ l r A p d → Related env U registry Γ r l A p d)
    {Γ : List VExpr} {left right type : VExpr}
    {key : Key n} {output : Atom n} {typeProfile : Profile (n + 1)}
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output typeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ right left type key output typeProfile := by
  obtain ⟨seed, A, B, domain, rows, result, hpi, hrow, htyped, display, behavior⟩ := H
  refine ⟨seed, A, B, domain, rows, result, hpi, hrow, htyped, display, ?_⟩
  intro Δ ρ future x y admitted
  obtain ⟨hl, hr, cross⟩ := behavior Δ ρ future x y admitted
  exact ⟨hr, hl, lowerSymm _ _ _ _ _ _ cross⟩

private theorem related_symm_of_core
    (coreSymm : ∀ Γ l r A (p d : Profile n),
      CoreRelated env U registry Γ l r A p d → CoreRelated env U registry Γ r l A p d)
    {Γ : List VExpr} {left right type : VExpr} {value typeProfile : Profile n}
    (H : Related env U registry Γ left right type value typeProfile) :
    Related env U registry Γ right left type value typeProfile := by
  cases n <;> intro atom ha Δ ρ future
  all_goals
    rcases H atom ha Δ ρ future with empty | ⟨Ω, τ, insertion, core⟩
    · exact .inl empty
    · exact .inr ⟨Ω, τ, insertion, coreSymm _ _ _ _ _ _ core⟩

private theorem saturated_trans
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (coreTrans : ∀ Γ l m r A (p d₁ d₂ : Profile n),
      CoreRelated env U registry Γ l m A p d₁ →
      CoreRelated env U registry Γ m r A p d₂ →
      CoreRelated env U registry Γ l r A p d₂)
    {Γ : List VExpr} {left middle right type : VExpr}
    {value firstType secondType : Profile n}
    (first : SaturatedTerm env U (CoreRelated env U registry)
      Γ left middle type value firstType)
    (second : SaturatedTerm env U (CoreRelated env U registry)
      Γ middle right type value secondType) :
    SaturatedTerm env U (CoreRelated env U registry)
      Γ left right type value secondType := by
  rcases first with hempty | ⟨Δ₁, ρ₁, I₁, first⟩
  · exact .inl hempty
  rcases second with hempty | ⟨Δ₂, ρ₂, I₂, second⟩
  · exact .inl hempty
  obtain ⟨Ω, j, i, J, I, hmaps⟩ := I₁.pushoutProof I₂ henv
  have first' := first.future henv hscoped I.toFuture
  have second' := second.future henv hscoped J.toFuture
  simp only [← lift'_comp, ← Profile.rename_comp, hmaps] at first' second'
  exact .inr ⟨Ω, ρ₂.comp j, I₂.comp J henv,
    coreTrans _ _ _ _ _ _ _ _ first' second'⟩

private theorem related_trans_of_core
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (coreTrans : ∀ Γ l m r A (p d₁ d₂ : Profile n),
      CoreRelated env U registry Γ l m A p d₁ →
      CoreRelated env U registry Γ m r A p d₂ →
      CoreRelated env U registry Γ l r A p d₂)
    {Γ : List VExpr} {left middle right type : VExpr}
    {value firstType secondType : Profile n}
    (first : Related env U registry Γ left middle type value firstType)
    (second : Related env U registry Γ middle right type value secondType) :
    Related env U registry Γ left right type value secondType := by
  cases n <;> intro requested hm Δ ρ future
  all_goals
    exact saturated_trans henv hscoped coreTrans
      (first requested hm Δ ρ future) (second requested hm Δ ρ future)

theorem RankLaws.lowerEquality (henv : env.Ordered) (laws : RankLaws env U registry n) :
    RankedData.LowerEquality env U registry (relations env U registry n) where
  code := fun route related => route.code henv related
  term := fun route related => route.term henv related
  retag := fun typed code related => Related.retag henv typed code related
  symm := fun related => laws.termSymm _ _ _ _ _ _ related
  trans := by
    intro scope Γ left middle right type value before after first second
    exact laws.termTrans scope Γ left middle right type value before after first second

theorem RankLaws.succ_codeTrans (henv : env.Ordered) (lower : RankLaws env U registry n)
    {Γ : List VExpr} {left middle right : VExpr} {profile : Profile (n + 1)}
    (first : TypeRelated env U registry Γ left middle profile)
    (second : TypeRelated env U registry Γ middle right profile) :
    TypeRelated env U registry Γ left right profile := by
  intro Δ ρ future atom member
  have before := first Δ ρ future atom member
  have after := second Δ ρ future atom member
  cases atom with
  | sort relevant => exact before.compose henv after
  | fn | ctor | record => exact before.elim
  | pad atom => exact lower.codeTrans _ _ _ _ _ before after
  | pi A B domain rows =>
    obtain ⟨firstDisplay⟩ := before
    obtain ⟨secondDisplay⟩ := after
    exact firstDisplay.trans henv lower.codeTrans secondDisplay
  | family demand =>
    obtain ⟨firstDisplay⟩ := before
    obtain ⟨secondDisplay⟩ := after
    exact firstDisplay.trans henv (lower.lowerEquality henv) secondDisplay

theorem RankLaws.zero_termSymm
    (codes : SupportLaws env U registry 0)
    {Γ : List VExpr} {left right type : VExpr} {value support : Profile 0}
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Γ right left type value support := by
  apply related_symm_of_core ?_ related
  intro Γ left right type value support core
  exact ⟨core.1, core.2.1, codes.symm _ _ _ _ core.1.wf_value core.2.2⟩

theorem RankLaws.succ_termSymm (henv : env.Ordered) (lower : RankLaws env U registry n)
    (codes : SupportLaws env U registry (n + 1))
    {Γ : List VExpr} {left right type : VExpr} {value support : Profile (n + 1)}
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Γ right left type value support := by
  apply related_symm_of_core ?_ related
  intro Γ left right type value support core
  refine ⟨core.1, core.2.1, ?_⟩
  intro atom member
  have witness := core.2.2 atom member
  have formed := (core.1.singleton_of_mem member).wf_value
  cases atom with
  | fn key output => exact FunctionBehavior.symm lower.termSymm witness
  | pad atom => exact lower.termSymm _ _ _ _ _ _ witness
  | sort | pi | family => exact codes.symm _ _ _ _ formed witness
  | ctor demand => exact RankedData.ConstructorRelation.symm henv (lower.lowerEquality henv) witness
  | record demand => exact RankedData.RecordRelation.symm henv (lower.lowerEquality henv) witness

theorem RankLaws.zero_termTrans (henv : env.Ordered) (scope : registry.Scoped)
    {Γ : List VExpr} {left middle right type : VExpr} {value first second : Profile 0}
    (before : Related env U registry Γ left middle type value first)
    (after : Related env U registry Γ middle right type value second) :
    Related env U registry Γ left right type value second := by
  apply related_trans_of_core henv scope ?_ before after
  intro Γ left middle right type value first second before after
  refine ⟨after.1, after.2.1, ?_⟩
  intro Δ ρ future atom member
  exact (before.2.2 Δ ρ future atom member).compose henv
    (after.2.2 Δ ρ future atom member)

theorem RankLaws.succ_termTrans (henv : env.Ordered) (lower : RankLaws env U registry n)
    (scope : registry.Scoped)
    {Γ : List VExpr} {left middle right type : VExpr} {value first second : Profile (n + 1)}
    (before : Related env U registry Γ left middle type value first)
    (after : Related env U registry Γ middle right type value second) :
    Related env U registry Γ left right type value second := by
  apply related_trans_of_core henv scope ?_ before after
  intro Γ left middle right type value first second before after
  refine ⟨after.1, after.2.1, ?_⟩
  intro atom member
  have firstWitness := before.2.2 atom member
  have secondWitness := after.2.2 atom member
  cases atom with
  | fn key output =>
    exact FunctionBehavior.trans henv (lower.termTrans scope) firstWitness secondWitness
  | pad atom => exact lower.termTrans scope _ _ _ _ _ _ _ _ firstWitness secondWitness
  | sort | pi | family => exact lower.succ_codeTrans henv firstWitness secondWitness
  | ctor demand =>
    exact RankedData.ConstructorRelation.trans henv (lower.lowerEquality henv)
      firstWitness secondWitness
  | record demand =>
    exact RankedData.RecordRelation.trans henv (lower.lowerEquality henv)
      firstWitness secondWitness

end Lean4Lean.AnchoredSemantics
