import Lean4Lean.Theory.Typing.AnchoredDataLaws
import Lean4Lean.Theory.Typing.AnchoredSemantics
import Lean4Lean.Theory.Typing.TypedWorldMixed

/-! Semantic transport along a conversion of context declarations which
preserves variable positions. Raw terms, profiles, anchors, and row keys are
unchanged. The proof decreases only the finite observation rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private def CodeContext {env : VEnv} {U : Nat} (lower : Relations n) : Prop :=
  ∀ {Γ Γ' : List VExpr}, IsDefEqCtx env U [] Γ Γ' →
    ∀ {left right profile}, lower.code Γ left right profile → lower.code Γ' left right profile

private def TermContext {env : VEnv} {U : Nat} (lower : Relations n) : Prop :=
  ∀ {Γ Γ' : List VExpr}, IsDefEqCtx env U [] Γ Γ' →
    ∀ {left right type value support}, lower.term Γ left right type value support →
      lower.term Γ' left right type value support

private theorem admission_context
    (henv : env.Ordered) (code : CodeContext (env := env) (U := U) lower)
    (term : TermContext (env := env) (U := U) lower)
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (admitted : Admission env U lower Γ key left right) :
    Admission env U lower Γ' key left right := by
  obtain ⟨anchor, pair, support, typed, formed, typeCode, first, second⟩ := admitted
  exact ⟨anchor.defeqDFC henv conversion, pair.defeqDFC henv conversion,
    support, typed, formed, code conversion typeCode,
    term conversion first, term conversion second⟩

/-- Source context conversion retains the final display. Only the literal
front/post world changes; its typed conversion is reversed at the terminal. -/
theorem Exposure.convertContext
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (exposure : Exposure env U registry Γ expression Δ ρ head) :
    Nonempty (Exposure env U registry Γ' expression Δ ρ head) := by
  have generated := exposure.generated.convertBase_exact henv conversion
  simp only [convertedContext_skipN] at generated
  have post := exposure.post.convertBase_exact henv generated.2
  exact ⟨{
    added := exposure.added
    result := exposure.result
    postMap := exposure.postMap
    postContext := _
    trace := exposure.trace
    generated := generated.1
    post := post.1
    terminal := (ContextChain.single (post.2.symm henv)).trans exposure.terminal
    map_eq := exposure.map_eq
    result_eq := exposure.result_eq
    sound := exposure.sound
    headType := exposure.headType }⟩

private theorem pi_context
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (display : PiWitness env U registry lower Γ left right A B domain rows) :
    ∃ changed : PiWitness env U registry lower Γ' left right A B domain rows,
      changed.context = display.context ∧
      changed.map = display.map ∧ changed.leftBody = display.leftBody := by
  obtain ⟨leftExposure⟩ := display.leftExposure.convertContext henv conversion
  obtain ⟨rightExposure⟩ := display.rightExposure.convertContext henv conversion
  exact ⟨{ display with leftExposure := leftExposure, rightExposure := rightExposure },
    rfl, rfl, rfl⟩

private theorem sort_context
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (related : SortRelated env U registry Γ left right relevant) :
    SortRelated env U registry Γ' left right relevant := by
  obtain ⟨Δ, ρ, u, v, ⟨left⟩, ⟨right⟩, equal, flag⟩ := related
  exact ⟨Δ, ρ, u, v,
    left.convertContext henv conversion, right.convertContext henv conversion, equal, flag⟩

private theorem function_context
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (code : CodeContext (env := env) (U := U) lower)
    (term : TermContext (env := env) (U := U) lower)
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (behavior : FunctionBehavior env U registry lower Γ left right type key output support) :
    FunctionBehavior env U registry lower Γ' left right type key output support := by
  obtain ⟨anchor, A, B, domain, rows, result, typeMember, rowMember, typed, display, behavior⟩ := behavior
  obtain ⟨newDisplay, contextEq, mapEq, bodyEq⟩ := pi_context henv conversion display
  refine ⟨admission_context henv code term conversion anchor, A, B, domain, rows, result,
    typeMember, rowMember, typed, newDisplay, ?_⟩
  simpa only [contextEq, mapEq, bodyEq] using behavior

private theorem context_congruence (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (henv : env.Ordered) (n : Nat) :
    CodeContext (env := env) (U := U) (relations env U registry n) ∧
    TermContext (env := env) (U := U) (relations env U registry n) := by
  induction n with
  | zero =>
    have code : CodeContext (env := env) (U := U) (relations env U registry 0) := by
      intro Γ Γ' conversion left right profile related Δ ρ future atom member
      obtain ⟨oldΔ, oldFuture, reverse⟩ := future.convertBase henv (conversion.symm henv)
      exact sort_context henv (reverse.symm henv) (related oldΔ ρ oldFuture atom member)
    refine ⟨code, ?_⟩
    intro Γ Γ' conversion left right type value support related requested member Δ ρ future
    obtain ⟨oldΔ, oldFuture, reverse⟩ := future.convertBase henv (conversion.symm henv)
    rcases related requested member oldΔ ρ oldFuture with empty | ⟨oldΩ, τ, frame, typed, typeCode, valueCode⟩
    · exact .inl empty
    · obtain ⟨Ω, newFrame, changed⟩ := frame.convertBase henv (reverse.symm henv)
      exact .inr ⟨Ω, τ, newFrame, typed, code changed typeCode, code changed valueCode⟩
  | succ n ih =>
    have atomContext : ∀ {Γ Γ'}, IsDefEqCtx env U [] Γ Γ' → ∀ {left right atom},
        CodeAtom env U registry (relations env U registry n) Γ left right atom →
        CodeAtom env U registry (relations env U registry n) Γ' left right atom := by
      intro Γ Γ' conversion left right atom related
      cases atom with
      | sort relevant => exact sort_context henv conversion related
      | fn | ctor | record => exact False.elim related
      | family data =>
        obtain ⟨witness⟩ := related
        exact ⟨witness.changeBase henv (.single conversion)⟩
      | pad atom => exact ih.1 conversion related
      | pi A B domain rows =>
        obtain ⟨display⟩ := related
        obtain ⟨changed, _, _, _⟩ := pi_context henv conversion display
        exact ⟨changed⟩
    have code : CodeContext (env := env) (U := U) (relations env U registry (n + 1)) := by
      intro Γ Γ' conversion left right profile related Δ ρ future atom member
      obtain ⟨oldΔ, oldFuture, reverse⟩ := future.convertBase henv (conversion.symm henv)
      exact atomContext (reverse.symm henv) (related oldΔ ρ oldFuture atom member)
    refine ⟨code, ?_⟩
    intro Γ Γ' conversion left right type value support related requested member Δ ρ future
    obtain ⟨oldΔ, oldFuture, reverse⟩ := future.convertBase henv (conversion.symm henv)
    rcases related requested member oldΔ ρ oldFuture with empty | ⟨oldΩ, τ, frame, typed, typeCode, values⟩
    · exact .inl empty
    · obtain ⟨Ω, newFrame, changed⟩ := frame.convertBase henv (reverse.symm henv)
      refine .inr ⟨Ω, τ, newFrame, typed, code changed typeCode, ?_⟩
      intro atom member
      have value := values atom member
      cases atom with
      | fn key output => exact function_context henv ih.1 ih.2 changed value
      | pad atom => exact ih.2 changed value
      | sort relevant => exact code changed value
      | pi A B domain rows => exact code changed value
      | family data => exact code changed value
      | ctor data => exact RankedData.ConstructorRelation.context henv (.single changed) value
      | record data => exact RankedData.RecordRelation.context henv (.single changed) value

/-- Change only context declarations, preserving all variable positions. -/
theorem TypeRelated.convertContext
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (related : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ' left right profile :=
  (context_congruence env U registry henv _).1 conversion related

theorem Related.convertContext
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Γ' left right type value support :=
  (context_congruence env U registry henv _).2 conversion related

theorem Admitted.convertContext {key : Key n}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (admitted : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ' key left right := by
  have ih := context_congruence env U registry henv n
  exact admission_context henv ih.1 ih.2 conversion admitted

namespace ContextChain

theorem code (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Δ left right profile := by
  induction chain with
  | refl => exact related
  | tail _ edge ih => exact ih.convertContext henv edge

theorem term (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Δ left right type value support := by
  induction chain with
  | refl => exact related
  | tail _ edge ih => exact ih.convertContext henv edge

theorem admitted (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : Admitted env U registry Γ key left right) :
    Admitted env U registry Δ key left right := by
  induction chain with
  | refl => exact related
  | tail _ edge ih => exact ih.convertContext henv edge

end ContextChain

end Lean4Lean.AnchoredSemantics
