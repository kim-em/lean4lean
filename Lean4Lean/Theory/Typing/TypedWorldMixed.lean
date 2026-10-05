import Lean4Lean.Theory.Typing.TypedWorldContextConversion
import Lean4Lean.Theory.Typing.DependentTypeConversion
import Lean4Lean.Theory.Typing.NativeCaptureAbstraction

/-! Finite world routes made only from generated proof insertions and typed
identity-position context conversions. No semantic predicates occur here. -/

namespace Lean4Lean.VEnv

theorem TypeConversion.defeqDFC {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    (henv : env.Ordered) (conversion : IsDefEqCtx env U [] Γ Γ')
    (path : TypeConversion env U Γ A B) : TypeConversion env U Γ' A B := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (edge.defeqDFC henv conversion)

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv

inductive ContextChain (env : VEnv) (U : Nat) : List VExpr → List VExpr → Prop where
  | refl : ContextChain env U Γ Γ
  | tail (previous : ContextChain env U Γ Δ) (edge : IsDefEqCtx env U [] Δ Ω) :
      ContextChain env U Γ Ω

namespace ContextChain

theorem trans (first : ContextChain env U Γ Δ) (second : ContextChain env U Δ Ω) :
    ContextChain env U Γ Ω := by
  induction second with
  | refl => exact first
  | tail _ edge ih => exact .tail ih edge

theorem single (edge : IsDefEqCtx env U [] Γ Δ) : ContextChain env U Γ Δ :=
  .tail .refl edge

theorem symm (henv : env.Ordered) (chain : ContextChain env U Γ Δ) :
    ContextChain env U Δ Γ := by
  induction chain with
  | refl => exact .refl
  | tail _ edge ih => exact (single (edge.symm henv)).trans ih

theorem eq (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (h : env.IsDefEq U Γ left right type) : env.IsDefEq U Δ left right type := by
  induction chain with
  | refl => exact h
  | tail _ edge ih => exact ih.defeqDFC henv edge

theorem isType (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (h : env.IsType U Γ type) : env.IsType U Δ type := by
  obtain ⟨u, h⟩ := h
  exact ⟨u, chain.eq henv h⟩

theorem path (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (h : TypeConversion env U Γ left right) : TypeConversion env U Δ left right := by
  induction chain with
  | refl => exact h
  | tail _ edge ih => exact ih.defeqDFC henv edge

theorem targetWF (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (hΓ : OnCtx Γ (env.IsType U)) : OnCtx Δ (env.IsType U) := by
  cases chain with
  | refl => exact hΓ
  | tail _ edge => exact (edge.symm henv).isType

theorem underBinder (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (hA : env.IsType U Γ A) : ContextChain env U (A :: Γ) (A :: Δ) := by
  induction chain with
  | refl => exact .refl
  | tail previous edge ih =>
    obtain ⟨u, hA⟩ := previous.isType henv hA
    exact .tail ih (.succ edge hA)

theorem pullProof (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (insertion : ProofInsertion env U Γ' Δ' ρ) :
    ∃ Δ, ProofInsertion env U Γ Δ ρ ∧ ContextChain env U Δ Δ' := by
  induction chain generalizing Δ' with
  | refl => exact ⟨_, insertion, .refl⟩
  | tail _ edge ih =>
    obtain ⟨middle, insertion', changed⟩ := insertion.convertBase henv (edge.symm henv)
    obtain ⟨Δ, previous, conversion⟩ := ih insertion'
    exact ⟨Δ, previous, .tail conversion (changed.symm henv)⟩

theorem pullFuture (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (insertion : FutureInsertion env U Γ' Δ' ρ) :
    ∃ Δ, FutureInsertion env U Γ Δ ρ ∧ ContextChain env U Δ Δ' := by
  induction chain generalizing Δ' with
  | refl => exact ⟨_, insertion, .refl⟩
  | tail _ edge ih =>
    obtain ⟨middle, insertion', changed⟩ := insertion.convertBase henv (edge.symm henv)
    obtain ⟨Δ, previous, conversion⟩ := ih insertion'
    exact ⟨Δ, previous, .tail conversion (changed.symm henv)⟩

theorem pushProof (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (insertion : ProofInsertion env U Γ Γ' ρ) :
    ∃ Δ', ProofInsertion env U Δ Δ' ρ ∧ ContextChain env U Γ' Δ' := by
  obtain ⟨Δ', future, changed⟩ := (chain.symm henv).pullProof henv insertion
  exact ⟨Δ', future, changed.symm henv⟩

theorem pushFuture (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (insertion : FutureInsertion env U Γ Γ' ρ) :
    ∃ Δ', FutureInsertion env U Δ Δ' ρ ∧ ContextChain env U Γ' Δ' := by
  obtain ⟨Δ', future, changed⟩ := (chain.symm henv).pullFuture henv insertion
  exact ⟨Δ', future, changed.symm henv⟩

end ContextChain

inductive MixedInsertion (env : VEnv) (U : Nat) : List VExpr → List VExpr → Lift → Prop where
  | proof (insertion : ProofInsertion env U Γ Δ ρ) : MixedInsertion env U Γ Δ ρ
  | context (chain : ContextChain env U Γ Δ) : MixedInsertion env U Γ Δ .refl
  | comp (first : MixedInsertion env U Γ Δ ρ) (second : MixedInsertion env U Δ Ω τ) :
      MixedInsertion env U Γ Ω (ρ.comp τ)

namespace MixedInsertion

theorem eq (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : env.IsDefEq U Γ left right type) :
    env.IsDefEq U Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) := by
  induction route generalizing left right type with
  | proof insertion => exact h.weak' henv insertion.weakening
  | context chain => simpa only [lift'_refl] using chain.eq henv h
  | comp _ _ first second => simpa only [lift'_comp] using second (first h)

theorem isType (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : env.IsType U Γ type) : env.IsType U Δ (type.lift' ρ) := by
  obtain ⟨u, h⟩ := h
  exact ⟨u, route.eq henv h⟩

theorem path (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : TypeConversion env U Γ left right) :
    TypeConversion env U Δ (left.lift' ρ) (right.lift' ρ) := by
  induction route generalizing left right with
  | proof insertion => exact h.weak' henv insertion.weakening
  | context chain => simpa only [lift'_refl] using chain.path henv h
  | comp _ _ first second => simpa only [lift'_comp] using second (first h)

theorem targetWF (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (hΓ : OnCtx Γ (env.IsType U)) : OnCtx Δ (env.IsType U) := by
  induction route with
  | proof insertion => exact insertion.targetWF henv
  | context chain => exact chain.targetWF henv hΓ
  | comp _ _ first second => exact second (first hΓ)

theorem eqUnderBinder (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (hA : env.IsType U Γ A) (h : env.IsDefEq U (A :: Γ) left right type) :
    env.IsDefEq U (A.lift' ρ :: Δ)
      (left.lift' ρ.cons) (right.lift' ρ.cons) (type.lift' ρ.cons) := by
  induction route generalizing A left right type with
  | proof insertion => exact h.weak' henv (.cons insertion.weakening)
  | context chain =>
    simpa only [lift'_refl, lift'_depth_zero (l := Lift.cons .refl) rfl] using
      (chain.underBinder henv hA).eq henv h
  | comp before after first second =>
    have hm := before.isType henv hA
    simpa only [← lift'_comp, Lift.comp] using second hm (first hA h)

theorem isTypeUnderBinder (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (hA : env.IsType U Γ A) (h : env.IsType U (A :: Γ) type) :
    env.IsType U (A.lift' ρ :: Δ) (type.lift' ρ.cons) := by
  obtain ⟨u, h⟩ := h
  exact ⟨u, route.eqUnderBinder henv hA h⟩

/-- Binder paths transport without pretending that a context-conversion leg
is a literal retained binder insertion. -/
theorem pathUnderBinder (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (hA : env.IsType U Γ A) (h : TypeConversion env U (A :: Γ) left right) :
    TypeConversion env U (A.lift' ρ :: Δ) (left.lift' ρ.cons) (right.lift' ρ.cons) := by
  induction route generalizing A left right with
  | proof insertion => exact h.weak' henv (.cons insertion.weakening)
  | context chain =>
    simpa only [lift'_refl, lift'_depth_zero (l := Lift.cons .refl) rfl] using
      (chain.underBinder henv hA).path henv h
  | comp before after first second =>
    have hm := before.isType henv hA
    simpa only [← lift'_comp, Lift.comp] using second hm (first hA h)

theorem pathBack (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : TypeConversion env U Δ (left.lift' ρ) (right.lift' ρ)) :
    TypeConversion env U Γ left right := by
  induction route generalizing left right with
  | proof insertion =>
    obtain ⟨embedding, map⟩ := insertion.toEmbedding henv
    have result := h.substTarget henv embedding.baseWF embedding.typed
    simpa only [← map, embedding.leftInv] using result
  | context chain =>
    apply (chain.symm henv).path henv
    simpa only [lift'_refl] using h
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp] using h

/-- Pull a future query through a mixed route. Only its final declarations
change; the composite variable map is retained exactly. -/
theorem pullFuture (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (future : FutureInsertion env U Δ Ω τ) :
    ∃ Ω', FutureInsertion env U Γ Ω' (ρ.comp τ) ∧ ContextChain env U Ω' Ω := by
  induction route generalizing Ω τ with
  | proof insertion => exact ⟨_, insertion.toFuture.comp future henv, .refl⟩
  | context chain =>
    simpa only [Lift.refl_comp] using chain.pullFuture henv future
  | comp before after first second =>
    obtain ⟨middle, middleFuture, endChange⟩ := second future
    obtain ⟨start, startFuture, firstChange⟩ := first middleFuture
    exact ⟨start, by simpa only [Lift.comp_assoc] using startFuture,
      firstChange.trans endChange⟩

/-- Amalgamate a mixed display route with an actual future argument world.
The argument-side leg is mixed, while the display-side leg remains a future. -/
theorem pushout (route : MixedInsertion env U Γ Δ ρ)
    (future : FutureInsertion env U Γ Ω τ) (henv : env.Ordered) :
    ∃ V α β, MixedInsertion env U Ω V α ∧ FutureInsertion env U Δ V β ∧
      ρ.comp β = τ.comp α := by
  induction route generalizing Ω τ with
  | proof insertion =>
    obtain ⟨V, α, β, proof, extension, maps⟩ := insertion.pushout future henv
    exact ⟨V, α, β, .proof proof, extension, maps⟩
  | context chain =>
    obtain ⟨V, extension, changed⟩ := chain.pushFuture henv future
    exact ⟨V, .refl, τ, .context changed, extension, by simp only [Lift.refl_comp, Lift.comp]⟩
  | comp before after first second =>
    obtain ⟨middle, α, β, firstLeg, middleFuture, firstMaps⟩ := first future
    obtain ⟨V, γ, δ, secondLeg, lastFuture, secondMaps⟩ := second middleFuture
    refine ⟨V, α.comp γ, δ, .comp firstLeg secondLeg, lastFuture, ?_⟩
    rw [Lift.comp_assoc, secondMaps, ← Lift.comp_assoc, firstMaps, Lift.comp_assoc]

end MixedInsertion
end Lean4Lean.AnchoredSemantics
