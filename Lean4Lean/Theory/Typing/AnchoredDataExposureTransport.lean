import Lean4Lean.Theory.Typing.AnchoredTypeExposure
import Lean4Lean.Theory.Typing.AnchoredDataExposure

/-! Raw comparison and transport of actual data traces. No anchored semantic
relation is needed to compare their deterministic terminal results. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

private theorem MixedInsertion.proofThenContext
    (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (formed : OnCtx Γ (env.IsType U)) :
    ∃ Ω, ProofInsertion env U Γ Ω ρ ∧ ContextChain env U Ω Δ := by
  induction route with
  | proof insertion => exact ⟨_, insertion, .refl⟩
  | context chain => exact ⟨_, .refl formed, chain⟩
  | comp before after first second =>
    obtain ⟨Ω, initial, changed⟩ := first formed
    obtain ⟨V, suffix, final⟩ := second (before.targetWF henv formed)
    obtain ⟨W, suffix', changed'⟩ := changed.pullProof henv suffix
    exact ⟨W, initial.comp suffix' henv, changed'.trans final⟩

namespace ConstructorExposure

theorem insertion (henv : env.Ordered)
    (display : ConstructorExposure env U registry Γ expression type Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := by
  have before := display.generated.comp display.post henv
  rw [display.map_eq] at before
  simpa only [Lift.comp] using MixedInsertion.comp (.proof before) (.context display.terminal)

/-- Append only an actual mixed insertion history; no private field is
retracted and no arbitrary context embedding is introduced. -/
theorem transport (henv : env.Ordered)
    (display : ConstructorExposure env U registry Γ expression type Δ ρ head)
    (route : MixedInsertion env U Δ Ω τ) :
    Nonempty (ConstructorExposure env U registry Γ expression type Ω (ρ.comp τ)
      (head.lift' τ)) := by
  let after := MixedInsertion.comp (.context display.terminal) route
  obtain ⟨postContext, post, terminal⟩ :=
    after.proofThenContext henv (display.post.targetWF henv)
  refine ⟨{
    added := display.added
    result := display.result
    postMap := display.postMap.comp τ
    trace := display.trace
    generated := display.generated
    postContext := postContext
    post := display.post.comp (by simpa only [after, Lift.refl_comp] using post) henv
    terminal := terminal
    map_eq := ?_
    result_eq := ?_
    sound := ?_ }⟩
  · rw [← Lift.comp_assoc, display.map_eq]
  · rw [lift'_comp, display.result_eq]
  · simpa only [← lift'_comp] using route.eq henv display.sound

/-- Deterministic terminal comparison applies to value heads as well as Pi
heads. The proof compares traces before amalgamating their post-insertions. -/
theorem sameHead (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : ConstructorExposure env U registry Γ expression type₁ Δ₁ ρ₁ head₁)
    (second : ConstructorExposure env U registry Γ expression type₂ Δ₂ ρ₂ head₂)
    (terminal₁ : CanonicalDataHead.step registry head₁ = none)
    (terminal₂ : CanonicalDataHead.step registry head₂ = none) :
    ∃ Ω i j, MixedInsertion env U Δ₁ Ω i ∧ MixedInsertion env U Δ₂ Ω j ∧
      ρ₁.comp i = ρ₂.comp j ∧ head₁.lift' i = head₂.lift' j := by
  have stopped₁ : CanonicalDataHead.step registry first.result = none := by
    have stopped := terminal₁
    rw [← first.result_eq, CanonicalDataHead.step_rename registry hscoped] at stopped
    exact Option.map_eq_none_iff.mp stopped
  have stopped₂ : CanonicalDataHead.step registry second.result = none := by
    have stopped := terminal₂
    rw [← second.result_eq, CanonicalDataHead.step_rename registry hscoped] at stopped
    exact Option.map_eq_none_iff.mp stopped
  obtain ⟨sameAdded, sameResult⟩ := first.trace.terminal_unique second.trace stopped₁ stopped₂
  have secondPost := second.post
  rw [← sameAdded] at secondPost
  obtain ⟨Ω, j, i, right, left, maps⟩ := first.post.pushoutProof secondPost henv
  refine ⟨Ω, i, j, ?_, ?_, ?_, ?_⟩
  · simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (first.terminal.symm henv)) (.proof left)
  · simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (second.terminal.symm henv)) (.proof right)
  · rw [← first.map_eq, ← second.map_eq, ← sameAdded,
      Lift.comp_assoc, Lift.comp_assoc, maps]
  · rw [← first.result_eq, ← second.result_eq, ← lift'_comp,
      ← lift'_comp, sameResult, maps]

end ConstructorExposure

private theorem proofSkip_inv
    (generated : ProofInsertion env U Γ (P :: Δ) ρ.skip) :
    ∃ q, ProofInsertion env U Γ Δ ρ ∧
      env.HasType U Δ P (.sort .zero) ∧ env.HasType U Δ q P := by
  cases generated with
  | skip previous formed witness => exact ⟨_, previous, formed, witness⟩

private theorem ProofInsertion.changeFront
    {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    (henv : env.Ordered) (added : List VExpr)
    (generated : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length))
    (chain : ContextChain env U Γ Γ') :
    ProofInsertion env U Γ' (added ++ Γ') (.skipN .refl added.length) ∧
      ContextChain env U (added ++ Γ) (added ++ Γ') := by
  induction added with
  | nil => exact ⟨.refl (chain.targetWF henv generated.baseWF), chain⟩
  | cons P rest ih =>
    change ProofInsertion env U Γ (P :: (rest ++ Γ))
      (.skip (.skipN .refl rest.length)) at generated
    obtain ⟨_, previous, hP, hq⟩ := proofSkip_inv generated
    obtain ⟨changed, extended⟩ := ih previous
    exact ⟨changed.skip (extended.eq henv hP) (extended.eq henv hq),
      extended.underBinder henv ⟨_, hP⟩⟩

/-- Change only the source declarations. The same concrete terminal world
is recovered through the inverse terminal context change. -/
noncomputable def ConstructorExposure.context
    (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (display : ConstructorExposure env U registry Γ expression type Δ ρ head) :
    ConstructorExposure env U registry Γ' expression type Δ ρ head := by
  obtain ⟨generated, extended⟩ := ProofInsertion.changeFront henv display.added display.generated chain
  let shifted := extended.pushProof henv display.post
  let postContext := Classical.choose shifted
  have post := (Classical.choose_spec shifted).1
  have changed := (Classical.choose_spec shifted).2
  exact {
    added := display.added
    result := display.result
    postMap := display.postMap
    trace := display.trace
    generated := generated
    postContext := postContext
    post := post
    terminal := (changed.symm henv).trans display.terminal
    map_eq := display.map_eq
    result_eq := display.result_eq
    sound := display.sound }

private theorem MixedInsertion.normalizeProof
    (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (formed : OnCtx Γ (env.IsType U)) :
    ∃ Ω, ProofInsertion env U Γ Ω ρ ∧ ContextChain env U Ω Δ := by
  induction route with
  | proof insertion => exact ⟨_, insertion, .refl⟩
  | context chain => exact ⟨_, .refl formed, chain⟩
  | comp before after first second =>
    obtain ⟨Ω, initial, changed⟩ := first formed
    obtain ⟨V, suffix, final⟩ := second (before.targetWF henv formed)
    obtain ⟨W, suffix', changed'⟩ := changed.pullProof henv suffix
    exact ⟨W, initial.comp suffix' henv, changed'.trans final⟩

/-- Two private proof displays have a concrete common world, preserving the
maps from their shared base. No ordinary binder is duplicated or retracted. -/
theorem MixedInsertion.amalgam
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (first : MixedInsertion env U Γ Δ ρ) (second : MixedInsertion env U Γ Ω τ) :
    ∃ V i j, MixedInsertion env U Δ V i ∧ MixedInsertion env U Ω V j ∧
      ρ.comp i = τ.comp j := by
  obtain ⟨P, left, leftChange⟩ := first.normalizeProof henv formed
  obtain ⟨Q, right, rightChange⟩ := second.normalizeProof henv formed
  obtain ⟨V, j, i, rightLeg, leftLeg, maps⟩ := left.pushoutProof right henv
  exact ⟨V, i, j,
    by simpa only [Lift.refl_comp] using
      MixedInsertion.comp (.context (leftChange.symm henv)) (.proof leftLeg),
    by simpa only [Lift.refl_comp] using
      MixedInsertion.comp (.context (rightChange.symm henv)) (.proof rightLeg), maps⟩

namespace Exposure

/-- Append only an actual mixed insertion history; no private field is
retracted and no arbitrary context embedding is introduced. -/
theorem transport (henv : env.Ordered)
    (display : Exposure env U registry Γ expression Δ ρ head)
    (route : MixedInsertion env U Δ Ω τ) :
    Nonempty (Exposure env U registry Γ expression Ω (ρ.comp τ)
      (head.lift' τ)) := by
  let after := MixedInsertion.comp (.context display.terminal) route
  obtain ⟨postContext, post, terminal⟩ :=
    after.proofThenContext henv (display.post.targetWF henv)
  refine ⟨{
    added := display.added
    result := display.result
    postMap := display.postMap.comp τ
    trace := display.trace
    generated := display.generated
    postContext := postContext
    post := display.post.comp (by simpa only [after, Lift.refl_comp] using post) henv
    terminal := terminal
    map_eq := ?_
    result_eq := ?_
    sound := ?_
    headType := route.isType henv display.headType }⟩
  · rw [← Lift.comp_assoc, display.map_eq]
  · rw [lift'_comp, display.result_eq]
  · simpa only [← lift'_comp] using route.path henv display.sound

/-- Deterministic terminal comparison applies to value heads as well as Pi
heads. The proof compares traces before amalgamating their post-insertions. -/
theorem sameHead (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : Exposure env U registry Γ expression Δ₁ ρ₁ head₁)
    (second : Exposure env U registry Γ expression Δ₂ ρ₂ head₂)
    (terminal₁ : CanonicalDataHead.step registry head₁ = none)
    (terminal₂ : CanonicalDataHead.step registry head₂ = none) :
    ∃ Ω i j, MixedInsertion env U Δ₁ Ω i ∧ MixedInsertion env U Δ₂ Ω j ∧
      ρ₁.comp i = ρ₂.comp j ∧ head₁.lift' i = head₂.lift' j := by
  have stopped₁ : CanonicalDataHead.step registry first.result = none := by
    have stopped := terminal₁
    rw [← first.result_eq, CanonicalDataHead.step_rename registry hscoped] at stopped
    exact Option.map_eq_none_iff.mp stopped
  have stopped₂ : CanonicalDataHead.step registry second.result = none := by
    have stopped := terminal₂
    rw [← second.result_eq, CanonicalDataHead.step_rename registry hscoped] at stopped
    exact Option.map_eq_none_iff.mp stopped
  obtain ⟨sameAdded, sameResult⟩ := first.trace.terminal_unique second.trace stopped₁ stopped₂
  have secondPost := second.post
  rw [← sameAdded] at secondPost
  obtain ⟨Ω, j, i, right, left, maps⟩ := first.post.pushoutProof secondPost henv
  refine ⟨Ω, i, j, ?_, ?_, ?_, ?_⟩
  · simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (first.terminal.symm henv)) (.proof left)
  · simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (second.terminal.symm henv)) (.proof right)
  · rw [← first.map_eq, ← second.map_eq, ← sameAdded,
      Lift.comp_assoc, Lift.comp_assoc, maps]
  · rw [← first.result_eq, ← second.result_eq, ← lift'_comp,
      ← lift'_comp, sameResult, maps]

end Exposure

noncomputable def Exposure.context
    (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (display : Exposure env U registry Γ expression Δ ρ head) :
    Exposure env U registry Γ' expression Δ ρ head := by
  obtain ⟨generated, extended⟩ := ProofInsertion.changeFront henv display.added display.generated chain
  let shifted := extended.pushProof henv display.post
  let postContext := Classical.choose shifted
  have post := (Classical.choose_spec shifted).1
  have changed := (Classical.choose_spec shifted).2
  exact {
    added := display.added
    result := display.result
    postMap := display.postMap
    trace := display.trace
    generated := generated
    postContext := postContext
    post := post
    terminal := (changed.symm henv).trans display.terminal
    map_eq := display.map_eq
    result_eq := display.result_eq
    sound := display.sound
    headType := display.headType }

end Lean4Lean.AnchoredSemantics
