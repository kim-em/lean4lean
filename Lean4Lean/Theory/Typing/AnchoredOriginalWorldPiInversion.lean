import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiAdequacy
import Lean4Lean.Theory.Typing.AnchoredInversionReadback
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy

/-! Adequacy of the proposed global world interfaces for the exact public
Pi-inversion contracts. All observations, identity frames and semantic
component comparisons are computed by actual bank calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

/-- This is the full existing stratified Pi-inversion conclusion, with its
original heights intact. Neither component conversion nor universe equality
is a supplied premise: equality and assigned comparison produce them. -/
theorem rawPiStratifiedInversionOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (equal : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (left : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (right : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A :: Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A :: Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A' :: Γ) B' (.sort u) true n' := by
  obtain ⟨assigned, equal⟩ := equal
  obtain ⟨original⟩ := Derivation.reify (equal.strong henv formed)
  have related := piCodeOfWorldBanks strata henv hscoped formed unary original
  exact related.literalPiStratifiedInversion henv formed
    (fun hcontext first second => sortTypingLevelsOfWorldBanks strata henv hcontext replay first second)
    left right

/-- The unstratified public consequence follows from the same bank execution. -/
theorem rawPiInversionOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (equal : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
      ∃ u, env.IsDefEq U (A :: Γ) B B' (.sort u) := by
  obtain ⟨assigned, raw⟩ := equal
  obtain ⟨left, right⟩ := (raw.strong henv formed).hasType'
  obtain ⟨_, left⟩ := left.stratify
  obtain ⟨_, right⟩ := right.stratify
  obtain ⟨⟨u, domain, _⟩, v, body, _⟩ := rawPiStratifiedInversionOfWorldBanks
    strata henv hscoped formed unary replay ⟨assigned, raw⟩ left right
  exact ⟨⟨u, domain⟩, v, body⟩

/-- The same nonempty Pi query rules out a universe on its other side. -/
theorem rawSortPiSeparationOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := by
  rintro ⟨assigned, equal⟩
  obtain ⟨original⟩ := Derivation.reify (equal.symm.strong henv formed)
  have related := piCodeOfWorldBanks strata henv hscoped formed unary original
  have literal := related Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at literal
  obtain ⟨witness⟩ := literal (.pi A B (.empty : Profile 0) []) (List.mem_singleton_self _)
  have impossible := witness.rightExposure.literalSort_head
  cases impossible

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
