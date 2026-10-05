import Lean4Lean.Theory.Typing.AnchoredOriginalWorldSortAdequacy
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldInitialFrame

/-! Conditional adequacy at the raw typing interface. Only the global world
banks and their explicit registry/stratification parameters remain hypotheses;
all identity frames, controls, resources, sponsors and query seeds are built. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- All target equations are installed at initial entry. The seed query and
all stored context observations have zero charged depth. -/
def worldAdequacyControls (strata : EquationStratification env) (henv : env.Ordered) :
    OriginalWorldControls strata env :=
  ⟨henv, strata.rules.length, Nat.le_refl _, strata.fullCutoff, fun _ => 0⟩

/-- The universe inversion consequence of an actual total unary producer. -/
theorem sortLevelsOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (original : Derivation env U Γ (.sort left) (.sort right) assigned) : left ≈ right := by
  let controls := worldAdequacyControls strata henv
  obtain ⟨context, locals, frame, captured, allReady⟩ := initialWorldFrame (registry := registry) controls formed
  obtain ⟨data⟩ := allReady [originalCallWorld controls .expressionReindex (.ref (.left original)) captured]
  exact Derivation.sortLevelsOfWorldUnary original henv hscoped formed controls frame captured data
    (fun _ _ member => False.elim (List.not_mem_nil member)) (Ctx.SubstEq.id henv formed) banks

theorem strongSortLevelsOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (equal : env.IsDefEqStrong U Γ (.sort left) (.sort right) assigned) : left ≈ right := by
  obtain ⟨original⟩ := Derivation.reify equal
  exact sortLevelsOfWorldBanks strata henv hscoped formed banks original

/-- This has the requested raw `IsDefEqU.sort_inv` conclusion. The only
additional substantive premise is the total unary producer at every world. -/
theorem rawSortLevelsOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (equal : env.IsDefEqU U Γ (.sort left) (.sort right)) : left ≈ right := by
  obtain ⟨assigned, equal⟩ := equal
  exact strongSortLevelsOfWorldBanks strata henv hscoped formed banks (equal.strong henv formed)

/-- Assigned comparison identifies the sorts of independently derived typings
of the same expression; it does not assume general uniqueness of typing. -/
theorem sortTypingLevelsOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (first : env.HasType U Γ expression (.sort left))
    (second : env.HasType U Γ expression (.sort right)) : left ≈ right := by
  obtain ⟨firstOriginal⟩ := Derivation.reify (first.strong henv formed)
  obtain ⟨secondOriginal⟩ := Derivation.reify (second.strong henv formed)
  let controls := worldAdequacyControls strata henv
  obtain ⟨context, locals, frame, captured, allReady⟩ := initialWorldFrame (registry := registry) controls formed
  obtain ⟨data⟩ := allReady
    [originalCallWorld controls .expressionReindex (.ref (.left firstOriginal)) captured,
     originalCallWorld controls .expressionReindex (.ref (.left secondOriginal)) captured]
  exact EndpointRef.sortTypingLevelsOfWorldReplay (.left firstOriginal) (.left secondOriginal)
    henv formed controls frame captured data
    (fun _ _ member => False.elim (List.not_mem_nil member)) (Ctx.SubstEq.id henv formed) banks

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
