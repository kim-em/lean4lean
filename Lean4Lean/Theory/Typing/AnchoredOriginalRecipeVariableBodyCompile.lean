import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredSortableEtaPack
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Execute the literal-variable terminal of a retained recipe program.
The input is an actual legacy body certificate and its original binder pack,
not the unported assertion that every rich variable query is already legacy.
The destination is the actual selected argument endpoint and table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000


structure RecipeVariableDemand (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (keyInput output : Profile n) where
  input : Profile n
  covered : input.atoms ⊆ keyInput.atoms
  rank : Nat
  bound : n ≤ rank
  adapter : GeneralNormalProfileAdapter env U registry target
    (raiseProfile rank bound input) (raiseProfile rank bound output)

/-- This is the actual binder-owned demand, computed from stored body syntax.
No unrelated entries of the enclosing argument support are requested. -/
theorem SortableCert.recipeVariableDemand
    {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (body : SortableCert env U registry target (Locals.push locals)
      (σ.cons anchor) (.bvar 0) relevant (output : Profile n) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : packed.atoms ⊆ keyInput.atoms)
    (resources : outside.Available available) :
    Nonempty (RecipeVariableDemand env U registry target keyInput output) := by
  let localNeeds := bodyFootprint.localNeeds
  have supplied := pack.available_atomized_localNeeds resources
  have leaves : ∀ index need, (index, need) ∈ bodyFootprint → index = 0 ∧
      need ∈ localNeeds ++ localNeeds.flatMap Need.singletons := by
    intro index need member
    have indexEq := body.variableTrace.indices member
    subst index
    exact ⟨rfl, supplied 0 need member⟩
  have bounded : ∀ index need, (index, need) ∈ bodyFootprint → need.rank ≤ n := by
    intro index need member
    exact (pack.atomized_localNeeds need (leaves index need member).2).1
  have included : (bodyFootprint.atGrade n).atoms ⊆ keyInput.atoms := by
    intro atom member
    obtain ⟨⟨index, need⟩, selected, belongs⟩ := List.mem_flatMap.mp member
    exact covered ((pack.atomized_localNeeds need (leaves index need selected).2).2 atom belongs)
  let trace := body.variableTrace
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  refine ⟨⟨bodyFootprint.atGrade n, included, N, hn, ?_⟩⟩
  rw [← Footprint.atGrade_raise hn bounded]
  exact trace.normalize henv hscoped formed N ht

/-- The `Family #0` application branch uses its actual variable argument
program and the SAME enclosing binder pack. Function-side demands stay outside
this selection. The result targets the application's advertised input through
its retained adapter. -/
theorem SortableObs.recipeVariableArgumentDemand
    {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (argument : SortableObs env U registry target (Locals.push locals)
      (σ.cons anchor) (.bvar 0) (rawInput : Profile n) argumentFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput requested)
    (pack : BinderPack n packed (functionFootprint ++ argumentFootprint) outside)
    (covered : packed.atoms ⊆ keyInput.atoms)
    (resources : outside.Available available) :
    Nonempty (RecipeVariableDemand env U registry target keyInput requested) := by
  let localNeeds := (functionFootprint ++ argumentFootprint).localNeeds
  have supplied := pack.available_atomized_localNeeds resources
  have leaves : ∀ index need, (index, need) ∈ argumentFootprint → index = 0 ∧
      need ∈ localNeeds ++ localNeeds.flatMap Need.singletons := by
    intro index need member
    have indexEq := argument.variableTrace.indices member
    subst index
    exact ⟨rfl, supplied 0 need (List.mem_append_right _ member)⟩
  have bounded : ∀ index need, (index, need) ∈ argumentFootprint → need.rank ≤ n := by
    intro index need member
    exact (pack.atomized_localNeeds need (leaves index need member).2).1
  have included : (argumentFootprint.atGrade n).atoms ⊆ keyInput.atoms := by
    intro atom member
    obtain ⟨⟨index, need⟩, selected, belongs⟩ := List.mem_flatMap.mp member
    exact covered ((pack.atomized_localNeeds need (leaves index need selected).2).2 atom belongs)
  let trace := argument.variableTrace
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  refine ⟨⟨argumentFootprint.atGrade n, included, N, hn, ?_⟩⟩
  rw [← Footprint.atGrade_raise hn bounded]
  exact (trace.normalize henv hscoped formed N ht).comp
    (GeneralNormalProfileAdapter.raise henv hscoped formed hn adapter)

/-- Only grade and finite adapter change; the destination observation keeps
its exact footprint and actual original endpoint. -/
noncomputable def RecipeVariableDemand.replay
    (demand : RecipeVariableDemand env U registry target keyInput output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable demand.input) :
    RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable output := by
  let N := max argument.rank demand.rank
  have ha : argument.rank ≤ N := Nat.le_max_left _ _
  have hp : demand.rank ≤ N := Nat.le_max_right _ _
  let raised := argument.raiseTo henv hscoped formed N ha
  refine ⟨N, Nat.le_trans demand.bound hp, raised.raw, raised.footprint,
    raised.observation, ?_, raised.resources, raised.live⟩
  have mapped := GeneralNormalProfileAdapter.raise henv hscoped formed hp demand.adapter
  simp only [raiseProfile_trans] at mapped
  exact raised.adapter.comp mapped

/-- The actual ordinary destination certificate uses only the selected
argument table; no old capture map is stored in its syntax. -/
theorem RecipeVariableDemand.compile
    (demand : RecipeVariableDemand env U registry target keyInput output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sorted : output.HasType (.sort relevant))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable demand.input) :
    ∃ footprint, ∃ certificate : RichCert argumentEnv env U registry target argumentNode
      argumentLocals argumentσ relevant output footprint,
      footprint.Available argumentAvailable ∧
      ∀ policy, certificate.headDepth policy ≤ argument.observation.headDepth policy := by
  let replayed := demand.replay henv hscoped formed argument
  obtain ⟨footprint, certificate, resources, depth⟩ := replayed.code_headDepth henv sorted
  refine ⟨footprint, certificate, resources, ?_⟩
  intro policy
  have bounded := depth policy
  simpa only [replayed, RecipeVariableDemand.replay, RichGradedResult.raiseTo,
    RichObs.headDepth_raise] using bounded

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
