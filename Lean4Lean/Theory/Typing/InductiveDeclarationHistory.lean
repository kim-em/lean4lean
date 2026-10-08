import Lean4Lean.Theory.Typing.InductiveDeclarationStages
import Lean4Lean.Theory.Typing.DefinitionHistory

/-! Recover the original block and typing stages from an actual declaration
history. The predecessor history is strictly shorter, even when later
eliminator/projection registrations leave the declaration list unchanged.
-/

namespace Lean4Lean.VEnv
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory

structure InductiveStage (env : VEnv) (source : VInductDecl) (historyLength : Nat) where
  base : VEnv
  installed : VEnv
  block : VInductBlock
  earlierDeclarations : List VDecl
  earlierHistory : base.WF' earlierDeclarations
  earlier : earlierDeclarations.length < historyLength
  originalSource : source.WF base
  compilation : source.CompilesTo base block
  typing : VInductBlock.TypingStages base block installed
  installedBelow : installed ≤ env

namespace InductiveStage

def later {env extended : VEnv} {source : VInductDecl} {n m : Nat}
    (stage : InductiveStage env source n) (hle : env ≤ extended) (bound : n ≤ m) :
    InductiveStage extended source m where
  base := stage.base
  installed := stage.installed
  block := stage.block
  earlierDeclarations := stage.earlierDeclarations
  earlierHistory := stage.earlierHistory
  earlier := Nat.lt_of_lt_of_le stage.earlier bound
  originalSource := stage.originalSource
  compilation := stage.compilation
  typing := stage.typing
  installedBelow := stage.installedBelow.trans hle

end InductiveStage

/-- A source declaration occurring in the history retains its exact original
compiled block. No attempt is made to infer a predecessor proof from a
constant or rule lookup in the final environment. -/
theorem WF'.inductiveStage {env : VEnv} {declarations : List VDecl}
    (history : env.WF' declarations) {source : VInductDecl}
    (member : VDecl.induct source ∈ declarations) :
    Nonempty (InductiveStage env source declarations.length) := by
  induction history with
  | empty => cases member
  | @decl declaration installed declarations base declarationWF previous ih =>
    rcases List.mem_cons.mp member with same | old
    · cases same
      cases declarationWF with
      | induct original installation =>
        cases installation with
        | intro original' compilation blockWF eliminatorsWF installed =>
          obtain ⟨stages⟩ := VInductBlock.TypingStages.ofInstallation
            ⟨declarations, previous⟩ original compilation blockWF eliminatorsWF installed
          exact ⟨⟨base, _, _, declarations, previous, Nat.lt_succ_self _,
            original', compilation, stages, .rfl⟩⟩
    · obtain ⟨stage⟩ := ih old
      exact ⟨stage.later (declaration_le declarationWF) (Nat.le_succ _)⟩
  | inductEliminators _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨stage⟩ := ih member
    exact ⟨stage.later VEnv.addEliminator_le (Nat.le_refl _)⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨stage⟩ := ih member
    exact ⟨stage.later VEnv.addProjections_le (Nat.le_refl _)⟩

end Lean4Lean.VEnv
