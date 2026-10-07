import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration

/-! The original typing environments of an installed inductive block.

In particular, equation typing is retained before the block's equations are
added. Moving its raw typing to a later environment is harmless; using that
move as a new semantic induction child would lose this stage information.
The intermediate well-formedness proofs below use fresh constant additions
and the actual projection registration, without installing any current rule.
-/

namespace Lean4Lean
open VExpr VEnv

structure VInductBlock.TypingStages (base : VEnv) (block : VInductBlock)
    (installed : VEnv) where
  types : VEnv
  constructors : VEnv
  recursors : VEnv
  addTypes : base.addConstVals block.types = some types
  addConstructors : types.addConstVals block.ctors = some constructors
  addRecursors : ((constructors.addEliminators block.eliminators).addProjections block.projections).addConstVals
    block.recursors = some recursors
  installed_eq : installed = recursors.addDefEqRules block.rules
  typesWF : types.WF
  constructorsWF : constructors.WF
  projectionsWF : ((constructors.addEliminators block.eliminators).addProjections block.projections).WF
  recursorsWF : recursors.WF
  originalTypes : ∀ ci ∈ block.types, ci.toVConstant.WF base
  originalConstructors : ∀ ci ∈ block.ctors, ci.toVConstant.WF types
  originalRecursors : ∀ ci ∈ block.recursors,
    ci.toVConstant.WF ((constructors.addEliminators block.eliminators).addProjections block.projections)
  originalRules : ∀ df ∈ block.rules, df.WF recursors

namespace VInductBlock.TypingStages

theorem ofInstallation {base installed : VEnv} {source : VInductDecl}
    {block : VInductBlock} (hbase : base.WF)
    (hsource : source.WF base) (hcompile : source.CompilesTo base block)
    (hblock : block.WF base) (helim : VInductBlock.EliminatorsWF base source block)
    (hinstall : block.install base = some installed) :
    Nonempty (TypingStages base block installed) := by
  obtain ⟨types, constructors, recursors, ht, hc, hr, wt, wc, wr, we⟩ := hblock
  have typesWF := hbase.addConstVals wt ht
  have constructorsWF := typesWF.addConstVals wc hc
  have ht' : base.addConstVals source.typeConstants = some types := by
    simpa only [hcompile.types] using ht
  have projectionsWF := VInductBlock.EliminatorsWF.projectionsWF helim hbase hsource hcompile ht hc
  have recursorsWF := projectionsWF.addConstVals wr hr
  have installed_eq : installed = recursors.addDefEqRules block.rules := by
    simpa [VInductBlock.install, ht, hc, hr] using hinstall.symm
  exact ⟨⟨types, constructors, recursors, ht, hc, hr, installed_eq,
    typesWF, constructorsWF, projectionsWF, recursorsWF, wt, wc, wr, we⟩⟩

variable {base installed : VEnv} {block : VInductBlock}

/-- All rules usable in the equation-typing stage come from the old base.
Current recursor constants are present but have no newly installed equations. -/
theorem recursor_defeqs (stages : TypingStages base block installed) :
    stages.recursors.defeqs = base.defeqs := by
  rw [VEnv.addConstVals_defeqs stages.addRecursors, VEnv.addProjections_defeqs,
    VEnv.addEliminators_defeqs, VEnv.addConstVals_defeqs stages.addConstructors,
    VEnv.addConstVals_defeqs stages.addTypes]

theorem base_le_recursors (stages : TypingStages base block installed) :
    base ≤ stages.recursors :=
  (VEnv.addConstVals_le stages.addTypes).trans <|
    (VEnv.addConstVals_le stages.addConstructors).trans <|
      VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le stages.addRecursors)

theorem recursors_le (stages : TypingStages base block installed) :
    stages.recursors ≤ installed := by
  simpa only [stages.installed_eq] using
    (VEnv.addDefEqRules_le (env := stages.recursors) (dfs := block.rules))

/-- The original equation endpoints may be strengthened once, at their
actual predecessor stage. They are available to the stage induction without
looking up the rule in the completed environment. -/
theorem ruleStrong (stages : TypingStages base block installed)
    {equation : VDefEq} (member : equation ∈ block.rules) :
    stages.recursors.IsDefEqStrong equation.uvars [] equation.lhs equation.lhs equation.type ∧
      stages.recursors.IsDefEqStrong equation.uvars [] equation.rhs equation.rhs equation.type :=
  ⟨(stages.originalRules equation member).1.strong stages.recursorsWF.ordered trivial,
    (stages.originalRules equation member).2.strong stages.recursorsWF.ordered trivial⟩

/-- Recursor-domain formation precedes even the current recursor constants.
The original proof, rather than a final-environment constant inversion, is
the source of literal telescope formation payloads. -/
theorem recursorTypeStrong (stages : TypingStages base block installed)
    {value : VConstVal} (member : value ∈ block.recursors) :
    ∃ level, ((stages.constructors.addEliminators block.eliminators).addProjections block.projections).IsDefEqStrong
      value.uvars [] value.type value.type (.sort level) := by
  obtain ⟨level, original⟩ := stages.originalRecursors value member
  exact ⟨level, original.strong stages.projectionsWF.ordered trivial⟩

end VInductBlock.TypingStages
end Lean4Lean
