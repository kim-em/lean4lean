import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Rules.RulesWF

/-! # The rule phase

The rules of the installed recursors are the generator's equations: each kernel rule's reduct
translates to the generated equation's reduct (`TrRecursorRule`), the generated equations are
well formed in the recursor-stage environment (as `VDefEq`s, for the compiled block), and each
model rule is typed as a schematic ι rule (`VEnv.PatTyped`, the `rules_wf` clause of
`VInductDecl.WF`; PORT_PLAN section 2.3 restates the source branch's `generatorEquationWF` in the
open equation context as the generic instance). `RuleTranslations` is the frozen interface;
`RecursorCheck.generatedRuleTranslation` is the boundary theorem.

Wave 2 scaffold: owned by the `Rules/**` agent (source branch: `Rules/{Alignment,EquationList,
EquationTranslation,EquationWF,FromTemplates,Lhs,LhsTranslation,MinorContext,MinorPremise,
Motive,RecursiveApplication,RecursiveBody,RecursiveCall,RecursiveCallScope,RecursiveResults,
Rhs,RuleSyntax,RuleTranslations,Translation}.lean`). The rule phase consumes the recursor
phase's internals (rule templates, minor contexts), so its port lands after the recursor
agent's. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The rule translations of a recursor check: coverage of every kernel rule by the generated
equation of its constructor, well-formedness of the generated equations in the recursor stage,
and the typing of every model rule as a registered ι rule. -/
structure RuleTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : Prop where
  /-- Each kernel recursor's rules are, in order, the generated equations of the constructors
  it owns. -/
  trRules : List.Forall₂ (fun (owner : Fin H.signature.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule H.generation H.outVEnv rval.levelParams)
        (H.signature.ownedConstructors owner) rval.rules)
    (List.finRange H.signature.families.size) H.rvals
  /-- The generated equations are well formed in the recursor stage (the `rules` clause of
  `VInductBlock.WF` for the compiled block). -/
  equationsWF : ∀ df ∈ H.generation.equations, df.WF H.outVEnv
  /-- `VInductDecl.WF.rules_wf`: every model rule is typed as a schematic ι rule in the
  recursor stage. -/
  rules_wf : ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
    H.outVEnv.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

namespace RuleTranslations

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
  {H : RecursorCheck R outEnv}

/-- The compiled block of the recursor check: the declaration's constants, the generated
recursors and equations, the declaration's projection entries. -/
def block (_T : RuleTranslations H) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  recursors := H.generation.recursors
  rules := H.generation.equations
  projections := decl.projectionEntries

/-- The block compiles the declaration (`InductiveSignature.Compiles`). -/
theorem compiles (T : RuleTranslations H) :
    InductiveSignature.Compiles sourceEnv decl T.block :=
  ⟨H.signature, H.generation, R.headerVEnv, H.models, R.core.typesAdded, H.admissible,
    ⟨R.ctorVEnv, R.core.ctorsAdded, H.ihsWellTyped, H.familyTypesWF⟩,
    H.recursorNames, rfl, rfl⟩

/-- The block is well formed in the source environment (`VInductBlock.WF`). -/
theorem blockWF (T : RuleTranslations H) : T.block.WF sourceEnv :=
  ⟨R.headerVEnv, R.ctorVEnv, H.outVEnv, R.core.typesAdded, R.core.ctorsAdded,
    by
      have := H.recsAdded
      rw [VInductDecl.addRecs, VInductDecl.withRecs_recs] at this
      -- `addRecs` is `addConstVals` over the recursors' constants
      -- WAVE 2 STUB (Install): `VInductDecl.addRecs_eq_addConstVals`, then `recursors_eq`
      sorry,
    R.typesWF, R.ctorsWF,
    by rw [show T.block.recursors = H.recs.map (·.toVConstVal) from H.recursors_eq.symm]
       intro ci hci; obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci; exact H.recsWF r hr,
    T.equationsWF⟩

/-- The declaration compiles to the block (`VInductDecl.CompilesTo`, the ordinary case of
`CompiledInductive`). -/
theorem compilesTo (T : RuleTranslations H) : H.decl'.CompilesTo sourceEnv T.block := by
  -- WAVE 2 STUB (Install): `CompiledInductive.intro` with no auxiliaries, from `compiles`,
  -- `blockWF`, `R.formation`, `R.core` (the source branch's
  -- `OrdinaryCompilationCertificate.compilesTo`, `Compilation.lean`).
  have := T.compiles; have := T.blockWF; sorry

/-- The model recursors and rules are read off the block (`VInductDecl.RecsOf`): the recursors
by `recursors_eq`, the rules through `TrRecursorRule` and `TrRecursor` agreeing on the reducts
(`VRecRule.OfEquation.ofTr`). -/
theorem recsOf (T : RuleTranslations H) : H.decl'.RecsOf T.block := by
  -- WAVE 2 STUB (Install)
  have := T.trRules; have := H.trRecs; sorry

/-- `VInductDecl.RecsCompiled` of the installed declaration. -/
theorem recsCompiled (T : RuleTranslations H) : H.decl'.RecsCompiled sourceEnv :=
  ⟨T.block, T.compilesTo, T.recsOf⟩

/-- The recursor half of `VInductDecl.WF`. -/
theorem recursorsWF (T : RuleTranslations H) : RecursorsWF sourceEnv H.decl' where
  recsCompiled := T.recsCompiled
  recs_wf envP hP := by
    have : envP = R.envP := by
      have h := R.addTypesCtorsProjs (decl := decl)
      rw [show H.decl'.addTypesCtorsProjs sourceEnv = decl.addTypesCtorsProjs sourceEnv from rfl,
        h] at hP
      exact (Option.some.inj hP).symm
    subst this; exact H.recsWF
  rec_shape := H.rec_shape
  rules_nodup := H.rules_nodup
  rules_ctor envC hC r hr ru hru := by
    have : envC = R.ctorVEnv := by
      have h := R.addTypesCtors (decl := decl)
      rw [show H.decl'.addTypesCtors sourceEnv = decl.addTypesCtors sourceEnv from rfl, h] at hC
      exact (Option.some.inj hC).symm
    subst this; exact H.rules_ctor r hr ru hru
  rule_shape := H.rule_shape
  rules_wf envR hR := by
    have : envR = H.outVEnv := by
      rw [H.addTypesCtorsProjsRecs] at hR; exact (Option.some.inj hR).symm
    subst this; exact T.rules_wf

end RuleTranslations

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- Rule coverage: each kernel rule's constructor, field count and reduct are the generated
equation's. -/
theorem RecursorCheck.rulesCovered (H : RecursorCheck R outEnv) : H.RulesCovered := by
  -- WAVE 2 STUB (Rules, pending the recursor phase's internals): the source branch's
  -- `RecursorCheck.trRules` (`Rules/RuleTranslations.lean`) from `ruleRhsTranslations`
  -- (`Rules/Translation.lean`), `ruleAlignment` (`Rules/Alignment.lean`) and the rule templates
  -- of `mkRecInfos` (`generated_rules_eq`); stated against the source `RecursorCheck`'s
  -- `recInfos`, `generated`, `canonicalGeneration`, `origins`, which the scaffold's
  -- `RecursorCheck` does not carry yet.
  have := H; sorry

/-- The generated equations are well formed in the recursor stage. -/
theorem RecursorCheck.equationsWF (H : RecursorCheck R outEnv) : H.EquationsWF := by
  -- WAVE 2 STUB (Rules, pending the recursor phase's internals): the source branch's
  -- `RecursorCheck.equationsWF` (`Rules/EquationWF.lean`) from the typed rule templates
  -- (`ruleTyping : TypedRecursorRulesRange`, `RuleAlignment.generatorEquationWF`) and
  -- `equationBodyTranslations_of`.
  have := H; sorry

/-- Every model rule fires on a constructor with the signature's parameter count. -/
theorem RecursorCheck.ruleCtorParams (H : RecursorCheck R outEnv) : H.RuleCtorParams := by
  -- WAVE 2 STUB (Rules, pending an upstream field): `TrRecursor.rules` reads `ctorParams` off
  -- the constructor's `ctorInfo` in `outEnv`; that it is `decl.nparams` (= `signature.params.length`
  -- by `models.nparams`) is the kernel constructors' `numParams` (`declareConstructors`), which
  -- `ConstructorCheck` does not record (`ivals` carries no `numParams` fact).
  have := H; sorry

end

/-- The boundary theorem of the rule phase: the recursor check determines its rule
translations. No rule, telescope, or equation is chosen by the caller. The `rules_wf` clause is
the `PatTyped` restatement of the generated equations' `VDefEq.WF` (`RecursorCheck.rules_wf_of`,
PORT_PLAN section 2.3). -/
theorem RecursorCheck.generatedRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : RuleTranslations H where
  trRules := H.rulesCovered
  equationsWF := H.equationsWF
  rules_wf := H.rules_wf_of H.rulesCovered H.equationsWF H.ruleCtorParams

end VerifyInductive
end Lean4Lean
