import Lean4Lean.Verify.Inductive.Recursor.Check

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

/-- `InductiveSignature.Models` reads only the source fields of the declaration. -/
theorem _root_.Lean4Lean.InductiveSignature.Models.withRecs {s : InductiveSignature} {env : VEnv}
    {decl : VInductDecl} (H : s.Models env decl) (recs : List VRecursor) :
    s.Models env (decl.withRecs recs) where
  uvars := H.uvars
  nparams := H.nparams
  safety := H.safety
  families := H.families
  constructors := H.constructors
  classifiedFields := H.classifiedFields
  constructorArity := H.constructorArity

/-- `InductiveSignature.Compiles` reads only the source fields of the declaration. -/
theorem _root_.Lean4Lean.InductiveSignature.Compiles.withRecs {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : InductiveSignature.Compiles env decl block)
    (recs : List VRecursor) : InductiveSignature.Compiles env (decl.withRecs recs) block :=
  let ⟨s, g, envTypes, hm, rest⟩ := H.generated
  ⟨s, g, envTypes, hm.withRecs recs, rest⟩

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
      have h := H.recsAdded
      rw [VInductDecl.addRecs_eq_addConstVals, VInductDecl.withRecs_recs, H.recursors_eq] at h
      exact h,
    R.typesWF, R.ctorsWF,
    by rw [show T.block.recursors = H.recs.map (·.toVConstVal) from H.recursors_eq.symm]
       intro ci hci; obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci; exact H.recsWF r hr,
    T.equationsWF⟩

/-- The declaration compiles to the block (`VInductDecl.CompilesTo`, the ordinary case of
`CompiledInductive`). -/
theorem compilesTo (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    H.decl'.CompilesTo sourceEnv T.block := by
  have hnames : ((T.block.types ++ T.block.ctors ++ T.block.recursors).map (·.name)).Nodup := by
    have hR := H.addTypesCtorsProjsRecs
    rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
    obtain ⟨envF, hF, -⟩ := Option.map_eq_some_iff.1 hR
    have hnd := VEnv.addConst_foldlM_nodup (nm := Prod.fst) (ci := Prod.snd) hF
    have hrecs : T.block.recursors = H.recs.map (·.toVConstVal) := H.recursors_eq.symm
    rw [hrecs]
    simpa [block, VInductDecl.consts, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_append, List.map_map, Function.comp_def,
      List.map_flatMap] using hnd
  exact CompiledInductive.ordinary
    (VInductDecl.SourceWF.withRecs (TrInductDeclCore.sourceWF_ofNonempty R.core
      (TrInductDeclCore.nonempty R.core hnonempty)) H.recs)
    (R.formation.withRecs H.recs).formationWF (T.compiles.withRecs H.recs) T.blockWF rfl rfl rfl
    hnames

/-- Every model rule fires on a constructor with the signature's parameter count.

WAVE 2 STUB (Install, needs Recursor): `TrRecursor` reads `ru.ctorParams` off the constructor's
`ctorInfo` in the output map (`numParams`); the kernel declares the block's constructors with
`numParams = nparams` (`CtorInfoAlignment.numParams` of `inductInfosFromDecl`) and
`H.models.nparams` identifies `nparams` with the signature's parameter count. -/
theorem _root_.Lean4Lean.VerifyInductive.RecursorCheck.rules_ctorParams
    (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ru.ctorParams = H.signature.params.length := by
  have := H; sorry

/-- The model recursors and rules are read off the block (`VInductDecl.RecsOf`): the recursors
by `recursors_eq`, the rules through `TrRecursorRule` and `TrRecursor` agreeing on the reducts
(`VRecRule.OfEquation.ofTr`). -/
theorem recsOf (T : RuleTranslations H) : H.decl'.RecsOf T.block := by
  have hlenR : H.rvals.length = H.recs.length := (List.Forall₂.length_eq H.trRecs)
  have hlenF : (List.finRange H.signature.families.size).length = H.rvals.length :=
    (List.Forall₂.length_eq T.trRules)
  -- the rule `j` of recursor `i` is the generated equation of the `j`-th constructor of owner `i`
  have core : ∀ i (hiF : i < (List.finRange H.signature.families.size).length)
      (hiR : i < H.rvals.length) (hi : i < H.recs.length)
      j (hjO : j < (H.signature.ownedConstructors
        (List.finRange H.signature.families.size)[i]).length)
      (hjR : j < H.rvals[i].rules.length) (hj : j < H.recs[i].rules.length),
      VRecRule.OfEquation H.recs[i] H.recs[i].rules[j]
        (H.generation.equation (H.signature.ownedConstructors
          (List.finRange H.signature.families.size)[i])[j]) := by
    intro i hiF hiR hi j hjO hjR hj
    have htr := Lean4Lean.List.Forall₂.getElem_of H.trRecs i hiR hi
    have hrules := Lean4Lean.List.Forall₂.getElem_of T.trRules i hiF hiR
    have hmeta := Lean4Lean.List.Forall₂.getElem_of H.metadata i hiF hiR
    have hru := Lean4Lean.List.Forall₂.getElem_of htr.rules j hjR hj
    have hrule := Lean4Lean.List.Forall₂.getElem_of hrules j hjO hjR
    have howner : H.signature.constructors[(H.signature.ownedConstructors
        (List.finRange H.signature.families.size)[i])[j]].owner =
        (List.finRange H.signature.families.size)[i] := by
      have hmem := List.getElem_mem (l := H.signature.ownedConstructors
        (List.finRange H.signature.families.size)[i]) hjO
      simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
      exact hmem.2
    have hname : H.recs[i].name = H.generation.recursorName
        (List.finRange H.signature.families.size)[i] := by
      have h := congrArg (fun l => l[i]?) H.recursors_eq
      simp only [InductiveSignature.Instance.recursors, List.getElem?_map,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiF, Option.map_some,
        Option.some.injEq] at h
      exact congrArg VConstVal.name h
    refine InductiveSignature.VRecRule.OfEquation.ofTr hrule ?_ hru.1 hru.2.1 hru.2.2.2 ?_ ?_
    · rw [hname]; congr 1; exact (congrArg (fun o : Fin _ => o) howner).symm
    · rw [VRecursor.getMajorIdx, htr.numParams, htr.numMotives, htr.numMinors, htr.numIndices,
        hmeta.numParams, hmeta.numMotives, hmeta.numMinors, hmeta.numIndices]
      have hidx := congrArg
        (fun o : Fin H.signature.families.size => H.signature.families[o].indices.length) howner
      simp only [Fin.getElem_fin] at hidx ⊢
      omega
    · have := H.rules_ctorParams _ (List.getElem_mem hi) _ (List.getElem_mem hj)
      exact this
  refine ⟨H.recursors_eq, ?_, ?_⟩
  · intro r hr ru hru
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hru
    have hiR : i < H.rvals.length := hlenR ▸ hi
    have hiF : i < (List.finRange H.signature.families.size).length := hlenF ▸ hiR
    have htr := Lean4Lean.List.Forall₂.getElem_of H.trRecs i hiR hi
    have hrules := Lean4Lean.List.Forall₂.getElem_of T.trRules i hiF hiR
    have hjR : j < H.rvals[i].rules.length := (List.Forall₂.length_eq htr.rules) ▸ hj
    have hjO := (List.Forall₂.length_eq hrules) ▸ hjR
    exact ⟨_, List.mem_map_of_mem (List.mem_finRange _), core i hiF hiR hi j hjO hjR hj⟩
  · intro df hdf
    obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf
    let owner := H.signature.constructors[index].owner
    have hiF : owner.val < (List.finRange H.signature.families.size).length := by simp
    have hiR : owner.val < H.rvals.length := hlenF ▸ hiF
    have hi : owner.val < H.recs.length := hlenR ▸ hiR
    have hfin : (List.finRange H.signature.families.size)[owner.val] = owner := by simp
    have hmem : index ∈ H.signature.ownedConstructors
        (List.finRange H.signature.families.size)[owner.val] := by
      rw [hfin]
      simp [InductiveSignature.ownedConstructors, owner]
    obtain ⟨j, hjO, hj⟩ := List.getElem_of_mem hmem
    have htr := Lean4Lean.List.Forall₂.getElem_of H.trRecs owner.val hiR hi
    have hrules := Lean4Lean.List.Forall₂.getElem_of T.trRules owner.val hiF hiR
    have hjR : j < H.rvals[owner.val].rules.length := (List.Forall₂.length_eq hrules) ▸ hjO
    have hjr : j < H.recs[owner.val].rules.length := (List.Forall₂.length_eq htr.rules) ▸ hjR
    refine ⟨_, List.getElem_mem hi, _, List.getElem_mem hjr, ?_⟩
    have := core owner.val hiF hiR hi j hjO hjR hjr
    rw [hj] at this
    exact this

/-- `VInductDecl.RecsCompiled` of the installed declaration. -/
theorem recsCompiled (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    H.decl'.RecsCompiled sourceEnv :=
  ⟨T.block, T.compilesTo hnonempty, T.recsOf⟩

/-- The recursor half of `VInductDecl.WF`. -/
theorem recursorsWF (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    RecursorsWF sourceEnv H.decl' where
  recsCompiled := T.recsCompiled hnonempty
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

/-- The boundary theorem of the rule phase: the recursor check determines its rule
translations. No rule, telescope, or equation is chosen by the caller. -/
theorem RecursorCheck.generatedRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : RuleTranslations H := by
  -- WAVE 2 STUB (Rules/**): the source branch's `RecursorCheck.generatedRuleTranslation`
  -- (`Rules/RuleTranslations.lean`: `ruleRhsTranslations`, `equationsWF`, `trRules`) plus the
  -- `PatTyped` restatement of `generatorEquationWF` (PORT_PLAN section 2.3).
  have := H; sorry

end VerifyInductive
end Lean4Lean
