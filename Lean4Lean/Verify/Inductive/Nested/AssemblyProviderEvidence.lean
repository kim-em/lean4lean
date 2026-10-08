import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.CompletedEquationFinal
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryEvidence
import Lean4Lean.Verify.Inductive.Nested.FormationNativeEvidence
import Lean4Lean.Verify.Inductive.CompletedEquationSetup
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun
import Lean4Lean.Verify.Inductive.Nested.ValidationEnvironmentRegistry
import Lean4Lean.Verify.Inductive.Nested.FinalShapes
import Lean4Lean.Verify.Inductive.Nested.CaseEliminators
import Lean4Lean.Verify.Inductive.Nested.ConstructorTelescopes

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! # Exact evidence boundary for nested final assembly

`NestedFinalAssemblyShapeEvidence` is the certificate-facing aggregate.
This module decomposes that aggregate into evidence indexed by the exact
lowering/restoration run. Source non-emptiness, source-map well-formedness,
and the fresh-constant trace are derived operationally. None of the remaining
semantic records is intended to be supplied at the public declaration
boundary; the final construction must derive them from the same run.

The fields are split by role:

* `NestedFinalAssemblyExactLayout` only aligns the exact fresh entries with
  canonical dependency order and identifies the recursor value suffix;
* `NestedFinalAuxiliaryEvidence` contains the genuinely semantic auxiliary
  recursor/rule trace and its final well-formedness proof;
* `NestedFinalAssemblyShapeSemanticEvidence` retains canonical installation,
  formation, and pointwise source/primary semantics, but no executable
  freshness or lowering non-emptiness assumptions.
-/

private theorem List.nodup_of_map_nodup
    {values : List α} (f : α → β) (H : (values.map f).Nodup) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.nodup_cons] at H ⊢
      exact ⟨fun hmem => H.1 (List.mem_map_of_mem hmem), ih H.2⟩

/-- Strengthen the restored-recursion shape constructor with the two exact
production cardinalities which the specification-facing shape deliberately
does not retain.  This repeats the existing telescope split while keeping its
chosen motive/minor lists visible to primary-iota assembly. -/
theorem RecursorRestoration.nestedRecursorShapeWithCardinality
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (Harities : RecInfoArities stats recInfos)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (hdeclOwner : ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[ownerIdx] = owner)
    (recursor : VConstVal)
    (hname : recursor.name = sourceDecl.recursorName owner)
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (hnparams : sourceDecl.nparams = result.nparams)
    (hmotives : sourceDecl.types.length ≤
      (recInfos.map (·.motive)).size)
    (hminors : sourceDecl.ownedConstructors.length ≤
      (recInfos.flatMap (·.minors)).size)
    (hindices : owner.numIndices = recInfos[ownerIdx]!.indices.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type recursor.type) :
    ∃ Hshape : sourceDecl.NestedRecursorShape owner recursor,
      Hshape.motives.length = (recInfos.map (·.motive)).size ∧
      Hshape.minors.length = (recInfos.flatMap (·.minors)).size ∧
      owner.numIndices = newInfo.numIndices ∧
      newInfo.numParams = result.nparams ∧
      newInfo.numMotives = (recInfos.map (·.motive)).size ∧
      newInfo.numMinors = (recInfos.flatMap (·.minors)).size := by
  have Htelescope := Hrestore.typeConcreteRecursorResultForallTelescope
    Hentry Hselections howner hnoalias hparams
  rcases TrExprS.forallTelescope_shape_with_context Htelescope Htranslation
      with ⟨domains, abstractResult, hdomainsLength, htype, Hresult⟩
  have htotal : result.nparams + (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 ≤ domains.length := by
    rw [hdomainsLength]
    simp only [Nat.add_assoc, Nat.le_refl]
  have hownerMotive : ownerIdx < (recInfos.map (·.motive)).size := by
    simpa using howner
  have hresultConcrete := TrExprS.concreteRecursorResult_eq
    (numParams := result.nparams) hownerMotive htotal Hresult
  have hdomainsSpec : domains.length =
      sourceDecl.nparams + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + owner.numIndices + 1 := by
    rw [hdomainsLength, hnparams, hindices]
    simp only [Nat.add_assoc]
  rcases List.exists_append_five_of_length_eq domains sourceDecl.nparams
      (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size owner.numIndices 1 hdomainsSpec with
    ⟨params, motives, minors, indices, major, hdomains,
      hparamsLength, hmotivesLength, hminorsLength, hindicesLength,
      hmajorLength⟩
  have hresult : abstractResult = sourceDecl.recursorResultWithCounts
      ownerIdx motives.length minors.length owner := by
    simpa [VInductDecl.recursorResultWithCounts, List.map_reverse,
      hmotivesLength, hminorsLength, hindices] using hresultConcrete
  let Hshape := VInductDecl.NestedRecursorShape.ofWrapped hdeclOwner hownerEq
    hname huvars hparamsLength (by simpa [hmotivesLength] using hmotives)
    (by simpa [hminorsLength] using hminors) hindicesLength hmajorLength
    (by simpa [hdomains] using htype) hresult
  refine ⟨Hshape, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change motives.length = (recInfos.map (·.motive)).size
    exact hmotivesLength
  · change minors.length = (recInfos.flatMap (·.minors)).size
    exact hminorsLength
  · calc
      owner.numIndices = recInfos[ownerIdx]!.indices.size := hindices
      _ = stats.nindices[ownerIdx]! := Harities ownerIdx howner
      _ = Hentry.info.numIndices := Hentry.numIndices.symm
      _ = newInfo.numIndices := Hrestore.numIndices.symm
  · exact (Hrestore.numParams.trans Hentry.numParams).trans hparams.symm
  · exact Hrestore.numMotives.trans Hentry.numMotives
  · exact Hrestore.numMinors.trans Hentry.numMinors

/-- The operational/source constructor join is lockstep in all three lists.
This exposes the rule-cardinality fact needed to fold one restored primary
recursor without asking final assembly to restate constructor layout. -/
theorem RestoredConstructorSemanticMappingTrace.lengths
    (H : RestoredConstructorSemanticMappingTrace result mappingEnv loweredEnv
      params nparams safety lparams canonicalEnv sources state targets
        finalState sourceProdEnv targetProdEnv constructors) :
    sources.length = targets.length ∧ targets.length = constructors.length := by
  induction H with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ _ Hrest ih =>
    exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- Fold the literal restoration list from pointwise rule certificates produced
by the post-restoration validator. Each certificate names the exact declarative
rule and its WF proof in the final checked environment. -/
theorem RestoredPrimaryIotaFamilySemantics.ofValidatedExactRules
    {decl : VInductDecl} {block : VInductBlock} {targetVEnv : VEnv}
    {owner : VInductiveType} {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {P : NestedInstalledProduction loweredEnv}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {indType : InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv}
    (hlength : owner.ctors.length =
      Hstep.restored.recursor.oldInfo.rules.length)
    (Hvalidated : ∀ i (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length),
      ∃ abstractRule : VDefEq,
        Nonempty (decl.NestedIotaRule block owner owner.ctors[i] abstractRule) ∧
        abstractRule.WF targetVEnv) :
    Nonempty (RestoredPrimaryIotaFamilySemantics decl block targetVEnv owner
      P Hstep) := by
  let H := Hstep.restored.recursor.restored.restoration.rules
  have fold : ∀ {oldRules newRules}
      (Hrules : RulesRestoration result loweredEnv auxRec
        (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName oldRules newRules)
      (ctors : List VConstVal),
      ctors.length = oldRules.length →
      (∀ i (hctor : i < ctors.length) (hold : i < oldRules.length)
        (hnew : i < newRules.length),
        ∃ abstractRule : VDefEq,
          Nonempty (decl.NestedIotaRule block owner ctors[i] abstractRule) ∧
          abstractRule.WF targetVEnv) →
      ∃ rules, RestoredPrimaryIotaRuleTrace decl block owner result
        loweredEnv P targetVEnv auxRec (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName Hrules ctors rules := by
    intro oldRules newRules Hrules
    induction Hrules with
    | nil =>
        intro ctors hctors _Hpoint
        have : ctors = [] := List.eq_nil_of_length_eq_zero hctors
        subst ctors
        exact ⟨[], .nil⟩
    | @cons oldRule newRule oldRules newRules Hrule Htail ih =>
        intro ctors hctors Hpoint
        cases ctors with
        | nil => simp at hctors
        | cons ctor ctors =>
            have htail : ctors.length = oldRules.length := by
              simpa using hctors
            rcases Hpoint 0 (by simp) (by simp) (by simp) with
              ⟨abstractRule, ⟨Hshape⟩, Hwf⟩
            rcases ih ctors htail (fun i hctor hold hnew => by
              have Hnext := Hpoint (Nat.succ i) (by simpa) (by simpa)
                (by simpa)
              simpa using Hnext) with ⟨rules, Hrest⟩
            exact ⟨abstractRule :: rules,
              .cons Hrule Htail abstractRule Hshape Hwf Hrest⟩
  rcases fold H owner.ctors hlength Hvalidated with ⟨rules, Htrace⟩
  exact ⟨⟨rules, Htrace⟩⟩

/-- Rule cardinality is forced by the exact generated recursor entry and the
lockstep source/lowered/abstract constructor trace. -/
theorem RestoredPrimaryOperationalFamilySemantics.ruleCardinality
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor) :
    owner.ctors.length = Hstep.restored.recursor.oldInfo.rules.length := by
  have Hlengths := F.constructors.lengths
  obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp A.targetAt
  have harray : result.types.toArray[familyIdx]! = A.target := by
    simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
  let E := Hprod.generated.entry familyIdx hentry
  have holdInfo := Hprod.restoredPrimaryInfo_eq_generated familyIdx hentry
    Hstep.restored.recursor A.oldRecName
  calc
    owner.ctors.length = A.target.ctors.length := Hlengths.2.symm
    _ = result.types.toArray[familyIdx]!.ctors.length := by rw [harray]
    _ = E.info.rules.length := E.rules.length.symm
    _ = Hstep.restored.recursor.oldInfo.rules.length := by rw [holdInfo]

/-- Reconstruct the exact restored source-recursion shape at the same family
position as the operational primary restoration.  Unlike the shape projected
through `RestoredPrimaryRecursorSemantics`, this witness retains the generated
motive/minor cardinalities needed to reinterpret the canonical equation. -/
theorem RestoredPrimaryOperationalFamilyAlignment.exactSourceRecursorShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    (A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (owner : VInductiveType)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[familyIdx] = owner)
    (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor recEnv) :
    ∃ Hshape : sourceDecl.NestedRecursorShape owner Hrecursor.recursor,
      Hshape.motives.length = loweredDecl.types.length ∧
      Hshape.minors.length = loweredDecl.ownedConstructors.length ∧
      owner.numIndices = Hstep.restored.recursor.restored.newInfo.numIndices ∧
      Hstep.restored.recursor.restored.newInfo.numParams = result.nparams ∧
      Hstep.restored.recursor.restored.newInfo.numMotives =
        loweredDecl.types.length ∧
      Hstep.restored.recursor.restored.newInfo.numMinors =
        loweredDecl.ownedConstructors.length := by
  let E := Hprod.generated.entry familyIdx hentry
  have holdInfo := Hprod.restoredPrimaryInfo_eq_generated familyIdx hentry
    Hstep.restored.recursor A.oldRecName
  have Hrestore : RecursorRestoration result loweredEnv auxRec allIndNames
      (Lean.mkRecName sourceTypes[familyIdx].name)
      Hstep.restored.recursor.restored.newRecName E.info
      Hstep.restored.recursor.restored.newInfo := by
    simpa only [holdInfo] using
      Hstep.restored.recursor.restored.restoration
  rcases Hrecursor.shape with ⟨HexistingShape⟩
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlowering.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    simpa [Hprod.cardinality.records] using hrecInfo
  have hindices : owner.numIndices = Hprod.recInfos[familyIdx]!.indices.size := by
    have hsourceIndices := Hmetadata.numIndices hdeclLength familyIdx hdecl
      hloweredDecl
    rw [hownerEq] at hsourceIndices
    exact hsourceIndices.trans
      (Hprod.cardinality.indices familyIdx hrecInfo).symm
  have hmotives : sourceDecl.types.length ≤
      (Hprod.recInfos.map (·.motive)).size := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlowering.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = Hprod.recInfos.size := Hprod.cardinality.records.symm
      _ = (Hprod.recInfos.map (·.motive)).size := by simp
  have hminors : sourceDecl.ownedConstructors.length ≤
      (Hprod.recInfos.flatMap (·.minors)).size := by
    calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        Hlowering.toResult.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          R.core
      _ = (Hprod.recInfos.flatMap (·.minors)).size :=
        Hprod.cardinality.minors.symm
  have Htranslation : TrExprS recEnv E.info.levelParams []
      Hstep.restored.recursor.restored.newInfo.type Hrecursor.recursor.type := by
    simpa only [holdInfo] using Hrecursor.type
  rcases Hrestore.nestedRecursorShapeWithCardinality E
      A.recursor.selections Hprod.arities A.recursor.owner_lt A.recursor.noAlias
      A.recursor.nparams_eq sourceDecl owner hdecl hownerEq
      Hrecursor.recursor HexistingShape.name HexistingShape.uvars
      (Hsource.nparams.trans Hlowering.toResult.resultNParams.symm)
      hmotives hminors hindices Htranslation with
    ⟨Hshape, hmotivesExact, hminorsExact, hindicesExact, hparamsExact,
      hmotivesInfo, hminorsInfo⟩
  exact ⟨Hshape,
    hmotivesExact.trans (by
      simpa using Hprod.cardinality.records),
    hminorsExact.trans Hprod.cardinality.minors,
    hindicesExact, hparamsExact,
    hmotivesInfo.trans (by simpa using Hprod.cardinality.records),
    hminorsInfo.trans Hprod.cardinality.minors⟩

/-- Construct one complete primary family directly from the successful
post-restoration rule validator.  The generated producer and lowering traces
are used only to identify the exact owner/constructor metadata; equation
shape, guardedness, and WF all come from the literal checked rule. -/
theorem RestoredPrimaryOperationalFamilySemantics.primaryIotaFamilyOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor recEnv}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (hdecl : familyIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[familyIdx] = owner)
    (restoredBlock : VInductBlock) (targetVEnv : VEnv)
    (hrecursorMem : Hrecursor.recursor ∈ restoredBlock.recursors)
    (hrecursorNames : restoredBlock.recursors.map (·.name) =
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        auxRec.getD oldName oldName) ++
      auxRecNames.map fun oldName => auxRec.getD oldName oldName)
    (hprimaryName : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName sourceTypes[familyIdx].name)
    (Hvalid : CheckingEnv.Valid c.safety ruleEnv targetVEnv)
    (Hrun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      c.lparams c.safety validationFuel result auxRec allIndNames sourceTypes
        auxRecNames = .ok ()) :
    let P : NestedInstalledProduction loweredEnv := {
      c := c
      stats := stats
      loweredDecl := loweredDecl
      nparams := nparams
      depth := depth
      isUnsafe := isUnsafe
      initialEnv := sourceVEnv
      indTypes := result.types.toArray
      headerEnv := headerEnv
      ctorEnv := ctorEnv
      headers := Hheaders
      constructors := R
      production := Hprod }
    Nonempty (RestoredPrimaryIotaFamilySemantics sourceDecl restoredBlock
      targetVEnv owner P Hstep) := by
  dsimp only
  let P : NestedInstalledProduction loweredEnv := {
    c := c
    stats := stats
    loweredDecl := loweredDecl
    nparams := nparams
    depth := depth
    isUnsafe := isUnsafe
    initialEnv := sourceVEnv
    indTypes := result.types.toArray
    headerEnv := headerEnv
    ctorEnv := ctorEnv
    headers := Hheaders
    constructors := R
    production := Hprod }
  apply RestoredPrimaryIotaFamilySemantics.ofValidatedExactRules
    F.ruleCardinality
  intro i hctor hold hnew
  have htype : sourceTypes[familyIdx] ∈ sourceTypes :=
    List.getElem_mem hfamily
  have hsourceRule : Hstep.restored.recursor.oldInfo.rules[i] ∈
      Hstep.restored.recursor.oldInfo.rules := List.getElem_mem hold
  have Hexact :=
    validateRestoredRecursorRules.primaryValidatedExactRule_of_run Hvalid
      Hrun htype Hstep.restored.recursor.lookup hsourceRule
  dsimp only at Hexact
  rw [← Hstep.restored.recursor.restored.produced] at Hexact
  have HnewRule : Hstep.restored.recursor.restored.newInfo.rules[i] =
      result.restoreRule loweredEnv auxRec
        (Lean.mkRecName sourceTypes[familyIdx].name)
        (auxRec.getD (Lean.mkRecName sourceTypes[familyIdx].name)
          (Lean.mkRecName sourceTypes[familyIdx].name))
        Hstep.restored.recursor.oldInfo.rules[i] := by
    have HrulesEq : Hstep.restored.recursor.restored.newInfo.rules =
        Hstep.restored.recursor.oldInfo.rules.map
          (result.restoreRule loweredEnv auxRec
            (Lean.mkRecName sourceTypes[familyIdx].name)
            (auxRec.getD (Lean.mkRecName sourceTypes[familyIdx].name)
              (Lean.mkRecName sourceTypes[familyIdx].name))) := by
      simpa only [Lean4Lean.ElimNestedInductive.Result.restoreRecursor] using
        congrArg RecursorVal.rules
          Hstep.restored.recursor.restored.produced
    apply (List.getElem_eq_iff hnew).2
    rw [HrulesEq, List.getElem?_map, List.getElem?_eq_getElem hold]
    rfl
  rw [← HnewRule] at Hexact
  rcases Hexact with
    ⟨lhs, _lhsInferred, _residual, plan, canonicalPlan, domains, lhsBody,
      rhsBody, typeBody, abstractRule, _Hbuild, _Hplan, Hindices,
      HctorUvars, _Hprefix, _Hcanonical, _Hrhs, _Hlhs, HruleUvars,
      ⟨Hwf⟩, _Htelescope, _hresidual, hdomains, HlhsWrapped,
      HrhsWrapped, HtypeWrapped, Hguard, ⟨HlhsSpine⟩, shape,
      ⟨HrhsSpine⟩⟩
  rcases A.exactSourceRecursorShape Hsource Hmetadata hempty owner hdecl
      hownerEq Hrecursor with
    ⟨Hshape, Hmotives, Hminors, HownerIndices, Hparams, HinfoMotives,
      HinfoMinors⟩
  have HdeclParams : sourceDecl.nparams = result.nparams :=
    Hsource.nparams.trans Hlowering.toResult.resultNParams.symm
  have Hprefix : sourceDecl.nparams + Hshape.motives.length +
      Hshape.minors.length =
        Hstep.restored.recursor.restored.newInfo.numParams +
          Hstep.restored.recursor.restored.newInfo.numMotives +
          Hstep.restored.recursor.restored.newInfo.numMinors := by
    rw [HdeclParams, Hmotives, Hminors, Hparams, HinfoMotives, HinfoMinors]
  have HrecursorName : Hrecursor.recursor.name =
      Hstep.restored.recursor.restored.newInfo.name :=
    Hrecursor.name.trans
      Hstep.restored.recursor.restored.restoration.name.symm
  have HrecursorUvars : Hrecursor.recursor.uvars =
      Hstep.restored.recursor.restored.newInfo.levelParams.length :=
    Hrecursor.uvars.symm.trans (congrArg List.length
      Hstep.restored.recursor.restored.restoration.levelParams.symm)
  have HdeclNparams : sourceDecl.nparams =
      Hstep.restored.recursor.restored.newInfo.numParams :=
    HdeclParams.trans Hparams.symm
  have HownerPlanIndices : owner.numIndices = plan.indices.size :=
    HownerIndices.trans Hindices.symm
  have HdeclCtorUvars : sourceDecl.uvars = plan.ctorLevels.length :=
    Hsource.uvars.trans HctorUvars.symm
  have hsourceCtor : i < sourceTypes[familyIdx].ctors.length := by
    simpa [F.constructors.lengths.1, F.constructors.lengths.2] using hctor
  have htargetCtor : i < A.target.ctors.length := by
    simpa [F.constructors.lengths.2] using hctor
  rcases F.constructorAt i hsourceCtor htargetCtor hctor with
    ⟨_before, _after, _ctorSourceEnv, _ctorTargetEnv, Hmapping, HctorStep,
      HctorSemantic, HctorStepName, HconstructorEq⟩
  have HabstractCtorName : owner.ctors[i].name = A.target.ctors[i].name := by
    calc
      owner.ctors[i].name = HctorSemantic.constructor.name :=
        congrArg VConstVal.name HconstructorEq.symm
      _ = sourceTypes[familyIdx].ctors[i].name :=
        HctorSemantic.sourceTranslation.name
      _ = A.target.ctors[i].name := Hmapping.name.symm
  have holdInfo := Hprod.restoredPrimaryInfo_eq_generated familyIdx hentry
    Hstep.restored.recursor A.oldRecName
  have hgenerated : i < result.types.toArray[familyIdx]!.ctors.length := by
    obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp A.targetAt
    have harray : result.types.toArray[familyIdx]! = A.target := by
      simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
    rw [harray]
    exact htargetCtor
  rcases Hprod.generatedRuleAlignment familyIdx hentry i hgenerated with
    ⟨G⟩
  have HoldCtorName : Hstep.restored.recursor.oldInfo.rules[i].ctor =
      A.target.ctors[i].name := by
    obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp A.targetAt
    have harray : result.types.toArray[familyIdx]! = A.target := by
      simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
    have HgeneratedCtor :
        ((Hprod.generated.entry familyIdx hentry).info.rules[i]'G.sourceRule_lt).ctor =
          result.types.toArray[familyIdx]!.ctors[i].name :=
      G.rule.ctor_eq
    have HoldRuleEq : Hstep.restored.recursor.oldInfo.rules[i] =
        (Hprod.generated.entry familyIdx hentry).info.rules[i]'G.sourceRule_lt := by
      have HrulesEq := congrArg RecursorVal.rules holdInfo
      apply (List.getElem_eq_iff hold).2
      rw [HrulesEq, List.getElem?_eq_getElem G.sourceRule_lt]
    have HgeneratedCtor' : Hstep.restored.recursor.oldInfo.rules[i].ctor =
        result.types.toArray[familyIdx]!.ctors[i].name := by
      exact (congrArg RecursorRule.ctor HoldRuleEq).trans HgeneratedCtor
    have HctorsEq := congrArg InductiveType.ctors harray
    have HtargetCtorEq : result.types.toArray[familyIdx]!.ctors[i] =
        A.target.ctors[i] := by
      apply (List.getElem_eq_iff hgenerated).2
      rw [HctorsEq, List.getElem?_eq_getElem htargetCtor]
    exact HgeneratedCtor'.trans (congrArg Constructor.name HtargetCtorEq)
  have HnewCtorName :
      Hstep.restored.recursor.restored.newInfo.rules[i].ctor =
        Hstep.restored.recursor.oldInfo.rules[i].ctor := by
    have Hrule := Hstep.restored.recursor.restored.restoration.rules.entry
      i hold hnew
    rw [Hrule.ctor]
    simp [hprimaryName, A.oldRecName]
  have HctorName : owner.ctors[i].name =
      Hstep.restored.recursor.restored.newInfo.rules[i].ctor :=
    HabstractCtorName.trans
      (HoldCtorName.symm.trans HnewCtorName.symm)
  have Hdomains : domains.length =
      Hstep.restored.recursor.restored.newInfo.numParams +
        Hstep.restored.recursor.restored.newInfo.numMotives +
        Hstep.restored.recursor.restored.newInfo.numMinors +
        Hstep.restored.recursor.restored.newInfo.rules[i].nfields :=
    hdomains.trans shape.source_arity |>.trans shape.arity_eq
  have Hguard' : rhsBody.GuardedIota
      (restoredBlock.recursors.map (·.name))
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        (allIndNames.map Lean.mkRecName ++ auxRecNames)
        Hstep.restored.recursor.oldInfo.rules[i].rhs) 0 := by
    rw [hrecursorNames]
    exact Hguard
  have Hnested :=
    validateRestoredRecursorRules.nestedIotaRule_of_canonicalSpines
      Hrecursor.recursor hrecursorMem Hshape HrecursorName HrecursorUvars
      HdeclNparams Hprefix HownerPlanIndices HdeclCtorUvars HctorName Hdomains
      HlhsWrapped HrhsWrapped HtypeWrapped HruleUvars HlhsSpine shape
      HrhsSpine Hguard'
  exact ⟨abstractRule, ⟨Hnested⟩, Hwf⟩

/-- Whole-source-family form of `primaryIotaFamilyOfValidation`.  All family,
owner, constructor, and production indices are recovered from the lowering
and restoration traces; callers provide only the already executed validator
and the canonical block's recursor-name equality. -/
theorem NestedLoweringResultClosed.primaryFamiliesOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (hrecEnv : envCtors ≤ recEnv)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (restoredBlock : VInductBlock) (targetVEnv : VEnv)
    (Hnames : restoredBlock.recursors.map (·.name) =
      (sourceTypes.map (·.name)).map (fun name =>
        let oldName := Lean.mkRecName name
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.getD oldName
          oldName) ++
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1.map fun oldName =>
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.getD oldName
          oldName)
    (Hvalid : CheckingEnv.Valid c.safety ruleEnv targetVEnv)
    (Hrun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      c.lparams c.safety validationFuel result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()) :
    let P : NestedInstalledProduction loweredEnv := {
      c := c
      stats := stats
      loweredDecl := loweredDecl
      nparams := nparams
      depth := depth
      isUnsafe := isUnsafe
      initialEnv := sourceVEnv
      indTypes := result.types.toArray
      headerEnv := headerEnv
      ctorEnv := ctorEnv
      headers := Hheaders
      constructors := R
      production := Hprod }
    ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) indType stepSource stepTarget)
      (hsource : indType ∈ sourceTypes)
      (Hheader : TrSourceConst sourceVEnv c.lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredSourceConstructorTrace result loweredEnv
        c.lparams c.safety envTypes Hstep.oldInfo.ctors
          Hstep.restored.headerEnv Hstep.restored.constructorEnv indType.ctors
            owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
        Hstep.restored.recursor recEnv),
      Hrecursor.recursor ∈ restoredBlock.recursors →
      Nonempty (RestoredPrimaryIotaFamilySemantics sourceDecl restoredBlock
        targetVEnv owner P Hstep) := by
  dsimp only
  intro indType stepSource stepTarget owner Hstep hsource _Hheader
    Hconstructors Hrecursor hrecursor
  rcases List.mem_iff_getElem.mp hsource with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    exact hresult
  rcases H.primaryOperationalFamilyAlignmentAtFresh Hc Hprod hempty
      familyIdx hfamily hentry Hstep with ⟨A⟩
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨_finalState, HlowerRun, _Hcache, _Hparams⟩
    exact HlowerRun.resultFamilyNamesReservedFresh hempty
  have HauxConstructors : RestoreAuxConstructorsFresh result loweredEnv
      envTypes :=
    H.restoreAuxConstructorsFreshAtTypes Hc Hprod Hsource Howners hempty
  have Hsyntax := (Hsources.getElem familyIdx hfamily).constructors
  have Hdisjoint : ∀ source ∈ sourceTypes[familyIdx].ctors,
      RestoreSourceDisjoint result loweredEnv source.type := by
    intro source hsourceCtor
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hconstructors.forall₂
        source hsourceCtor with
      ⟨constructor, _hconstructor, Htranslation⟩
    exact (Hsyntax.of_mem hsourceCtor).noNestedAux
      |>.restoreSourceDisjointOfFresh
        Htranslation.type.constantsDefined Hfamilies HauxConstructors
  have HconstructorTranslations : List.Forall₂
      (fun source constructor =>
        TrSourceConst recEnv c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors owner.ctors :=
    Lean4Lean.List.Forall₂.imp
      (fun _source _constructor Htranslation =>
        Htranslation.mono ((VEnv.addConstVals_le Hsource.ctorsAdded).trans hrecEnv))
      Hconstructors.forall₂
  let F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor := {
    constructors := by
      apply A.constructors.sourceSemanticMapping HconstructorTranslations
        Hsyntax Hdisjoint rfl A.fvars A.params A.paramsNodup
          H.toResult.resultNParams A.paramsSize }
  have hrestoredName : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName sourceTypes[familyIdx].name := by
    have hunmapped := H.sourceRecursorUnmappedAtFresh Hc Hprod hempty
      familyIdx hfamily
    rw [Hstep.restored.recursor.restored.mappedName]
    apply Std.TreeMap.getD_eq_fallback_of_contains_eq_false
    change Std.TreeMap.contains
      (show Std.TreeMap Name Name Name.quickCmp from
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
        (Lean.mkRecName sourceTypes[familyIdx].name) = false
    rw [Std.TreeMap.contains_eq_isSome_getElem?]
    change ((Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name)).isSome = false
    rw [hunmapped]
    rfl
  have HsourceAt := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hdecl
  have hsourceOwnerName : sourceDecl.types[familyIdx].name =
      sourceTypes[familyIdx].name := by
    simpa using HsourceAt.header.name
  rcases Hrecursor.shape with ⟨Hshape⟩
  have hrecursorName : Hrecursor.recursor.name =
      sourceDecl.recursorName sourceDecl.types[familyIdx] := by
    calc
      Hrecursor.recursor.name =
          Hstep.restored.recursor.restored.newRecName := Hrecursor.name
      _ = Lean.mkRecName sourceTypes[familyIdx].name := hrestoredName
      _ = Lean.mkRecName sourceDecl.types[familyIdx].name :=
        congrArg Lean.mkRecName hsourceOwnerName.symm
      _ = sourceDecl.recursorName sourceDecl.types[familyIdx] := by
        rw [VInductDecl.recursorName_eq_mkRecName]
  have hownerIdx :=
    Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
      Hshape familyIdx hdecl hrecursorName
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup Hsource)
  have hownerEq : sourceDecl.types[familyIdx] = owner := by
    simpa only [hownerIdx] using Hshape.owner_eq
  exact F.primaryIotaFamilyOfValidation Hsource Hmetadata hempty hdecl
    hownerEq restoredBlock targetVEnv hrecursor Hnames hrestoredName Hvalid Hrun

/-- The semantic residue of the auxiliary restoration fold.  Both fields are
indexed by the same exact operational trace and the same final abstract
environment. -/
structure NestedFinalAuxiliaryEvidence
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (safety : DefinitionSafety)
    (main : VInductiveType)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (canonicalVEnv finalBaseVEnv : VEnv) : Prop where
  semantics : RestoredAuxiliaryShapeTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonicalVEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  wf : RestoredAuxiliaryFinalWFTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonicalVEnv canonicalVEnv
      finalBaseVEnv semantics [] [] auxiliaryRecursors auxiliaryRules

/-- Telescope-translation specialization of the pointwise source producer.
The source recursor, its shape, metadata refinement, and installation typing
are reconstructed from the exact production/restoration join. -/
theorem NestedLoweringResultClosed.restoredPrimaryTelescopeAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hvalid : CheckingEnv.Valid validationSafety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationLparams validationSafety validationFuel result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes auxRecNames = .ok ())
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (stepSource stepTarget : Environment)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes[familyIdx]
        stepSource stepTarget) :
    ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType := by
  rcases H.primaryOperationalFamilyAlignmentAtFresh Hc Hprod hempty
      familyIdx hfamily hentry Hstep with ⟨A⟩
  have Htel := A.recursor.restoredForallTelescope
  rcases validateRestoredRecursorTypes.translation_of_run Hvalid Hrun
      (List.getElem_mem hfamily)
      Hstep.restored.recursor.lookup with ⟨targetType, Htr, Htype⟩
  rw [← Hstep.restored.recursor.restored.produced] at Htr Htype
  rw [Hstep.restored.recursor.restored.restoration.levelParams] at Htr Htype
  exact ⟨targetType, by
    simpa only [Nat.add_assoc] using
      Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel Htr Htype⟩

/-- The retained whole-block validation pass also constructs the exact
translated and typed auxiliary recursor payload selected by one restoration
step. -/
theorem RestoredAuxiliaryGeneratedStepAlignment.recursorStepOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : RestoredAuxiliaryGeneratedStepAlignment Hprod Hstep)
    (Hvalid : CheckingEnv.Valid c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationLparams c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames) :
    Nonempty (RestoredAuxiliaryRecursorStep c.safety envCtors envCtors
      Hstep) := by
  rcases validateRestoredRecursorTypes.auxiliaryTranslation_of_run Hvalid Hrun
      hrec Hstep.lookup with ⟨targetType, Htranslation, Htype⟩
  rw [← Hstep.restored.produced] at Htranslation Htype
  have Hmetadata := Hprod.restoredPrimaryRecursorMetadata A.ownerIdx
    A.entry_lt Hstep A.oldRecName_eq
  have Hsafety : c.safety ≤
      (ConstantInfo.recInfo Hstep.restored.newInfo).safety := by
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, Hstep.restored.restoration.isUnsafe] using
        Hmetadata.1
  exact ⟨RestoredAuxiliaryRecursorStep.ofTypeTranslation targetType Hsafety
    Htranslation Htype⟩

/-- Construct the complete abstract rule batch for one literal auxiliary
restoration step from the retained executable validation run.  The list is
chosen pointwise only after the checker has fixed each concrete rule's LHS,
RHS, and common type; every chosen rule is therefore both well formed and
guarded with respect to the exact restored recursor-name list. -/
theorem RestoredAuxiliaryGeneratedStepAlignment.rulesOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (_A : RestoredAuxiliaryGeneratedStepAlignment Hprod Hstep)
    (Hvalid : CheckingEnv.Valid c.safety validationEnv targetVEnv)
    (Hrun : Lean4Lean.validateRestoredRecursorRules.run validationEnv
      loweredEnv validationLparams c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames) :
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        auxRec.getD oldName oldName) ++
      auxRecNames.map fun oldName => auxRec.getD oldName oldName
    ∃ abstractRules : List VDefEq,
      abstractRules.length = Hstep.restored.newInfo.rules.length ∧
      (∀ rule ∈ abstractRules, rule.WF targetVEnv) ∧
      ∀ rule ∈ abstractRules,
        rule.rhs.GuardedRuleRhs restoredRecursorNames := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv auxRec allIndNames
    oldRecName (auxRec.getD oldRecName oldRecName) Hstep.oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      auxRec.getD oldName oldName) ++
    auxRecNames.map fun oldName => auxRec.getD oldName oldName
  have Hpoint : ∀ concreteRule ∈ restored.rules,
      ∃ abstractRule : VDefEq,
        abstractRule.WF targetVEnv ∧
        abstractRule.rhs.GuardedRuleRhs restoredRecursorNames := by
    intro concreteRule hconcrete
    rcases validateRestoredRecursorRules.auxiliaryValidatedAbstractRule_of_run
        Hvalid Hrun hrec Hstep.lookup hconcrete with
      ⟨_lhs, _lhsInferred, abstractRule, _Hbuild, _Hrhs, _Hlhs, _Htype,
        _Huvars, ⟨Hwf⟩, Hguard⟩
    exact ⟨abstractRule, Hwf, Hguard⟩
  have chooseRules : ∀ concreteRules : List RecursorRule,
      (∀ rule ∈ concreteRules, rule ∈ restored.rules) →
      ∃ abstractRules : List VDefEq,
        abstractRules.length = concreteRules.length ∧
        (∀ rule ∈ abstractRules, rule.WF targetVEnv) ∧
        ∀ rule ∈ abstractRules,
          rule.rhs.GuardedRuleRhs restoredRecursorNames := by
    intro concreteRules Hsubset
    induction concreteRules with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons concreteRule concreteRules ih =>
        rcases Hpoint concreteRule (Hsubset concreteRule (by simp)) with
          ⟨abstractRule, Hwf, Hguard⟩
        have Htail : ∀ rule ∈ concreteRules, rule ∈ restored.rules := by
          intro rule hrule
          exact Hsubset rule (by simp [hrule])
        rcases ih Htail with
          ⟨abstractRules, Hlength, HrulesWF, HrulesGuarded⟩
        exact ⟨abstractRule :: abstractRules, by simp [Hlength],
          by
            intro rule hrule
            rcases List.mem_cons.mp hrule with rfl | htail
            · exact Hwf
            · exact HrulesWF rule htail,
          by
            intro rule hrule
            rcases List.mem_cons.mp hrule with rfl | htail
            · exact Hguard
            · exact HrulesGuarded rule htail⟩
  have Hchosen := chooseRules restored.rules (fun _ h => h)
  simpa only [restored, ← Hstep.restored.produced] using Hchosen

/-- Rule-validation half of `finalEvidenceOfValidation` when the exact
recursor payload has already been fixed by a synchronized pre-rule trace.
This avoids selecting the auxiliary recursor a second time while folding the
rule certificates. -/
theorem RestoredAuxiliaryGeneratedStepAlignment.finalEvidenceOfRecursorTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv ruleEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : RestoredAuxiliaryGeneratedStepAlignment Hprod Hstep)
    (Hrecursor : RestoredAuxiliaryRecursorStep c.safety recursorEnv
      recursorEnv Hstep)
    (HruleValid : CheckingEnv.Valid c.safety ruleEnv ruleVEnv)
    (HruleRun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      validationLparams c.safety validationFuel result auxRec allIndNames
      validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames)
    (Hnames : block.recursors.map (·.name) =
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        auxRec.getD oldName oldName) ++
      auxRecNames.map fun oldName => auxRec.getD oldName oldName)
    (priorRecursors : List VConstVal) :
    Nonempty { E : RestoredAuxiliaryStepFinalEvidence decl block main
        c.safety recursorEnv recursorEnv ruleVEnv Hstep priorRecursors //
      E.semantics.recursor = Hrecursor.recursor } := by
  rcases A.rulesOfValidation HruleValid HruleRun hrec with
    ⟨rules, Hlength, HrulesWF, HrulesGuarded⟩
  let Hsemantics : RestoredAuxiliaryStepShape decl block main c.safety
      recursorEnv Hstep priorRecursors := {
    recursor := Hrecursor.recursor
    rules := rules
    translated := Hrecursor.translated
    rulesLength := Hlength
    guarded := by
      intro i _hsource _hrestored habstract _Hrestoration
      have hmember : rules[i] ∈ rules := List.getElem_mem habstract
      exact (HrulesGuarded rules[i] hmember).congrRecursors (by
        intro name
        rw [Hnames]) }
  exact ⟨⟨{
    semantics := Hsemantics
    recursorWF := Hrecursor.wf
    rulesWF := HrulesWF }, rfl⟩⟩

/-- Reindex one auxiliary semantic step across blocks with extensionally the
same recursor-name set.  The block's type, constructor, and rule fields do
not occur in the step judgment; guardedness observes only recursor-name
membership. -/
def RestoredAuxiliaryStepShape.rebaseBlock
    (H : RestoredAuxiliaryStepShape decl block main safety trEnv Hstep
      priorRecursors)
    (Hnames : ∀ name,
      name ∈ block.recursors.map (·.name) ↔
        name ∈ block'.recursors.map (·.name)) :
    RestoredAuxiliaryStepShape decl block' main safety trEnv Hstep
      priorRecursors where
  recursor := H.recursor
  rules := H.rules
  translated := H.translated
  rulesLength := H.rulesLength
  guarded := by
    intro i hsource hrestored habstract Hrestoration
    exact (H.guarded i hsource hrestored habstract Hrestoration).congrRecursors
      Hnames

/-- Reindex a completed auxiliary semantic/WF fold across blocks with the
same recursor-name support.  This is useful because the final rule list is an
output of the fold, while the guardedness checker needs only the recursor
list, which is fixed beforehand by the independent recursor trace. -/
noncomputable def RestoredAuxiliaryFinalWFTrace.rebaseBlock
    {Hsemantic : RestoredAuxiliaryShapeTrace decl block main safety trEnv
      Htrace priorRecursors priorRules finalRecursors finalRules}
    (H : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv
      recursorEnv ruleEnv Hsemantic priorRecursors priorRules finalRecursors
        finalRules)
    (Hnames : ∀ name,
      name ∈ block.recursors.map (·.name) ↔
        name ∈ block'.recursors.map (·.name)) :
    Nonempty { Hsemantic' : RestoredAuxiliaryShapeTrace decl block' main
        safety trEnv Htrace priorRecursors priorRules finalRecursors finalRules //
      RestoredAuxiliaryFinalWFTrace decl block' main safety trEnv recursorEnv
        ruleEnv Hsemantic' priorRecursors priorRules finalRecursors
          finalRules } :=
  match H with
  | .nil sourceEnv recursors rules =>
      ⟨⟨RestoredAuxiliaryShapeTrace.nil sourceEnv recursors rules,
        .nil sourceEnv recursors rules⟩⟩
  | .cons Hstep Htail Hhead Hrest Hrecursor Hrules Hfinal => by
      let Hhead' := Hhead.rebaseBlock Hnames
      rcases Hfinal.rebaseBlock Hnames with ⟨⟨Hrest', Hfinal'⟩⟩
      let Hsemantic' : RestoredAuxiliaryShapeTrace decl block' main safety
          trEnv (.cons Hstep Htail) _ _ _ _ :=
        .cons Hstep Htail Hhead' Hrest'
      exact ⟨⟨Hsemantic', .cons Hstep Htail Hhead' Hrest' Hrecursor Hrules
        Hfinal'⟩⟩

/-- Fold the executable validation certificates over the exact auxiliary
restoration trace.  Membership in the validation suffix is inherited from
the literal `StateForMTrace` name list. -/
theorem RestoredAuxiliaryGeneratedAlignmentTrace.recursorTraceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : RestoredAuxiliaryGeneratedAlignmentTrace Hprod Htrace)
    (Hvalid : CheckingEnv.Valid c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationLparams c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (Hnames : ∀ name ∈ names, name ∈ auxRecNames)
    (priorRecursors : List VConstVal) :
    ∃ finalRecursors, RestoredAuxiliaryRecursorTrace c.safety envCtors
      envCtors Htrace priorRecursors finalRecursors := by
  induction H generalizing priorRecursors with
  | nil sourceEnv => exact ⟨priorRecursors, .nil sourceEnv priorRecursors⟩
  | @cons oldRecName stepSource middleEnv tail targetEnv Hstep Htail A Hrest ih =>
      rcases A.recursorStepOfValidation Hvalid Hrun
          (Hnames oldRecName (by simp)) with ⟨Hhead⟩
      have HtailNames : ∀ name ∈ tail, name ∈ auxRecNames := by
        intro name hname
        exact Hnames name (by simp [hname])
      rcases ih HtailNames (priorRecursors ++ [Hhead.recursor]) with
        ⟨finalRecursors, Hfinal⟩
      exact ⟨finalRecursors,
        RestoredAuxiliaryRecursorTrace.cons Hstep Htail Hhead Hfinal⟩

/-- The source semantic trace fixes the ordered primary-recursor names to the
literal executable restoration renaming.  This is producer evidence: no
block-level name equality is supplied by a final-assembly caller. -/
theorem RestoredSourceInductiveSemanticTrace.recursorNames
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    recursors.map (fun recursor => recursor.name) =
      sourceTypes.map (fun indType =>
        let oldName := Lean.mkRecName indType.name
        auxRec.getD oldName oldName) := by
  induction H with
  | nil => rfl
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
      simp only [List.map_cons, List.cons.injEq, ih, and_true]
      exact Hrecursor.name.trans
        (Hstep.restored.recursor.restored.mappedName)

/-- The block-independent auxiliary trace likewise fixes the ordered suffix
of restored recursor names.  The more general prefix statement matches the
append-oriented trace index and specializes to the empty initial suffix used
by canonical staging. -/
theorem RestoredAuxiliaryRecursorTrace.recursorNames
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : RestoredAuxiliaryRecursorTrace safety trEnv recursorEnv Htrace
      priorRecursors finalRecursors) :
    finalRecursors.map (fun recursor => recursor.name) =
      priorRecursors.map (fun recursor => recursor.name) ++
        names.map (fun oldName => auxRec.getD oldName oldName) := by
  induction H with
  | nil => simp
  | @cons oldRecName stepSource middleEnv tail targetEnv prior final Hstep
      Htail Hhead Hrest ih =>
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq]
      have hname : Hhead.recursor.name = auxRec.getD oldRecName oldRecName :=
        Hhead.translated.2.symm.trans
          (Hstep.restored.restoration.name.trans Hstep.restored.mappedName)
      simp only [hname]

/-- Fold literal rule-validation results along an already fixed exact
auxiliary-recursor trace.  Hence the output rule list is chosen by the
checker, while the output recursor list is definitionally the one used by
canonical installation. -/
noncomputable def RestoredAuxiliaryRecursorTrace.finalEvidenceOfRuleValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv ruleEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (Hrecursors : RestoredAuxiliaryRecursorTrace c.safety recursorEnv
      recursorEnv Htrace priorRecursors finalRecursors)
    (Halignment : RestoredAuxiliaryGeneratedAlignmentTrace Hprod Htrace)
    (HruleValid : CheckingEnv.Valid c.safety ruleEnv ruleVEnv)
    (HruleRun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      validationLparams c.safety validationFuel result auxRec allIndNames
      validationTypes auxRecNames = .ok ())
    (Hmembers : ∀ name ∈ names, name ∈ auxRecNames)
    (Hnames : block.recursors.map (·.name) =
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        auxRec.getD oldName oldName) ++
      auxRecNames.map fun oldName => auxRec.getD oldName oldName)
    (decl : VInductDecl) (main : VInductiveType)
    (priorRules : List VDefEq) :
    ∃ finalRules,
      ∃ Hsemantic : RestoredAuxiliaryShapeTrace decl block main
          c.safety recursorEnv Htrace priorRecursors priorRules
            finalRecursors finalRules,
        RestoredAuxiliaryFinalWFTrace decl block main c.safety recursorEnv
          recursorEnv ruleVEnv Hsemantic priorRecursors priorRules
            finalRecursors finalRules :=
  match Hrecursors with
  | .nil sourceEnv recursors => by
      let Hsemantic : RestoredAuxiliaryShapeTrace decl block main
          c.safety recursorEnv
            (StateForMTrace.nil
              (P := RestoredRecursorStep result loweredEnv auxRec allIndNames)
              (source := sourceProdEnv))
            recursors priorRules recursors priorRules :=
        .nil sourceProdEnv recursors priorRules
      let Hwf : RestoredAuxiliaryFinalWFTrace decl block main c.safety
          recursorEnv recursorEnv ruleVEnv Hsemantic recursors priorRules
            recursors priorRules :=
        .nil sourceProdEnv recursors priorRules
      exact ⟨priorRules, Hsemantic, Hwf⟩
  | .cons Hstep Htail Hhead Hrest => by
      cases Halignment with
      | cons _ _ A Arest =>
          let HstepResult := Classical.choice
            (A.finalEvidenceOfRecursorTrace (decl := decl) (main := main)
              Hhead HruleValid HruleRun (Hmembers _ (by simp)) Hnames
                priorRecursors)
          let HstepFinal := HstepResult.val
          have hrecursor := HstepResult.property
          have Hrest' : RestoredAuxiliaryRecursorTrace c.safety recursorEnv
              recursorEnv Htail
                (priorRecursors ++ [HstepFinal.semantics.recursor])
                finalRecursors := by
            rw [hrecursor]
            exact Hrest
          rcases Hrest'.finalEvidenceOfRuleValidation Arest HruleValid HruleRun (fun name hname => Hmembers name (by simp [hname]))
              Hnames decl main
              (priorRules ++ HstepFinal.semantics.rules) with
            ⟨finalRules, Hsemantic, Hfinal⟩
          exact ⟨finalRules,
            .cons Hstep Htail HstepFinal.semantics Hsemantic,
            .cons Hstep Htail HstepFinal.semantics Hsemantic
              HstepFinal.recursorWF HstepFinal.rulesWF Hfinal⟩

/-- Construct the complete final auxiliary semantic/WF payload from the
exact pre-rule recursor trace and the literal rule-validation run.  The rule
list is an output of this theorem.  Reindexing from the temporary empty rule
suffix to that output is sound because guardedness depends only on the
already fixed recursor-name set. -/
theorem RestoredNestedDeclarationsResult.finalAuxiliaryEvidenceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv ruleEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : CompletedRecursorPhasesResult R.completed loweredEnv}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (Halignment : RestoredAuxiliaryGeneratedAlignmentTrace Hprod
      H.auxiliaries)
    (Hrecursors : RestoredAuxiliaryRecursorTrace c.safety recursorEnv
      recursorEnv H.auxiliaries [] auxiliaryRecursors)
    (HruleValid : CheckingEnv.Valid c.safety ruleEnv ruleVEnv)
    (HruleRun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      validationLparams c.safety validationFuel result auxRec allIndNames
      sourceTypes auxRecNames = .ok ())
    (decl : VInductDecl) (main : VInductiveType) (sourceEnv : VEnv)
    (primaryRecursors : List VConstVal) (primaryRules : List VDefEq)
    (Hnames : (canonicalRestoredBlock decl primaryRecursors
      auxiliaryRecursors primaryRules []).recursors.map (·.name) =
        allIndNames.map (fun name =>
          let oldName := Lean.mkRecName name
          auxRec.getD oldName oldName) ++
        auxRecNames.map fun oldName => auxRec.getD oldName oldName) :
    ∃ auxiliaryRules,
      NestedFinalAuxiliaryEvidence H sourceEnv decl c.safety main
        primaryRecursors auxiliaryRecursors primaryRules auxiliaryRules
          recursorEnv ruleVEnv := by
  rcases Hrecursors.finalEvidenceOfRuleValidation Halignment HruleValid HruleRun (fun _ h => h) Hnames decl main [] with
    ⟨auxiliaryRules, Hsemantic, Hwf⟩
  let block' := canonicalRestoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  have Hsame : ∀ name,
      name ∈ (canonicalRestoredBlock decl primaryRecursors
        auxiliaryRecursors primaryRules []).recursors.map (·.name) ↔
      name ∈ block'.recursors.map (·.name) := by
    intro name
    simp only [canonicalRestoredBlock, block']
  rcases Hwf.rebaseBlock (block' := block') Hsame with
    ⟨⟨Hsemantic', Hwf'⟩⟩
  exact ⟨auxiliaryRules, ⟨Hsemantic', Hwf'⟩⟩

/-- Construct the canonical constant installation for an exact nonempty
nested restoration using only the source semantic trace, executable recursor
validation, and the primitive/non-delta companion traces of that same run. -/
theorem NestedLoweringResultClosed.existsValidatedExactStagedRestoration
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv validationEnv primaryProdEnv outProdEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hcore : TrInductDeclCore sourceVEnv c.lparams nparams (main :: rest)
      isUnsafe decl envTypes envCtors)
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
      ((main :: rest).map (·.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1
      ((), outProdEnv))
    (Hsource : RestoredSourceInductiveSemanticTrace decl c.lparams c.safety
      sourceVEnv envTypes ((envCtors.addEliminators es).addProjections decl.projectionEntries)
      Hrestored.inductives decl.types primaryRecursors)
    (HvalidationValid : CheckingEnv.Valid c.safety validationEnv
      ((envCtors.addEliminators es).addProjections decl.projectionEntries))
    (HrecursorValidation :
      Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
        validationLparams c.safety validationFuel result
        (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
        ((main :: rest).map (·.name)) (main :: rest)
        (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1 = .ok ())
    (Hparams : decl.SourceParameterWF sourceVEnv)
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hprimitive : PrimitiveSafeFreshConstantTrace false c.env
      primitiveEntries outProdEnv)
    (Hcases : VInductBlock.EliminatorsWF sourceVEnv decl (decl.caseBlock es)) :
    ∃ auxiliaryRecursors,
      RestoredAuxiliaryRecursorTrace c.safety
          ((envCtors.addEliminators es).addProjections decl.projectionEntries)
          ((envCtors.addEliminators es).addProjections decl.projectionEntries)
          Hrestored.auxiliaries [] auxiliaryRecursors ∧
        ∃ replay : CanonicalRestorationReplay c.safety c.env outProdEnv
          sourceVEnv envTypes ((envCtors.addEliminators es).addProjections decl.projectionEntries)
          decl.types primaryRecursors auxiliaryRecursors,
        ∃ canonicalProdEnv finalVEnv,
          Nonempty { S : CompletedStagedBlock c.safety c.env sourceVEnv replay.typeEntries
            replay.constructorEntries replay.recursorEntries
              decl.projectionEntries canonicalProdEnv finalVEnv // S.eliminators = es } ∧
          ∀ name, outProdEnv.constants.find? name =
            canonicalProdEnv.constants.find? name := by
  have Halignment := Hrestored.generatedAlignmentTraceOfProduction Hlower Hc
    Hprod hempty
  rcases Halignment.recursorTraceOfValidation HvalidationValid HrecursorValidation (fun _ h => h) [] with
    ⟨auxiliaryRecursors, Hauxiliary⟩
  rcases Hrestored.freshTraceNondelta Hc.checking.tr.map_wf with
    ⟨nondeltaEntries, Hnondelta, hnondelta⟩
  rcases Hsource.existsExactStagedRestoration Hauxiliary Hlower Hc Hprod
      Hcore Hparams hempty hvisible Hprimitive Hnondelta hnondelta Hcases with
    ⟨replay, canonicalProdEnv, finalVEnv, Hstaged, hlookup⟩
  exact ⟨auxiliaryRecursors, Hauxiliary, replay, canonicalProdEnv, finalVEnv,
    Hstaged, hlookup⟩

/-- Construct the final nested certificate directly from the exact traces
retained by the executable run.  Primary rules are first selected by the
literal rule validator; only then are the auxiliary rules selected and the
canonical replay sealed into the final certificate.  Thus neither rule batch,
the recursor-name alignment, nor a final-assembly callback is a premise. -/
theorem NestedLoweringResultClosed.validatedFinalAssemblyCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv ruleEnv outEnv canonicalProdEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hcore : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (P : NestedInstalledProduction loweredEnv)
    (hP : P = {
      c := c
      stats := stats
      loweredDecl := loweredDecl
      nparams := nparams
      depth := depth
      isUnsafe := isUnsafe
      initialEnv := sourceVEnv
      indTypes := result.types.toArray
      headerEnv := headerEnv
      ctorEnv := ctorEnv
      headers := Hheaders
      constructors := R
      production := Hprod })
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (fun type => type.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv))
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (Hsource : RestoredSourceInductiveSemanticTrace sourceDecl c.lparams
      c.safety sourceVEnv envTypes
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
      Hrestored.inductives sourceDecl.types primaryRecursors)
    (HauxiliaryRecursors : RestoredAuxiliaryRecursorTrace c.safety
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
      Hrestored.auxiliaries [] auxiliaryRecursors)
    (replay : CanonicalRestorationReplay c.safety c.env outEnv sourceVEnv
      envTypes ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
      sourceDecl.types primaryRecursors auxiliaryRecursors)
    (canonical : CompletedStagedBlock c.safety c.env sourceVEnv replay.typeEntries
      replay.constructorEntries replay.recursorEntries
        sourceDecl.projectionEntries canonicalProdEnv finalBaseVEnv)
    (HruleValid : CheckingEnv.Valid c.safety ruleEnv finalBaseVEnv)
    (HruleRun : Lean4Lean.validateRestoredRecursorRules.run ruleEnv loweredEnv
      c.lparams c.safety validationFuel result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (fun type => type.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ())
    (Hformation : NestedFormationAssembly sourceVEnv sourceDecl)
    (hformationExpanded : Hformation.expanded = loweredDecl)
    (huvars : sourceDecl.uvars = c.lparams.length)
    (hnumParams : sourceDecl.nparams = nparams)
    (hunsafeEq : sourceDecl.isUnsafe = isUnsafe)
    (hsourceNonempty : sourceTypes ≠ [])
    (hcanonicalElims : canonical.eliminators = es)
    (Hcases : VInductBlock.EliminatorsWF sourceVEnv sourceDecl (sourceDecl.caseBlock es))
    (Hreplay : sourceDecl.CaseEliminators sourceVEnv
      (fun n => c.env.constants.find? n = none) es)
    (HelimRestored : NestedEliminatorsRestored P result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 sourceDecl c.lparams es) :
    Nonempty { C : NestedFinalAssemblyShape Hrestored sourceVEnv
        sourceDecl c.lparams nparams isUnsafe c.safety //
      C.production = P ∧ CheckingEnv.Valid c.safety ruleEnv C.finalBaseVEnv } := by
  subst P
  have HsourceCons : ∃ main rest, sourceTypes = main :: rest := by
    cases htypes : sourceTypes with
    | nil => exact (hsourceNonempty htypes).elim
    | cons main rest => exact ⟨main, rest, rfl⟩
  rcases HsourceCons with ⟨sourceMain, sourceRest, rfl⟩
  have HprimaryNames := Hsource.recursorNames
  have HauxiliaryNames := HauxiliaryRecursors.recursorNames
  simp only [List.map_nil, List.nil_append] at HauxiliaryNames
  have Hnames :
      (canonicalRestoredShapeBlock sourceDecl primaryRecursors
        auxiliaryRecursors).recursors.map (fun recursor => recursor.name) =
        ((sourceMain :: sourceRest).map (fun type => type.name)).map (fun name =>
          let oldName := Lean.mkRecName name
          (Lean4Lean.mkAuxRecNameMap loweredEnv
            (sourceMain :: sourceRest)).2.getD oldName
            oldName) ++
        (Lean4Lean.mkAuxRecNameMap loweredEnv
          (sourceMain :: sourceRest)).1.map fun oldName =>
          (Lean4Lean.mkAuxRecNameMap loweredEnv
            (sourceMain :: sourceRest)).2.getD oldName oldName := by
    simp only [canonicalRestoredShapeBlock, canonicalRestoredBlock,
      List.map_append]
    rw [HprimaryNames, HauxiliaryNames]
    simp only [List.map_map, Function.comp_def]
  have hcanonicalTypes : canonical.venvTypes = envTypes := by
    have hadded := canonical.abstract_types
    rw [replay.typeValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.typesAdded)
  have hcanonicalCtors : canonical.venvCtors = envCtors := by
    have hadded := canonical.abstract_ctors
    rw [hcanonicalTypes, replay.constructorValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.ctorsAdded)
  have Hfamilies := Hlower.primaryFamiliesOfValidation
    (recEnv := (envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) Hc Hprod
    Hsources Hcore VEnv.addEliminators_addProjections_le Hmetadata Howners hempty
      (canonicalRestoredShapeBlock sourceDecl primaryRecursors
        auxiliaryRecursors) finalBaseVEnv Hnames HruleValid HruleRun
  rcases Hsource.primaryIotaSemanticTraceOfMemberships
      ({
        c := c
        stats := stats
        loweredDecl := loweredDecl
        nparams := nparams
        depth := depth
        isUnsafe := isUnsafe
        initialEnv := sourceVEnv
        indTypes := result.types.toArray
        headerEnv := headerEnv
        ctorEnv := ctorEnv
        headers := Hheaders
        constructors := R
        production := Hprod } : NestedInstalledProduction loweredEnv)
      finalBaseVEnv (by
        intro indType stepSource stepTarget owner Hstep hsource Hheader
          Hconstructors Hrecursor hrecursor
        apply Hfamilies indType stepSource stepTarget owner Hstep hsource
          Hheader Hconstructors Hrecursor
        simp only [canonicalRestoredShapeBlock, canonicalRestoredBlock]
        exact List.mem_append_left auxiliaryRecursors hrecursor) with
    ⟨primaryRules, Hprimary⟩
  have hownersNonempty : sourceDecl.types ≠ [] :=
    fun hnil => by
      have hlength := Lean4Lean.List.Forall₂.length_eq Hsource.types
      rw [hnil] at hlength
      simp at hlength
  cases htypesSource : sourceDecl.types with
  | nil => exact (hownersNonempty htypesSource).elim
  | cons main rest =>
      have Hsource' : RestoredSourceInductiveSemanticTrace sourceDecl
          c.lparams c.safety sourceVEnv envTypes
          ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
          Hrestored.inductives (main :: rest) primaryRecursors := by
        simpa only [htypesSource] using Hsource
      have Hprimary' : RestoredPrimaryIotaSemanticTrace sourceDecl
          (canonicalRestoredShapeBlock sourceDecl primaryRecursors
            auxiliaryRecursors) finalBaseVEnv
          ({
            c := c
            stats := stats
            loweredDecl := loweredDecl
            nparams := nparams
            depth := depth
            isUnsafe := isUnsafe
            initialEnv := sourceVEnv
            indTypes := result.types.toArray
            headerEnv := headerEnv
            ctorEnv := ctorEnv
            headers := Hheaders
            constructors := R
            production := Hprod } : NestedInstalledProduction loweredEnv)
          Hsource' (main :: rest) primaryRules := by
        simpa only [htypesSource] using Hprimary
      have Halignment := Hrestored.generatedAlignmentTraceOfProduction
        Hlower Hc Hprod hempty
      rcases Hrestored.finalAuxiliaryEvidenceOfValidation Halignment
          HauxiliaryRecursors HruleValid HruleRun sourceDecl main sourceVEnv
          primaryRecursors primaryRules Hnames with
        ⟨auxiliaryRules, Hauxiliary⟩
      have HauxiliarySemantics : RestoredAuxiliaryShapeTrace sourceDecl
          (canonicalRestoredBlock sourceDecl primaryRecursors
            auxiliaryRecursors primaryRules auxiliaryRules)
          main c.safety
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          Hrestored.auxiliaries [] []
            auxiliaryRecursors auxiliaryRules := by
        simpa only [hcanonicalCtors, hcanonicalElims] using Hauxiliary.semantics
      have HauxiliaryWF : RestoredAuxiliaryFinalWFTrace sourceDecl
          (canonicalRestoredBlock sourceDecl primaryRecursors
            auxiliaryRecursors primaryRules auxiliaryRules)
          main c.safety
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
            finalBaseVEnv HauxiliarySemantics [] [] auxiliaryRecursors
              auxiliaryRules := by
        simpa only [hcanonicalCtors, hcanonicalElims] using Hauxiliary.wf
      let P' : NestedInstalledProduction loweredEnv := {
          c := c
          stats := stats
          loweredDecl := loweredDecl
          nparams := nparams
          depth := depth
          isUnsafe := isUnsafe
          initialEnv := sourceVEnv
          indTypes := result.types.toArray
          headerEnv := headerEnv
          ctorEnv := ctorEnv
          headers := Hheaders
          constructors := R
          production := Hprod }
      let Remainder : NestedFinalAssemblyRemainder P' Hrestored sourceVEnv
          sourceDecl c.lparams nparams isUnsafe c.safety main rest
          primaryRecursors auxiliaryRecursors primaryRules auxiliaryRules
          replay.typeEntries replay.constructorEntries replay.recursorEntries
          canonicalProdEnv finalBaseVEnv canonical := {
        productionOrder := ⟨replay.actualEntries, replay.fresh,
          replay.productionOrder⟩
        sourceMapWF := Hc.checking.tr.map_wf
        auxiliarySemantics := HauxiliarySemantics
        recursorValues := replay.recursorValues
        auxiliaryWF := HauxiliaryWF }
      have HsourceCanonical : RestoredSourceInductiveSemanticTrace sourceDecl
          c.lparams c.safety sourceVEnv canonical.venvTypes
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          Hrestored.inductives (main :: rest)
            primaryRecursors := by
        simpa only [hcanonicalTypes, hcanonicalCtors, hcanonicalElims] using Hsource'
      have HprimaryCanonical : RestoredPrimaryIotaSemanticTrace sourceDecl
          (canonicalRestoredShapeBlock sourceDecl primaryRecursors
            auxiliaryRecursors) finalBaseVEnv P' HsourceCanonical
              (main :: rest) primaryRules := by
        simpa only [P', hcanonicalTypes, hcanonicalCtors, hcanonicalElims] using Hprimary'
      exact ⟨⟨Remainder.certificate HsourceCanonical HprimaryCanonical
        replay.typeValues replay.constructorValues Hformation
        hformationExpanded Hmetadata huvars hnumParams hunsafeEq htypesSource
        hsourceNonempty (by rw [hcanonicalElims]; exact Hcases)
        (by rw [hcanonicalElims]; exact Hreplay)
        (by rw [hcanonicalElims]; exact HelimRestored), rfl,
        HruleValid⟩⟩

/- Work-in-progress adapter retained outside the active declarations while
the dependent production record is reindexed as one aggregate rather than by
its proof-valued component fields.

/-- Assemble a pre-certificate validated execution from its own production,
restoration, validation, and native-source traces.  Formation is kept explicit
here only as the next local lemma to derive from the retained header and
constructor-parameter validations; no final rule, replay, or assembly package
is supplied. -/
theorem NestedValidatedRunResult.assemblyOfFormation
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hformation : NestedFormationAssembly sourceVEnv sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl) :
    Nonempty { C : NestedFinalAssemblyShape E.restoration sourceVEnv
        sourceDecl lparams nparams isUnsafe safety //
      C.production = E.production } := by
  have HsourceCons : ∃ main rest, sourceTypes = main :: rest := by
    have hnonempty : sourceTypes ≠ [] := by
      rcases E.lowering with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
      rcases Hrun.source with
        ⟨first, tail, _tail, _paramsState, _lctx, _params, hsource, _⟩
      rw [hsource]
      simp
    cases htypes : sourceTypes with
    | nil => exact (hnonempty htypes).elim
    | cons main rest => exact ⟨main, rest, rfl⟩
  rcases HsourceCons with ⟨main, rest, rfl⟩
  have hproductionUnsafe : E.production.isUnsafe = isUnsafe := by
    calc
      E.production.isUnsafe = E.production.loweredDecl.isUnsafe :=
        E.production.constructors.core.isUnsafe.symm
      _ = Hformation.expanded.isUnsafe := by rw [hformationExpanded]
      _ = sourceDecl.isUnsafe := Hformation.isUnsafe
      _ = E.nativeSource.sourceDecl.isUnsafe :=
        congrArg VInductDecl.isUnsafe E.nativeSourceDecl_eq.symm
      _ = isUnsafe := E.nativeSource.core.isUnsafe
  have Hheaders : DeclaredHeadersResult E.productionContext
      E.production.stats E.production.loweredDecl nparams isUnsafe
      E.production.depth sourceVEnv result.types.toArray
        E.production.headerEnv := by
    simpa only [E.production_c, E.production_nparams, hproductionUnsafe,
      E.production_initialEnv, E.production_indTypes] using
        E.production.headers
  have R : ConstructorPhasesResult Hheaders E.production.ctorEnv := by
    have hheaders : E.production.headers = Hheaders := Subsingleton.elim _ _
    exact Eq.mp
      (congrArg (fun headers =>
        ConstructorPhasesResult headers E.production.ctorEnv) hheaders)
      E.production.constructors
  have Hprod : CompletedRecursorPhasesResult R.completed E.loweredEnv := by
    have hconstructors : E.production.constructors = R :=
      Subsingleton.elim _ _
    exact Eq.mp
      (congrArg (fun constructors =>
        CompletedRecursorPhasesResult constructors.completed E.loweredEnv) hconstructors)
      E.production.production
  have Hlower : NestedLoweringResultClosed E.productionContext.env
      E.validationFuel.inductiveFuel nparams (main :: rest)
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := (main :: rest).toArray } result := by
    rw [E.productionContext_env]
    simpa using E.lowering
  have hempty :
      (({ lvls := lparams.map .param, newTypes := #[] } :
        Lean4Lean.ElimNestedInductive.State).nestedAux) = #[] := by
    apply Array.ext
    intro i hi₁ hi₂
    simp at hi₂
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases Hlower with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh rfl
  have Hcore : TrInductDeclCore sourceVEnv
      E.productionContext.lparams nparams (main :: rest) isUnsafe sourceDecl
        E.nativeSource.envTypes E.nativeSource.envCtors := by
    simpa only [E.productionContext_lparams, E.nativeSourceDecl_eq] using
      E.nativeSource.core
  have Hmetadata : MaterializedInductivePrefix sourceDecl
      E.production.loweredDecl := by
    exact Eq.mp
      (congrArg (fun decl => MaterializedInductivePrefix decl
        E.production.loweredDecl) E.nativeSourceDecl_eq)
      E.nativeSource.materialized
  have HownersContext : ConstructorOwnersPresent E.productionContext.env := by
    rw [E.productionContext_env]
    exact Howners
  have Hrestored : RestoredNestedDeclarationsResult result E.loweredEnv
      E.productionContext.env
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1
      ((), outEnv) := by
    rw [E.productionContext_env]
    exact E.restoration
  have Hconstructors : RestoreAuxConstructorsFresh result E.loweredEnv
      E.nativeSource.envTypes :=
    Hlower.restoreAuxConstructorsFreshAtTypes E.productionContextWF
      Hprod Hcore HownersContext hempty
  have HexactSource :=
    Hlower.sourceSemanticTraceAtFreshOfTelescopeTranslations
      E.productionContextWF Hprod Hsources
      Hcore Hmetadata Hfamilies Hconstructors
      hempty Hrestored (by
        intro familyIdx hfamily _hdecl hentry stepSource stepTarget Hstep
        exact Hlower.restoredPrimaryTelescopeAtFreshOfValidation
          E.productionContextWF Hprod
          E.nativeSource.validationValid E.recursorTypeValidation hempty
          familyIdx hfamily hentry stepSource stepTarget Hstep)
  rcases HexactSource with ⟨primaryRecursors, Hsource⟩
  rcases E.primitiveSafe with ⟨primitiveEntries, Hprimitive⟩
  rcases Hlower.existsValidatedExactStagedRestoration
      E.productionContextWF Hprod Hcore
      Hrestored Hsource E.nativeSource.validationValid
      E.recursorTypeValidation hempty hvisible Hprimitive with
    ⟨auxiliaryRecursors, HauxiliaryRecursors, replay, canonicalProdEnv,
      finalBaseVEnv, ⟨canonical⟩, _hlookup⟩
  have HruleValid : CheckingEnv.Valid safety outEnv finalBaseVEnv :=
    canonical.validOfFreshPermutation replay.fresh
      replay.productionOrder (by
        rw [E.productionContext_env]
        simpa only [E.productionContext_safety] using
          E.productionContextWF.checking)
  have huvars : sourceDecl.uvars = lparams.length :=
    E.nativeSource.core.uvars
  have hnumParams : sourceDecl.nparams = nparams :=
    E.nativeSource.core.nparams
  have hunsafeEq : sourceDecl.isUnsafe = isUnsafe :=
    E.nativeSource.core.isUnsafe
  apply Hlower.validatedFinalAssemblyCertificate E.productionContextWF
    Hprod Hsources Hcore
    Hmetadata (by
      simpa only [E.productionContext_env] using Howners) hempty E.production
  · apply Eq.symm
    cases E.production
    simp_all
  · exact Hrestored
  · exact primaryRecursors
  · exact auxiliaryRecursors
  · exact Hsource
  · exact HauxiliaryRecursors
  · exact replay
  · exact canonical
  · exact HruleValid
  · exact E.recursorRuleValidation
  · exact Hformation
  · exact hformationExpanded
  · exact huvars
  · exact hnumParams
  · exact hunsafeEq
  · simp
-/

/-- Transporting the environment index of a formation assembly does not alter
its data-valued expanded declaration. -/
private theorem NestedFormationAssembly.expanded_eq_of_envTransport
    {env₁ env₂ : VEnv} {decl : VInductDecl} (h : env₁ = env₂)
    (H : NestedFormationAssembly env₂ decl) :
    (Eq.mpr (congrArg (fun env => NestedFormationAssembly env decl) h)
      H).expanded = H.expanded := by
  subst env₂
  rfl

/-- Dependent eta for an installed production whose complete phase package is
transported together with its inductive-type array. -/
private theorem NestedInstalledProduction.rebuildIndTypes_eq
    {outEnv : Environment} (P : NestedInstalledProduction outEnv)
    (newIndTypes : Array InductiveType) (h : P.indTypes = newIndTypes) :
    let PhasePack := fun indTypes =>
      Sigma fun Hheaders : DeclaredHeadersResult P.c P.stats P.loweredDecl
          P.nparams P.isUnsafe P.depth P.initialEnv indTypes P.headerEnv =>
        Sigma fun R : ConstructorPhasesResult Hheaders P.ctorEnv =>
          CompletedRecursorPhasesResult R.completed outEnv
    let pack : PhasePack newIndTypes :=
      Eq.mp (congrArg PhasePack h)
        (⟨P.headers, P.constructors, P.production⟩ : PhasePack P.indTypes)
    ({ c := P.c
       stats := P.stats
       loweredDecl := P.loweredDecl
       nparams := P.nparams
       depth := P.depth
       isUnsafe := P.isUnsafe
       initialEnv := P.initialEnv
       indTypes := newIndTypes
       headerEnv := P.headerEnv
       ctorEnv := P.ctorEnv
       headers := pack.1
       constructors := pack.2.1
       production := pack.2.2 } : NestedInstalledProduction outEnv) = P := by
  subst newIndTypes
  rfl

/-- The source families reconstructed by native restoration inherit the
ordinary header shapes of the exact lowered prefix.  The source-core builder
retains literal header values, while materialization retains the separately
checked index count and result universe. -/
theorem NestedValidatedRunResult.nativeSourceTypeShapes
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ target ∈ sourceDecl.types,
      sourceDecl.TypeShape sourceVEnv
        E.production.headers.sourceMaterialized.headers.params target := by
  let P := E.production
  have hinitial : P.initialEnv = sourceVEnv := E.production_initialEnv
  have Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl E.nativeSource.envTypes E.nativeSource.envCtors := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.core
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have hloweredLength : P.loweredDecl.types.length = result.types.length :=
    by
      have harray := congrArg Array.toList E.production_indTypes
      simp at harray
      exact (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        P.constructors.core).symm.trans (congrArg List.length harray)
  have hprefix : sourceDecl.types.length ≤ P.loweredDecl.types.length := by
    rw [hsourceLength, hloweredLength]
    let initialState : Lean4Lean.ElimNestedInductive.State :=
      { lvls := lparams.map .param, newTypes := #[] }
    have Hresult : NestedLoweringResult sourceProdEnv
        E.validationFuel.inductiveFuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        result := E.lowering.toResult
    exact Hresult.sourceTypes_length_le
  have huvarsEq : sourceDecl.uvars = P.loweredDecl.uvars := by
    calc
      sourceDecl.uvars = lparams.length := Hsource.uvars
      _ = P.c.lparams.length := by rw [E.production_c,
        E.productionContext_lparams]
      _ = P.loweredDecl.uvars := P.constructors.core.uvars.symm
  have hnparamsEq : sourceDecl.nparams = P.loweredDecl.nparams := by
    calc
      sourceDecl.nparams = nparams := Hsource.nparams
      _ = P.nparams := E.production_nparams.symm
      _ = P.loweredDecl.nparams := P.constructors.core.nparams.symm
  intro target htarget
  rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
  have hiExpanded : i < P.loweredDecl.types.length :=
    Nat.lt_of_lt_of_le hi hprefix
  let sourceTarget := sourceDecl.types[i]
  let expandedTarget := P.loweredDecl.types[i]
  have hvalue : sourceTarget.toVConstVal = expandedTarget.toVConstVal := by
    have hvaluesAll : sourceDecl.typeConstants =
        (P.loweredDecl.types.take sourceTypes.length).map
          VInductiveType.toVConstVal := by
      simpa only [P, E.nativeSourceDecl_eq] using
        E.nativeSource.sourceTypeValues
    have hvalues := congrArg (fun values => values[i]?)
      hvaluesAll
    have hiTake : i <
        (P.loweredDecl.types.take sourceTypes.length).length := by
      simp only [List.length_take]
      rw [← hsourceLength]
      omega
    simp only [VInductDecl.typeConstants, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiTake,
      List.getElem_take, Option.map_some] at hvalues
    simpa only [sourceTarget, expandedTarget] using Option.some.inj hvalues
  have htype : sourceTarget.type = expandedTarget.type :=
    congrArg (fun value : VConstVal => value.type) hvalue
  have Hmetadata : MaterializedInductivePrefix sourceDecl P.loweredDecl := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.materialized
  have hnumIndices : sourceTarget.numIndices = expandedTarget.numIndices :=
    Hmetadata.numIndices hprefix i hi hiExpanded
  have hresultLevel : sourceTarget.resultLevel = expandedTarget.resultLevel :=
    Hmetadata.resultLevel hprefix i hi hiExpanded
  have Hshape : P.loweredDecl.TypeShape sourceVEnv
      P.headers.sourceMaterialized.headers.params expandedTarget := by
    have H := P.headers.sourceMaterialized.headers.typeShapes expandedTarget
      (List.getElem_mem hiExpanded)
    simpa only [P.headers.sourceContextVEnv, hinitial] using H
  rcases Hshape with
    ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
      Hnormalized, Hparams, Hindices, HparamsDefEq, Hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
    by simpa only [sourceTarget, expandedTarget, huvarsEq, htype] using
      Hnormalized,
    by simpa only [hnparamsEq] using Hparams,
    by simpa only [sourceTarget, expandedTarget, hnumIndices] using Hindices,
    by simpa [VInductDecl.ParamsDefEq, huvarsEq] using HparamsDefEq,
    by simpa only [sourceTarget, expandedTarget, huvarsEq, hresultLevel] using
      Hresult⟩

/-- The literal restored-constructor parameter validator supplies the raw
common-parameter shape of every reconstructed source constructor.  The
family header shape above identifies the validator's opened domains with the
single parameter telescope retained by ordinary header production. -/
theorem NestedValidatedRunResult.nativeSourceParameterWF
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hraw : ∀ type ∈ sourceDecl.types, ∀ ctor ∈ type.ctors,
      sourceDecl.RawCtorShape type ctor) :
    sourceDecl.SourceParameterWF sourceVEnv := by
  let P := E.production
  let params := P.headers.sourceMaterialized.headers.params
  have Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl E.nativeSource.envTypes E.nativeSource.envCtors := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.core
  have hsourceWF : sourceVEnv.WF := by
    have Hwf := E.productionContextWF.checking.tr.wf
    rw [E.productionContext_venv] at Hwf
    exact Hwf
  have htypesWF : E.nativeSource.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource hsourceWF
  have hsourceLE : sourceVEnv ≤ E.nativeSource.envTypes :=
    VEnv.addConstVals_le Hsource.typesAdded
  have HtypeShapesBase : ∀ target ∈ sourceDecl.types,
      sourceDecl.TypeShape sourceVEnv params target :=
    E.nativeSourceTypeShapes
  have HtypeShapes : ∀ target ∈ sourceDecl.types,
      sourceDecl.TypeShape E.nativeSource.envTypes params target := by
    intro target htarget
    exact (HtypeShapesBase target htarget).mono hsourceLE
  let initialState : Lean4Lean.ElimNestedInductive.State :=
    { lvls := lparams.map .param, newTypes := #[] }
  have Hlower : NestedLoweringResultClosed sourceProdEnv
      E.validationFuel.inductiveFuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := by
    simpa only [initialState] using E.lowering
  rcases Hlower with ⟨finalState, Hrun, Hcache, HparamsNodup⟩
  rcases Hrun.source with
    ⟨first, rest, sourceTail, paramsState, sourceLCtx, sourceParams,
      hsourceTypes, Hopening, _hnewTypes, _hnestedAux, _hnextIdx,
      _hprefix, _Hbinding, _Hselection, Hqueue⟩
  have hfirstSource : 0 < sourceTypes.length := by
    rw [hsourceTypes]
    simp
  have hfirstTarget : 0 < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfirstSource
  have HfirstType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    0 hfirstSource hfirstTarget
  have HfirstTranslation : TrExprS E.nativeSource.envTypes lparams []
      first.type sourceDecl.types[0].toVConstVal.type := by
    simpa [hsourceTypes] using HfirstType.header.type.mono hsourceLE
  have HopeningResult : NestedParamOpening {} #[] first.type nparams
      result.lctx sourceTail result.params := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact Hopening
  have hresultLCtxWF : result.lctx.WF := Hrun.resultContextWF
  have hresultFresh : ∀ fv ∈ result.lctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv :=
    Hrun.resultContextKernelFresh rfl
  refine ⟨params, E.nativeSource.envTypes, Hsource.typesAdded,
    HtypeShapesBase, ?_, Hraw⟩
  intro target htarget ctor hctor
  rcases List.mem_iff_getElem.1 htarget with ⟨familyIdx, hfamily, rfl⟩
  rcases List.mem_iff_getElem.1 hctor with ⟨ctorIdx, hctorTarget, rfl⟩
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    familyIdx hsourceFamily hfamily
  have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
    rw [Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    exact hctorTarget
  have HsourceCtor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx hsourceCtor hctorTarget
  have hparameterRun :=
    validateRestoredConstructorParameters.loop_eq_ok_of_run
      E.parameterValidation (List.getElem_mem hsourceFamily)
        (List.getElem_mem hsourceCtor)
  have HprefixZero : CheckedConstructorParameterPrefix
      E.nativeSource.envTypes lparams
      { P.stats with params := result.params }
      sourceTypes[familyIdx].ctors[ctorIdx].type 0
      sourceTypes[familyIdx].ctors[ctorIdx].type [] [] := .zero
  rcases HopeningResult.validateRestoredConstructorPrefix P.stats
      E.nativeSource.headerValidationValid
      hresultLCtxWF hresultFresh .nil rfl
      trivial nofun HfirstTranslation HsourceCtor.type HprefixZero
      hparameterRun with
    ⟨parameterMLCtx, constructorTail, constructorSourceDomains,
      familyDomains, familyTail, hparameterLCtx, hparameterWF,
      hfamilyTarget, hfamilyLength, hparameterContext, Hchecked⟩
  have Hchecked' : CheckedConstructorParameterPrefix
      E.nativeSource.envTypes lparams
      { P.stats with params := result.params }
      sourceTypes[familyIdx].ctors[ctorIdx].type sourceDecl.nparams
      constructorTail parameterMLCtx.vlctx constructorSourceDomains := by
    simpa only [Array.size_empty, Nat.zero_add, Hsource.nparams] using Hchecked
  have HfamilyShape := HtypeShapes sourceDecl.types[0]
    (List.getElem_mem hfirstTarget)
  rcases HfamilyShape with
    ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
      Hnormalized, HparamsTake, _HindicesTake, HcanonicalOwn, _Hresult⟩
  rcases VExpr.takeForalls_rebuild HparamsTake with
    ⟨hnormalized, hownLength⟩
  have HfamilyOwn : E.nativeSource.envTypes.IsDefEqU sourceDecl.uvars []
      (VExpr.wrapForalls familyDomains familyTail)
      (VExpr.wrapForalls ownParams afterParams) := by
    rw [← hfamilyTarget, ← hnormalized]
    exact ⟨exprType, Hnormalized⟩
  have hdomainLength : familyDomains.length = ownParams.length := by
    calc
      familyDomains.length = nparams := hfamilyLength
      _ = sourceDecl.nparams := Hsource.nparams.symm
      _ = ownParams.length := hownLength.symm
  have HfamilyOwnCtx : E.nativeSource.envTypes.IsDefEqCtx
      sourceDecl.uvars [] familyDomains.reverse ownParams.reverse :=
    by
      simpa using VEnv.IsDefEqU.wrapForalls_context htypesWF
        (VEnv.IsDefEqCtx.refl (by trivial)) hdomainLength HfamilyOwn
  have HcanonicalFamily : E.nativeSource.envTypes.IsDefEqCtx
      sourceDecl.uvars [] params.reverse familyDomains.reverse := by
    have HcanonicalOwn' : E.nativeSource.envTypes.IsDefEqCtx
        sourceDecl.uvars [] params.reverse ownParams.reverse := by
      simpa [VInductDecl.ParamsDefEq] using HcanonicalOwn
    exact VEnv.IsDefEqCtx.transEmpty htypesWF HcanonicalOwn'
      (HfamilyOwnCtx.symm htypesWF.ordered)
  have HcanonicalScope : E.nativeSource.envTypes.IsDefEqCtx lparams.length []
      params.reverse parameterMLCtx.vlctx.toCtx := by
    have hparameterContext' : parameterMLCtx.vlctx.toCtx =
        familyDomains.reverse := by
      simpa [VLCtx.toCtx] using hparameterContext
    rw [hparameterContext']
    simpa only [Hsource.uvars] using HcanonicalFamily
  exact Hchecked'.ctorParameterShape htypesWF hparameterWF.tr.wf
    HsourceCtor.type Hsource.uvars HcanonicalScope

/-- Assemble a validated execution in the production record's native
dependent indices, then transport the completed certificate once to the
public indices.  Transporting only the finished aggregate avoids splitting
the dependent header/constructor/recursor phase chain apart. -/
private theorem NestedValidatedRunResult.assemblyOfFormationNative
    {ves : VEnvs} {sourceVEnv : VEnv} {safety : DefinitionSafety}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (wf : ves.WFCore sourceProdEnv)
    (hsourceVEnv : sourceVEnv = ves.venv (if isUnsafe then .unsafe else .safe))
    (hsafetyEq : safety = if isUnsafe then .unsafe else .safe)
    (hnested : result.aux2nested.size ≠ 0)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hformation : NestedFormationAssembly sourceVEnv sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl) :
    Nonempty { C : NestedFinalAssemblyShape E.restoration sourceVEnv
        sourceDecl lparams nparams isUnsafe safety //
      C.production = E.production ∧
        CheckingEnv.Valid safety
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
          C.finalBaseVEnv } := by
  subst hsourceVEnv hsafetyEq
  have hctorNames := Hformation.sourceConstructorNames hformationExpanded
  let P := E.production
  have hc : P.c = E.productionContext := E.production_c
  have henv : P.c.env = sourceProdEnv :=
    (congrArg AddInductive.Context.env hc).trans E.productionContext_env
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams hc).trans
      E.productionContext_lparams
  have hsafety : P.c.safety = if isUnsafe then .unsafe else .safe :=
    (congrArg AddInductive.Context.safety hc).trans
      E.productionContext_safety
  have hnparams : P.nparams = nparams := E.production_nparams
  have hinitial : P.initialEnv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.production_initialEnv
  have hindTypes : P.indTypes = result.types.toArray := E.production_indTypes
  have hisUnsafe : P.isUnsafe = isUnsafe := by
    exact E.production_isUnsafe_source
  have HcP : ContextWF P.c := by
    rw [hc]
    exact E.productionContextWF
  have HsourceCons : ∃ main rest, sourceTypes = main :: rest := by
    have hnonempty : sourceTypes ≠ [] := by
      rcases E.lowering with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
      rcases Hrun.source with
        ⟨first, tail, _tail, _paramsState, _lctx, _params, hsource, _⟩
      rw [hsource]
      simp
    cases htypes : sourceTypes with
    | nil => exact (hnonempty htypes).elim
    | cons main rest => exact ⟨main, rest, rfl⟩
  rcases HsourceCons with ⟨main, rest, rfl⟩
  let initialState : Lean4Lean.ElimNestedInductive.State :=
    { lvls := P.c.lparams.map .param, newTypes := #[] }
  have hempty : initialState.nestedAux = #[] := by
    apply Array.ext
    · change 0 = 0
      rfl
    · intro i _hi₁ hi₂
      simp at hi₂
  have Hlower : NestedLoweringResultClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result := by
    simpa only [henv, hnparams, hlparams, initialState] using E.lowering
  let PhasePack := fun indTypes =>
    Sigma fun Hheaders : DeclaredHeadersResult P.c P.stats P.loweredDecl P.nparams
        P.isUnsafe P.depth P.initialEnv indTypes P.headerEnv =>
      Sigma fun R : ConstructorPhasesResult Hheaders P.ctorEnv =>
        CompletedRecursorPhasesResult R.completed E.loweredEnv
  let Hpack : PhasePack result.types.toArray :=
    Eq.mp (congrArg PhasePack hindTypes)
      (⟨P.headers, P.constructors, P.production⟩ : PhasePack P.indTypes)
  let Hheaders := Hpack.1
  let R := Hpack.2.1
  let Hprod := Hpack.2.2
  let P' : NestedInstalledProduction E.loweredEnv := {
    c := P.c
    stats := P.stats
    loweredDecl := P.loweredDecl
    nparams := P.nparams
    depth := P.depth
    isUnsafe := P.isUnsafe
    initialEnv := P.initialEnv
    indTypes := result.types.toArray
    headerEnv := P.headerEnv
    ctorEnv := P.ctorEnv
    headers := Hheaders
    constructors := R
    production := Hprod }
  have Hcore : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      (main :: rest) P.isUnsafe sourceDecl E.nativeSource.envTypes
        E.nativeSource.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe,
      E.nativeSourceDecl_eq] using E.nativeSource.core
  have Hmetadata : MaterializedInductivePrefix sourceDecl P.loweredDecl := by
    exact Eq.mp
      (congrArg (fun decl => MaterializedInductivePrefix decl P.loweredDecl)
        E.nativeSourceDecl_eq)
      E.nativeSource.materialized
  have HownersP : ConstructorOwnersPresent P.c.env := by
    rw [henv]
    exact Howners
  let RestorationAt := fun env =>
    RestoredNestedDeclarationsResult result E.loweredEnv env
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1
      ((), outEnv)
  let Hrestored : RestorationAt P.c.env :=
    Eq.mpr (congrArg RestorationAt henv) E.restoration
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases Hlower with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors : RestoreAuxConstructorsFresh result E.loweredEnv
      E.nativeSource.envTypes :=
    Hlower.restoreAuxConstructorsFreshAtTypes HcP Hprod Hcore
      HownersP hempty
  have Hparams : sourceDecl.SourceParameterWF P.initialEnv := by
    rw [hinitial]
    exact Hformation.sourceParameters
  have Harity : sourceDecl.ConstructorArityPrefix P.loweredDecl := by
    have h := Hformation.constructorArityPrefix
    rw [hformationExpanded] at h
    exact h
  have HbaseValid : CheckingEnv.Valid P.c.safety P.c.env P.initialEnv := by
    have Hchecking := E.productionContextWF.checking
    simpa only [hc, hinitial, E.productionContext_venv] using Hchecking
  obtain ⟨es, Hcases, Hreplay, key, sL, auxC, hcompEl, hesEq, -, -, -, -, -, -, -, DC, -, -⟩ :=
    E.caseEliminators wf Hsources Howners Hformation hformationExpanded
  have HelimRestored : NestedEliminatorsRestored P' result
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2 sourceDecl P.c.lparams es := by
    have hP'P : P' = P := by
      simpa only [P', Hheaders, R, Hprod, Hpack] using
        NestedInstalledProduction.rebuildIndTypes_eq P result.types.toArray hindTypes
    rw [hP'P, hlparams]
    exact ⟨key, sL, auxC, hcompEl, hesEq, DC⟩
  have HcasesP : VInductBlock.EliminatorsWF P.initialEnv sourceDecl (sourceDecl.caseBlock es) := by
    rw [hinitial]; exact Hcases
  -- the corner in the environments containing the restored constructors
  have hcornerAt : ∀ {venv'}, E.nativeSource.envTypes ≤ venv' →
      ProjectionCorner P.c.safety outEnv venv' ∧
      ProjectionCorner P.c.safety E.validationEnv venv' := by
    intro venv' hle
    have hsourceLE : P.initialEnv ≤ E.nativeSource.envTypes :=
      VEnv.addConstVals_le Hcore.typesAdded
    rcases HbaseValid.corner with hch | hcert
    · exact ⟨.inl (hch.mono (hsourceLE.trans hle)), .inl (hch.mono (hsourceLE.trans hle))⟩
    · rw [henv, hinitial, hsafety] at hcert
      have H := E.restoredCtorTelescopes Hsources Howners wf.envGF hcert
      rw [hsafety]
      exact ⟨.inr (CtorTelescopes.mono H.1 hle), .inr (CtorTelescopes.mono H.2 hle)⟩
  have HtypeValid : CheckingEnv.Valid P.c.safety E.validationEnv
      ((E.nativeSource.envCtors.addEliminators es).addProjections
        sourceDecl.projectionEntries) := by
    have hvalidCore : CheckingEnv.ValidCore P.c.safety E.validationEnv
        E.nativeSource.envCtors := by
      simpa only [hsafety] using E.nativeSource.validationValid
    have HV : RestoredConstructorValidationEnvironment result E.loweredEnv
        P.c.env ((main :: rest).map (fun type => type.name)) false
        (main :: rest) E.validationEnv := by
      rw [henv]
      exact E.validationEnvironment
    obtain ⟨hcasesWF, hprojectedWF⟩ := HcasesP.windowWF HbaseValid.tr.wf Hcore Hparams
    exact HV.validProjected Hlower HcP Hprod Hcore Hmetadata Hsources Harity
      hempty Hrestored hvalidCore HbaseValid.projectionRegistry
      HbaseValid.recursors HbaseValid.quot hcasesWF hprojectedWF
      (hcornerAt (VEnv.addConstVals_le Hcore.ctorsAdded)).2
  have HtypeRun : Lean4Lean.validateRestoredRecursorTypes.run
      E.validationEnv E.loweredEnv P.c.lparams P.c.safety
      E.validationFuel result
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 = .ok () := by
    simpa only [hlparams, hsafety] using E.recursorTypeValidation
  have HexactSource :=
    Hlower.sourceSemanticTraceAtFreshOfTelescopeTranslations HcP Hprod
      Hsources Hcore Hmetadata Hfamilies Hconstructors hempty Hrestored (by
        intro familyIdx hfamily _hdecl hentry stepSource stepTarget Hstep
        exact Hlower.restoredPrimaryTelescopeAtFreshOfValidation HcP
          Hprod HtypeValid HtypeRun hempty familyIdx hfamily hentry
            stepSource stepTarget Hstep)
  rcases HexactSource with ⟨primaryRecursors, Hsource⟩
  rcases E.primitiveSafe with ⟨primitiveEntries, HprimitiveRaw⟩
  have Hprimitive : PrimitiveSafeFreshConstantTrace false P.c.env
      primitiveEntries outEnv := by
    simpa only [henv] using HprimitiveRaw
  have hvisibleP : P.c.safety ≤
      (if P.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    simpa only [hsafety, hisUnsafe] using hvisible
  rcases Hlower.existsValidatedExactStagedRestoration
      (primaryProdEnv := Hrestored.primaryEnv) HcP Hprod Hcore
      Hrestored Hsource HtypeValid HtypeRun Hparams hempty hvisibleP Hprimitive HcasesP
      with
    ⟨auxiliaryRecursors, HauxiliaryRecursors, replay, canonicalProdEnv,
      finalBaseVEnv, ⟨⟨canonical, hcanonicalElims⟩⟩, _hlookup⟩
  have HruleValid : CheckingEnv.Valid P.c.safety
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2 (main :: rest)
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1))
      finalBaseVEnv :=
    E.finalValidOfStaged_of_hitShape wf Hsources hnested Hlower HcP Hprod Hcore
      Hmetadata Harity hempty Hrestored replay.fresh canonical replay.productionOrder
      (by simpa [VInductDecl.typeConstants] using replay.typeValues)
      (by simpa [VInductDecl.constructorConstants] using replay.constructorValues)
      HbaseValid henv hinitial hctorNames Hsource HauxiliaryRecursors
      replay.recursorValues (hcornerAt (by
        have h1 := canonical.abstract_types
        rw [show _ = _ from replay.typeValues] at h1
        have h2 : P.initialEnv.addConstVals
            (List.map VInductiveType.toVConstVal sourceDecl.types) =
              some E.nativeSource.envTypes := Hcore.typesAdded
        rw [h2] at h1
        rw [Option.some.inj h1]
        exact canonical.formationAdded.constructorLE.trans
          (VEnv.addEliminators_addProjections_le.trans canonical.recursorsAdded.le))).1
  have HruleRun : Lean4Lean.validateRestoredRecursorRules.run
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2 (main :: rest)
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1))
      E.loweredEnv P.c.lparams P.c.safety E.validationFuel result
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 = .ok () := by
    simpa only [hlparams, hsafety] using E.recursorRuleValidation
  let HformationP : NestedFormationAssembly P.initialEnv sourceDecl :=
    Eq.mpr
      (congrArg (fun env => NestedFormationAssembly env sourceDecl) hinitial)
      Hformation
  have hformationExpandedP : HformationP.expanded = P.loweredDecl := by
    calc
      HformationP.expanded = Hformation.expanded :=
        NestedFormationAssembly.expanded_eq_of_envTransport hinitial Hformation
      _ = E.production.loweredDecl := hformationExpanded
      _ = P.loweredDecl := rfl
  have huvars : sourceDecl.uvars = P.c.lparams.length := Hcore.uvars
  have hnumParams : sourceDecl.nparams = P.nparams := Hcore.nparams
  have hunsafeEq : sourceDecl.isUnsafe = P.isUnsafe := Hcore.isUnsafe
  have hP' : P' = {
      c := P.c
      stats := P.stats
      loweredDecl := P.loweredDecl
      nparams := P.nparams
      depth := P.depth
      isUnsafe := P.isUnsafe
      initialEnv := P.initialEnv
      indTypes := result.types.toArray
      headerEnv := P.headerEnv
      ctorEnv := P.ctorEnv
      headers := Hheaders
      constructors := R
      production := Hprod } := rfl
  rcases Hlower.validatedFinalAssemblyCertificate HcP Hprod Hsources
      Hcore Hmetadata HownersP hempty P' hP' Hrestored primaryRecursors
      auxiliaryRecursors Hsource HauxiliaryRecursors replay canonical
      HruleValid HruleRun HformationP hformationExpandedP huvars hnumParams
      hunsafeEq (by simp) hcanonicalElims HcasesP
      (by rw [hinitial, henv]; exact Hreplay) HelimRestored with ⟨⟨C, hproduction, hCvalid⟩⟩
  have hproductionOriginal : C.production = P := by
    calc
      C.production = P' := hproduction
      _ = P := by
        simpa only [P', Hheaders, R, Hprod, Hpack] using
          NestedInstalledProduction.rebuildIndTypes_eq P
            result.types.toArray hindTypes
  let CertificateAt := fun q : Sigma RestorationAt =>
    Nonempty { C : NestedFinalAssemblyShape q.2 P.initialEnv sourceDecl
        P.c.lparams P.nparams P.isUnsafe P.c.safety //
      C.production = P ∧
        CheckingEnv.Valid P.c.safety
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2 (main :: rest)
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1))
          C.finalBaseVEnv }
  have hp : (⟨P.c.env, Hrestored⟩ : Sigma RestorationAt) =
      ⟨sourceProdEnv, E.restoration⟩ := by
    apply Sigma.ext henv
    change (Eq.mpr (congrArg RestorationAt henv) E.restoration) ≍
      E.restoration
    rw [eq_mpr_eq_cast]
    exact cast_heq _ _
  have Hcertificate : CertificateAt ⟨P.c.env, Hrestored⟩ :=
    ⟨⟨C, hproductionOriginal, hCvalid⟩⟩
  have HcertificateOriginal : CertificateAt
      ⟨sourceProdEnv, E.restoration⟩ :=
    Eq.mp (congrArg CertificateAt hp) Hcertificate
  simp only [CertificateAt] at HcertificateOriginal
  rw [hinitial, hlparams, hnparams, hisUnsafe, hsafety] at HcertificateOriginal
  simpa only [P] using HcertificateOriginal

/-- Unconditional final assembly for the exact validated execution.  Ordinary
formation comes from the installed constructor phases; source parameter
formation comes from the literal restored-parameter validator; and the full
ordered nested expansion comes from the producer-owned generated registry.
No declaration-specific evidence is accepted from the caller. The stripped
output environment checked by the rule validator is valid in the shape's
final abstract environment. -/
theorem NestedValidatedRunResult.assemblyShapeNativeValid
    {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) :
    Nonempty { C : NestedFinalAssemblyShape E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production ∧
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
          C.finalBaseVEnv } := by
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.production
  have hc : P.c = E.productionContext := E.production_c
  have henv : P.c.env = sourceProdEnv :=
    (congrArg AddInductive.Context.env hc).trans E.productionContext_env
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams hc).trans
      E.productionContext_lparams
  have hnparams : P.nparams = nparams := E.production_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.production_initialEnv
  have hindTypes : P.indTypes = result.types.toArray := E.production_indTypes
  have hisUnsafe : P.isUnsafe = isUnsafe := E.production_isUnsafe_source
  have HcP : ContextWF P.c := by
    rw [hc]
    exact E.productionContextWF
  let initialState : Lean4Lean.ElimNestedInductive.State :=
    { lvls := P.c.lparams.map .param, newTypes := #[] }
  have Hlower : NestedLoweringResultClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := by
    simpa only [henv, hnparams, hlparams, initialState] using E.lowering
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hclosed : NestedLoweringResultClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  let PhasePack := fun indTypes =>
    Sigma fun Hheaders : DeclaredHeadersResult P.c P.stats P.loweredDecl
        P.nparams P.isUnsafe P.depth P.initialEnv indTypes P.headerEnv =>
      Sigma fun R : ConstructorPhasesResult Hheaders P.ctorEnv =>
        CompletedRecursorPhasesResult R.completed E.loweredEnv
  let Hpack : PhasePack result.types.toArray :=
    Eq.mp (congrArg PhasePack hindTypes)
      (⟨P.headers, P.constructors, P.production⟩ : PhasePack P.indTypes)
  let Hheaders := Hpack.1
  let R := Hpack.2.1
  let Hprod := Hpack.2.2
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.nativeSource.envTypes
        E.nativeSource.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.nativeSourceDecl_eq] using E.nativeSource.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hheaders.context.venv
        R.declared.venvCtors := by
    exact R.core
  have Hmetadata : MaterializedInductivePrefix sourceDecl P.loweredDecl := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.materialized
  have wfP : ves.WFCore P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.nativeSource.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.nativeSource.envTypes := by
    simpa only [hinitial, safety] using E.nativeSource.sourceAdded
  have HsourceTypesWF : E.nativeSource.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource
      (by simpa only [hinitial, safety] using
        (wf.tr (safety := safety)).wf)
  have Htranslations : ClosedNestedAuxiliaryTranslations
      E.nativeSource.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_native]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := by
    rfl
  rcases Hrun.nativeGeneratedFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N⟩
  have Htypes := Hrun.allExpansionsOfNativeSources Hcache Hparams Hsource
    Htarget Hmetadata Hsources
      (VEnvs.WFCore.environmentTypesClosed wfP) wfP.inductivesClosed
      (by simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf)
      hempty N E.auxiliarySelection
  have hnonempty : result.types ≠ [] := by
    rcases Hrun.source with
      ⟨first, rest, _tail, _paramsState, _lctx, _params, hsource, _⟩
    have hsourceTypes : sourceTypes ≠ [] := by
      rw [hsource]
      simp
    intro hresult
    have hle := Hclosed.toResult.sourceTypes_length_le
    rw [hresult] at hle
    have hz : sourceTypes.length = 0 := Nat.eq_zero_of_le_zero (by
      simpa using hle)
    exact hsourceTypes (List.eq_nil_of_length_eq_zero hz)
  have hnonemptyArray : result.types.toArray.toList ≠ [] := by
    simpa using hnonempty
  have huvars : P.loweredDecl.uvars = sourceDecl.uvars := by
    calc
      P.loweredDecl.uvars = P.c.lparams.length := R.core.uvars
      _ = sourceDecl.uvars := Hsource.uvars.symm
  have hdeclParams : P.loweredDecl.nparams = sourceDecl.nparams := by
    calc
      P.loweredDecl.nparams = P.nparams := R.core.nparams
      _ = sourceDecl.nparams := Hsource.nparams.symm
  have hloweredNodup : (P.loweredDecl.types.map (·.name)).Nodup := by
    have h := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)).1
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using h
  have Hraw : ∀ type ∈ sourceDecl.types, ∀ ctor ∈ type.ctors,
      sourceDecl.RawCtorShape type ctor :=
    VInductDecl.rawShapesOfNestedExpansions Htypes
      R.formation.formationWF.sourceParameterWF.rawCtorShape huvars hdeclParams
      hloweredNodup
  have Hparameters : sourceDecl.SourceParameterWF P.initialEnv := by
    simpa only [hinitial, safety] using E.nativeSourceParameterWF Hraw
  have hdeclUnsafe : P.loweredDecl.isUnsafe = sourceDecl.isUnsafe := by
    calc
      P.loweredDecl.isUnsafe = P.isUnsafe := R.core.isUnsafe
      _ = sourceDecl.isUnsafe := Hsource.isUnsafe.symm
  let HformationP : NestedFormationAssembly P.initialEnv sourceDecl :=
    NestedFormationAssembly.ofConstructorPhases R N.generated hnonemptyArray
      Hparameters huvars hdeclParams hdeclUnsafe Htypes
  let FormationAt := fun env => NestedFormationAssembly env sourceDecl
  let Hformation : FormationAt (ves.venv safety) :=
    Eq.mp (congrArg FormationAt hinitial) HformationP
  have hformationExpanded : Hformation.expanded = E.production.loweredDecl := by
    have hexpanded : Hformation.expanded = HformationP.expanded := by
      exact NestedFormationAssembly.expanded_eq_of_envTransport hinitial.symm
        HformationP
    exact hexpanded.trans rfl
  exact E.assemblyOfFormationNative wf rfl rfl hnested Hsources wf.constructorOwners
    (by cases isUnsafe <;> decide) Hformation (by
      simpa only [safety] using hformationExpanded)

end VerifyInductive
end Lean4Lean
