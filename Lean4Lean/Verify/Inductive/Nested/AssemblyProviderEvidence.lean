import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaBlockTransport
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryEvidence
import Lean4Lean.Verify.Inductive.Nested.FormationNativeEvidence
import Lean4Lean.Verify.Inductive.Nested.RecursorSemantics
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

private theorem List.set_getElem_eq_self
    (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.set i xs[i] = xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.set, List.cons.injEq, true_and]
      exact ih i (by simpa using hi)

/-! # Exact evidence boundary for nested final assembly

`NestedFinalAssemblyProducerEvidence` is the certificate-facing aggregate.
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
* `NestedFinalAssemblySemanticEvidence` retains canonical installation,
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

/-- The exact concrete/abstract primary-recursor pairs selected by a source
semantic trace.  The trace is proposition-valued, so the list is exposed
relationally rather than by an illicit proof-to-data projection. -/
theorem RestoredSourceInductiveSemanticTrace.existsRecursorEntries
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    ∃ entries : List (ConstantInfo × VConstVal),
      entries.map Prod.snd = recursors ∧
      ∀ entry ∈ entries, TrConstVal safety envCtors entry.1 entry.2 := by
  induction H with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
      rcases ih with ⟨entries, hvalues, htranslated⟩
      let head : ConstantInfo × VConstVal :=
        (.recInfo Hstep.restored.recursor.restored.newInfo,
          Hrecursor.recursor)
      refine ⟨head :: entries, by simp [head, hvalues], ?_⟩
      intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | htail
      · exact Hstep.restored.recursor.restored.restoration.translatedOfMetadata
          Hrecursor.safety_le Hrecursor.uvars Hrecursor.type Hrecursor.name
      · exact htranslated entry htail

/-- The exact concrete/abstract auxiliary-recursor pairs selected by an
auxiliary semantic trace. -/
theorem RestoredAuxiliarySemanticTrace.existsRecursorEntries
    (H : RestoredAuxiliarySemanticTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules) :
    ∃ entries : List (ConstantInfo × VConstVal),
      finalRecursors = priorRecursors ++ entries.map Prod.snd ∧
      ∀ entry ∈ entries, TrConstVal safety trEnv entry.1 entry.2 := by
  induction H with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
      rcases ih with ⟨entries, hvalues, htranslated⟩
      let head : ConstantInfo × VConstVal :=
        (.recInfo Hstep.restored.newInfo, Hsemantic.recursor)
      refine ⟨head :: entries, ?_, ?_⟩
      · simpa [head, List.append_assoc] using hvalues
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | htail
        · exact Hsemantic.translated
        · exact htranslated entry htail

/-- The two trace relations jointly select one exact dependency-ordered
restored recursor batch with the required primary/auxiliary value split. -/
theorem existsExactRestoredRecursorEntries
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors sourceTrace owners primaryRecursors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl block main safety trEnv
      auxiliaryTrace [] [] auxiliaryRecursors auxiliaryRules) :
    ∃ primaryEntries auxiliaryEntries : List (ConstantInfo × VConstVal),
      primaryEntries.map Prod.snd = primaryRecursors ∧
      auxiliaryEntries.map Prod.snd = auxiliaryRecursors ∧
      (primaryEntries ++ auxiliaryEntries).map Prod.snd =
        primaryRecursors ++ auxiliaryRecursors := by
  rcases Hsource.existsRecursorEntries with
    ⟨primaryEntries, hprimary, _hprimaryTranslated⟩
  rcases Hauxiliary.existsRecursorEntries with
    ⟨auxiliaryEntries, hauxiliary, _hauxiliaryTranslated⟩
  have hauxiliaryValues : auxiliaryEntries.map Prod.snd =
      auxiliaryRecursors := by
    simpa using hauxiliary.symm
  refine ⟨primaryEntries, auxiliaryEntries, hprimary, hauxiliaryValues, ?_⟩
  simp [hprimary, hauxiliaryValues]

private theorem VExpr.wrapLams_left_cancel
    (domains : List VExpr)
    (H : VExpr.wrapLams domains left = VExpr.wrapLams domains right) :
    left = right := by
  induction domains with
  | nil => simpa [VExpr.wrapLams] using H
  | cons domain domains ih =>
    simp only [VExpr.wrapLams] at H
    injection H with _ hbody
    exact ih hbody

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

/-- Fold the exact executable rule-restoration list into the abstract rule
batch for one family.  The only pointwise input is semantic evidence for the
rule selected at the same list index. -/
theorem RestoredPrimaryIotaFamilySemantics.ofRuleSemantics
    {decl : VInductDecl} {block : VInductBlock} {targetVEnv : VEnv}
    {owner : VInductiveType} {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {P : NestedInstalledProduction loweredEnv}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {indType : InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv}
    (hlength : owner.ctors.length =
      Hstep.restored.recursor.oldInfo.rules.length)
    (Hsemantic : ∀ i (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length),
      Nonempty (RestoredPrimaryIotaRuleSemantics decl block owner
        owner.ctors[i] result loweredEnv P targetVEnv auxRec
        (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName
        Hstep.restored.recursor.oldInfo.rules[i]
        Hstep.restored.recursor.restored.newInfo.rules[i]
        (Hstep.restored.recursor.restored.restoration.rules.entry i hold
          hnew))) :
    Nonempty (RestoredPrimaryIotaFamilySemantics decl block targetVEnv owner
      P Hstep) := by
  rcases Hstep.restored.recursor.restored.restoration.rules.primaryIotaRuleTrace
      owner.ctors hlength Hsemantic with ⟨rules, Hrules⟩
  exact ⟨⟨rules, Hrules⟩⟩

/-- Fold the literal restoration list from rule certificates produced by the
post-restoration validator.  Unlike `ofRuleSemantics`, this constructor does
not route through the legacy generated/restored structural payload: each
pointwise certificate already names the exact declarative rule and its WF
proof in the final checked environment. -/
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
    {Hprod : RecursorPhasesResult R loweredEnv}
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
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
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
      Hstep.restored.recursor envCtors) :
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
  have Htranslation : TrExprS envCtors E.info.levelParams []
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

/-- The exact operational/source family join discharges the list-level side
condition of the restored-rule fold.  Callers supply only pointwise rule
semantics at the corresponding executable restoration entries. -/
theorem RestoredPrimaryOperationalFamilySemantics.primaryIotaFamily
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {P : NestedInstalledProduction loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor)
    {block : VInductBlock} {targetVEnv : VEnv}
    (Hsemantic : ∀ i (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length),
      Nonempty (RestoredPrimaryIotaRuleSemantics sourceDecl block owner
        owner.ctors[i] result loweredEnv P targetVEnv auxRec
        (Lean.mkRecName sourceTypes[familyIdx].name)
        Hstep.restored.recursor.restored.newRecName
        Hstep.restored.recursor.oldInfo.rules[i]
        Hstep.restored.recursor.restored.newInfo.rules[i]
        (Hstep.restored.recursor.restored.restoration.rules.entry i hold
          hnew))) :
    Nonempty (RestoredPrimaryIotaFamilySemantics sourceDecl block targetVEnv
      owner P Hstep) :=
  RestoredPrimaryIotaFamilySemantics.ofRuleSemantics F.ruleCardinality
    Hsemantic

/-- A canonical generated-equation witness already determines the complete
ordinary iota judgment for that same owner and constructor.  The temporary
singleton rule list is irrelevant to the recursor layout; it merely gives
`blockCertificate` the exact rule whose retained `WF` proof is used here. -/
theorem RecursorPhasesResult.GeneratedEquationWitness.ordinaryIotaRule
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule) :
    ∃ block : VInductBlock,
      block.recursors = H.entries.map Prod.snd ∧
      Nonempty (decl.IotaRule R.declared.venvCtors block
        (getElem decl.types owner G.alignment.abstractOwner_lt)
        (getElem
          (getElem decl.types owner G.alignment.abstractOwner_lt).ctors i
          G.alignment.abstractCtor_lt) rule) := by
  let hrules : ∀ candidate ∈ [rule], candidate.WF H.outVEnv := by
    intro candidate hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact G.wf
  let B := H.blockCertificate [rule] hrules
  rcases G.alignment.iotaEquationTranslation [rule] hrules G.translation
      G.uvars with ⟨Hequation⟩
  have hcontext : VLCtx.NoIndConsts
      (B.block.recursors.map (·.name)) [] := by
    intro v mapped type hfind
    simp [VLCtx.find?] at hfind
  rcases H.stagedIotaRuleTranslation [rule] hrules Us [] owner howner i hctor
      G.alignment
      (getElem decl.types owner G.alignment.abstractOwner_lt)
      (getElem
        (getElem decl.types owner G.alignment.abstractOwner_lt).ctors i
        G.alignment.abstractCtor_lt)
      rule Hequation hcontext with ⟨Hstaged⟩
  refine ⟨B.block, ?_, G.alignment.rule.iotaRule_ofStagedTranslation
    Hstaged⟩
  rfl

/-- Data-valued ordinary interpretation of one generated equation, retaining
the exact translated bodies needed to reinterpret it as a source nested
equation. -/
structure RecursorPhasesResult.GeneratedEquationWitness.OrdinarySource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule) where
  block : VInductBlock
  blockRecursors : block.recursors = H.entries.map Prod.snd
  semantics : decl.IotaRule R.declared.venvCtors block
    (getElem decl.types owner G.alignment.abstractOwner_lt)
    (getElem
      (getElem decl.types owner G.alignment.abstractOwner_lt).ctors i
      G.alignment.abstractCtor_lt) rule
  domains : G.translation.domains = semantics.domains
  lhsBody : G.translation.lhsBody = semantics.lhsBody
  typeBody : G.translation.typeBody = semantics.typeBody

/-- Strengthen `ordinaryIotaRule` with definitional body alignment.  This
replays only the final certificate assembly; all executable field selection
and guarded recursive-result evidence still comes from the retained
generated-rule semantics. -/
noncomputable def
    RecursorPhasesResult.GeneratedEquationWitness.ordinarySource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule) :
    Nonempty G.OrdinarySource := by
  let hrules : ∀ candidate ∈ [rule], candidate.WF H.outVEnv := by
    intro candidate hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact G.wf
  let B := H.blockCertificate [rule] hrules
  rcases G.alignment.iotaEquationTranslation [rule] hrules G.translation
      G.uvars with ⟨Hequation⟩
  have hcontext : VLCtx.NoIndConsts
      (B.block.recursors.map (·.name)) [] := by
    intro v mapped type hfind
    simp [VLCtx.find?] at hfind
  rcases H.stagedIotaRuleTranslation [rule] hrules Us [] owner howner i hctor
      G.alignment
      (getElem decl.types owner G.alignment.abstractOwner_lt)
      (getElem
        (getElem decl.types owner G.alignment.abstractOwner_lt).ctors i
        G.alignment.abstractCtor_lt)
      rule Hequation hcontext with ⟨Hstaged⟩
  let Hselection := Hstaged.selection.map
    (fun arg => arg.abstractList G.alignment.rule.binders)
  rcases Hselection.exists_materialization Hstaged.args with
    ⟨fields, Hfields⟩
  let Hfield := Hfields.iotaFieldCertificate Hselection
    Hstaged.equation.field_args Hstaged.args
      G.alignment.rule.abstractedRecursiveArgsUnique
  have HrhsExists := G.alignment.rule.iotaRhsCertificateFor
    Hstaged.equation.domains_length Hstaged.equation.rhs_residual
    Hstaged.equation.field_args Hstaged.args Hstaged.fields_recursor_free
    Hstaged.recursive_results
  rcases HrhsExists with ⟨Hrhs⟩
  let Hordinary := VInductDecl.IotaRule.ofCertificates
    Hstaged.equation.shape Hfield Hrhs
  have hdomainsShape : G.translation.domains =
      Hstaged.equation.shape.domains := by
    have Hwrapped := G.translation.type_wrapped.symm.trans
      Hstaged.equation.shape.type_wrapped
    exact VExpr.wrapForalls_prefix_domains_eq
      (left := G.translation.domains)
      (right := Hstaged.equation.shape.domains)
      (suffix := []) (leftBody := G.translation.typeBody)
      (rightBody := Hstaged.equation.shape.typeBody)
      G.translation.domains_length Hstaged.equation.domains_length
      (by simpa using Hwrapped)
  have hlhsBodyShape : G.translation.lhsBody =
      Hstaged.equation.shape.lhsBody := by
    apply VExpr.wrapLams_left_cancel G.translation.domains
    have Hwrapped := G.translation.lhs_wrapped.symm.trans
      Hstaged.equation.shape.lhs_wrapped
    rw [← hdomainsShape] at Hwrapped
    exact Hwrapped
  have htypeBodyShape : G.translation.typeBody =
      Hstaged.equation.shape.typeBody := by
    apply VExpr.wrapForalls_left_cancel G.translation.domains
    have Hwrapped := G.translation.type_wrapped.symm.trans
      Hstaged.equation.shape.type_wrapped
    rw [← hdomainsShape] at Hwrapped
    exact Hwrapped
  exact ⟨{
    block := B.block
    blockRecursors := rfl
    semantics := Hordinary
    domains := hdomainsShape
    lhsBody := hlhsBodyShape
    typeBody := htypeBodyShape }⟩

/-- Reinterpret the exact ordinary generated equation at its original source
family.  Source/lowered index compatibility is recovered from the retained
metadata-prefix materialization; all remaining telescope and constructor
identities come from the exact lowering and declaration translations. -/
theorem RecursorPhasesResult.GeneratedEquationWitness.nestedSourceOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {nparams depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < result.types.toArray[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      owner howner i hctor rule)
    (O : G.OrdinarySource)
    (hfamily : owner < sourceTypes.length) :
    ∃ hsourceOwner : owner < sourceDecl.types.length,
      ∃ hsourceCtor : i <
          (sourceDecl.types[owner]'hsourceOwner).ctors.length,
        ∃ S : H.GeneratedNestedIotaSource G sourceDecl O.block
            (sourceDecl.types[owner]'hsourceOwner)
            ((sourceDecl.types[owner]'hsourceOwner).ctors[i]'hsourceCtor),
          S.source.recursor_shape.motives.length = loweredDecl.types.length ∧
          S.source.recursor_shape.minors.length =
            loweredDecl.ownedConstructors.length ∧
          S.source.recursor = getElem (H.entries.map Prod.snd) owner
            (by simpa using howner) := by
  have hsourceOwner : owner < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases Hlower.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have harray : result.types.toArray[owner]! = target := by
    simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
  have htargetCtor : i < target.ctors.length := by
    rw [← harray]
    exact hctor
  have hsourceConcreteCtor : i < sourceTypes[owner].ctors.length := by
    simpa [Hmapping.constructors.length] using htargetCtor
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource owner hfamily hsourceOwner
  have hsourceCtor : i <
      (sourceDecl.types[owner]'hsourceOwner).ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length HsourceType]
    exact hsourceConcreteCtor
  have hloweredOwner : owner < loweredDecl.types.length :=
    G.alignment.abstractOwner_lt
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlower.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hindices : (sourceDecl.types[owner]'hsourceOwner).numIndices =
      (loweredDecl.types[owner]'hloweredOwner).numIndices :=
    Hmetadata.numIndices hdeclLength owner hsourceOwner hloweredOwner
  have hrecursorIndex : owner < (H.entries.map Prod.snd).length := by
    simpa using howner
  rcases (H.generatedCertificate.recursorCertificate H.localWF H.bindings
      H.params H.noAlias H.cardinality R.core).shapes owner hloweredOwner
      hrecursorIndex with ⟨HordinaryShape⟩
  let HloweredShape := HordinaryShape.toNested
  rcases Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.toSourceOfLowering
      Hlower.toResult hempty Hsource R.core owner hfamily hsourceOwner
      hloweredOwner HloweredShape hindices with
    ⟨HsomeSourceShape⟩
  have hshapeIdx : HloweredShape.ownerIdx = owner := by
    exact Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
      HloweredShape owner hloweredOwner HloweredShape.name
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have hsourceMotives : sourceDecl.types.length ≤
      HloweredShape.motives.length :=
    Nat.le_trans hdeclLength HloweredShape.source_motives
  have hsourceMinors : sourceDecl.ownedConstructors.length ≤
      HloweredShape.minors.length := by
    calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        Hlower.toResult.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          R.core
      _ ≤ HloweredShape.minors.length := HloweredShape.source_minors
  let HsourceShape := HloweredShape.ofCompatible
    (by simpa [hshapeIdx] using hsourceOwner)
    (by simpa [hshapeIdx]) HsomeSourceShape.name HsomeSourceShape.uvars
    (Hsource.nparams.trans R.core.nparams.symm) hsourceMotives hsourceMinors
    hindices
  rcases Hmapping.constructors.mappingAt i hsourceConcreteCtor with
    ⟨sourceCtor, targetCtor, _before, _after, hsourceCtorEq,
      htargetCtorEq, HctorMapping⟩
  obtain ⟨_, hsourceCtorVal⟩ :=
    _root_.getElem?_eq_some_iff.mp hsourceCtorEq
  obtain ⟨_, htargetCtorVal⟩ :=
    _root_.getElem?_eq_some_iff.mp htargetCtorEq
  have HsourceCtor :=
    Lean4Lean.VerifyInductive.TrInductiveType.ctorAt HsourceType i
      hsourceConcreteCtor hsourceCtor
  have hloweredCtor : i <
      (loweredDecl.types[owner]'hloweredOwner).ctors.length :=
    G.alignment.abstractCtor_lt
  have hresultCtorOpt : result.types.toArray[owner]!.ctors[i]? =
      some targetCtor := by
    have hctors := congrArg InductiveType.ctors harray
    rw [hctors]
    exact htargetCtorEq
  obtain ⟨_, hresultCtorVal⟩ :=
    _root_.getElem?_eq_some_iff.mp hresultCtorOpt
  have hctorName :
      (sourceDecl.types[owner]'hsourceOwner).ctors[i].name =
        (loweredDecl.types[owner]'hloweredOwner).ctors[i].name := by
    calc
      _ = sourceTypes[owner].ctors[i].name := HsourceCtor.name
      _ = sourceCtor.name := by rw [hsourceCtorVal]
      _ = targetCtor.name := HctorMapping.name.symm
      _ = result.types.toArray[owner]!.ctors[i].name :=
        congrArg Constructor.name hresultCtorVal.symm
      _ = _ := by
        simpa [Array.getElem!_eq_getD, Array.getD,
          G.alignment.sourceOwner_lt, hresult] using
            G.alignment.ctorTranslation.name.symm
  have hrecursorMem : (H.entries.map Prod.snd)[owner] ∈ O.block.recursors := by
    rw [O.blockRecursors]
    exact List.getElem_mem hrecursorIndex
  have hrecursorName : (H.entries.map Prod.snd)[owner].name =
      O.semantics.recursor.name :=
    by simpa using
      HloweredShape.name.trans O.semantics.recursor_name.symm
  have hrecursorUvars : (H.entries.map Prod.snd)[owner].uvars =
      O.semantics.recursor.uvars := by
    simpa using G.uvars.symm.trans O.semantics.rule_uvars
  have hmotives : HsourceShape.motives.length =
      loweredDecl.types.length := by
    change HordinaryShape.motives.length = loweredDecl.types.length
    exact VExpr.takeForalls_domains_length HordinaryShape.motives_take
  have hminors : HsourceShape.minors.length =
      loweredDecl.ownedConstructors.length := by
    change HordinaryShape.minors.length = loweredDecl.ownedConstructors.length
    exact VExpr.takeForalls_domains_length HordinaryShape.minors_take
  let S := RecursorPhasesResult.GeneratedNestedIotaSource.ofOrdinaryCompatible
    G O.semantics (H.entries.map Prod.snd)[owner] HsourceShape hrecursorMem rfl
    hrecursorName hrecursorUvars (Hsource.uvars.trans R.core.uvars.symm)
    (Hsource.nparams.trans R.core.nparams.symm) hindices hmotives hminors
    hctorName O.domains O.lhsBody O.typeBody
    ((H.recursorUvarsAt owner howner).trans G.uvars.symm)
  exact ⟨hsourceOwner, hsourceCtor, S, hmotives, hminors, rfl⟩

/-- Replace the ordinary-production recursor retained by a recovered source
equation with the exact restored source recursor and simultaneously reindex
the equation over its final block presentation.  Equation bodies and all
constructor-field evidence are unchanged; the only telescope facts needed
are equality of the motive/minor cardinalities visible in the two independent
recursor-shape witnesses. -/
def RecursorPhasesResult.GeneratedNestedIotaSource.recursorCompatibleReblock
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {ownerIdx : Nat} {howner : ownerIdx < H.entries.length}
    {i : Nat} {hctor : i < indTypes[ownerIdx]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us ownerIdx howner i hctor generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock targetBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    (targetRecursor : VConstVal)
    (Hshape : sourceDecl.NestedRecursorShape sourceOwner targetRecursor)
    (hmem : targetRecursor ∈ targetBlock.recursors)
    (hnames : targetBlock.recursors.map (·.name) =
      sourceBlock.recursors.map (·.name))
    (hname : targetRecursor.name = S.source.recursor.name)
    (huvars : targetRecursor.uvars = S.source.recursor.uvars)
    (hmotives : Hshape.motives.length =
      S.source.recursor_shape.motives.length)
    (hminors : Hshape.minors.length =
      S.source.recursor_shape.minors.length) :
    H.GeneratedNestedIotaSource G sourceDecl targetBlock sourceOwner
      sourceCtor := by
  let Hsource : sourceDecl.NestedIotaRule targetBlock sourceOwner sourceCtor
      generatedRule := {
    S.source with
    recursor := targetRecursor
    recursor_mem := hmem
    recursor_shape := Hshape
    rule_uvars := S.source.rule_uvars.trans huvars.symm
    lhs_pattern := by simpa [hname] using S.source.lhs_pattern
    recursor_levels := S.source.recursor_levels.trans huvars.symm
    leading_arity := by simpa [hmotives, hminors] using S.source.leading_arity
    domains_arity := by simpa [hmotives, hminors] using S.source.domains_arity
    rhs_guarded := by rw [hnames]; exact S.source.rhs_guarded }
  exact {
    source := Hsource
    domains := S.domains
    lhsBody := S.lhsBody
    typeBody := S.typeBody
    uvars := S.uvars }

/-- Recover the exact source nested equation at one constructor of the
operational family join and install the restored source recursor as its head.
The generated equation, source owner/constructor, restored telescope shape,
and recursor metadata are all selected internally from the same production
and restoration step.  Final layout enters only through recursor membership
and equality of the block's ordered recursor-name list. -/
theorem RestoredPrimaryOperationalFamilySemantics.generatedNestedSourceAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor envCtors}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (hdecl : familyIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[familyIdx] = owner)
    (i : Nat) (hctor : i < owner.ctors.length) :
    ∃ hgenerated : i < result.types.toArray[familyIdx]!.ctors.length,
      ∃ generatedRule : VDefEq,
        ∃ G : Hprod.GeneratedEquationWitness
            (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
            familyIdx hentry i hgenerated generatedRule,
          ∃ sourceBlock,
            ∃ S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock
              owner (owner.ctors[i]'hctor),
              S.source.recursor = Hrecursor.recursor := by
  subst owner
  have htargetCtor : i < A.target.ctors.length := by
    rw [F.constructors.lengths.2]
    exact hctor
  obtain ⟨hresult, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp A.targetAt
  have harray : result.types.toArray[familyIdx]! = A.target := by
    simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
  have hgenerated : i < result.types.toArray[familyIdx]!.ctors.length := by
    rw [harray]
    exact htargetCtor
  rcases Hprod.generatedRuleAlignment familyIdx hentry i hgenerated with
    ⟨Hgenerated⟩
  rcases Hgenerated.finalCanonicalEquationWitness with
    ⟨generatedRule, ⟨G⟩⟩
  rcases G.ordinarySource with ⟨O⟩
  rcases G.nestedSourceOfLowering Hlowering Hsource Hmetadata hempty O
      hfamily with
    ⟨hsourceOwner, hsourceCtor, S, hsourceMotives, hsourceMinors,
      hsourceRecursor⟩
  have hsourceOwnerEq : hsourceOwner = hdecl := Subsingleton.elim _ _
  subst hsourceOwner
  have hsourceCtorEq : hsourceCtor = hctor := Subsingleton.elim _ _
  subst hsourceCtor
  rcases A.exactSourceRecursorShape Hsource Hmetadata hempty
      (sourceDecl.types[familyIdx]'hdecl) hdecl rfl Hrecursor with
    ⟨Hshape, htargetMotives, htargetMinors, _hindicesExact,
      _hparamsExact, _hmotivesInfo, _hminorsInfo⟩
  have hrecursorName : Hrecursor.recursor.name = S.source.recursor.name :=
    Hshape.name.trans S.source.recursor_shape.name.symm
  let E := Hprod.generated.entry familyIdx hentry
  have holdInfo := Hprod.restoredPrimaryInfo_eq_generated familyIdx hentry
    Hstep.restored.recursor A.oldRecName
  have hentryUvars : E.info.levelParams.length =
      Hprod.entries[familyIdx].2.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal, E] using
      E.translated.1.2.1
  have htargetUvars : Hrecursor.recursor.uvars =
      Hprod.entries[familyIdx].2.uvars := by
    calc
      Hrecursor.recursor.uvars = Hstep.restored.recursor.oldInfo.levelParams.length :=
        Hrecursor.uvars.symm
      _ = E.info.levelParams.length :=
        congrArg (fun info : RecursorVal => info.levelParams.length) holdInfo
      _ = Hprod.entries[familyIdx].2.uvars := hentryUvars
  have hrecursorUvars : Hrecursor.recursor.uvars =
      S.source.recursor.uvars := by
    rw [hsourceRecursor]
    simpa using htargetUvars
  have hblockIdx : familyIdx < O.block.recursors.length := by
    rw [O.blockRecursors]
    simpa using hentry
  let sourceBlock : VInductBlock := {
    O.block with
    recursors := O.block.recursors.set familyIdx Hrecursor.recursor }
  have hsourceMem : Hrecursor.recursor ∈ sourceBlock.recursors := by
    exact List.mem_set hblockIdx Hrecursor.recursor
  have holdAt : O.block.recursors[familyIdx] = S.source.recursor := by
    simpa only [O.blockRecursors, List.getElem_map] using hsourceRecursor.symm
  have hnames : sourceBlock.recursors.map (·.name) =
      O.block.recursors.map (·.name) := by
    change (O.block.recursors.set familyIdx Hrecursor.recursor).map
        (·.name) = O.block.recursors.map (·.name)
    rw [List.map_set]
    have hmapIdx : familyIdx <
        (O.block.recursors.map (fun recursor => recursor.name)).length := by
      simpa using hblockIdx
    have hnameAt : Hrecursor.recursor.name =
        (O.block.recursors.map (·.name))[familyIdx]'hmapIdx := by
      calc
        Hrecursor.recursor.name = S.source.recursor.name := hrecursorName
        _ = (O.block.recursors[familyIdx]'hblockIdx).name :=
          congrArg (fun recursor : VConstVal => recursor.name) holdAt.symm
        _ = (O.block.recursors.map (·.name))[familyIdx]'hmapIdx := by
          simp only [List.getElem_map]
    rw [hnameAt]
    exact List.set_getElem_eq_self _ _ hmapIdx
  let Sfinal := S.recursorCompatibleReblock Hrecursor.recursor Hshape
    hsourceMem hnames hrecursorName hrecursorUvars
      (htargetMotives.trans hsourceMotives.symm)
      (htargetMinors.trans hsourceMinors.symm)
  exact ⟨hgenerated, generatedRule, G, sourceBlock, Sfinal, rfl⟩

/-- Assemble one exact restored primary rule after the generated/source join.
The operational family alignment discharges both bookkeeping premises of
`ofGeneratedAtomicStructural`: the old recursor name and the concrete old
rule are forced by the same production entry consumed by restoration.  The
remaining arguments are precisely the semantic interpretation of the actual
RHS plan and restored dependent LHS spine. -/
noncomputable def
    RestoredPrimaryIotaRuleSemantics.ofOperationalGeneratedAtomicStructural
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {i : Nat} {hgenerated : i < result.types.toArray[familyIdx]!.ctors.length}
    {generatedRule : VDefEq}
    {G : Hprod.GeneratedEquationWitness
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
      familyIdx hentry i hgenerated generatedRule}
    {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal}
    (S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner ctor)
    (recursorMem : S.source.recursor ∈ restoredBlock.recursors)
    (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
    (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length)
    {sourceEnv targetEnv : VEnv}
    (Hrhs : RestoredRuleRhsTranslation result loweredEnv auxRec
      (Lean.mkRecName sourceTypes[familyIdx].name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.oldInfo.rules[i]
      Hstep.restored.recursor.restored.newInfo.rules[i]
      (Hstep.restored.recursor.restored.restoration.rules.entry i hold hnew)
      sourceEnv targetEnv
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams))
    (Halignment : GeneratedEquationRestorationAlignment G Hrhs)
    (sourceRecursors : List Name)
    (Hnodes : NestedRestorationNodeEvidence sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hrhs.plan.nodes)
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext :
      (abstractForallContext [] Hrhs.sourceScope).WF sourceEnv
        (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length)
    (htargetContext :
      (abstractForallContext [] Hrhs.targetScope).WF targetEnv
        (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length)
    (domains_eq : Hrhs.targetScope.toCtx.reverse = S.source.domains)
    (rhsArgs : List VExpr)
    (rhs_spine : Hrhs.targetBody.getAppFnArgs =
      (.bvar S.source.minorVar, rhsArgs))
    (field_args : rhsArgs.take
      (S.source.ctorArgs.length - sourceDecl.nparams) =
        S.source.ctorArgs.drop sourceDecl.nparams)
    (recursive_results :
      (rhsArgs.drop
        (S.source.ctorArgs.length - sourceDecl.nparams)).length =
          S.source.recursiveArgs.length)
    (HlhsAlignment : S.RestoredPrimaryLhsSpineAlignment targetEnv)
    (Htyping : TypedExprRestoration Hrhs.plan
      (Hnodes.atomicProvenance.semantics hsourceEnv htargetEnv hsourceContext
        htargetContext)
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody G.translation.typeBody
        S.source.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) S.source.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
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
    RestoredPrimaryIotaRuleSemantics sourceDecl restoredBlock owner ctor result
      loweredEnv P targetEnv auxRec
      (Lean.mkRecName sourceTypes[familyIdx].name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.oldInfo.rules[i]
      Hstep.restored.recursor.restored.newInfo.rules[i]
      (Hstep.restored.recursor.restored.restoration.rules.entry i hold hnew) := by
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
  have holdInfo := Hprod.restoredPrimaryInfo_eq_generated familyIdx hentry
    Hstep.restored.recursor A.oldRecName
  have hconcrete :
      getElem Hstep.restored.recursor.oldInfo.rules i hold =
        getElem (Hprod.generated.entry familyIdx hentry).info.rules i
          G.alignment.sourceRule_lt := by
    simpa only [holdInfo]
  exact RestoredPrimaryIotaRuleSemantics.ofGeneratedAtomicStructural
    (P := P) S Hrhs recursorMem A.oldRecName hconcrete Halignment
      sourceRecursors Hnodes hsourceEnv htargetEnv hsourceContext
      htargetContext domains_eq rhsArgs rhs_spine field_args
      recursive_results HlhsAlignment Htyping Hguard

/-- The irreducibly semantic payload for one exact restored primary rule.
Production identity, generated equation selection, source owner/constructor,
and old-rule identity are deliberately absent: the operational join derives
all of them.  Every field here instead interprets the actual RHS restoration
entry selected by `hold` and `hnew`, or reconstructs its dependent LHS in the
actual target environment. -/
structure RestoredPrimaryIotaStructuralRestorationEvidence
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {i : Nat} {hgenerated : i < result.types.toArray[familyIdx]!.ctors.length}
    {generatedRule : VDefEq}
    {G : Hprod.GeneratedEquationWitness
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
      familyIdx hentry i hgenerated generatedRule}
    {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal}
    (S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner ctor)
    (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
    (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length)
    (targetEnv : VEnv) where
  sourceEnv : VEnv
  rhs : RestoredRuleRhsTranslation result loweredEnv auxRec
    (Lean.mkRecName sourceTypes[familyIdx].name)
    Hstep.restored.recursor.restored.newRecName
    Hstep.restored.recursor.oldInfo.rules[i]
    Hstep.restored.recursor.restored.newInfo.rules[i]
    (Hstep.restored.recursor.restored.restoration.rules.entry i hold hnew)
    sourceEnv targetEnv
    (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
  alignment : GeneratedEquationRestorationAlignment G rhs
  sourceRecursors : List Name
  nodes : NestedRestorationNodeEvidence sourceRecursors
    (restoredBlock.recursors.map (·.name)) rhs.plan.nodes
  sourceEnvOrdered : sourceEnv.Ordered
  targetEnvOrdered : targetEnv.Ordered
  sourceContextWF :
    (abstractForallContext [] rhs.sourceScope).WF sourceEnv
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length
  targetContextWF :
    (abstractForallContext [] rhs.targetScope).WF targetEnv
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length
  domains : rhs.targetScope.toCtx.reverse = S.source.domains
  rhsArgs : List VExpr
  rhsSpine : rhs.targetBody.getAppFnArgs =
    (.bvar S.source.minorVar, rhsArgs)
  fieldArgs : rhsArgs.take
    (S.source.ctorArgs.length - sourceDecl.nparams) =
      S.source.ctorArgs.drop sourceDecl.nparams
  recursiveResults :
    (rhsArgs.drop
      (S.source.ctorArgs.length - sourceDecl.nparams)).length =
        S.source.recursiveArgs.length
  lhsAlignment : S.RestoredPrimaryLhsSpineAlignment targetEnv
  typing : TypedExprRestoration rhs.plan
    (nodes.atomicProvenance.semantics sourceEnvOrdered targetEnvOrdered
      sourceContextWF targetContextWF)
    (abstractForallContext [] rhs.sourceScope).toCtx
    (abstractForallContext [] rhs.targetScope).toCtx
    rhs.sourceBody rhs.targetBody G.translation.typeBody S.source.typeBody
  guarded : GuardedExprRestoration rhs.plan.Relates sourceRecursors
    (restoredBlock.recursors.map (·.name)) S.source.fieldVars 0
    rhs.sourceBody rhs.targetBody

/-- Consume the exact structural payload for one rule.  This is a thin
projection-only adapter; all production bookkeeping is still discharged by
`ofOperationalGeneratedAtomicStructural`. -/
noncomputable def RestoredPrimaryIotaStructuralRestorationEvidence.semantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {i : Nat} {hgenerated : i < result.types.toArray[familyIdx]!.ctors.length}
    {generatedRule : VDefEq}
    {G : Hprod.GeneratedEquationWitness
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
      familyIdx hentry i hgenerated generatedRule}
    {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal}
    {S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner ctor}
    {hold : i < Hstep.restored.recursor.oldInfo.rules.length}
    {hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length}
    {targetEnv : VEnv}
    (E : RestoredPrimaryIotaStructuralRestorationEvidence
      (Hlowering := Hlowering) (A := A) (restoredBlock := restoredBlock)
        S hold hnew targetEnv)
    (recursorMem : S.source.recursor ∈ restoredBlock.recursors) :
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
    RestoredPrimaryIotaRuleSemantics sourceDecl restoredBlock owner ctor result
      loweredEnv P targetEnv auxRec
      (Lean.mkRecName sourceTypes[familyIdx].name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.oldInfo.rules[i]
      Hstep.restored.recursor.restored.newInfo.rules[i]
      (Hstep.restored.recursor.restored.restoration.rules.entry i hold hnew) :=
  RestoredPrimaryIotaRuleSemantics.ofOperationalGeneratedAtomicStructural
    (Hlowering := Hlowering) (A := A) S recursorMem hold hnew E.rhs E.alignment
      E.sourceRecursors E.nodes
      E.sourceEnvOrdered E.targetEnvOrdered E.sourceContextWF
      E.targetContextWF E.domains E.rhsArgs E.rhsSpine
      E.fieldArgs E.recursiveResults E.lhsAlignment E.typing E.guarded

/-- Fold one exact primary recursor from the operational/source family join
and pointwise structural interpretations of its actual restoration entries.
Generated rules and source nested equations are selected internally at each
constructor index; the callback cannot substitute either one. -/
theorem
    RestoredPrimaryOperationalFamilySemantics.primaryIotaFamilyOfStructuralRestorations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor envCtors}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (hdecl : familyIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[familyIdx] = owner)
    (restoredBlock : VInductBlock) (targetVEnv : VEnv)
    (hrestoredRecursorMem : Hrecursor.recursor ∈ restoredBlock.recursors)
    (Hstructural : ∀ i (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length)
      (hgenerated : i < result.types.toArray[familyIdx]!.ctors.length)
      (generatedRule : VDefEq)
      (G : Hprod.GeneratedEquationWitness
        (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
        familyIdx hentry i hgenerated generatedRule)
      (sourceBlock : VInductBlock)
      (S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner
        (owner.ctors[i]'hctor)),
      Nonempty (RestoredPrimaryIotaStructuralRestorationEvidence
        (Hlowering := Hlowering) (A := A) (restoredBlock := restoredBlock)
          S hold hnew targetVEnv)) :
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
  apply F.primaryIotaFamily
  intro i hctor hold hnew
  rcases F.generatedNestedSourceAt Hsource Hmetadata hempty hdecl hownerEq
      i hctor with
    ⟨hgenerated, generatedRule, G, sourceBlock, S, hsourceRecursor⟩
  rcases Hstructural i hctor hold hnew hgenerated generatedRule G sourceBlock S with
    ⟨E⟩
  exact ⟨E.semantics (by
    rw [hsourceRecursor]
    exact hrestoredRecursorMem)⟩

/-- Construct one complete primary family directly from the successful
post-restoration rule validator.  The generated producer and lowering traces
are used only to identify the exact owner/constructor metadata; equation
shape, guardedness, and WF all come from the literal checked rule. -/
theorem RestoredPrimaryOperationalFamilySemantics.primaryIotaFamilyOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor envCtors}
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

/-- Construct the complete pointwise `primaryFamilies` callback for one exact
ordinary-production/restoration run.  Family and production indices,
operational recursor alignment, source-constructor semantics, generated
equations, rule-list cardinality, and the positional source-owner identity
are all derived.  The remaining callback is indexed only by the exact
per-rule restoration and its structural expression evidence. -/
theorem NestedLoweringResultClosed.primaryFamiliesOfStructuralRestorations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (restoredBlock : VInductBlock) (targetVEnv : VEnv)
    (Hstructural : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes[familyIdx]
          stepSource stepTarget)
      (A : RestoredPrimaryOperationalFamilyAlignment H Hprod familyIdx
        hfamily hentry Hstep)
      (owner : VInductiveType)
      (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
        Hstep.restored.recursor envCtors)
      (i : Nat) (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length)
      (hgenerated : i < result.types.toArray[familyIdx]!.ctors.length)
      (generatedRule : VDefEq)
      (G : Hprod.GeneratedEquationWitness
        (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
        familyIdx hentry i hgenerated generatedRule)
      (sourceBlock : VInductBlock)
      (S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner
        (owner.ctors[i]'hctor)),
      Nonempty (RestoredPrimaryIotaStructuralRestorationEvidence
        (Hlowering := H) (A := A) (restoredBlock := restoredBlock)
          S hold hnew targetVEnv)) :
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
      (Hconstructors : RestoredSourceConstructorTrace result loweredEnv c.lparams c.safety
        envTypes Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
        Hstep.restored.recursor envCtors),
      Hrecursor.recursor ∈ restoredBlock.recursors →
      Nonempty (RestoredPrimaryIotaFamilySemantics sourceDecl restoredBlock
        targetVEnv owner P Hstep) := by
  dsimp only
  intro indType stepSource stepTarget owner Hstep hsource Hheader
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
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
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
        TrSourceConst envCtors c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors owner.ctors :=
    Lean4Lean.List.Forall₂.imp
      (fun _source _constructor Htranslation =>
        Htranslation.mono (VEnv.addConstVals_le Hsource.ctorsAdded))
      Hconstructors.forall₂
  let F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor := {
    constructors := by
      apply A.constructors.sourceSemanticMapping HconstructorTranslations
        Hsyntax Hdisjoint rfl A.fvars A.params A.paramsNodup
          H.toResult.resultNParams }
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
  apply F.primaryIotaFamilyOfStructuralRestorations Hsource Hmetadata hempty
    hdecl hownerEq restoredBlock targetVEnv hrecursor
  intro i hctor hold hnew hgenerated generatedRule G sourceBlock S
  exact Hstructural familyIdx hfamily hentry stepSource stepTarget Hstep A
    owner Hrecursor i hctor hold hnew hgenerated generatedRule G sourceBlock S

/-- Whole-source-family form of `primaryIotaFamilyOfValidation`.  All family,
owner, constructor, and production indices are recovered from the lowering
and restoration traces; callers provide only the already executed validator
and the canonical block's recursor-name equality. -/
theorem NestedLoweringResultClosed.primaryFamiliesOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
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
        Hstep.restored.recursor envCtors),
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
        TrSourceConst envCtors c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors owner.ctors :=
    Lean4Lean.List.Forall₂.imp
      (fun _source _constructor Htranslation =>
        Htranslation.mono (VEnv.addConstVals_le Hsource.ctorsAdded))
      Hconstructors.forall₂
  let F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor := {
    constructors := by
      apply A.constructors.sourceSemanticMapping HconstructorTranslations
        Hsyntax Hdisjoint rfl A.fvars A.params A.paramsNodup
          H.toResult.resultNParams }
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

/-- Select the canonical generated equation directly from the exact installed
production package.  Once the operational join has supplied these two
indices, no equation-shaped or semantic callback remains. -/
theorem NestedInstalledProduction.generatedEquationAt
    (P : NestedInstalledProduction loweredEnv)
    (familyIdx : Nat) (hentry : familyIdx < P.production.entries.length)
    (i : Nat) (hctor : i < P.indTypes[familyIdx]!.ctors.length) :
    ∃ rule : VDefEq, Nonempty (P.production.GeneratedEquationWitness
      (AddInductive.getRecLevelParams P.production.elimLevel P.c.lparams)
      familyIdx hentry i hctor rule) := by
  rcases P.production.generatedRuleAlignment familyIdx hentry i hctor with
    ⟨G⟩
  exact G.finalCanonicalEquationWitness

/-- Build the finite node certificate by inspecting the exact provenance of
each plan entry.  Recursor-renaming nodes and non-recursor source-head shape
are forced by provenance; only the three semantic freeness facts for
family/constructor hits remain explicit. -/
theorem NestedRestorationNodeEvidence.ofNonrecursor
    {nodes : List (NestedRestoredNode result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext)}
    (HsourceHead : ∀ node ∈ nodes,
      node.provenance.IsNonrecursor → ∀ name levels,
      node.input.getAppFn = .const name levels → name ∉ sourceRecursors)
    (HsourceAvoids : ∀ node ∈ nodes, node.provenance.IsNonrecursor →
      node.output.AvoidsConsts restoredRecursors)
    (HcontextFree : ∀ node ∈ nodes, node.provenance.IsNonrecursor →
      VLCtx.NoIndConsts restoredRecursors targetContext) :
    NestedRestorationNodeEvidence sourceRecursors restoredRecursors nodes := by
  induction nodes with
  | nil => exact .nil
  | cons node nodes ih =>
    have HsourceHeadTail : ∀ candidate ∈ nodes,
        candidate.provenance.IsNonrecursor → ∀ name levels,
        candidate.input.getAppFn = .const name levels →
          name ∉ sourceRecursors := by
      intro candidate hcandidate
      exact HsourceHead candidate (by simp [hcandidate])
    have HsourceAvoidsTail : ∀ candidate ∈ nodes,
        candidate.provenance.IsNonrecursor →
        candidate.output.AvoidsConsts restoredRecursors := by
      intro candidate hcandidate
      exact HsourceAvoids candidate (by simp [hcandidate])
    have HcontextFreeTail : ∀ candidate ∈ nodes,
        candidate.provenance.IsNonrecursor →
        VLCtx.NoIndConsts restoredRecursors targetContext := by
      intro candidate hcandidate
      exact HcontextFree candidate (by simp [hcandidate])
    have Htail := ih HsourceHeadTail HsourceAvoidsTail HcontextFreeTail
    have Hclassification :
        (∃ oldName newName levels,
          node.provenance.IsRecursor ∧
          auxRec.find? oldName = some newName ∧
          node.input = .const oldName levels ∧
          node.output = .const newName levels) ∨
        node.provenance.IsNonrecursor := by
      rcases node with ⟨input, output, source, target, provenance,
        sourceTranslation, targetTranslation⟩
      cases provenance with
      | recursor hfind =>
        exact Or.inl ⟨_, _, _, .intro hfind, hfind, rfl, rfl⟩
      | family hfind hhead hhit =>
        exact Or.inr (.family hfind hhead hhit)
      | constructor hfind hhead hhit =>
        exact Or.inr (.constructor hfind hhead hhit)
    rcases Hclassification with
      ⟨oldName, newName, levels, Hrecursor, hfind, hinput, houtput⟩ |
        Hnonrecursor
    · exact .recursor Hrecursor hfind hinput houtput Htail
    · exact .nonrecursor {
        nonrecursor := Hnonrecursor
        sourceNotBVarHead := node.sourceNotBVarHeadOfNonrecursor Hnonrecursor
        sourceHeadNotRecursor := HsourceHead node (by simp) Hnonrecursor
        sourceAvoids := HsourceAvoids node (by simp) Hnonrecursor
        contextFree := HcontextFree node (by simp) Hnonrecursor
      } Htail

/-- Fresh insertion payloads from one source are permutations whenever their
targets have extensionally equal kernel lookup maps.  This is the endpoint
form needed when canonical dependency order and restoration order produce
distinct `Environment` values with the same constants. -/
theorem FreshConstantTrace.permOfTargetLookupEq
    (Hleft : FreshConstantTrace source leftEntries leftTarget)
    (Hright : FreshConstantTrace source rightEntries rightTarget)
    (hsourceWF : source.constants.WF)
    (htarget : ∀ name, leftTarget.find? name = rightTarget.find? name) :
    leftEntries ~ rightEntries := by
  have leftNodup : leftEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hleft.namesNodup hsourceWF)
  have rightNodup : rightEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hright.namesNodup hsourceWF)
  apply List.Subperm.antisymm
  · apply List.subperm_of_subset leftNodup
    intro ci hci
    have hfind : rightTarget.find? ci.name = some ci := by
      rw [← htarget]
      exact Hleft.findEntry hsourceWF hci
    rcases Hright.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hleft.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry
  · apply List.subperm_of_subset rightNodup
    intro ci hci
    have hfind : leftTarget.find? ci.name = some ci := by
      rw [htarget]
      exact Hright.findEntry hsourceWF hci
    rcases Hleft.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hright.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry

/-- Pure list/layout evidence for the already selected restoration trace. -/
structure NestedFinalAssemblyExactLayout
    (actualEntries : List ConstantInfo)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (primaryRecursors auxiliaryRecursors : List VConstVal) : Prop where
  productionOrder : actualEntries ~
    (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  recursorValues : recursorEntries.map Prod.snd =
    primaryRecursors ++ auxiliaryRecursors

/-- Derive the exact list permutation from the canonical staged installation
and extensional equality of its production endpoint with restoration's
endpoint.  Callers retain only the semantic recursor-value split. -/
theorem NestedFinalAssemblyExactLayout.ofCanonical
    {source actualTarget canonicalTarget : Environment}
    {sourceVEnv canonicalVEnv : VEnv}
    {actualEntries : List ConstantInfo}
    {typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal)}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    (Hactual : FreshConstantTrace source actualEntries actualTarget)
    (Hcanonical : StagedBlock safety source sourceVEnv typeEntries
      constructorEntries recursorEntries canonicalTarget canonicalVEnv)
    (hsourceWF : source.constants.WF)
    (htarget : ∀ name,
      actualTarget.find? name = canonicalTarget.find? name)
    (hrecursors : recursorEntries.map Prod.snd =
      primaryRecursors ++ auxiliaryRecursors) :
    NestedFinalAssemblyExactLayout actualEntries typeEntries
      constructorEntries recursorEntries primaryRecursors
        auxiliaryRecursors where
  productionOrder := Hactual.permOfTargetLookupEq
    Hcanonical.combined.freshTrace hsourceWF htarget
  recursorValues := hrecursors

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
  semantics : RestoredAuxiliarySemanticTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonicalVEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  wf : RestoredAuxiliaryFinalWFTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonicalVEnv canonicalVEnv
      finalBaseVEnv semantics [] [] auxiliaryRecursors auxiliaryRules

/-- Construct final auxiliary evidence by folding pointwise witnesses over the
literal restoration suffix.  The only non-semantic residue is identification
of the fold's forced output lists with the lists retained by canonical
assembly; no caller supplies an independently assembled semantic/WF trace. -/
theorem NestedFinalAuxiliaryEvidence.ofStepEvidence
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
    (canonicalVEnv finalBaseVEnv : VEnv)
    (Hsteps : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      (priorRecursors : List VConstVal),
      Nonempty (RestoredAuxiliaryStepFinalEvidence decl
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules)
        main safety canonicalVEnv canonicalVEnv finalBaseVEnv Hstep
          priorRecursors))
    (Houtputs : ∀ finalRecursors finalRules,
      RestoredAuxiliarySemanticTrace decl
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules)
        main safety canonicalVEnv H.auxiliaries [] [] finalRecursors finalRules →
      finalRecursors = auxiliaryRecursors ∧ finalRules = auxiliaryRules) :
    NestedFinalAuxiliaryEvidence H sourceEnv decl safety main
      primaryRecursors auxiliaryRecursors primaryRules auxiliaryRules
        canonicalVEnv finalBaseVEnv := by
  rcases H.auxiliaries.auxiliaryFinalEvidenceEmpty Hsteps with
    ⟨finalRecursors, finalRules, Hsemantics, Hwf⟩
  rcases Houtputs finalRecursors finalRules Hsemantics with ⟨rfl, rfl⟩
  exact ⟨Hsemantics, Hwf⟩

/-- Fold-independent canonical data.  These choices are fixed before either
the source-family or primary-rule folds run; in particular, the auxiliary
suffix and canonical environments cannot depend on the rules later returned
by primary restoration. -/
structure NestedFinalCanonicalEvidence
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety) where
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  canonicalProdEnv : Environment
  finalBaseVEnv : VEnv
  canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
    constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
  typeValues : typeEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  formationAssembly : NestedFormationAssembly sourceEnv decl
  formationExpanded : formationAssembly.expanded = P.loweredDecl
  materialized : MaterializedInductivePrefix decl P.loweredDecl
  uvars : decl.uvars = lparams.length
  numParams : decl.nparams = nparams
  unsafeEq : decl.isUnsafe = isUnsafe
  auxiliaryRecursors : List VConstVal
  auxiliaryRules : List VDefEq

/-- Construct all declaration metadata and nested-formation fields from the
exact ordinary production's constructor phases.  The only formation premise
left is the lowering-specific ordered expansion relation itself; ordinary
source/formation WF and all source declaration metadata are derived. -/
def NestedFinalCanonicalEvidence.ofProduction
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv)
    (htypeValues : typeEntries.map Prod.snd = decl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      decl.constructorConstants)
    (auxiliaryRecursors : List VConstVal) (auxiliaryRules : List VDefEq)
    (generated : List VInductiveType)
    (hnonempty : P.indTypes.toList ≠ [])
    (hinitialEnv : P.initialEnv = sourceEnv)
    (hlparams : P.c.lparams = lparams)
    (hnparams : P.nparams = nparams)
    (hisUnsafe : P.isUnsafe = isUnsafe)
    (huvarsExpansion : P.loweredDecl.uvars = decl.uvars)
    (hnparamsExpansion : P.loweredDecl.nparams = decl.nparams)
    (hunsafeExpansion : P.loweredDecl.isUnsafe = decl.isUnsafe)
    (Hmaterialized : MaterializedInductivePrefix decl P.loweredDecl)
    (HsourceParameters : decl.SourceParameterWF sourceEnv)
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceEnv decl
        (VInductDecl.NestedAuxiliarySourceAbsolute sourceEnv decl generated))
      (decl.types ++ generated) P.loweredDecl.types) :
    NestedFinalCanonicalEvidence P H sourceEnv decl lparams nparams isUnsafe
      safety where
  typeEntries := typeEntries
  constructorEntries := constructorEntries
  recursorEntries := recursorEntries
  canonicalProdEnv := canonicalProdEnv
  finalBaseVEnv := finalBaseVEnv
  canonical := canonical
  typeValues := htypeValues
  constructorValues := hconstructorValues
  formationAssembly := by
    refine {
      expanded := P.loweredDecl
      generated := generated
      expandedSource := ?_
      expandedFormation := ?_
      sourceParameters := HsourceParameters
      uvars := huvarsExpansion
      nparams := hnparamsExpansion
      isUnsafe := hunsafeExpansion
      types := Htypes }
    · simpa only [hinitialEnv] using
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF_ofNonempty
          P.constructors.core
          (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty
            P.constructors.core hnonempty))
    · simpa only [hinitialEnv] using P.constructors.formation.formationWF
  formationExpanded := rfl
  materialized := Hmaterialized
  uvars := by
    calc
      decl.uvars = P.loweredDecl.uvars := huvarsExpansion.symm
      _ = P.c.lparams.length := P.constructors.core.uvars
      _ = lparams.length := congrArg List.length hlparams
  numParams := by
    calc
      decl.nparams = P.loweredDecl.nparams := hnparamsExpansion.symm
      _ = P.nparams := P.constructors.core.nparams
      _ = nparams := hnparams
  unsafeEq := by
    calc
      decl.isUnsafe = P.loweredDecl.isUnsafe := hunsafeExpansion.symm
      _ = P.isUnsafe := P.constructors.core.isUnsafe
      _ = isUnsafe := hisUnsafe
  auxiliaryRecursors := auxiliaryRecursors
  auxiliaryRules := auxiliaryRules

/-- Native formation specialization of `ofProduction`.  The generated
source-family list and the ordered expansion relation are reconstructed from
the exact lowering queue, validated auxiliary translations, and ordinary
header production.  In particular, neither datum is supplied by a final
assembly provider. -/
theorem NestedFinalCanonicalEvidence.ofProductionNativeFormation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv sourceEnvCtors targetTypesVEnv
      targetCtorsVEnv : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {ves : VEnvs}
    (Hrun : NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations sourceTypesVEnv
      c.lparams result selection)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl sourceTypesVEnv sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv c.lparams nparams result.types
      isUnsafe loweredDecl targetTypesVEnv targetCtorsVEnv)
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (lparams : List Name) (declUnsafe : Bool)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : StagedBlock safety sourceProdEnv sourceVEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv)
    (htypeValues : typeEntries.map Prod.snd = sourceDecl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      sourceDecl.constructorConstants)
    (auxiliaryRecursors : List VConstVal) (auxiliaryRules : List VDefEq)
    (hnonempty : P.indTypes.toList ≠ [])
    (hinitialEnv : P.initialEnv = sourceVEnv)
    (hlparams : P.c.lparams = lparams)
    (hnparams : P.nparams = nparams)
    (hisUnsafe : P.isUnsafe = declUnsafe)
    (huvarsExpansion : P.loweredDecl.uvars = sourceDecl.uvars)
    (hnparamsExpansion : P.loweredDecl.nparams = sourceDecl.nparams)
    (hunsafeExpansion : P.loweredDecl.isUnsafe = sourceDecl.isUnsafe)
    (Hmaterialized : MaterializedInductivePrefix sourceDecl P.loweredDecl)
    (HsourceParameters : sourceDecl.SourceParameterWF sourceVEnv)
    (hloweredDecl : P.loweredDecl = loweredDecl) :
    Nonempty (NestedFinalCanonicalEvidence P H sourceVEnv sourceDecl lparams
      nparams declUnsafe safety) := by
  rcases Hrun.nativeGeneratedFamilySources Hcache Hparams wf hsourceVEnv Hc
      Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF hempty
      selection Htranslations Htarget with ⟨N⟩
  have Htypes := Hrun.allExpansionsOfNativeSources Hcache Hparams Hsource
    Htarget (by simpa only [hloweredDecl] using Hmaterialized) Hsources
      (VEnvs.WF.environmentTypesClosed wf) wf.inductivesClosed
      (by simpa only [hsourceVEnv] using wf.tr.wf) hempty N selection
  refine ⟨NestedFinalCanonicalEvidence.ofProduction P H sourceVEnv sourceDecl
    lparams nparams declUnsafe safety typeEntries constructorEntries
    recursorEntries canonicalProdEnv finalBaseVEnv canonical htypeValues
    hconstructorValues auxiliaryRecursors auxiliaryRules N.generated
    hnonempty hinitialEnv hlparams hnparams hisUnsafe ?_ ?_ ?_ Hmaterialized
    HsourceParameters ?_⟩
  · simpa only [hloweredDecl] using huvarsExpansion
  · simpa only [hloweredDecl] using hnparamsExpansion
  · simpa only [hloweredDecl] using hunsafeExpansion
  · simpa only [hloweredDecl] using Htypes

/-- Reconstruct an indexed source-facing family realization for every member
of the actual lowered mutual block.  Original positions retain their exact
source index telescope.  Generated positions use the validated auxiliary
application at the recursor universe; native formation proves that their
index count is zero, so the empty telescope is constructed internally. -/
theorem NestedLoweringResultClosed.familyRestoredIndexedRealizationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv envCtors targetTypesVEnv targetCtorsVEnv : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {ves : VEnvs}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hrun : NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (wf : ves.WF c.env) (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl sourceTypesVEnv envCtors)
    (Htarget : TrInductDeclCore sourceVEnv c.lparams nparams result.types
      isUnsafe loweredDecl targetTypesVEnv targetCtorsVEnv)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (N : NestedGeneratedFamilyNativeSources Hrun sourceVEnv sourceTypesVEnv
      c.lparams loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
      result selection)
    (familyIdx : Nat) (hrecInfo : familyIdx < Hprod.recInfos.size) :
    let Us := AddInductive.getRecLevelParams Hprod.elimLevel c.lparams
    let parameterDomains :=
      (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse
    ∃ sourceFamily sourceIndexType, Nonempty
      (RestoredIndexedFamilyRealization envCtors Us parameterDomains
        Hprod.recInfos[familyIdx]!.indices.size sourceFamily sourceIndexType) := by
  dsimp only
  by_cases hfamily : familyIdx < sourceTypes.length
  · let sourceFamily := Expr.mkAppList
      (.const sourceTypes[familyIdx].name stats.levels)
      (sourceCanonicalVars
        (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse.length)
    refine ⟨sourceFamily, ?_⟩
    rcases H.originalFamilyRestoredRealizationAtFresh Hprod Hsource Hmetadata
        hempty familyIdx hfamily with ⟨sourceIndexType, ⟨F⟩⟩
    exact ⟨sourceIndexType, ⟨by simpa only [sourceFamily] using F⟩⟩
  · have hresult : familyIdx < result.types.length := by
      rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core,
        ← Hprod.cardinality.records]
      exact hrecInfo
    have hsuffix : sourceTypes.length ≤ familyIdx := Nat.le_of_not_gt hfamily
    rcases Hrun.finalGeneratedFamilyOriginAt
        (VEnvs.WF.environmentTypesClosed wf) wf.inductivesClosed Hsources
        (by simp) hsuffix hresult with ⟨Horigin⟩
    rcases Horigin.abstractContainerApplicationAtRecursor Hrun Hcache Hparams
        Hprod Hsource hempty selection Htranslations with
      ⟨realization, abstractLevels, baseArgs, Hlevels, hbaseLength, Hbase,
        HbaseClosed, hfamilyApp⟩
    let i := familyIdx - sourceTypes.length
    have hposition : sourceTypes.length + i = familyIdx := by
      simp [i, hsuffix]
    have hi : i < N.generated.length := by
      have hlength := N.length
      omega
    have htarget : sourceTypes.length + i < loweredDecl.types.length := by
      rw [hposition, ← Hprod.cardinality.records]
      exact hrecInfo
    have htargetZero := N.targetNumIndices_eq_zero
      (Hheaders := Hheaders) (R := R) HsourceTypesWF
      (VEnv.addConstVals_le HsourceAdded) Htarget i hi
      (by simpa only [hposition] using hresult) htarget
    have htargetZero' : loweredDecl.types[familyIdx].numIndices = 0 := by
      simpa only [hposition] using htargetZero
    have hindices : Hprod.recInfos[familyIdx]!.indices.size = 0 := by
      exact (Hprod.cardinality.indices familyIdx hrecInfo).trans htargetZero'
    let sourceFamily :=
      (mkAppRange (.const Horigin.generated.sourceName
      Horigin.generated.levels) 0 Horigin.generated.nestedNParams
        Horigin.generated.args).abstractList
          Horigin.generated.selection.fvars
    refine ⟨sourceFamily, sourceFamily, ?_⟩
    rw [hindices]
    exact ⟨by
      apply RestoredFamilyRealization.toIndexedZero
      simpa only [sourceFamily] using realization⟩

/-- Every row of the completed recursor array comes from the family at the
same position in the exact lowering result, and that family retains its
complete source-to-lowered expression mapping.  This is deliberately stated
uniformly over original and dynamically generated families: the latter are
not recovered through a caller-selected auxiliary source, but through the
queue origin stored by the lowering run itself. -/
theorem NestedLoweringResultClosed.familyLoweredMappingAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Henv : EnvironmentTypesClosed c.env)
    (hclosures : MutualInductivesClosed c.env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hrecInfo : familyIdx < Hprod.recInfos.size) :
    ∃ finalState,
      NestedLoweringRun c.env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ∃ origin : FinalLoweredFamilyOrigin c.env result.params nparams
          sourceTypes.toArray finalState result.types[familyIdx]!,
        Nonempty (LoweredInductiveMapping c.env result.params nparams result
          origin.source origin.stepState
            (result.types[familyIdx]!, origin.loweredState)) := by
  have hfamily : familyIdx < result.types.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core,
      ← Hprod.cardinality.records]
    exact hrecInfo
  rcases H.finalFamilyOriginAt Henv hclosures Hsources rfl hfamily with
    ⟨finalState, Hrun, ⟨O⟩⟩
  let O' : FinalLoweredFamilyOrigin c.env result.params nparams
      sourceTypes.toArray finalState result.types[familyIdx]! := by
    simpa [getElem!_pos result.types familyIdx hfamily] using O
  refine ⟨finalState, Hrun, O', ⟨?_⟩⟩
  exact O'.finalMapping (Hrun.resultAuxMapModelsOfEmpty hempty)

/-- Source-family provenance itself discharges constructor closure.  Initial
families use the checked source-syntax trace; dynamically appended families
use the closing context retained by their exact auxiliary builder. -/
theorem SourceFamilyOrigin.constructorsClosedOfSyntax
    (O : SourceFamilyOrigin env params initial nestedAux source)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks initial.toList) :
    InductiveConstructorsClosed source := by
  cases O with
  | original j hj =>
      exact Hsources.constructorsClosed
        (by simpa using Array.getElem_mem hj)
  | generated Hgenerated =>
      exact Hgenerated.constructorsClosed Henv

/-- A flattened generated-minor declaration selects the constructor mapping
at exactly its retained owner/local position.  In particular, auxiliary
family minors are connected to the dynamically generated pre-lowering
constructor through `FinalLoweredFamilyOrigin`, rather than through a second
source registry or a declaration-boundary callback. -/
theorem NestedLoweringResultClosed.flatMinorConstructorMappingAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Henv : EnvironmentTypesClosed c.env)
    (hclosures : MutualInductivesClosed c.env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    {minorIdx : Nat}
    (D : BoundFVarDeclarationAt Hprod.localContext
      (Hprod.recInfos.flatMap (fun info => info.minors)) minorIdx)
    (O : Hprod.origins.FlatMinorOrigin D) :
    ∃ finalState,
      NestedLoweringRun c.env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ∃ familyOrigin : FinalLoweredFamilyOrigin c.env result.params nparams
          sourceTypes.toArray finalState result.types[O.owner]!,
        ∃ sourceCtor before after,
          sourceCtor ∈ familyOrigin.source.ctors ∧
          Nonempty (LoweredConstructorMapping c.env result.params nparams
            result sourceCtor before (O.shape.constructor, after)) := by
  have hownerResult : O.owner < result.types.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core,
      ← Hprod.cardinality.records]
    exact O.owner_lt
  have hownerArray : O.owner < result.types.toArray.size := by
    simpa using hownerResult
  have P := Hprod.minorSemanticSourceOfFlatOrigin D O hownerArray
  have htargetCtor : O.localIndex < result.types[O.owner]!.ctors.length := by
    have hcount := Hprod.minorCounts O.owner O.owner_lt
    have hlocal : O.localIndex <
        Hprod.recInfos[O.owner]!.minors.size := by
      simpa [getElem!_pos Hprod.recInfos O.owner O.owner_lt] using O.local_lt
    rw [hcount] at hlocal
    simpa [getElem!_pos result.types O.owner hownerResult] using hlocal
  rcases H.familyLoweredMappingAtFresh Hprod Henv hclosures Hsources hempty
      O.owner O.owner_lt with
    ⟨finalState, Hrun, familyOrigin, ⟨F⟩⟩
  have hsourceCtor : O.localIndex < familyOrigin.source.ctors.length := by
    rw [← F.constructors.length]
    simpa [getElem!_pos result.types O.owner hownerResult] using htargetCtor
  rcases F.constructors.mappingAt O.localIndex hsourceCtor with
    ⟨sourceCtor, targetCtor, before, after, hsource, htarget, M⟩
  have hsourceEq : familyOrigin.source.ctors[O.localIndex] = sourceCtor :=
    Option.some.inj
      ((List.getElem?_eq_getElem hsourceCtor).symm.trans hsource)
  have hsourceMem : sourceCtor ∈ familyOrigin.source.ctors := by
    rw [← hsourceEq]
    exact List.getElem_mem hsourceCtor
  have htargetShape : targetCtor = O.shape.constructor := by
    have htarget' : result.types.toArray[O.owner]!.ctors[O.localIndex]? =
        some targetCtor := by
      simpa [getElem!_pos result.types O.owner hownerResult] using htarget
    exact Option.some.inj (htarget'.symm.trans P.constructorAt)
  subst targetCtor
  exact ⟨finalState, Hrun, familyOrigin, sourceCtor, before, after,
    hsourceMem, ⟨M⟩⟩

/-- The exact constructor selected by a flattened minor can be reopened at
any restoration parameter array.  The alpha data and source closure are both
producer facts: the former is retained by the closed lowering result, while
the latter follows by cases on the retained original/generated family
origin. -/
theorem NestedLoweringResultClosed.flatMinorConstructorReopeningAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Henv : EnvironmentTypesClosed c.env)
    (hclosures : MutualInductivesClosed c.env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (restoreAs : Array Expr)
    {minorIdx : Nat}
    (D : BoundFVarDeclarationAt Hprod.localContext
      (Hprod.recInfos.flatMap (fun info => info.minors)) minorIdx)
    (O : Hprod.origins.FlatMinorOrigin D) :
    ∃ finalState,
      NestedLoweringRun c.env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ∃ familyOrigin : FinalLoweredFamilyOrigin c.env result.params nparams
          sourceTypes.toArray finalState result.types[O.owner]!,
        ∃ sourceCtor before after,
          sourceCtor ∈ familyOrigin.source.ctors ∧
          Nonempty (LoweredConstructorReopening c.env result.params nparams
            result restoreAs sourceCtor before
              (O.shape.constructor, after)) := by
  rcases H.flatMinorConstructorMappingAtFresh Hprod Henv hclosures Hsources
      hempty D O with
    ⟨finalState, Hrun, familyOrigin, sourceCtor, before, after,
      hsourceCtor, ⟨M⟩⟩
  rcases H.resultParamsNodup with ⟨paramFvars, hparams, hnodup⟩
  have Hclosed : sourceCtor.type.FVarsIn fun _ => False :=
    familyOrigin.sourceOrigin.constructorsClosedOfSyntax Henv
      (by simpa using Hsources) sourceCtor hsourceCtor
  exact ⟨finalState, Hrun, familyOrigin, sourceCtor, before, after,
    hsourceCtor, ⟨M.reopens rfl paramFvars hparams hnodup Hclosed⟩⟩

/-- Every flattened minor row has a constructor source which was translated
before lowering.  Original rows use the checked source declaration at the
same family/constructor position.  Generated rows use the native source
retained by the exact generated-family registry.  In both cases the very
same concrete source constructor is connected, by the final lowering map, to
the constructor selected by the recursor producer.

This is the constructor-level join needed by restored-minor replay: it does
not identify an arbitrary post-hoc source with a lowering origin, and it does
not require generated auxiliary constructors to occur in the final source
declaration. -/
theorem NestedLoweringResultClosed.flatMinorSourceConstructorTranslationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv sourceEnvCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hrun : NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl sourceTypesVEnv sourceEnvCtors)
    (N : NestedGeneratedFamilyNativeSources Hrun sourceVEnv sourceTypesVEnv
      c.lparams loweredDecl)
    (Henv : EnvironmentTypesClosed c.env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    {minorIdx : Nat}
    (D : BoundFVarDeclarationAt Hprod.localContext
      (Hprod.recInfos.flatMap (fun info => info.minors)) minorIdx)
    (O : Hprod.origins.FlatMinorOrigin D) :
    ∃ sourceCtor sourceTarget before after,
      TrSourceConstRaw sourceTypesVEnv c.lparams sourceCtor.name
          sourceCtor.type sourceTarget ∧
        sourceCtor.type.FVarsIn (fun _ => False) ∧
        Nonempty (LoweredConstructorMapping c.env result.params nparams
          result sourceCtor before (O.shape.constructor, after)) := by
  have hownerResult : O.owner < result.types.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core,
      ← Hprod.cardinality.records]
    exact O.owner_lt
  have hownerArray : O.owner < result.types.toArray.size := by
    simpa using hownerResult
  have P := Hprod.minorSemanticSourceOfFlatOrigin D O hownerArray
  have htargetCtor : O.localIndex < result.types[O.owner]!.ctors.length := by
    have hcount := Hprod.minorCounts O.owner O.owner_lt
    have hlocal : O.localIndex <
        Hprod.recInfos[O.owner]!.minors.size := by
      simpa [getElem!_pos Hprod.recInfos O.owner O.owner_lt] using O.local_lt
    rw [hcount] at hlocal
    simpa [getElem!_pos result.types O.owner hownerResult] using hlocal
  by_cases horiginal : O.owner < sourceTypes.length
  · have hsourceDecl : O.owner < sourceDecl.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
      exact horiginal
    have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
      Hsource O.owner horiginal hsourceDecl
    rcases H.sourceFinalMappingAtFreshAligned hempty horiginal with
      ⟨_params, stepState, target, loweredState, _hparams, _hnodup,
        _hsize, F, htarget⟩
    obtain ⟨_hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
    have htargetBang : result.types[O.owner]! = target := by
      simp [getElem!_pos result.types O.owner hownerResult, htargetEq]
    have htargetCtor' : O.localIndex < target.ctors.length := by
      simpa [htargetBang] using htargetCtor
    have hsourceCtor : O.localIndex < sourceTypes[O.owner].ctors.length := by
      rw [← F.constructors.length]
      exact htargetCtor'
    have habstractCtor : O.localIndex <
        (sourceDecl.types[O.owner]'hsourceDecl).ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length HsourceType]
      exact hsourceCtor
    rcases F.constructors.mappingAt O.localIndex hsourceCtor with
      ⟨sourceCtor, targetCtor, before, after, hsourceAt, htargetAt, M⟩
    have htargetShape : targetCtor = O.shape.constructor := by
      have htargetAt' : result.types.toArray[O.owner]!.ctors[O.localIndex]? =
          some targetCtor := by
        simpa [Array.getElem!_eq_getD, Array.getD, hownerResult,
          htargetEq] using htargetAt
      exact Option.some.inj (htargetAt'.symm.trans P.constructorAt)
    have hsourceValue : sourceTypes[O.owner].ctors[O.localIndex] =
        sourceCtor := by
      exact Option.some.inj
        ((List.getElem?_eq_getElem hsourceCtor).symm.trans hsourceAt)
    have Htranslated :=
      (Lean4Lean.VerifyInductive.TrInductiveType.ctorAt HsourceType
        O.localIndex hsourceCtor habstractCtor).raw
    rw [hsourceValue] at Htranslated
    have Hclosed : sourceCtor.type.FVarsIn fun _ => False := by
      apply (Hsources.constructorsClosed
        (List.getElem_mem horiginal) sourceCtor)
      rw [← hsourceValue]
      exact List.getElem_mem hsourceCtor
    subst targetCtor
    exact ⟨sourceCtor,
      (sourceDecl.types[O.owner]'hsourceDecl).ctors[O.localIndex], before,
      after, Htranslated, Hclosed, ⟨M⟩⟩
  · have hsuffix : sourceTypes.length ≤ O.owner :=
      Nat.le_of_not_gt horiginal
    let generatedIdx := O.owner - sourceTypes.length
    have hposition : sourceTypes.length + generatedIdx = O.owner := by
      simp [generatedIdx, hsuffix]
    have hgenerated : generatedIdx < N.generated.length := by
      have hlength := N.length
      omega
    have htargetOwner : O.owner < loweredDecl.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
      exact hownerResult
    rcases N.sourceAt generatedIdx hgenerated
        (by simpa only [hposition] using hownerResult)
        (by simpa only [hposition] using htargetOwner) with
      ⟨Horigin, Nsource, _hsource⟩
    have F := Horigin.finalMapping
      (Hrun.resultAuxMapModelsOfEmpty hempty)
    have hsourceCtor : O.localIndex < Horigin.source.ctors.length := by
      rw [← F.constructors.length]
      simpa [getElem!_pos result.types O.owner hownerResult,
        hposition] using htargetCtor
    have habstractCtor : O.localIndex < Nsource.payload.source.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length
        Nsource.payload.translation]
      exact hsourceCtor
    rcases F.constructors.mappingAt O.localIndex hsourceCtor with
      ⟨sourceCtor, targetCtor, before, after, hsourceAt, htargetAt, M⟩
    have htargetShape : targetCtor = O.shape.constructor := by
      have htargetAt' : result.types.toArray[O.owner]!.ctors[O.localIndex]? =
          some targetCtor := by
        simpa [Array.getElem!_eq_getD, Array.getD, hownerResult,
          hposition] using htargetAt
      exact Option.some.inj (htargetAt'.symm.trans P.constructorAt)
    have hsourceValue : Horigin.source.ctors[O.localIndex] = sourceCtor := by
      exact Option.some.inj
        ((List.getElem?_eq_getElem hsourceCtor).symm.trans hsourceAt)
    have Htranslated :=
      Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
        Nsource.payload.translation O.localIndex hsourceCtor habstractCtor
    rw [hsourceValue] at Htranslated
    have Hclosed : sourceCtor.type.FVarsIn fun _ => False := by
      apply Horigin.generated.constructorsClosed Henv sourceCtor
      rw [← hsourceValue]
      exact List.getElem_mem hsourceCtor
    subst targetCtor
    exact ⟨sourceCtor, Nsource.payload.source.ctors[O.localIndex], before,
      after, Htranslated, Hclosed, ⟨M⟩⟩

/-- The source translation and lowering reopening for a flattened minor refer
to one and the same constructor.  This is the exact join required by minor
replay: neither side may choose a merely extensionally related source row. -/
theorem NestedLoweringResultClosed.flatMinorSourceConstructorReopeningAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv sourceEnvCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hrun : NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl sourceTypesVEnv sourceEnvCtors)
    (N : NestedGeneratedFamilyNativeSources Hrun sourceVEnv sourceTypesVEnv
      c.lparams loweredDecl)
    (Henv : EnvironmentTypesClosed c.env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (restoreAs : Array Expr)
    {minorIdx : Nat}
    (D : BoundFVarDeclarationAt Hprod.localContext
      (Hprod.recInfos.flatMap (fun info => info.minors)) minorIdx)
    (O : Hprod.origins.FlatMinorOrigin D) :
    ∃ sourceCtor sourceTarget before after,
      TrSourceConstRaw sourceTypesVEnv c.lparams sourceCtor.name
          sourceCtor.type sourceTarget ∧
        Nonempty (LoweredConstructorReopening c.env result.params nparams
          result restoreAs sourceCtor before (O.shape.constructor, after)) := by
  rcases H.flatMinorSourceConstructorTranslationAtFresh Hrun Hprod Hsource N
      Henv Hsources hempty D O with
    ⟨sourceCtor, sourceTarget, before, after, Htranslated, Hclosed, ⟨M⟩⟩
  rcases H.resultParamsNodup with ⟨paramFvars, hparams, hnodup⟩
  exact ⟨sourceCtor, sourceTarget, before, after, Htranslated,
    ⟨M.reopens rfl paramFvars hparams hnodup Hclosed⟩⟩

/-- Pointwise source-family producer extracted from the closed lowering run,
ordinary recursor production, and the exact restoration step.  Header and
constructor translations, family/entry indices, and restored recursor
refinement are all derived; the remaining family premise is one joint source
recursor realization for that exact step. -/
theorem NestedLoweringResultClosed.sourceFamiliesAtFreshOfRealizations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (Hrealizations : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
        recursor)) :
    ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams
        c.safety sourceVEnv envTypes envCtors Hstep) := by
  intro indType stepSource stepTarget Hstep hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases Hrealizations familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨recursor, ⟨Hrealization⟩⟩
  have Hrefinement := Hrealization.refinement
  rw [← Hrealization.recursor_eq] at Hrefinement
  exact H.sourceInductiveSemanticsAtFresh Hc Hprod Hsources hempty familyIdx
    hfamily hdecl hentry
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hdecl) Hfamilies Hconstructors Hstep Hrealization.source
        Hrefinement

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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
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
    {Hprod : RecursorPhasesResult R loweredEnv}
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

/-- Select target-side translated typing for the literal restored primary
rule at one operational family/index position.  The rule is read from the
actual `RestoredInductiveStep`; its semantic typing comes from the retained
post-installation executable validation run. -/
theorem RestoredPrimaryOperationalFamilyAlignment.ruleTypingOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed c.env loweringFuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget}
    (A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep)
    (Hvalid : CheckingEnv.Valid c.safety restoredEnv targetVEnv)
    (Hrun : Lean4Lean.validateRestoredRecursorRules.run restoredEnv loweredEnv
      validationLparams c.safety validationFuel result auxRec allIndNames
      sourceTypes auxRecNames = .ok ())
    (i : Nat) (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length) :
    ∃ inferred target targetType,
      TrTyping targetVEnv
        Hstep.restored.recursor.restored.newInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.rules[i].rhs inferred
          target targetType := by
  have hmember : Hstep.restored.recursor.restored.newInfo.rules[i] ∈
      Hstep.restored.recursor.restored.newInfo.rules :=
    List.getElem_mem hnew
  have htype : sourceTypes[familyIdx] ∈ sourceTypes :=
    List.getElem_mem hfamily
  have Htyping := validateRestoredRecursorRules.primaryTranslation_of_run
    Hvalid Hrun htype Hstep.restored.recursor.lookup
      (rule := Hstep.restored.recursor.restored.newInfo.rules[i]) (by
        simpa only [← Hstep.restored.recursor.restored.produced] using
          hmember)
  simpa only [← Hstep.restored.recursor.restored.produced] using Htyping

/-- Auxiliary analogue of `ruleTypingOfValidation`, indexed by the exact
restoration step and literal restored-rule position. -/
theorem RestoredAuxiliaryGeneratedStepAlignment.ruleTypingOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : RestoredAuxiliaryGeneratedStepAlignment Hprod Hstep)
    (Hvalid : CheckingEnv.Valid c.safety restoredEnv targetVEnv)
    (Hrun : Lean4Lean.validateRestoredRecursorRules.run restoredEnv loweredEnv
      validationLparams c.safety validationFuel result auxRec allIndNames
      validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames)
    (i : Nat) (hnew : i < Hstep.restored.newInfo.rules.length) :
    ∃ inferred target targetType,
      TrTyping targetVEnv Hstep.restored.newInfo.levelParams []
        Hstep.restored.newInfo.rules[i].rhs inferred target targetType := by
  have hmember : Hstep.restored.newInfo.rules[i] ∈
      Hstep.restored.newInfo.rules := List.getElem_mem hnew
  have Htyping := validateRestoredRecursorRules.auxiliaryTranslation_of_run
    Hvalid Hrun hrec Hstep.lookup
      (rule := Hstep.restored.newInfo.rules[i]) (by
        simpa only [← Hstep.restored.produced] using hmember)
  simpa only [← Hstep.restored.produced] using Htyping

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
    {Hprod : RecursorPhasesResult R loweredEnv}
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

/-- Assemble all semantic and final-WF data for one actual auxiliary
restoration step from the two retained post-installation validation runs.
The only reindexing fact is equality between the canonical block's recursor
names and the executable validator's concrete primary-plus-auxiliary list. -/
theorem RestoredAuxiliaryGeneratedStepAlignment.finalEvidenceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv ruleEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : RestoredAuxiliaryGeneratedStepAlignment Hprod Hstep)
    (HtypeValid : CheckingEnv.Valid c.safety validationEnv recursorEnv)
    (HtypeRun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationLparams c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
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
    Nonempty (RestoredAuxiliaryStepFinalEvidence decl block main c.safety
      recursorEnv recursorEnv ruleVEnv Hstep priorRecursors) := by
  rcases A.recursorStepOfValidation HtypeValid HtypeRun hrec with
    ⟨Hrecursor⟩
  rcases A.rulesOfValidation HruleValid HruleRun hrec with
    ⟨rules, Hlength, HrulesWF, HrulesGuarded⟩
  let Hsemantics : RestoredAuxiliaryStepSemantics decl block main c.safety
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
  exact ⟨{
    semantics := Hsemantics
    recursorWF := Hrecursor.wf
    rulesWF := HrulesWF }⟩

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
    {Hprod : RecursorPhasesResult R loweredEnv}
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
  let Hsemantics : RestoredAuxiliaryStepSemantics decl block main c.safety
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
def RestoredAuxiliaryStepSemantics.rebaseBlock
    (H : RestoredAuxiliaryStepSemantics decl block main safety trEnv Hstep
      priorRecursors)
    (Hnames : ∀ name,
      name ∈ block.recursors.map (·.name) ↔
        name ∈ block'.recursors.map (·.name)) :
    RestoredAuxiliaryStepSemantics decl block' main safety trEnv Hstep
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
    {Hsemantic : RestoredAuxiliarySemanticTrace decl block main safety trEnv
      Htrace priorRecursors priorRules finalRecursors finalRules}
    (H : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv
      recursorEnv ruleEnv Hsemantic priorRecursors priorRules finalRecursors
        finalRules)
    (Hnames : ∀ name,
      name ∈ block.recursors.map (·.name) ↔
        name ∈ block'.recursors.map (·.name)) :
    Nonempty { Hsemantic' : RestoredAuxiliarySemanticTrace decl block' main
        safety trEnv Htrace priorRecursors priorRules finalRecursors finalRules //
      RestoredAuxiliaryFinalWFTrace decl block' main safety trEnv recursorEnv
        ruleEnv Hsemantic' priorRecursors priorRules finalRecursors
          finalRules } :=
  match H with
  | .nil sourceEnv recursors rules =>
      ⟨⟨RestoredAuxiliarySemanticTrace.nil sourceEnv recursors rules,
        .nil sourceEnv recursors rules⟩⟩
  | .cons Hstep Htail Hhead Hrest Hrecursor Hrules Hfinal => by
      let Hhead' := Hhead.rebaseBlock Hnames
      rcases Hfinal.rebaseBlock Hnames with ⟨⟨Hrest', Hfinal'⟩⟩
      let Hsemantic' : RestoredAuxiliarySemanticTrace decl block' main safety
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
    {Hprod : RecursorPhasesResult R loweredEnv}
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
    {Hprod : RecursorPhasesResult R loweredEnv}
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
      ∃ Hsemantic : RestoredAuxiliarySemanticTrace decl block main
          c.safety recursorEnv Htrace priorRecursors priorRules
            finalRecursors finalRules,
        RestoredAuxiliaryFinalWFTrace decl block main c.safety recursorEnv
          recursorEnv ruleVEnv Hsemantic priorRecursors priorRules
            finalRecursors finalRules :=
  match Hrecursors with
  | .nil sourceEnv recursors => by
      let Hsemantic : RestoredAuxiliarySemanticTrace decl block main
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
          rcases Hrest'.finalEvidenceOfRuleValidation Arest HruleValid
              HruleRun (fun name hname => Hmembers name (by simp [hname]))
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
    {Hprod : RecursorPhasesResult R loweredEnv}
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
  rcases Hrecursors.finalEvidenceOfRuleValidation Halignment HruleValid
      HruleRun (fun _ h => h) Hnames decl main [] with
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
    (Hlower : NestedLoweringResultClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hcore : TrInductDeclCore sourceVEnv c.lparams nparams (main :: rest)
      isUnsafe decl envTypes envCtors)
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
      ((main :: rest).map (·.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1
      ((), outProdEnv))
    (Hsource : RestoredSourceInductiveSemanticTrace decl c.lparams c.safety
      sourceVEnv envTypes envCtors Hrestored.inductives decl.types
        primaryRecursors)
    (HvalidationValid : CheckingEnv.Valid c.safety validationEnv envCtors)
    (HrecursorValidation :
      Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
        validationLparams c.safety validationFuel result
        (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
        ((main :: rest).map (·.name)) (main :: rest)
        (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1 = .ok ())
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hprimitive : PrimitiveSafeFreshConstantTrace false c.env
      primitiveEntries outProdEnv) :
    ∃ auxiliaryRecursors,
      RestoredAuxiliaryRecursorTrace c.safety envCtors envCtors
          Hrestored.auxiliaries [] auxiliaryRecursors ∧
        ∃ replay : CanonicalRestorationReplay c.safety c.env outProdEnv
          sourceVEnv envTypes envCtors decl.types primaryRecursors
            auxiliaryRecursors,
        ∃ canonicalProdEnv finalVEnv,
          Nonempty (StagedBlock c.safety c.env sourceVEnv replay.typeEntries
            replay.constructorEntries replay.recursorEntries canonicalProdEnv
              finalVEnv) ∧
          ∀ name, outProdEnv.constants.find? name =
            canonicalProdEnv.constants.find? name := by
  have Halignment := Hrestored.generatedAlignmentTraceOfProduction Hlower Hc
    Hprod hempty
  rcases Halignment.recursorTraceOfValidation HvalidationValid
      HrecursorValidation (fun _ h => h) [] with
    ⟨auxiliaryRecursors, Hauxiliary⟩
  rcases Hrestored.freshTraceNondelta Hc.checking.tr.map_wf with
    ⟨nondeltaEntries, Hnondelta, hnondelta⟩
  rcases Hsource.existsExactStagedRestoration Hauxiliary Hlower Hc Hprod
      Hcore hempty hvisible Hprimitive Hnondelta hnondelta with
    ⟨replay, canonicalProdEnv, finalVEnv, Hstaged, hlookup⟩
  exact ⟨auxiliaryRecursors, Hauxiliary, replay, canonicalProdEnv, finalVEnv,
    Hstaged, hlookup⟩

/-- Telescope-translation specialization of the pointwise source producer.
The source recursor, its shape, metadata refinement, and installation typing
are reconstructed from the exact production/restoration join. -/
theorem NestedLoweringResultClosed.sourceFamiliesAtFreshOfTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtelescopeTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
        Hstep.restored.recursor.oldInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.type
        (result.nparams + (Hprod.recInfos.map (·.motive)).size +
          (Hprod.recInfos.flatMap (·.minors)).size +
          Hprod.recInfos[familyIdx]!.indices.size + 1)
        targetType) :
    ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams
        c.safety sourceVEnv envTypes envCtors Hstep) := by
  apply H.sourceFamiliesAtFreshOfRealizations Hc Hprod Hsources Hsource
    Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  rcases HtelescopeTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htype⟩
  exact H.sourcePrimaryRecursorRealizationAtFreshOfTelescope Hprod Hsource
    Hmetadata hempty familyIdx hfamily hdecl hentry Hstep targetType Htype

/-- Installed-suffix specialization of the pointwise source producer.  It
derives generated-family namespace reservation, auxiliary-constructor
freshness, and the complete restored primary telescope.  The remaining input
is the source-facing semantic invariant for the exact generated recursor
suffix. -/
theorem NestedLoweringResultClosed.sourceFamiliesOfInstalledSuffixes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (Hsuffixes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget)
      (A : GeneratedRecursorRestorationTelescopeAlignment result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        Hstep.restored.recursor.restored.newInfo
        (Hprod.generated.entry familyIdx hentry)),
      GeneratedRecursorRestoredSuffixTranslationsInvariant A Hprod.origins
        envCtors []
        ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse)) :
    ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams
        c.safety sourceVEnv envTypes envCtors Hstep) := by
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors :
      RestoreAuxConstructorsFresh result loweredEnv envTypes :=
    H.restoreAuxConstructorsFreshAtTypes Hc Hprod Hsource Howners hempty
  apply H.sourceFamiliesAtFreshOfTelescopeTranslations Hc Hprod Hsources
    Hsource Hmetadata Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  exact H.restoredPrimaryTelescopeAtFreshOfSuffix Hprod Hsource familyIdx
    hfamily hentry Hstep hempty fun A =>
      Hsuffixes familyIdx hfamily hdecl hentry stepSource stepTarget Hstep A

/-- Specification-facing evidence for one exact production/restoration run.
The executable part of the adapter supplies the fresh trace and map WF; this
record supplies only its canonical interpretation and semantic payloads. -/
structure NestedFinalAssemblySemanticEvidence
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (actualEntries : List ConstantInfo) where
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  canonicalProdEnv : Environment
  finalBaseVEnv : VEnv
  canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
    constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
  typeValues : typeEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  formationAssembly : NestedFormationAssembly sourceEnv decl
  formationExpanded : formationAssembly.expanded = P.loweredDecl
  materialized : MaterializedInductivePrefix decl P.loweredDecl
  uvars : decl.uvars = lparams.length
  numParams : decl.nparams = nparams
  unsafeEq : decl.isUnsafe = isUnsafe
  auxiliaryRecursors : List VConstVal
  auxiliaryRules : List VDefEq
  exactSource : ∃ primaryRecursors,
    RestoredSourceInductiveSemanticTrace decl lparams safety sourceEnv
      canonical.venvTypes canonical.venvCtors H.inductives decl.types
        primaryRecursors
  primaryFamilies : ∀ primaryRecursors
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      decl.types primaryRecursors),
    ∀ indType stepSource stepTarget owner
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType stepSource stepTarget)
    (hsource : indType ∈ sourceTypes)
    (Hheader : TrSourceConst sourceEnv lparams indType.name indType.type
      owner.toVConstVal)
    (Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety
      canonical.venvTypes Hstep.oldInfo.ctors Hstep.restored.headerEnv
        Hstep.restored.constructorEnv indType.ctors owner.ctors)
    (Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
      Hstep.restored.recursor canonical.venvCtors),
    Hrecursor.recursor ∈ primaryRecursors →
    Nonempty (RestoredPrimaryIotaFamilySemantics decl
      (canonicalRestoredShapeBlock decl primaryRecursors
        auxiliaryRecursors) finalBaseVEnv owner P Hstep)
  finish : ∀ main rest primaryRecursors
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      (main :: rest) primaryRecursors)
    primaryRules
    (Hprimary : RestoredPrimaryIotaSemanticTrace decl
      (canonicalRestoredShapeBlock decl primaryRecursors
        auxiliaryRecursors) finalBaseVEnv P Hsource (main :: rest)
          primaryRules),
    NestedFinalAssemblyExactLayout actualEntries typeEntries
        constructorEntries recursorEntries primaryRecursors
          auxiliaryRecursors ∧
      NestedFinalAuxiliaryEvidence H sourceEnv decl safety main
        primaryRecursors auxiliaryRecursors primaryRules auxiliaryRules
          canonical.venvCtors finalBaseVEnv

/-- Build the exact semantic aggregate from fold-independent canonical data,
pointwise source/primary producers, an exact pre-rule layout callback, and
only the genuinely post-primary auxiliary semantics.  This is the preferred
field-by-field constructor for the native producer proof. -/
theorem NestedFinalAssemblySemanticEvidence.ofCanonical
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (actualEntries : List ConstantInfo)
    (C : NestedFinalCanonicalEvidence P H sourceEnv decl lparams nparams
      isUnsafe safety)
    (HexactSource : ∃ primaryRecursors,
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceEnv
        C.canonical.venvTypes C.canonical.venvCtors H.inductives decl.types
          primaryRecursors)
    (HprimaryFamilies : ∀ primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors H.inductives
        decl.types primaryRecursors),
      ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget)
      (hsource : indType ∈ sourceTypes)
      (Hheader : TrSourceConst sourceEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety
        C.canonical.venvTypes Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor C.canonical.venvCtors),
      Hrecursor.recursor ∈ primaryRecursors →
      Nonempty (RestoredPrimaryIotaFamilySemantics decl
        (canonicalRestoredShapeBlock decl primaryRecursors
          C.auxiliaryRecursors) C.finalBaseVEnv owner P Hstep))
    (Hlayout : ∀ owners primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors H.inductives
        owners primaryRecursors),
      NestedFinalAssemblyExactLayout actualEntries C.typeEntries
        C.constructorEntries C.recursorEntries primaryRecursors
          C.auxiliaryRecursors)
    (Hauxiliary : ∀ main rest primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors H.inductives
        (main :: rest) primaryRecursors)
      primaryRules
      (Hprimary : RestoredPrimaryIotaSemanticTrace decl
        (canonicalRestoredShapeBlock decl primaryRecursors
          C.auxiliaryRecursors) C.finalBaseVEnv P Hsource (main :: rest)
            primaryRules),
      NestedFinalAuxiliaryEvidence H sourceEnv decl safety main
        primaryRecursors C.auxiliaryRecursors primaryRules C.auxiliaryRules
          C.canonical.venvCtors C.finalBaseVEnv) :
    Nonempty (NestedFinalAssemblySemanticEvidence P H sourceEnv decl lparams
      nparams isUnsafe safety actualEntries) := by
  exact ⟨{
    typeEntries := C.typeEntries
    constructorEntries := C.constructorEntries
    recursorEntries := C.recursorEntries
    canonicalProdEnv := C.canonicalProdEnv
    finalBaseVEnv := C.finalBaseVEnv
    canonical := C.canonical
    typeValues := C.typeValues
    constructorValues := C.constructorValues
    formationAssembly := C.formationAssembly
    formationExpanded := C.formationExpanded
    materialized := C.materialized
    uvars := C.uvars
    numParams := C.numParams
    unsafeEq := C.unsafeEq
    auxiliaryRecursors := C.auxiliaryRecursors
    auxiliaryRules := C.auxiliaryRules
    exactSource := HexactSource
    primaryFamilies := HprimaryFamilies
    finish := by
      intro main rest primaryRecursors Hsource primaryRules Hprimary
      exact ⟨Hlayout (main :: rest) primaryRecursors Hsource,
        Hauxiliary main rest primaryRecursors Hsource primaryRules Hprimary⟩ }⟩

/-- Exact-production specialization of `ofCanonical` which constructs the
whole primary-family callback from pointwise structural restoration evidence.
The source core, family owner positions, generated equations, and the final
recursor reblocking are all recovered from the retained canonical and
restoration traces. -/
theorem NestedFinalAssemblySemanticEvidence.ofCanonicalStructuralPrimary
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
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
    (actualEntries : List ConstantInfo)
    (C : NestedFinalCanonicalEvidence P Hrestored sourceVEnv sourceDecl
      c.lparams nparams isUnsafe c.safety)
    (HsourceCore : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl C.canonical.venvTypes C.canonical.venvCtors)
    (validationEnv : Environment)
    (HvalidationValid : CheckingEnv.Valid c.safety validationEnv
      C.canonical.venvCtors)
    (HrecursorValidation :
      Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
        c.lparams c.safety validationFuel result
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ())
    (Hactual : FreshConstantTrace c.env actualEntries outEnv)
    (htarget : ∀ name,
      outEnv.find? name = C.canonicalProdEnv.find? name)
    (HrecursorValues : ∀ owners primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace sourceDecl c.lparams
        c.safety sourceVEnv C.canonical.venvTypes C.canonical.venvCtors
        Hrestored.inductives owners primaryRecursors),
      C.recursorEntries.map Prod.snd =
        primaryRecursors ++ C.auxiliaryRecursors)
    (Hauxiliary : ∀ main rest primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace sourceDecl c.lparams
        c.safety sourceVEnv C.canonical.venvTypes C.canonical.venvCtors
        Hrestored.inductives (main :: rest) primaryRecursors)
      primaryRules
      (Hprimary : RestoredPrimaryIotaSemanticTrace sourceDecl
        (canonicalRestoredShapeBlock sourceDecl primaryRecursors
          C.auxiliaryRecursors) C.finalBaseVEnv P Hsource (main :: rest)
            primaryRules),
      NestedFinalAuxiliaryEvidence Hrestored sourceVEnv sourceDecl c.safety
        main primaryRecursors C.auxiliaryRecursors primaryRules
          C.auxiliaryRules C.canonical.venvCtors C.finalBaseVEnv)
    (Hstructural : ∀ (primaryRecursors : List VConstVal) familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          stepSource stepTarget)
      (A : RestoredPrimaryOperationalFamilyAlignment Hlower Hprod familyIdx
        hfamily hentry Hstep)
      (owner : VInductiveType)
      (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
        Hstep.restored.recursor C.canonical.venvCtors)
      (i : Nat) (hctor : i < owner.ctors.length)
      (hold : i < Hstep.restored.recursor.oldInfo.rules.length)
      (hnew : i < Hstep.restored.recursor.restored.newInfo.rules.length)
      (hgenerated : i < result.types.toArray[familyIdx]!.ctors.length)
      (generatedRule : VDefEq)
      (G : Hprod.GeneratedEquationWitness
        (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
        familyIdx hentry i hgenerated generatedRule)
      (sourceBlock : VInductBlock)
      (S : Hprod.GeneratedNestedIotaSource G sourceDecl sourceBlock owner
        (owner.ctors[i]'hctor)),
      Nonempty (RestoredPrimaryIotaStructuralRestorationEvidence
        (Hlowering := Hlower) (A := A)
        (restoredBlock := canonicalRestoredShapeBlock sourceDecl
          primaryRecursors C.auxiliaryRecursors)
        S hold hnew C.finalBaseVEnv)) :
    Nonempty (NestedFinalAssemblySemanticEvidence P Hrestored sourceVEnv
      sourceDecl c.lparams nparams isUnsafe c.safety actualEntries) := by
  subst P
  have htypesAdded : sourceVEnv.addConstVals sourceDecl.typeConstants =
      some C.canonical.venvTypes := by
    rw [← C.typeValues]
    exact C.canonical.typesAdded.abstract
  have hconstructorsAdded :
      C.canonical.venvTypes.addConstVals sourceDecl.constructorConstants =
        some C.canonical.venvCtors := by
    rw [← C.constructorValues]
    exact C.canonical.ctorsAdded.abstract
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases Hlower with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors :
      RestoreAuxConstructorsFresh result loweredEnv C.canonical.venvTypes :=
    Hlower.restoreAuxConstructorsFreshAtTypes Hc Hprod HsourceCore Howners
      hempty
  have HexactSource :=
    Hlower.sourceSemanticTraceAtFreshOfTelescopeTranslations Hc Hprod Hsources
      HsourceCore Hmetadata Hfamilies Hconstructors hempty Hrestored (by
        intro familyIdx hfamily _hdecl hentry stepSource stepTarget Hstep
        exact Hlower.restoredPrimaryTelescopeAtFreshOfValidation Hc Hprod
          HvalidationValid HrecursorValidation hempty familyIdx hfamily
            hentry stepSource stepTarget Hstep)
  apply NestedFinalAssemblySemanticEvidence.ofCanonical _ Hrestored
    sourceVEnv sourceDecl c.lparams nparams isUnsafe c.safety actualEntries C
      HexactSource
  · intro primaryRecursors Hsource
    let Hcore := Hsource.core rfl C.uvars C.numParams C.unsafeEq
      htypesAdded hconstructorsAdded
    have Hall := Hlower.primaryFamiliesOfStructuralRestorations Hc Hprod Hsources
      Hcore Hmetadata Howners hempty
        (canonicalRestoredShapeBlock sourceDecl primaryRecursors
          C.auxiliaryRecursors) C.finalBaseVEnv
      (Hstructural := Hstructural primaryRecursors)
    intro indType stepSource stepTarget owner Hstep hsource Hheader
      Hconstructors Hrecursor hrecursor
    apply Hall indType stepSource stepTarget owner Hstep hsource Hheader
      Hconstructors Hrecursor
    simp only [canonicalRestoredShapeBlock, canonicalRestoredBlock]
    exact List.mem_append_left C.auxiliaryRecursors hrecursor
  · intro owners primaryRecursors Hsource
    exact NestedFinalAssemblyExactLayout.ofCanonical Hactual C.canonical
      Hc.checking.tr.map_wf htarget
        (HrecursorValues owners primaryRecursors Hsource)
  · exact Hauxiliary

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
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
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
      c.safety sourceVEnv envTypes envCtors Hrestored.inductives
        sourceDecl.types primaryRecursors)
    (HauxiliaryRecursors : RestoredAuxiliaryRecursorTrace c.safety envCtors
      envCtors Hrestored.auxiliaries [] auxiliaryRecursors)
    (replay : CanonicalRestorationReplay c.safety c.env outEnv sourceVEnv
      envTypes envCtors sourceDecl.types primaryRecursors
        auxiliaryRecursors)
    (canonical : StagedBlock c.safety c.env sourceVEnv replay.typeEntries
      replay.constructorEntries replay.recursorEntries canonicalProdEnv
        finalBaseVEnv)
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
    (hsourceNonempty : sourceTypes ≠ []) :
    Nonempty { C : NestedFinalAssemblyCertificate Hrestored sourceVEnv
        sourceDecl c.lparams nparams isUnsafe c.safety // C.production = P } := by
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
    have hadded := canonical.typesAdded.abstract
    rw [replay.typeValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.typesAdded)
  have hcanonicalCtors : canonical.venvCtors = envCtors := by
    have hadded := canonical.ctorsAdded.abstract
    rw [hcanonicalTypes, replay.constructorValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.ctorsAdded)
  have Hfamilies := Hlower.primaryFamiliesOfValidation Hc Hprod Hsources
    Hcore Hmetadata Howners hempty
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
          c.lparams c.safety sourceVEnv envTypes envCtors
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
      have HauxiliarySemantics : RestoredAuxiliarySemanticTrace sourceDecl
          (canonicalRestoredBlock sourceDecl primaryRecursors
            auxiliaryRecursors primaryRules auxiliaryRules)
          main c.safety canonical.venvCtors Hrestored.auxiliaries [] []
            auxiliaryRecursors auxiliaryRules := by
        simpa only [hcanonicalCtors] using Hauxiliary.semantics
      have HauxiliaryWF : RestoredAuxiliaryFinalWFTrace sourceDecl
          (canonicalRestoredBlock sourceDecl primaryRecursors
            auxiliaryRecursors primaryRules auxiliaryRules)
          main c.safety canonical.venvCtors canonical.venvCtors
            finalBaseVEnv HauxiliarySemantics [] [] auxiliaryRecursors
              auxiliaryRules := by
        simpa only [hcanonicalCtors] using Hauxiliary.wf
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
          canonical.venvCtors Hrestored.inductives (main :: rest)
            primaryRecursors := by
        simpa only [hcanonicalTypes, hcanonicalCtors] using Hsource'
      have HprimaryCanonical : RestoredPrimaryIotaSemanticTrace sourceDecl
          (canonicalRestoredShapeBlock sourceDecl primaryRecursors
            auxiliaryRecursors) finalBaseVEnv P' HsourceCanonical
              (main :: rest) primaryRules := by
        simpa only [P', hcanonicalTypes, hcanonicalCtors] using Hprimary'
      exact ⟨⟨Remainder.certificate HsourceCanonical HprimaryCanonical
        replay.typeValues replay.constructorValues Hformation
        hformationExpanded Hmetadata huvars hnumParams hunsafeEq htypesSource
        hsourceNonempty, rfl⟩⟩

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
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration sourceVEnv
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
  have Hprod : RecursorPhasesResult R E.loweredEnv := by
    have hconstructors : E.production.constructors = R :=
      Subsingleton.elim _ _
    exact Eq.mp
      (congrArg (fun constructors =>
        RecursorPhasesResult constructors E.loweredEnv) hconstructors)
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
    canonical.combined.validOfFreshPermutation replay.fresh
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
          RecursorPhasesResult R outEnv
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
      sourceDecl lparams nparams isUnsafe safety outEnv) :
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
    HtypeShapesBase, ?_⟩
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
      E.nativeSource.headerValidationValid hresultLCtxWF hresultFresh .nil rfl
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
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hformation : NestedFormationAssembly sourceVEnv sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration sourceVEnv
        sourceDecl lparams nparams isUnsafe safety //
      C.production = E.production } := by
  let P := E.production
  have hc : P.c = E.productionContext := E.production_c
  have henv : P.c.env = sourceProdEnv :=
    (congrArg AddInductive.Context.env hc).trans E.productionContext_env
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams hc).trans
      E.productionContext_lparams
  have hsafety : P.c.safety = safety :=
    (congrArg AddInductive.Context.safety hc).trans
      E.productionContext_safety
  have hnparams : P.nparams = nparams := E.production_nparams
  have hinitial : P.initialEnv = sourceVEnv := E.production_initialEnv
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
        RecursorPhasesResult R E.loweredEnv
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
  have HtypeValid : CheckingEnv.Valid P.c.safety E.validationEnv
      E.nativeSource.envCtors := by
    simpa only [hsafety] using E.nativeSource.validationValid
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
      Hrestored Hsource HtypeValid HtypeRun hempty hvisibleP Hprimitive with
    ⟨auxiliaryRecursors, HauxiliaryRecursors, replay, canonicalProdEnv,
      finalBaseVEnv, ⟨canonical⟩, _hlookup⟩
  have HbaseValid : CheckingEnv.Valid P.c.safety P.c.env P.initialEnv := by
    have Hchecking := E.productionContextWF.checking
    simpa only [hc, hinitial, E.productionContext_venv] using Hchecking
  have HruleValid : CheckingEnv.Valid P.c.safety outEnv finalBaseVEnv :=
    canonical.combined.validOfFreshPermutation replay.fresh
      replay.productionOrder HbaseValid
  have HruleRun : Lean4Lean.validateRestoredRecursorRules.run outEnv
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
      hunsafeEq (by simp) with ⟨⟨C, hproduction⟩⟩
  have hproductionOriginal : C.production = P := by
    calc
      C.production = P' := hproduction
      _ = P := by
        simpa only [P', Hheaders, R, Hprod, Hpack] using
          NestedInstalledProduction.rebuildIndTypes_eq P
            result.types.toArray hindTypes
  let CertificateAt := fun q : Sigma RestorationAt =>
    Nonempty { C : NestedFinalAssemblyCertificate q.2 P.initialEnv sourceDecl
        P.c.lparams P.nparams P.isUnsafe P.c.safety // C.production = P }
  have hp : (⟨P.c.env, Hrestored⟩ : Sigma RestorationAt) =
      ⟨sourceProdEnv, E.restoration⟩ := by
    apply Sigma.ext henv
    change (Eq.mpr (congrArg RestorationAt henv) E.restoration) ≍
      E.restoration
    rw [eq_mpr_eq_cast]
    exact cast_heq _ _
  have Hcertificate : CertificateAt ⟨P.c.env, Hrestored⟩ :=
    ⟨⟨C, hproductionOriginal⟩⟩
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
No declaration-specific evidence is accepted from the caller. -/
theorem NestedValidatedRunResult.assemblyNative
    {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } := by
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
        RecursorPhasesResult R E.loweredEnv
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
  have wfP : ves.WF P.c.env := by
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
      (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed
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
  have Hparameters : sourceDecl.SourceParameterWF P.initialEnv := by
    simpa only [hinitial, safety] using E.nativeSourceParameterWF
  have huvars : P.loweredDecl.uvars = sourceDecl.uvars := by
    calc
      P.loweredDecl.uvars = P.c.lparams.length := R.core.uvars
      _ = sourceDecl.uvars := Hsource.uvars.symm
  have hdeclParams : P.loweredDecl.nparams = sourceDecl.nparams := by
    calc
      P.loweredDecl.nparams = P.nparams := R.core.nparams
      _ = sourceDecl.nparams := Hsource.nparams.symm
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
  exact E.assemblyOfFormationNative Hsources wf.constructorOwners
    (by cases isUnsafe <;> decide) Hformation (by
      simpa only [safety] using hformationExpanded)

/-- Attach the three operational facts supplied by lowering/restoration and
obtain the certificate-facing producer aggregate. -/
theorem NestedFinalAssemblySemanticEvidence.producerEvidence
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {P : NestedInstalledProduction loweredEnv}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {actualEntries : List ConstantInfo}
    (E : NestedFinalAssemblySemanticEvidence P H sourceEnv decl lparams
      nparams isUnsafe safety actualEntries)
    (Hactual : FreshConstantTrace sourceProdEnv actualEntries outEnv)
    (hsourceMapWF : sourceProdEnv.constants.WF)
    (hsourceNonempty : sourceTypes ≠ []) :
    Nonempty (NestedFinalAssemblyProducerEvidence (sourceTypes := sourceTypes)
      P H sourceEnv decl lparams nparams isUnsafe safety) := by
  exact ⟨{
    typeEntries := E.typeEntries
    constructorEntries := E.constructorEntries
    recursorEntries := E.recursorEntries
    canonicalProdEnv := E.canonicalProdEnv
    finalBaseVEnv := E.finalBaseVEnv
    canonical := E.canonical
    typeValues := E.typeValues
    constructorValues := E.constructorValues
    formationAssembly := E.formationAssembly
    formationExpanded := E.formationExpanded
    materialized := E.materialized
    uvars := E.uvars
    numParams := E.numParams
    unsafeEq := E.unsafeEq
    sourceNonempty := hsourceNonempty
    auxiliaryRecursors := E.auxiliaryRecursors
    auxiliaryRules := E.auxiliaryRules
    exactSource := E.exactSource
    primaryFamilies := E.primaryFamilies
    finish := by
      intro main rest primaryRecursors Hsource primaryRules Hprimary
      rcases E.finish main rest primaryRecursors Hsource primaryRules
          Hprimary with ⟨Hlayout, Haux⟩
      exact ⟨{
        productionOrder := ⟨actualEntries, Hactual,
          Hlayout.productionOrder⟩
        sourceMapWF := hsourceMapWF
        auxiliarySemantics := Haux.semantics
        recursorValues := Hlayout.recursorValues
        auxiliaryWF := Haux.wf }⟩ }⟩

end VerifyInductive
end Lean4Lean
