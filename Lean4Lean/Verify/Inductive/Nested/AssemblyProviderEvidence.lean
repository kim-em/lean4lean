import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaBlockTransport
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryEvidence

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
      Hshape.minors.length = (recInfos.flatMap (·.minors)).size := by
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
  refine ⟨Hshape, ?_, ?_⟩
  · change motives.length = (recInfos.map (·.motive)).size
    exact hmotivesLength
  · change minors.length = (recInfos.flatMap (·.minors)).size
    exact hminorsLength

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
      Hshape.minors.length = loweredDecl.ownedConstructors.length := by
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
      A.recursor.selections A.recursor.owner_lt A.recursor.noAlias
      A.recursor.nparams_eq sourceDecl owner hdecl hownerEq
      Hrecursor.recursor HexistingShape.name HexistingShape.uvars
      (Hsource.nparams.trans Hlowering.toResult.resultNParams.symm)
      hmotives hminors hindices Htranslation with
    ⟨Hshape, hmotivesExact, hminorsExact⟩
  exact ⟨Hshape,
    hmotivesExact.trans (by
      simpa using Hprod.cardinality.records),
    hminorsExact.trans Hprod.cardinality.minors⟩

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
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule)
    (hproj : ProjectionConstPreservation) :
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
      rule Hequation hcontext (fun Hprojection hfree =>
        hproj _ Hprojection hfree) with ⟨Hstaged⟩
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
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule)
    (hproj : ProjectionConstPreservation) : Nonempty G.OrdinarySource := by
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
      rule Hequation hcontext (fun Hprojection hfree =>
        hproj _ Hprojection hfree) with ⟨Hstaged⟩
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
    (hproj : ProjectionConstPreservation)
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
  rcases G.ordinarySource hproj with ⟨O⟩
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
    ⟨Hshape, htargetMotives, htargetMinors⟩
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
    (hproj : ProjectionConstPreservation)
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
        htargetContext hproj)
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody G.translation.typeBody
        S.source.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.restoreNode sourceRecursors
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
      htargetContext hproj domains_eq rhsArgs rhs_spine field_args
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
    (targetEnv : VEnv) (hproj : ProjectionConstPreservation) where
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
      sourceContextWF targetContextWF hproj)
    (abstractForallContext [] rhs.sourceScope).toCtx
    (abstractForallContext [] rhs.targetScope).toCtx
    rhs.sourceBody rhs.targetBody G.translation.typeBody S.source.typeBody
  guarded : GuardedExprRestoration rhs.plan.restoreNode sourceRecursors
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
    {hproj : ProjectionConstPreservation}
    (E : RestoredPrimaryIotaStructuralRestorationEvidence
      (Hlowering := Hlowering) (A := A) (restoredBlock := restoredBlock)
        S hold hnew targetEnv hproj)
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
      E.targetContextWF hproj E.domains E.rhsArgs E.rhsSpine
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
    (hproj : ProjectionConstPreservation)
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
          S hold hnew targetVEnv hproj)) :
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
      hproj i hctor with
    ⟨hgenerated, generatedRule, G, sourceBlock, S, hsourceRecursor⟩
  rcases Hstructural i hctor hold hnew hgenerated generatedRule G sourceBlock S with
    ⟨E⟩
  exact ⟨E.semantics (by
    rw [hsourceRecursor]
    exact hrestoredRecursorMem)⟩

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
    (hproj : ProjectionConstPreservation)
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
          S hold hnew targetVEnv hproj)) :
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
    hdecl hownerEq restoredBlock targetVEnv hrecursor hproj
  intro i hctor hold hnew hgenerated generatedRule G sourceBlock S
  exact Hstructural familyIdx hfamily hentry stepSource stepTarget Hstep A
    owner Hrecursor i hctor hold hnew hgenerated generatedRule G sourceBlock S

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
      primaryRules auxiliaryRules) main safety sourceEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  wf : RestoredAuxiliaryFinalWFTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety sourceEnv canonicalVEnv
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
        main safety sourceEnv canonicalVEnv finalBaseVEnv Hstep
          priorRecursors))
    (Houtputs : ∀ finalRecursors finalRules,
      RestoredAuxiliarySemanticTrace decl
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules)
        main safety sourceEnv H.auxiliaries [] [] finalRecursors finalRules →
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
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceEnv decl
        (VInductDecl.NestedAuxiliarySource sourceEnv decl generated))
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
    have Htypes' : List.Forall₂
        (VInductDecl.NestedTypeExpansion P.initialEnv decl
          (VInductDecl.NestedAuxiliarySource P.initialEnv decl generated))
        (decl.types ++ generated) P.loweredDecl.types := by
      simpa only [hinitialEnv] using Htypes
    have Hformation := NestedFormationAssembly.ofConstructorPhases
      P.constructors generated hnonempty huvarsExpansion hnparamsExpansion
        hunsafeExpansion Htypes'
    simpa only [hinitialEnv] using Hformation
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
  sourceFamilies : ∀ indType stepSource stepTarget
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType stepSource stepTarget), indType ∈ sourceTypes →
    Nonempty (RestoredSourceInductiveSemantics decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors Hstep)
  typesSource : ∀ owners primaryRecursors
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      owners primaryRecursors),
    decl.types = owners
  primaryFamilies : ∀ owners primaryRecursors
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      owners primaryRecursors),
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
    (HsourceFamilies : ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      Nonempty (RestoredSourceInductiveSemantics decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors Hstep))
    (HtypesSource : ∀ owners primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors H.inductives
        owners primaryRecursors),
      decl.types = owners)
    (HprimaryFamilies : ∀ owners primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv C.canonical.venvTypes C.canonical.venvCtors H.inductives
        owners primaryRecursors),
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
    sourceFamilies := HsourceFamilies
    typesSource := HtypesSource
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
    (hproj : ProjectionConstPreservation)
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
    (HsourceFamilies : ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (fun type => type.name)) indType stepSource
          stepTarget), indType ∈ sourceTypes →
      Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams
        c.safety sourceVEnv C.canonical.venvTypes C.canonical.venvCtors
          Hstep))
    (HtypesSource : ∀ owners primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace sourceDecl c.lparams
        c.safety sourceVEnv C.canonical.venvTypes C.canonical.venvCtors
        Hrestored.inductives owners primaryRecursors),
      sourceDecl.types = owners)
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
        S hold hnew C.finalBaseVEnv hproj)) :
    Nonempty (NestedFinalAssemblySemanticEvidence P Hrestored sourceVEnv
      sourceDecl c.lparams nparams isUnsafe c.safety actualEntries) := by
  subst P
  apply NestedFinalAssemblySemanticEvidence.ofCanonical _ Hrestored
    sourceVEnv sourceDecl c.lparams nparams isUnsafe c.safety actualEntries C
      HsourceFamilies HtypesSource
  · intro owners primaryRecursors Hsource
    have htypesSource := HtypesSource owners primaryRecursors Hsource
    have htypesAdded : sourceVEnv.addConstVals sourceDecl.typeConstants =
        some C.canonical.venvTypes := by
      rw [← C.typeValues]
      exact C.canonical.typesAdded.abstract
    have hconstructorsAdded :
        C.canonical.venvTypes.addConstVals sourceDecl.constructorConstants =
          some C.canonical.venvCtors := by
      rw [← C.constructorValues]
      exact C.canonical.ctorsAdded.abstract
    let Hcore := Hsource.core htypesSource C.uvars C.numParams C.unsafeEq
      htypesAdded hconstructorsAdded
    have Hall := Hlower.primaryFamiliesOfStructuralRestorations Hc Hprod Hsources
      Hcore Hmetadata Howners hempty
        (canonicalRestoredShapeBlock sourceDecl primaryRecursors
          C.auxiliaryRecursors) C.finalBaseVEnv hproj
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
    sourceFamilies := E.sourceFamilies
    typesSource := E.typesSource
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
