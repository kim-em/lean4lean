import Lean4Lean.Verify.Inductive.Nested.Install.Certificate
import Lean4Lean.Verify.Inductive.Rules.Lhs
import Lean4Lean.Verify.Inductive.Nested.Lowering.Run
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryRecursorsWF
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources
import Lean4Lean.Verify.Inductive.Rules.Alignment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Checks
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ConstructorEnvironment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.StrippedRecursorShapes
import Lean4Lean.Verify.Inductive.Nested.CaseEliminators.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorTelescopes
import Lean4Lean.Verify.Inductive.Nested.Restoration.HeaderRenaming

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
* `NestedFinalAssemblyShapeSemanticEvidence` retains canonical installation,
  formation, and pointwise source/primary semantics, but no executable
  freshness or lowering non-emptiness assumptions.
-/

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

/-- Telescope-translation specialization of the pointwise source producer.
The source recursor, its shape, metadata refinement, and installation typing
are reconstructed from the exact production/restoration join. -/
theorem NestedLoweringResultClosed.restoredPrimaryTelescopeAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
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
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {Hprod : RecursorCheck R.toConstructorCheck loweredEnv}
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

/-- Fold the executable validation certificates over the exact auxiliary
restoration trace.  Membership in the validation suffix is inherited from
the literal `StateForMTrace` name list. -/
theorem RestoredAuxiliaryGeneratedAlignmentTrace.recursorTraceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv validationEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {Hprod : RecursorCheck R.toConstructorCheck loweredEnv}
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
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
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
        ∃ canonicalProdEnv installedVEnv,
          Nonempty { S : BlockInstallation c.safety c.env sourceVEnv replay.typeEntries
            replay.constructorEntries replay.recursorEntries
              decl.projectionEntries canonicalProdEnv installedVEnv // S.eliminators = es } ∧
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
    ⟨replay, canonicalProdEnv, installedVEnv, Hstaged, hlookup⟩
  exact ⟨auxiliaryRecursors, Hauxiliary, replay, canonicalProdEnv, installedVEnv,
    Hstaged, hlookup⟩

/-- Construct the rule-independent part of the final nested certificate
directly from the exact traces retained by the executable run. No rule list
is selected. -/
theorem NestedFinalAssemblyBase.ofReplay
    {c : AddInductive.Context} {sourceDecl : VInductDecl} {isUnsafe : Bool}
    {nparams : Nat} {sourceVEnv envTypes envCtors finalBaseVEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv outEnv canonicalProdEnv ruleEnv : Environment}
    {sourceTypes : List InductiveType}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (Hc : ContextWF c)
    (Hcore : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (P : NestedInstalledProduction loweredEnv)
    (Hmetadata : MaterializedInductivePrefix sourceDecl P.loweredDecl)
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
    (canonical : BlockInstallation c.safety c.env sourceVEnv replay.typeEntries
      replay.constructorEntries replay.recursorEntries
        sourceDecl.projectionEntries canonicalProdEnv finalBaseVEnv)
    (HruleValid : CheckingEnv.Valid c.safety ruleEnv finalBaseVEnv)
    (Hformation : NestedFormationAssembly sourceVEnv sourceDecl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
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
    Nonempty { B : NestedFinalAssemblyBase Hrestored sourceVEnv
        sourceDecl c.lparams nparams isUnsafe c.safety //
      B.production = P ∧ CheckingEnv.Valid c.safety ruleEnv B.finalBaseVEnv } := by
  have hcanonicalTypes : canonical.venvTypes = envTypes := by
    have hadded := canonical.abstract_types
    rw [replay.typeValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.typesAdded)
  have hcanonicalCtors : canonical.venvCtors = envCtors := by
    have hadded := canonical.abstract_ctors
    rw [hcanonicalTypes, replay.constructorValues] at hadded
    exact Option.some.inj (hadded.symm.trans Hcore.ctorsAdded)
  have hownersNonempty : sourceDecl.types ≠ [] :=
    fun hnil => by
      have hlength := Lean4Lean.List.Forall₂.length_eq Hsource.types
      rw [hnil] at hlength
      simp at hlength
      exact hsourceNonempty hlength
  cases htypesSource : sourceDecl.types with
  | nil => exact (hownersNonempty htypesSource).elim
  | cons main rest =>
      have Hsource' : RestoredSourceInductiveSemanticTrace sourceDecl
          c.lparams c.safety sourceVEnv envTypes
          ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
          Hrestored.inductives (main :: rest) primaryRecursors := by
        simpa only [htypesSource] using Hsource
      have HsourceCanonical : RestoredSourceInductiveSemanticTrace sourceDecl
          c.lparams c.safety sourceVEnv canonical.venvTypes
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          Hrestored.inductives (main :: rest)
            primaryRecursors := by
        simpa only [hcanonicalTypes, hcanonicalCtors, hcanonicalElims] using Hsource'
      have HauxiliaryCanonical : RestoredAuxiliaryRecursorTrace c.safety
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections sourceDecl.projectionEntries)
          Hrestored.auxiliaries [] auxiliaryRecursors := by
        simpa only [hcanonicalCtors, hcanonicalElims] using HauxiliaryRecursors
      exact ⟨⟨{
        production := P
        typeEntries := replay.typeEntries
        constructorEntries := replay.constructorEntries
        recursorEntries := replay.recursorEntries
        canonicalProdEnv := canonicalProdEnv
        finalBaseVEnv := finalBaseVEnv
        canonical := canonical
        productionOrder := fun actualEntries Hactual =>
          (Hactual.permOfSameTarget replay.fresh Hc.checking.tr.map_wf).trans
            replay.productionOrder
        main := main
        rest := rest
        typesSource := htypesSource
        primaryRecursors := primaryRecursors
        auxiliaryRecursors := auxiliaryRecursors
        sourceSemantics := HsourceCanonical
        auxiliaryRecursorTrace := HauxiliaryCanonical
        typeValues := replay.typeValues
        constructorValues := replay.constructorValues
        recursorValues := replay.recursorValues
        formationAssembly := Hformation
        formationExpanded := hformationExpanded
        materialized := Hmetadata
        uvars := huvars
        numParams := hnumParams
        unsafeEq := hunsafeEq
        sourceNonempty := hsourceNonempty
        eliminatorsWF := by rw [hcanonicalElims]; exact Hcases
        eliminatorsCertified := by rw [hcanonicalElims]; exact Hreplay
        eliminatorsRestored := by rw [hcanonicalElims]; exact HelimRestored },
        rfl, HruleValid⟩⟩

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
        Sigma fun R : OrdinaryConstructorCheck Hheaders P.ctorEnv =>
          RecursorCheck R.toConstructorCheck outEnv
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
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {params : List VExpr}
    (Hshapes : ∀ target ∈ E.production.loweredDecl.types,
      E.production.loweredDecl.TypeShape E.production.initialEnv params target) :
    ∀ target ∈ sourceDecl.types,
      sourceDecl.TypeShape sourceVEnv params target := by
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
  have Hshape : P.loweredDecl.TypeShape sourceVEnv params expandedTarget := by
    have H : P.loweredDecl.TypeShape P.initialEnv params expandedTarget :=
      Hshapes expandedTarget (List.getElem_mem hiExpanded)
    rw [hinitial] at H
    exact H
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

/-- Source parameter formation of a nested run, without a source-side
re-check. Lowering keeps the common-parameter prefix of every source
constructor verbatim (`LoweredConstructorMapping.sourceTargetSameForallPrefix`),
so the translated prefix of a source constructor is the one of its lowered
constructor, whose parameter shape the ordinary pipeline certified in the
lowered header environment. The header-stage renaming replacement
(`headerRenamingReplacement`) transports that certificate to the source header
environment: the parameters and the prefix mention no auxiliary family, so the
replacement fixes them. -/
theorem NestedValidatedRunResult.nativeSourceParameterWF
    {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hraw : ∀ type ∈ sourceDecl.types, ∀ ctor ∈ type.ctors,
      sourceDecl.RawCtorShape type ctor) :
    sourceDecl.SourceParameterWF (ves.venv (if isUnsafe then .unsafe else .safe)) := by
  let P := E.production
  have hinitial : P.initialEnv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.production_initialEnv
  obtain ⟨paramsL, envTypesL, haddedL, HtypeShapesL, HctorsL, -⟩ :=
    P.constructors.formation.formationWF.sourceParameterWF
  have hheaderL : envTypesL = P.constructors.toConstructorCheck.headerVEnv := by
    have h := P.constructors.toConstructorCheck.core.typesAdded
    rw [haddedL] at h
    exact Option.some.inj h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion, -, D,
      -, -⟩
  have hnodup : (InductiveSignature.familyNames P.loweredDecl.types ++
      P.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have S := E.headerRenamingReplacement wf hadded henvTypes Haux Hexpansion hnodup
    henvTypes.ordered VEnv.LE.rfl (E.eliminatorProjNames_of wf Hsources auxiliaries D)
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hbaseWF : (ves.venv (if isUnsafe then .unsafe else .safe)).WF := TrEnv'.wf wf.tr
  have hbaseFresh : ∀ n ∈ (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants n = none :=
    fun n hn => (VEnv.addConstVals_le hadded).constants_eq_none_left (hfresh n hn)
  have Hsource : TrInductDeclCore (ves.venv (if isUnsafe then .unsafe else .safe))
      lparams nparams sourceTypes isUnsafe sourceDecl E.nativeSource.envTypes
        E.nativeSource.envCtors := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.core
  have hnativeTypes : E.nativeSource.envTypes = envTypes := by
    have h := Hsource.typesAdded
    rw [hadded] at h
    exact (Option.some.inj h).symm
  have HtypeShapes := E.nativeSourceTypeShapes HtypeShapesL
  refine ⟨paramsL, envTypes, hadded, HtypeShapes, ?_, Hraw⟩
  intro target htarget ctor hctor
  rcases List.mem_iff_getElem.1 htarget with ⟨familyIdx, hfamily, rfl⟩
  rcases List.mem_iff_getElem.1 hctor with ⟨ctorIdx, hctorTarget, rfl⟩
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [TrInductDeclCore.types_length Hsource]
    exact hfamily
  have HsourceType := TrInductDeclCore.typeAt Hsource familyIdx hsourceFamily hfamily
  have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
    rw [TrInductiveType.ctors_length HsourceType]
    exact hctorTarget
  have HsourceCtor := TrInductiveType.ctorAt HsourceType ctorIdx hsourceCtor hctorTarget
  -- The lowered constructor at the same position.
  rcases E.lowering.sourceFinalMappingAtFreshAligned (initialState :=
      { lvls := lparams.map .param, newTypes := #[] }) rfl hsourceFamily with
    ⟨_, _, loweredType, _, _, _, _, Hmapping, hloweredType⟩
  rcases Hmapping.constructors.mappingAt ctorIdx hsourceCtor with
    ⟨sourceCtor, loweredCtor, _, _, hsourceCtorEq, hloweredCtorEq, HctorMapping⟩
  have hsourceCtorEq' : sourceCtor = sourceTypes[familyIdx].ctors[ctorIdx] := by
    rw [List.getElem?_eq_getElem hsourceCtor] at hsourceCtorEq
    exact (Option.some.inj hsourceCtorEq).symm
  subst hsourceCtorEq'
  have Hsame := HctorMapping.sourceTargetSameForallPrefix
    (by simpa using HsourceCtor.type.fvarsIn) HsourceCtor.type.closed
  -- Its translation in the lowered header environment.
  have hindTypes : P.indTypes.toList = result.types := by
    have harray := congrArg Array.toList E.production_indTypes
    simpa using harray
  have Hlowered := P.constructors.core
  have hloweredFamily : familyIdx < result.types.length := by
    rcases List.getElem?_eq_some_iff.1 hloweredType with ⟨h, _⟩
    exact h
  have hloweredFamily' : familyIdx < P.indTypes.toList.length := by
    rw [hindTypes]; exact hloweredFamily
  have hloweredDeclFamily : familyIdx < P.loweredDecl.types.length := by
    rw [← TrInductDeclCore.types_length Hlowered]; exact hloweredFamily'
  have HloweredType := TrInductDeclCore.typeAt Hlowered familyIdx hloweredFamily'
    hloweredDeclFamily
  have hloweredTypeEq : P.indTypes.toList[familyIdx] = loweredType := by
    have h : P.indTypes.toList[familyIdx]? = some loweredType := by
      rw [hindTypes]; exact hloweredType
    rw [List.getElem?_eq_getElem hloweredFamily'] at h
    exact Option.some.inj h
  have hloweredCtorIdx : ctorIdx < loweredType.ctors.length := by
    rcases List.getElem?_eq_some_iff.1 hloweredCtorEq with ⟨h, _⟩
    exact h
  have hloweredCtorIdx' : ctorIdx < P.indTypes.toList[familyIdx].ctors.length := by
    rw [hloweredTypeEq]; exact hloweredCtorIdx
  have hloweredDeclCtor : ctorIdx < P.loweredDecl.types[familyIdx].ctors.length := by
    rw [← TrInductiveType.ctors_length HloweredType]; exact hloweredCtorIdx'
  have HloweredCtor := TrInductiveType.ctorAt HloweredType ctorIdx hloweredCtorIdx'
    hloweredDeclCtor
  have hloweredCtorEq' : P.indTypes.toList[familyIdx].ctors[ctorIdx] = loweredCtor := by
    have h : loweredType.ctors[ctorIdx]? = some loweredCtor := hloweredCtorEq
    rw [List.getElem?_eq_getElem hloweredCtorIdx] at h
    simp only [hloweredTypeEq]
    exact Option.some.inj h
  have HloweredCtorType : TrExprS P.headers.context.venv P.c.lparams []
      loweredCtor.type P.loweredDecl.types[familyIdx].ctors[ctorIdx].type := by
    have h := HloweredCtor.type
    rw [hloweredCtorEq'] at h
    exact h
  -- The certified parameter shape of the lowered constructor.
  rcases HctorsL _ (List.getElem_mem hloweredDeclFamily) _
      (List.getElem_mem hloweredDeclCtor) with ⟨own, tail, htake, hdefeq⟩
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams E.production_c).trans
      E.productionContext_lparams
  have hnparamsEq : P.loweredDecl.nparams = sourceDecl.nparams :=
    P.constructors.core.nparams.trans (E.production_nparams.trans Hsource.nparams.symm)
  rw [hnparamsEq] at htake
  have hnparams : sourceDecl.nparams = nparams := Hsource.nparams
  rw [hnparams] at htake
  obtain ⟨tail', htake'⟩ := Hsame.takeForalls_of_trExprS .base
    (by simpa only [hlparams] using HsourceCtor.type)
    (by simpa only [hlparams] using HloweredCtorType) htake
  refine ⟨own, tail', by rw [hnparams]; exact htake', ?_⟩
  -- The prefix mentions no restorable name.
  have hownClean : ∀ A ∈ own,
      A.containsAnyConst (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames =
        false := by
    have hwf := HsourceCtor.wf
    rw [hnativeTypes] at hwf
    obtain ⟨u, hu⟩ := hwf
    have hclean := (hu.noFreshConsts henvTypes.ordered hfresh
      (fun _ h => by simp at h)).1
    rw [(VExpr.takeForalls_eq_wrapForalls htake').1] at hclean
    exact (VExpr.containsAnyConst_wrapForalls_inv hclean).1
  have huvars : P.loweredDecl.uvars = sourceDecl.uvars :=
    P.constructors.core.uvars.trans (by rw [hlparams, Hsource.uvars])
  have hdefeq' : P.constructors.toConstructorCheck.headerVEnv.IsDefEqCtx sourceDecl.uvars []
      paramsL.reverse own.reverse := by
    rw [← hheaderL, ← huvars]; exact hdefeq
  have Htransported := S.isDefEqCtx hdefeq'
  -- The parameters and the prefix mention no restorable name.
  have hparamsClean : ∀ A ∈ paramsL,
      A.containsAnyConst (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames =
        false := by
    rcases HtypeShapes _ htarget with ⟨_, _, _, _, _, _, _, _, _, hshape, _⟩
    have hctx := VEnv.Ordered.ctxNoFreshConsts hbaseWF.ordered hbaseFresh hshape.isType
    intro A hA
    exact hctx A (List.mem_reverse.mpr hA)
  have hmapParams : paramsL.reverse.map (fun A => A.replaceRen
      ((InductiveSignature.compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => P.compilationSignature.params)
      (InductiveSignature.compilationRestoration sourceDecl auxiliaries).renaming) = paramsL.reverse := by
    rw [List.map_congr_left (fun A hA => InductiveSignature.Restoration.replaceRen_eq_self
      (hparamsClean A (List.mem_reverse.mp hA))), List.map_id']
  have hmapOwn : own.reverse.map (fun A => A.replaceRen
      ((InductiveSignature.compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => P.compilationSignature.params)
      (InductiveSignature.compilationRestoration sourceDecl auxiliaries).renaming) = own.reverse := by
    rw [List.map_congr_left (fun A hA => InductiveSignature.Restoration.replaceRen_eq_self
      (hownClean A (List.mem_reverse.mp hA))), List.map_id']
  have Htransported' := Htransported
  rw [hmapParams, hmapOwn, List.map_nil] at Htransported'
  exact Htransported'

/-- Assemble the rule-independent base of a validated execution in the
production record's native dependent indices, without the recursor-rule
validator, then transport it once to the public indices.  Transporting only the finished aggregate avoids splitting
the dependent header/constructor/recursor phase chain apart. -/
private theorem NestedValidatedRunResult.assemblyBaseOfFormationNative
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
    Nonempty { C : NestedFinalAssemblyBase E.restoration sourceVEnv
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
      Sigma fun R : OrdinaryConstructorCheck Hheaders P.ctorEnv =>
        RecursorCheck R.toConstructorCheck E.loweredEnv
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
      CtorTelescopes P.c.safety outEnv venv' ∧
      CtorTelescopes P.c.safety E.validationEnv venv' := by
    intro venv' hle
    have hcert := HbaseValid.corner
    rw [henv, hinitial, hsafety] at hcert
    have H := E.restoredCtorTelescopes Hsources Howners wf.envGF hcert
    rw [hsafety]
    exact ⟨CtorTelescopes.mono H.1 hle, CtorTelescopes.mono H.2 hle⟩
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
        exact canonical.formation.constructorLE.trans
          (VEnv.addEliminators_addProjections_le.trans canonical.recursorsAdded.le))).1
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
  rcases NestedFinalAssemblyBase.ofReplay HcP Hcore P' Hmetadata
      Hrestored primaryRecursors auxiliaryRecursors Hsource HauxiliaryRecursors
      replay canonical HruleValid HformationP hformationExpandedP
      huvars hnumParams hunsafeEq (by simp) hcanonicalElims HcasesP
      (by rw [hinitial, henv]; exact Hreplay) HelimRestored with ⟨⟨C, hproduction, hCvalid⟩⟩
  have hproductionOriginal : C.production = P := by
    calc
      C.production = P' := hproduction
      _ = P := by
        simpa only [P', Hheaders, R, Hprod, Hpack] using
          NestedInstalledProduction.rebuildIndTypes_eq P
            result.types.toArray hindTypes
  let CertificateAt := fun q : Sigma RestorationAt =>
    Nonempty { C : NestedFinalAssemblyBase q.2 P.initialEnv sourceDecl
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

/-- Unconditional rule-independent final assembly base for the exact
validated execution, constructed without the recursor-rule validator.  Ordinary
formation comes from the installed constructor phases; source parameter
formation comes from the literal restored-parameter validator; and the full
ordered nested expansion comes from the producer-owned generated registry.
No declaration-specific evidence is accepted from the caller. The stripped
output environment is valid in the base's final abstract environment. -/
theorem NestedValidatedRunResult.assemblyBaseNativeValid
    {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) :
    Nonempty { B : NestedFinalAssemblyBase E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      B.production = E.production ∧
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
          B.finalBaseVEnv } := by
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
      Sigma fun R : OrdinaryConstructorCheck Hheaders P.ctorEnv =>
        RecursorCheck R.toConstructorCheck E.loweredEnv
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
    simpa only [hinitial, safety] using E.nativeSourceParameterWF wf Hsources Hraw
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
  exact E.assemblyBaseOfFormationNative wf rfl rfl hnested Hsources wf.constructorOwners
    (by cases isUnsafe <;> decide) Hformation (by
      simpa only [safety] using hformationExpanded)

end VerifyInductive
end Lean4Lean
