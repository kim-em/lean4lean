import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.Nested.ConcreteBoundary
import Lean4Lean.Verify.Inductive.Nested.ProductionOrigins
import Lean4Lean.Verify.Inductive.Run.EqCanonical
import Lean4Lean.Verify.Inductive.Run.FinalResult

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem abstractAddInduct_declWF
    (H : VEnv.AddInduct env decl target) : decl.WF env := by
  cases H with
  | intro hdecl => exact hdecl

private theorem FreshConstantTrace.quotInit_eq
    (H : FreshConstantTrace source entries target) :
    target.quotInit = source.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem FreshConstantTrace.trEnvIgnore
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hhidden : ∀ ci ∈ entries, ¬ observer ≤ ci.safety)
    (htr : TrEnv' observer source.constants source.quotInit venv) :
    TrEnv' observer target.constants target.quotInit venv := by
  induction H generalizing venv with
  | nil => exact htr
  | @cons rest target source ci hfresh Htail ih =>
      have hfreshMap : source.constants.find? ci.name = none := by
        rw [← hsourceWF.find?'_eq_find?]
        exact hfresh
      have hnextWF : (source.add ci).constants.WF :=
        constantsWF_add_checked hsourceWF hfresh
      have hhead : TrEnv' observer (source.add ci).constants
          (source.add ci).quotInit venv := by
        exact .ignore hfreshMap (hhidden ci (by simp)) htr
      exact ih hnextWF (fun entry hentry =>
        hhidden entry (by simp [hentry])) hhead

private def InductiveConstructorSemanticCoherenceAt.mapProduction
    (H : InductiveConstructorSemanticCoherenceAt source venv familyName
      familyInfo i hi)
    (heq : ∀ name, source.find? name = target.find? name) :
    InductiveConstructorSemanticCoherenceAt target venv familyName
      familyInfo i hi where
  info := H.info
  lookup := by
    rw [← heq]
    exact H.lookup
  induct := H.induct
  cidx := H.cidx
  numParams := H.numParams
  levelParams := H.levelParams
  isUnsafe := H.isUnsafe
  familyTarget := H.familyTarget
  constructorTarget := H.constructorTarget
  familyLookup := H.familyLookup
  constructorLookup := H.constructorLookup
  familyUvars := H.familyUvars
  constructorUvars := H.constructorUvars
  familyNormalized := H.familyNormalized
  constructorNormalized := H.constructorNormalized
  familyDomains := H.familyDomains
  constructorDomains := H.constructorDomains
  familyTail := H.familyTail
  constructorTail := H.constructorTail
  familyType := H.familyType
  constructorType := H.constructorType
  familyDefEq := H.familyDefEq
  constructorDefEq := H.constructorDefEq
  familyParams := H.familyParams
  constructorParams := H.constructorParams
  parameterDomains := H.parameterDomains

private theorem InductiveConstructorsSemanticallyCoherent.mapProduction
    (H : InductiveConstructorsSemanticallyCoherent safety source venv)
    (heq : ∀ name, source.find? name = target.find? name) :
    InductiveConstructorsSemanticallyCoherent safety target venv := by
  intro familyName familyInfo hfamily hvisible i hi
  have hfamily' : source.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [heq]
    exact hfamily
  rcases H familyName familyInfo hfamily' hvisible i hi with ⟨C⟩
  exact ⟨C.mapProduction heq⟩

/-- Forget the exact production alignment while retaining the independent
source declaration and abstract extension specification. -/
def NestedFinalEnvironmentResult.independentSpecification
    (H : NestedFinalEnvironmentResult sourceEnv decl lparams nparams
      sourceTypes isUnsafe safety outEnv) :
    InductiveSpecificationResult sourceEnv lparams nparams sourceTypes
      isUnsafe (H.baseVEnv.addDefEqRules
        H.rules) where
  decl := decl
  envTypes := H.envTypes
  envCtors := H.envCtors
  source := H.sourceCore
  extension := H.addInduct

/-- Recover the replayable staged block before `NestedFinalEnvironmentResult`
projects it to the independent `VEnv.AddInduct` judgment.  This is the exact
canonical production batch retained by the nested final assembly certificate;
in particular, its production endpoint is the environment actually returned
by restoration. -/
def NestedFinalAssemblyCertificate.blockCertificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    BlockCertificate safety sourceProdEnv sourceEnv C.typeEntries
      C.constructorEntries C.recursorEntries
      (C.primaryRules ++ C.auxiliaryRules) C.canonicalProdEnv
        C.finalBaseVEnv where
  staged := C.canonical
  projections := decl.projectionEntries
  typesWF := by
    rw [C.typeValues]
    exact C.sourceSemantics.typeConstantsWF C.typesSource
  ctorsWF := by
    rw [C.constructorValues]
    exact C.sourceSemantics.constructorConstantsWF C.typesSource
  recursorsWF := by
    rw [C.recursorValues]
    intro ci hci
    rcases List.mem_append.mp hci with hprimary | hauxiliary
    · exact (C.sourceSemantics.primaryRecursorsWF ci hprimary).mono
        VEnv.addProjections_le
    · exact (C.auxiliaryWF.recursorsWF (by simp) ci hauxiliary).mono
        VEnv.addProjections_le
  rulesWF := by
    intro df hdf
    rcases List.mem_append.mp hdf with hprimary | hauxiliary
    · exact C.primaryIota.rulesWF df hprimary
    · exact C.auxiliaryWF.rulesWF (by simp) df hauxiliary

theorem NestedFinalAssemblyCertificate.block_eq_canonicalRestoredBlock
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    C.blockCertificate.block =
      canonicalRestoredBlock decl C.primaryRecursors C.auxiliaryRecursors
        C.primaryRules C.auxiliaryRules := by
  simp [BlockCertificate.block, canonicalRestoredBlock,
    NestedFinalAssemblyCertificate.blockCertificate, C.typeValues,
    C.constructorValues, C.recursorValues]

/-- The replayable block is the same source nested compilation used by the
final independent `AddInduct` result. -/
noncomputable def NestedFinalAssemblyCertificate.compilation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    NestedCompilationCertificate sourceEnv decl C.blockCertificate.block := by
  rw [C.block_eq_canonicalRestoredBlock]
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl C.canonical.venvTypes C.canonical.venvCtors :=
    C.sourceSemantics.core C.typesSource C.uvars C.numParams C.unsafeEq
      C.typesAdded C.constructorsAdded
  let block := canonicalRestoredBlock decl C.primaryRecursors
    C.auxiliaryRecursors C.primaryRules C.auxiliaryRules
  have hvalues :
      (C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map
          Prod.snd = block.types ++ block.ctors ++ block.recursors := by
    simp only [List.map_append, block, canonicalRestoredBlock]
    rw [C.typeValues, C.constructorValues, C.recursorValues]
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    rw [← hvalues]
    exact VEnv.addConstVals_names_nodup C.canonical.productionTrace.abstract
  exact NestedCompilationCertificate.ofRestoration sourceEnv
    C.canonical.venvTypes C.canonical.venvCtors decl block C.main C.rest
    C.typesSource C.primaryRecursors C.auxiliaryRecursors C.primaryRules
    C.auxiliaryRules
    (C.sourceSemantics.primaryRecursors.recursorCertificate C.typesSource)
    C.primaryIotaBuild
    (C.primaryIota.length C.typesSource)
    (C.auxiliarySemantics.prefix
      (AuxiliaryRestorationPrefix.empty decl block C.main))
    rfl rfl rfl Hsource.typesAdded Hsource.ctorsAdded rfl rfl hnames

theorem NestedFinalAssemblyCertificate.declWF
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) : decl.WF sourceEnv := by
  let Hsource := C.sourceSemantics.core C.typesSource C.uvars C.numParams
    C.unsafeEq C.typesAdded C.constructorsAdded
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource
        C.sourceNonempty)
  exact ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
    .nested C.formationAssembly.formation VEnv.LE.rfl⟩

/-- The exact installed-production package retained by final assembly and the
exact restoration fold determine the source-family production origins.  The
equalities are only the indices erased when the executable semantic run is
unpacked; no independent origin witness remains. -/
theorem NestedFinalAssemblyCertificate.productionInductiveOrigins
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hmetadata : MaterializedInductivePrefix decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv)
    (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name)) :
    ProductionInductiveOrigins sourceProdEnv.constants outEnv.constants
      decl := by
  have Hsource : TrInductDeclCore sourceEnv c.lparams nparams sourceTypes
      isUnsafe decl C.canonical.venvTypes
        C.canonical.venvCtors := by
    simpa only [hlparams] using
      C.sourceSemantics.core C.typesSource C.uvars C.numParams C.unsafeEq
        C.typesAdded C.constructorsAdded
  have Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      c.env auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  have Horigins := Hrestored.productionInductiveOrigins Hlower Hc Hprod
    Hsource Hmetadata Hsources Howners hempty
  simpa only [henv] using Horigins

/-- The exact restoration trace, reindexed to the ordinary production
context retained by final assembly, preserves the persistent constructor
owner invariant. -/
theorem NestedFinalAssemblyCertificate.constructorOwnersPresent
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (_C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name)) :
    ConstructorOwnersPresent outEnv := by
  have Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  exact Hrestored.constructorOwnersPresent Hlower Hc Hprod hempty Howners

/-- A safe nested restoration extends every safety-indexed observer by
replaying the exact canonical restored block.  The result retains both the
complete final model and the source-facing nested final judgment produced by
the same assembly certificate. -/
private theorem NestedFinalAssemblyCertificate.extendSafe
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {ves : VEnvs}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool}
    (C : NestedFinalAssemblyCertificate H (ves.venv .safe) decl lparams
      nparams isUnsafe .safe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : ProductionInductiveOrigins sourceProdEnv.constants
      outEnv.constants decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules))) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (NestedFinalEnvironmentResult (ves.venv .safe) decl lparams
        nparams sourceTypes isUnsafe .safe outEnv) ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) := by
  let B := C.blockCertificate
  have Hvalid : CheckingEnv.Valid .safe sourceProdEnv (ves.venv .safe) :=
    (wf.tr (safety := .safe)).toCheckingValid
      (wf.hasPrimitives (safety := .safe)) wf.safePrimitives
      wf.typeAnnotationWrappers
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshConstantTrace sourceProdEnv entries outEnv } := by
    rcases H.freshTrace Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  have hlookup : ∀ name, outEnv.constants.find? name =
      C.canonicalProdEnv.constants.find? name :=
    actual.property.lookupEqOfPerm C.canonical.productionTrace.freshTrace
      Hvalid.tr.map_wf (C.productionOrder actual.val actual.property)
  have hlookupEnv : ∀ name, outEnv.find? name =
      C.canonicalProdEnv.find? name := by
    intro name
    change outEnv.constants.find?' name =
      C.canonicalProdEnv.constants.find?' name
    rw [(actual.property.targetWF Hvalid.tr.map_wf).find?'_eq_find?,
      (C.canonical.productionTrace.targetMapWF Hvalid.tr.map_wf).find?'_eq_find?]
    exact hlookup name
  have valid (observer : DefinitionSafety) :
      CheckingEnv.Valid observer sourceProdEnv (ves.venv observer) :=
    (wf.tr (safety := observer)).toCheckingValid
      (wf.hasPrimitives (safety := observer)) wf.safePrimitives
      wf.typeAnnotationWrappers
  have replay (observer : DefinitionSafety) :
      ∃ replayBase,
        ∃ Breplay : BlockCertificate observer sourceProdEnv
          (ves.venv observer) C.typeEntries C.constructorEntries
          C.recursorEntries (C.primaryRules ++ C.auxiliaryRules)
          C.canonicalProdEnv replayBase,
        Breplay.projections = decl.projectionEntries ∧
        AddInduct observer sourceProdEnv.constants (ves.venv observer) decl
          outEnv.constants Breplay.finalVEnv ∧
        B.finalVEnv ≤ Breplay.finalVEnv := by
    rcases B.rebaseAddInduct (valid observer) DefinitionSafety.le_safe
        (wf.mono DefinitionSafety.le_safe) C.declWF
        C.compilation.compilesTo with
      ⟨replayBase, Breplay, hprojections, Habstract, hout⟩
    have HcheckingCanonical : CheckingEnv observer C.canonicalProdEnv
        replayBase := (Breplay.staged.valid (valid observer)).tr
    have Hchecking : CheckingEnv observer outEnv replayBase :=
      CheckingEnv.mapExt HcheckingCanonical
        (actual.property.targetWF Hvalid.tr.map_wf)
        (fun name => (hlookup name).symm)
    have hdeclObserver : decl.WF (ves.venv observer) :=
      abstractAddInduct_declWF Habstract
    have HcheckingRules : CheckingEnv observer outEnv Breplay.finalVEnv := {
      aligned := by
        rw [BlockCertificate.finalVEnv]
        exact aligned_addDefEqs Hchecking.aligned
          (C.primaryRules ++ C.auxiliaryRules)
      wf := by
        rcases (wf.tr (safety := observer)).wf with ⟨ds, Hds⟩
        exact ⟨.induct decl :: ds,
          Hds.decl (.induct hdeclObserver Habstract)⟩
      of_value := by
        intro name ci value hfind hs hvalue
        exact (Hchecking.of_value hfind hs hvalue).mono
          VEnv.addDefEqRules_le
    }
    have Hadd := H.addInductConcrete Habstract HcheckingRules
      Hvalid.tr.map_wf Horigins
    exact ⟨replayBase, Breplay,
      hprojections.trans (by rfl), Hadd, hout⟩
  let pre (observer : DefinitionSafety) :=
    Classical.choose (replay observer)
  have replaySpec (observer : DefinitionSafety) :=
    Classical.choose_spec (replay observer)
  let cert (observer : DefinitionSafety) :=
    Classical.choose (replaySpec observer)
  have certSpec (observer : DefinitionSafety) :=
    Classical.choose_spec (replaySpec observer)
  let adds (observer : DefinitionSafety) := (certSpec observer).2.1
  let outputLE (observer : DefinitionSafety) := (certSpec observer).2.2
  let next (observer : DefinitionSafety) :=
    (cert observer).finalVEnv
  have hcompletedCanonical :
      InductiveConstructorsSemanticallyCoherent .safe C.canonicalProdEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules)) :=
    hconstructorSemantics.mapProduction hlookupEnv
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci hfind hprimitive
    apply (C.canonical.valid Hvalid).safePrimitives
    · rw [← hlookupEnv]
      exact hfind
    · exact hprimitive
  have Hmodels : ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ observer, ves.venv observer ≤ ves'.venv observer) ∧
      ∀ observer, ves'.venv observer = next observer := by
    apply wf.extendInductExact decl next adds actual.property.quotInit_eq
    · intro observer
      exact (cert observer).hasPrimitives
        (wf.hasPrimitives (safety := observer))
    · exact hsafePrimitives
    · exact hclosed
    · exact hconstructorOwners
    · intro observer
      have Hcanonical := B.replaySafeConstructorSemantics
        (cert observer) Hvalid.tr.map_wf
        (wf.constructorSemantics (safety := observer)) hcompletedCanonical
        (outputLE observer)
      exact Hcanonical.mapProduction (fun name => (hlookupEnv name).symm)
    · intro observer observer' hle
      have hblock : (cert observer').block = (cert observer).block :=
        (cert observer').block_eq_of_projections_eq (cert observer)
          ((certSpec observer').1.trans (certSpec observer).1.symm)
      have hinstall := (cert observer').install
      rw [hblock] at hinstall
      exact VInductBlock.install_mono (wf.mono hle)
        hinstall
        (cert observer).install
  rcases Hmodels with ⟨ves', wf', hle, hexact⟩
  refine ⟨ves', wf', hle, ⟨C.finalEnvironment Hvalid⟩, ?_⟩
  rw [hexact .safe]
  exact (adds .safe).toVEnv

/-- Declaration-dispatch form of the safe exact-restoration replay theorem. -/
private theorem NestedFinalAssemblyCertificate.safeInductiveFinalResult
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : NestedFinalAssemblyCertificate H (ves.venv .safe) decl lparams
      nparams false .safe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : ProductionInductiveOrigins sourceProdEnv.constants
      outEnv.constants decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
      false) := by
  rcases C.extendSafe wf Horigins hclosed
      hconstructorOwners hconstructorSemantics with
    ⟨ves', wf', hle, ⟨Hfinal⟩, hadd⟩
  exact ⟨InductiveFinalResult.ofModel ves' wf' hle
    { decl := decl
      envTypes := Hfinal.envTypes
      envCtors := Hfinal.envCtors
      source := Hfinal.sourceCore
      extension := hadd }⟩

/-- Safe final-model assembly with production origins discharged from the
exact closed lowering, ordinary production, and restoration traces. -/
theorem NestedFinalAssemblyCertificate.safeInductiveFinalResultOfProduction
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : NestedFinalAssemblyCertificate H (ves.venv .safe) decl lparams
      nparams false .safe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams false depth
      (ves.venv .safe) result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WF sourceProdEnv)
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hmetadata : MaterializedInductivePrefix decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
      false) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  exact C.safeInductiveFinalResult wf
    (C.productionInductiveOrigins Hlower Hc Hprod Hmetadata Hsources Howners
      hempty henv hlparams hnames)
    hclosed
    (C.constructorOwnersPresent Hlower Hc Hprod Howners hempty henv hnames)
    hconstructorSemantics

/-- An unsafe exact restoration changes only the unsafe abstract observer.
The premise is indexed by every exact fresh restoration trace, ruling out an
unrelated list of production constants; it is precisely the production
metadata fact needed to justify `TrEnv'.ignore` at partial and safe. -/
private theorem NestedFinalAssemblyCertificate.unsafeInductiveFinalResult
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : NestedFinalAssemblyCertificate H (ves.venv .unsafe) decl lparams
      nparams true .unsafe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : ProductionInductiveOrigins sourceProdEnv.constants
      outEnv.constants decl)
    (hentriesUnsafe : ∀ entries
      (_Hentries : FreshConstantTrace sourceProdEnv entries outEnv),
      ∀ entry ∈ entries, entry.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
      true) := by
  let B := C.blockCertificate
  have Hvalid : CheckingEnv.Valid .unsafe sourceProdEnv (ves.venv .unsafe) :=
    (wf.tr (safety := .unsafe)).toCheckingValid
      (wf.hasPrimitives (safety := .unsafe)) wf.safePrimitives
      wf.typeAnnotationWrappers
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshConstantTrace sourceProdEnv entries outEnv } := by
    rcases H.freshTrace Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  have hperm := C.productionOrder actual.val actual.property
  have hlookup : ∀ name, outEnv.constants.find? name =
      C.canonicalProdEnv.constants.find? name :=
    actual.property.lookupEqOfPerm C.canonical.productionTrace.freshTrace
      Hvalid.tr.map_wf hperm
  have hlookupEnv : ∀ name, outEnv.find? name =
      C.canonicalProdEnv.find? name := by
    intro name
    change outEnv.constants.find?' name =
      C.canonicalProdEnv.constants.find?' name
    rw [(actual.property.targetWF Hvalid.tr.map_wf).find?'_eq_find?,
      (C.canonical.productionTrace.targetMapWF Hvalid.tr.map_wf).find?'_eq_find?]
    exact hlookup name
  let F := C.finalEnvironment Hvalid
  have HcheckingRules : CheckingEnv .unsafe outEnv
      (C.finalBaseVEnv.addDefEqRules
        (C.primaryRules ++ C.auxiliaryRules)) := {
    aligned := aligned_addDefEqs F.checking.aligned
      (C.primaryRules ++ C.auxiliaryRules)
    wf := by
      rcases (wf.tr (safety := .unsafe)).wf with ⟨ds, Hds⟩
      exact ⟨.induct decl :: ds,
        Hds.decl (.induct (abstractAddInduct_declWF F.addInduct)
          F.addInduct)⟩
    of_value := by
      intro name ci value hfind hs hvalue
      exact (F.checking.of_value hfind hs hvalue).mono
        VEnv.addDefEqRules_le
  }
  have Hadd : AddInduct .unsafe sourceProdEnv.constants (ves.venv .unsafe)
      decl outEnv.constants
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules)) :=
    H.addInductConcrete F.addInduct HcheckingRules Hvalid.tr.map_wf
      Horigins
  have htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (C.finalBaseVEnv.addDefEqRules
        (C.primaryRules ++ C.auxiliaryRules)) := by
    rw [actual.property.quotInit_eq]
    exact .induct (abstractAddInduct_declWF F.addInduct) Hadd
      (wf.tr (safety := .unsafe))
  have hactualUnsafe : ∀ entry ∈ actual.val,
      entry.safety = .unsafe := hentriesUnsafe actual.val actual.property
  have htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial) := by
    apply actual.property.trEnvIgnore Hvalid.tr.map_wf
    · intro entry hentry
      rw [hactualUnsafe entry hentry]
      decide
    · exact wf.tr (safety := .partial)
  have htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe) := by
    apply actual.property.trEnvIgnore Hvalid.tr.map_wf
    · intro entry hentry
      rw [hactualUnsafe entry hentry]
      decide
    · exact wf.tr (safety := .safe)
  have hcanonicalUnsafe : ∀ entry ∈
      C.typeEntries ++ C.constructorEntries ++ C.recursorEntries,
      entry.1.safety = .unsafe := by
    intro entry hentry
    have hcanonical : entry.1 ∈
        (C.typeEntries ++ C.constructorEntries ++
          C.recursorEntries).map Prod.fst :=
      List.mem_map.mpr ⟨entry, hentry, rfl⟩
    exact hactualUnsafe entry.1 (hperm.mem_iff.mpr hcanonical)
  have hheadersCanonical := B.installedInductiveHeadersUnsafe
    Hvalid.tr.map_wf hcanonicalUnsafe
  have hheadersActual : InstalledInductiveHeadersUnsafe sourceProdEnv
      outEnv := by
    intro familyName familyInfo hfamily hfresh
    apply hheadersCanonical familyName familyInfo
    · rw [← hlookupEnv]
      exact hfamily
    · exact hfresh
  have hiddenSemantics (observer : DefinitionSafety)
      (hne : observer ≠ .unsafe) :
      InductiveConstructorsSemanticallyCoherent observer outEnv
        (ves.venv observer) := by
    have Hcanonical := B.hiddenUnsafeConstructorSemantics Hvalid.tr.map_wf
      (wf.constructorSemantics (safety := observer)) hne hheadersCanonical
    exact Hcanonical.mapProduction (fun name => (hlookupEnv name).symm)
  have hiddenProvenance (observer : DefinitionSafety)
      (hne : observer ≠ .unsafe) :
      InstalledInductiveProvenance observer outEnv.constants
        (ves.venv observer) := by
    apply InstalledInductiveProvenance.rebaseHidden
      (wf.inductiveProvenance (safety := observer))
      Hadd.preservesSourceFind
    intro familyName familyInfo hfamily hfresh
    have hfamilyEnv : outEnv.find? familyName =
        some (.inductInfo familyInfo) := by
      rw [Lean.Kernel.Environment.find?,
        (actual.property.targetWF Hvalid.tr.map_wf).find?'_eq_find?]
      exact hfamily
    have hfreshEnv : sourceProdEnv.find? familyName = none := by
      rw [Lean.Kernel.Environment.find?, Hvalid.tr.map_wf.find?'_eq_find?]
      exact hfresh
    have hunsafe := hheadersActual familyName familyInfo hfamilyEnv hfreshEnv
    have hnotle : ¬ observer ≤ DefinitionSafety.unsafe := by
      intro hle
      exact hne (DefinitionSafety.le_antisymm hle
        DefinitionSafety.unsafe_le)
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, hunsafe] using hnotle
  have hprovenance : ∀ observer,
      InstalledInductiveProvenance observer outEnv.constants
        (match observer with
        | .unsafe => C.finalBaseVEnv.addDefEqRules
            (C.primaryRules ++ C.auxiliaryRules)
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe)
    | .unsafe => InstalledInductiveProvenance.addInduct
        (wf.inductiveProvenance (safety := .unsafe)) Hadd
    | .partial => hiddenProvenance .partial (by decide)
    | .safe => hiddenProvenance .safe (by decide)
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci hfind hprimitive
    apply (C.canonical.valid Hvalid).safePrimitives
    · rw [← hlookupEnv]
      exact hfind
    · exact hprimitive
  rcases VEnvs.WF.extendUnsafeExact wf
      (C.finalBaseVEnv.addDefEqRules
        (C.primaryRules ++ C.auxiliaryRules))
      htrUnsafe htrPartial htrSafe
      (B.hasPrimitives (wf.hasPrimitives (safety := .unsafe)))
      hsafePrimitives
      (wf.typeAnnotationWrappers.rebase
        (actual.property.preservesSourceFind Hvalid.tr.map_wf))
      hclosed
      hconstructorOwners
      (fun observer => match observer with
        | .unsafe => hconstructorSemantics
        | .partial => hiddenSemantics .partial (by decide)
        | .safe => hiddenSemantics .safe (by decide))
      hprovenance (VInductBlock.install_le B.install) with
    ⟨ves', wf', hle, hexact⟩
  have haddExact : VEnv.AddInduct (ves.venv .unsafe) decl
      (ves'.venv .unsafe) := by
    rw [hexact]
    exact Hadd.toVEnv
  exact ⟨InductiveFinalResult.ofModel ves' wf' hle
    { decl := decl
      envTypes := F.envTypes
      envCtors := F.envCtors
      source := F.sourceCore
      extension := haddExact }⟩

/-- Unsafe final-model assembly with production origins discharged from the
exact closed lowering, ordinary production, and restoration traces. -/
theorem NestedFinalAssemblyCertificate.unsafeInductiveFinalResultOfProduction
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : NestedFinalAssemblyCertificate H (ves.venv .unsafe) decl lparams
      nparams true .unsafe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams true depth
      (ves.venv .unsafe) result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WF sourceProdEnv)
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hmetadata : MaterializedInductivePrefix decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hentriesUnsafe : ∀ entries
      (_Hentries : FreshConstantTrace sourceProdEnv entries outEnv),
      ∀ entry ∈ entries, entry.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
      true) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  exact C.unsafeInductiveFinalResult wf
    (C.productionInductiveOrigins Hlower Hc Hprod Hmetadata Hsources Howners
      hempty henv hlparams hnames)
    hentriesUnsafe hclosed
    (C.constructorOwnersPresent Hlower Hc Hprod Howners hempty henv hnames)
    hconstructorSemantics

end VerifyInductive
end Lean4Lean
