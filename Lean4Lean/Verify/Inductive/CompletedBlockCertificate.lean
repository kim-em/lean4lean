import Lean4Lean.Verify.Inductive.CompletedRecursorPhases

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Header and constructor installation may be ordinary or atomic primitive
installation; recursors always begin from the completed valid constructor
environment and use the ordinary validated installation trace. -/
structure CompletedStagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (projections : List VProjectionEntry)
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  formationAdded : CompletedFormationInstallation safety env venv types
    envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors
    (venvCtors.addProjections projections) recursors
    outEnv outVEnv

def CompletedStagedBlock.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : CompletedStagedBlock checkSafety env venv types ctors recursors projections
      outEnv outVEnv) :
    CompletedStagedBlock safety env venv types ctors recursors projections
      outEnv outVEnv where
  envTypes := H.envTypes
  venvTypes := H.venvTypes
  envCtors := H.envCtors
  venvCtors := H.venvCtors
  formationAdded := H.formationAdded.sf_mono hsafety
  recursorsAdded := H.recursorsAdded.sf_mono hsafety

theorem CompletedStagedBlock.abstract_types
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv) :
    venv.addConstVals (types.map Prod.snd) = some H.venvTypes :=
  H.formationAdded.headerAbstract

theorem CompletedStagedBlock.abstract_ctors
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv) :
    H.venvTypes.addConstVals (ctors.map Prod.snd) = some H.venvCtors :=
  H.formationAdded.constructorAbstract

theorem CompletedStagedBlock.abstract_recursors
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv) :
    (H.venvCtors.addProjections projections).addConstVals
      (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

theorem CompletedStagedBlock.valid
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv)
    (hvalidCtors : CheckingEnv.Valid safety H.envCtors
      (H.venvCtors.addProjections projections)) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid hvalidCtors

/-- Collapse the completed formation prefix and ordinary recursor suffix into
one atomic trace. This exposes whole-block provenance without manufacturing
a validity judgment for a primitive header prefix. -/
theorem CompletedStagedBlock.combinedAtomic
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv) :
    AtomicAddConstants safety env
      (venv.addProjections projections) (types ++ ctors ++ recursors)
      outEnv outVEnv := by
  have Hformation : AtomicAddConstants safety env venv (types ++ ctors)
      H.envCtors H.venvCtors := by
    cases H.formationAdded with
    | ordinary Htypes Hctors =>
        exact (AtomicAddConstants.ofAddConstants Htypes).append
          (AtomicAddConstants.ofAddConstants Hctors)
    | primitive Htypes Hctors _ => exact Htypes.append Hctors
  have Hformation' : AtomicAddConstants safety env
      (venv.addProjections projections) (types ++ ctors) H.envCtors
      (H.venvCtors.addProjections projections) := by
    exact Hformation.addProjections
  simpa [List.append_assoc] using
    Hformation'.append
      (AtomicAddConstants.ofAddConstants H.recursorsAdded)

theorem CompletedStagedBlock.quotInit_eq
    (H : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv) : outEnv.quotInit = env.quotInit :=
  H.recursorsAdded.quotInit_eq.trans H.formationAdded.quotInit_eq

/-- Semantic certificate for a block whose formation prefix is permitted to
be an atomic primitive batch.  Its well-formedness proof depends only on the
three abstract `addConstVals` equations, never on partial-batch validity. -/
structure CompletedBlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  projections : List VProjectionEntry
  staged : CompletedStagedBlock safety env venv types ctors recursors
    projections outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF staged.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF (staged.venvCtors.addProjections projections)
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def CompletedBlockCertificate.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : CompletedBlockCertificate checkSafety env venv types ctors recursors
      rules outEnv outVEnv) :
    CompletedBlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := H.projections
  staged := H.staged.sf_mono hsafety
  typesWF := H.typesWF
  ctorsWF := H.ctorsWF
  recursorsWF := H.recursorsWF
  rulesWF := H.rulesWF

def CompletedBlockCertificate.block
    (_H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules
  projections := _H.projections

def CompletedBlockCertificate.finalVEnv
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VEnv :=
  outVEnv.addDefEqRules rules

theorem CompletedBlockCertificate.block_eq_of_projections_eq
    (H₁ : CompletedBlockCertificate safety₁ env₁ venv₁ types ctors recursors
      rules outEnv₁ outVEnv₁)
    (H₂ : CompletedBlockCertificate safety₂ env₂ venv₂ types ctors recursors
      rules outEnv₂ outVEnv₂)
    (h : H₁.projections = H₂.projections) : H₁.block = H₂.block := by
  simp [CompletedBlockCertificate.block, h]

theorem CompletedBlockCertificate.wf
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.staged.venvTypes, H.staged.venvCtors,
    outVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors, H.typesWF, H.ctorsWF,
    H.recursorsWF, H.rulesWF⟩

theorem CompletedBlockCertificate.install
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some H.finalVEnv := by
  simp [CompletedBlockCertificate.block, VInductBlock.install,
    CompletedBlockCertificate.finalVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors]

theorem CompletedBlockCertificate.names
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    List.Nodup
      ((H.block.types ++ H.block.ctors ++ H.block.recursors).map
        (·.name)) := by
  have hall : (venv.addProjections H.projections).addConstVals
      (types.map Prod.snd ++ ctors.map Prod.snd ++ recursors.map Prod.snd) =
      some outVEnv := by
    simpa [List.map_append, List.append_assoc] using
      H.staged.combinedAtomic.abstract
  simpa [CompletedBlockCertificate.block, List.map_append] using
    VEnv.addConstVals_names_nodup hall

/-- Replay a completed block in a larger abstract source model.  Formation is
replayed with the sound completed-prefix theorem, so the atomic primitive case
never requires a valid header-only environment. -/
theorem CompletedBlockCertificate.rebaseCertificate
    {decl : VInductDecl}
    (H : CompletedBlockCertificate checkSafety prodEnv base types ctors
      recursors rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety <= checkSafety)
    (hbase : base <= largerBase)
    (Hdecl : decl.WF base)
    (Hcompile : decl.CompilesTo base H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : CompletedBlockCertificate safety prodEnv largerBase types
        ctors recursors rules outEnv largerOutBase,
      outBase ≤ largerOutBase ∧ Hlarger.projections = H.projections := by
  rcases H.staged.formationAdded.rebase Hvalid hsafety hbase with
    ⟨largerTypes, largerCtors, ⟨Hformation⟩, htypes, hctors⟩
  have HcheckingCtors : CheckingEnv safety H.staged.envCtors largerCtors :=
    Hformation.checking Hvalid.tr
  have hprojectedWF :
      (largerCtors.addProjections H.projections).WF := by
    apply VEnv.WF.inductProjections
        (base := largerBase) (envTypes := largerTypes)
        (decl := decl) (block := H.block)
    · exact Hvalid.tr.wf
    · exact HcheckingCtors.wf
    · exact Hcompile.sourceNames
    · exact Hdecl.1.2.2.2.1
    · exact Hcompile.types
    · exact Hcompile.ctors
    · exact Hcompile.projections
    · exact Hformation.headerAbstract
    · exact Hformation.constructorAbstract
  have HcheckingProjected : CheckingEnv safety H.staged.envCtors
      (largerCtors.addProjections H.projections) :=
    HcheckingCtors.addProjections hprojectedWF
  have hctorsProjected :
      H.staged.venvCtors.addProjections H.projections ≤
        largerCtors.addProjections H.projections :=
    VEnv.addProjections_mono hctors
  rcases H.staged.recursorsAdded.rebaseChecking HcheckingProjected hsafety
      hctorsProjected with ⟨largerOutBase, Hrecursors, hout⟩
  let Hlarger : CompletedBlockCertificate safety prodEnv largerBase types
      ctors recursors rules outEnv largerOutBase := {
    projections := H.projections
    staged := {
      envTypes := H.staged.envTypes
      venvTypes := largerTypes
      envCtors := H.staged.envCtors
      venvCtors := largerCtors
      formationAdded := Hformation
      recursorsAdded := Hrecursors }
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := fun ci hci => (H.ctorsWF ci hci).mono htypes
    recursorsWF := fun ci hci =>
      (H.recursorsWF ci hci).mono hctorsProjected
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hout }
  exact ⟨largerOutBase, Hlarger, hout, rfl⟩

/-- The abstract inductive extension depends only on the completed block's
well-formedness and installation equations, not on whether the formation
prefix was installed ordinarily or as one atomic primitive batch. -/
theorem CompletedBlockCertificate.addInductAbstract
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hdecl : decl.WF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl H.finalVEnv :=
  .intro Hdecl Hcompile H.wf H.install

/-- Concrete executable-to-specification boundary for a completed block.
Whole-block alignment and delta conservation use the atomic trace, which is
valid for ordinary and primitive formation alike. -/
theorem CompletedBlockCertificate.addInduct
    (H : CompletedBlockCertificate checkSafety prodEnv venv types ctors
      recursors rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsourceAligned : Aligned checkSafety prodEnv.constants venv) :
    AddInduct checkSafety prodEnv.constants venv decl outEnv.constants
      H.finalVEnv := by
  apply AddInduct.intro H.block hdecl hcompile H.wf H.install
  · exact horigins
  · intro name ci hfind
    have hfindEnv : prodEnv.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?,
        hsourceAligned.map_wf.find?'_eq_find?]
      exact hfind
    have hout := H.staged.combinedAtomic.preservesSourceFind
      hsourceAligned.map_wf hfindEnv
    have houtWF := H.staged.combinedAtomic.targetMapWF
      hsourceAligned.map_wf
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hout
    exact hout
  · intro Haligned
    exact aligned_addDefEqs
      (H.staged.combinedAtomic.aligned (.projections Haligned)) rules
  · exact H.staged.combinedAtomic.deltaConservative
      (.projections hsourceAligned)

/-- Replay a safe completed block into one observer model and construct the
corresponding concrete `AddInduct` witness. -/
theorem CompletedBlockCertificate.rebaseAddInductSafe
    (H : CompletedBlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid targetSafety prodEnv largerBase)
    (hbase : base <= largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl) :
    ∃ largerOutBase,
      ∃ Hlarger : CompletedBlockCertificate targetSafety prodEnv largerBase
        types ctors recursors rules outEnv largerOutBase,
      AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
        (largerOutBase.addDefEqRules rules) ∧
      H.finalVEnv ≤
        (largerOutBase.addDefEqRules rules) ∧
      Hlarger.projections = H.projections := by
  rcases H.rebaseCertificate Hvalid DefinitionSafety.le_safe hbase hdecl
      hcompile with
    ⟨largerOutBase, Hlarger, houtBase, hprojections⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    by
      have hblock := Hlarger.block_eq_of_projections_eq H hprojections
      rw [← hblock] at hcompile
      exact hcompile.mono hbase Hlarger.wf
  have hadd : AddInduct targetSafety prodEnv.constants largerBase decl
      outEnv.constants
        (largerOutBase.addDefEqRules rules) := by
    simpa [CompletedBlockCertificate.finalVEnv, hprojections] using
      Hlarger.addInduct hdeclLarger hcompileLarger horigins Hvalid.tr.aligned
  exact ⟨largerOutBase, Hlarger, hadd,
    VEnv.addDefEqRules_mono houtBase, hprojections⟩

theorem CompletedBlockCertificate.addInductOfFormation
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : decl.SourceWF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl H.finalVEnv :=
  H.addInductAbstract (Hformation.declWF Hsource) Hcompile

/-- Ordinary compilation closes a completed formation prefix, including the
atomic primitive prefix, once source translation supplies the independent
source well-formedness judgment. -/
theorem CompletedBlockCertificate.addInductOfOrdinaryCompilation
    (H : CompletedBlockCertificate safety env venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : OrdinaryCompilationCertificate venv decl H.block) :
    VEnv.AddInduct venv decl H.finalVEnv := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductOfFormation Hformation
    (Lean4Lean.TrInductDecl.sourceWF Htranslated)
    Hcompile.compilesTo

/-- Nested compilation closes against the same completed formation boundary. -/
theorem CompletedBlockCertificate.addInductOfNestedCompilation
    (H : CompletedBlockCertificate safety env venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : NestedCompilationCertificate venv decl H.block) :
    VEnv.AddInduct venv decl H.finalVEnv := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductOfFormation Hformation
    (Lean4Lean.TrInductDecl.sourceWF Htranslated)
    Hcompile.compilesTo

def GeneratedRecursors.toCompletedBlockCertificate
    (projections : List VProjectionEntry)
    (staged : CompletedStagedBlock safety env venv types ctors recursors
      projections outEnv outVEnv)
    (H : GeneratedRecursors safety
      (staged.venvCtors.addProjections projections) lparams elimLevel c stats
      indTypes recInfos recursors)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (htypes : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv)
    (hctors : ∀ ci ∈ ctors.map Prod.snd,
      ci.toVConstant.WF staged.venvTypes)
    (hrules : ∀ df ∈ rules, df.WF outVEnv) :
    CompletedBlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := projections
  staged := staged
  typesWF := htypes
  ctorsWF := hctors
  recursorsWF := H.recursorsWF Hc Hbindings Hparams
  rulesWF := hrules

theorem CompletedConstructorPhases.typesWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ∀ ci ∈ R.headerEntries.map Prod.snd,
      ci.toVConstant.WF sourceEnv := by
  rw [R.headerValues]
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types target htarget with
    ⟨source, _, Htarget⟩
  exact Htarget.header.wf

theorem CompletedConstructorPhases.ctorsWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ∀ ci ∈ R.constructorEntries.map Prod.snd,
      ci.toVConstant.WF R.headerVEnv := by
  rw [R.constructorValues]
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  rcases hci with ⟨target, htarget, hci⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types target htarget with
    ⟨source, _, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hci with
    ⟨ctor, _, Hctor⟩
  exact Hctor.wf

def CompletedRecursorPhasesResult.staged
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    CompletedStagedBlock c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries decl.projectionEntries outEnv H.outVEnv where
  envTypes := R.headerEnv
  venvTypes := R.headerVEnv
  envCtors := ctorEnv
  venvCtors := R.context.venv
  formationAdded := R.installation
  recursorsAdded := by
    simpa [H.localExtends.safety_eq, H.localExtends.env_eq] using H.installed

def CompletedRecursorPhasesResult.blockCertificate
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    CompletedBlockCertificate c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries rules outEnv H.outVEnv := by
  let Hgenerated : GeneratedRecursors c.safety
      (R.context.venv.addProjections decl.projectionEntries) c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  exact Hgenerated.toCompletedBlockCertificate decl.projectionEntries H.staged
    H.localWF H.bindings H.params R.typesWF R.ctorsWF hrules

@[simp] theorem CompletedRecursorPhasesResult.blockCertificate_projections
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    (H.blockCertificate rules hrules).projections = decl.projectionEntries := by
  rfl

end VerifyInductive
end Lean4Lean
