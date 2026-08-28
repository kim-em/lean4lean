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
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  formationAdded : CompletedFormationInstallation safety env venv types
    envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors
    outEnv outVEnv

theorem CompletedStagedBlock.abstract_types
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv) :
    venv.addConstVals (types.map Prod.snd) = some H.venvTypes :=
  H.formationAdded.headerAbstract

theorem CompletedStagedBlock.abstract_ctors
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv) :
    H.venvTypes.addConstVals (ctors.map Prod.snd) = some H.venvCtors :=
  H.formationAdded.constructorAbstract

theorem CompletedStagedBlock.abstract_recursors
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv) :
    H.venvCtors.addConstVals (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

theorem CompletedStagedBlock.valid
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv)
    (hvalidCtors : CheckingEnv.Valid safety H.envCtors H.venvCtors) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid hvalidCtors

/-- Collapse the completed formation prefix and ordinary recursor suffix into
one atomic trace. This exposes whole-block provenance without manufacturing
a validity judgment for a primitive header prefix. -/
theorem CompletedStagedBlock.combinedAtomic
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv) :
    AtomicAddConstants safety env venv (types ++ ctors ++ recursors)
      outEnv outVEnv := by
  have Hformation : AtomicAddConstants safety env venv (types ++ ctors)
      H.envCtors H.venvCtors := by
    cases H.formationAdded with
    | ordinary Htypes Hctors =>
        exact (AtomicAddConstants.ofAddConstants Htypes).append
          (AtomicAddConstants.ofAddConstants Hctors)
    | primitive Htypes Hctors _ => exact Htypes.append Hctors
  simpa [List.append_assoc] using
    Hformation.append
      (AtomicAddConstants.ofAddConstants H.recursorsAdded)

theorem CompletedStagedBlock.quotInit_eq
    (H : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv) : outEnv.quotInit = env.quotInit :=
  H.recursorsAdded.quotInit_eq.trans H.formationAdded.quotInit_eq

/-- Semantic certificate for a block whose formation prefix is permitted to
be an atomic primitive batch.  Its well-formedness proof depends only on the
three abstract `addConstVals` equations, never on partial-batch validity. -/
structure CompletedBlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  staged : CompletedStagedBlock safety env venv types ctors recursors
    outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF staged.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF staged.venvCtors
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def CompletedBlockCertificate.block
    (_H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules

theorem CompletedBlockCertificate.wf
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.staged.venvTypes, H.staged.venvCtors, outVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors, H.typesWF, H.ctorsWF, H.recursorsWF,
    H.rulesWF⟩

theorem CompletedBlockCertificate.install
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some (outVEnv.addDefEqRules rules) := by
  simp [CompletedBlockCertificate.block, VInductBlock.install,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors]

theorem CompletedBlockCertificate.names
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    List.Nodup
      ((H.block.types ++ H.block.ctors ++ H.block.recursors).map
        (·.name)) := by
  have hall : venv.addConstVals
      (types.map Prod.snd ++ ctors.map Prod.snd ++ recursors.map Prod.snd) =
      some outVEnv :=
    VEnv.addConstVals_append
      (VEnv.addConstVals_append H.staged.abstract_types
        H.staged.abstract_ctors)
      H.staged.abstract_recursors
  simpa [CompletedBlockCertificate.block, List.map_append] using
    VEnv.addConstVals_names_nodup hall

/-- Replay a completed block in a larger abstract source model.  Formation is
replayed with the sound completed-prefix theorem, so the atomic primitive case
never requires a valid header-only environment. -/
theorem CompletedBlockCertificate.rebaseCertificate
    (H : CompletedBlockCertificate checkSafety prodEnv base types ctors
      recursors rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety <= checkSafety)
    (hbase : base <= largerBase) :
    exists largerOutBase,
      Nonempty (CompletedBlockCertificate safety prodEnv largerBase types
        ctors recursors rules outEnv largerOutBase) /\
      outBase <= largerOutBase := by
  rcases H.staged.formationAdded.rebase Hvalid hsafety hbase with
    ⟨largerTypes, largerCtors, ⟨Hformation⟩, htypes, hctors⟩
  have HcheckingCtors : CheckingEnv safety H.staged.envCtors largerCtors :=
    Hformation.checking Hvalid.tr
  rcases H.staged.recursorsAdded.rebaseChecking HcheckingCtors hsafety
      hctors with ⟨largerOutBase, Hrecursors, hout⟩
  refine ⟨largerOutBase, ⟨?_⟩, hout⟩
  exact {
    staged := {
      envTypes := H.staged.envTypes
      venvTypes := largerTypes
      envCtors := H.staged.envCtors
      venvCtors := largerCtors
      formationAdded := Hformation
      recursorsAdded := Hrecursors }
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := fun ci hci => (H.ctorsWF ci hci).mono htypes
    recursorsWF := fun ci hci => (H.recursorsWF ci hci).mono hctors
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hout }

/-- The abstract inductive extension depends only on the completed block's
well-formedness and installation equations, not on whether the formation
prefix was installed ordinarily or as one atomic primitive batch. -/
theorem CompletedBlockCertificate.addInductAbstract
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hdecl : decl.WF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) :=
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
      (outVEnv.addDefEqRules rules) := by
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
    exact aligned_addDefEqs (H.staged.combinedAtomic.aligned Haligned) rules
  · exact H.staged.combinedAtomic.deltaConservative hsourceAligned

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
    exists largerOutBase,
      Nonempty (CompletedBlockCertificate targetSafety prodEnv largerBase
        types ctors recursors rules outEnv largerOutBase) /\
      AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
        (largerOutBase.addDefEqRules rules) /\
      outBase.addDefEqRules rules <=
        largerOutBase.addDefEqRules rules := by
  rcases H.rebaseCertificate Hvalid DefinitionSafety.le_safe hbase with
    ⟨largerOutBase, ⟨Hlarger⟩, houtBase⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    hcompile.mono hbase Hlarger.wf
  have hadd : AddInduct targetSafety prodEnv.constants largerBase decl
      outEnv.constants (largerOutBase.addDefEqRules rules) := by
    exact Hlarger.addInduct hdeclLarger hcompileLarger horigins
      Hvalid.tr.aligned
  exact ⟨largerOutBase, ⟨Hlarger⟩, hadd,
    VEnv.addDefEqRules_mono houtBase⟩

theorem CompletedBlockCertificate.addInductOfFormation
    (H : CompletedBlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : decl.SourceWF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) :=
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
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) := by
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
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductOfFormation Hformation
    (Lean4Lean.TrInductDecl.sourceWF Htranslated)
    Hcompile.compilesTo

def GeneratedRecursors.toCompletedBlockCertificate
    (staged : CompletedStagedBlock safety env venv types ctors recursors
      outEnv outVEnv)
    (H : GeneratedRecursors safety staged.venvCtors lparams elimLevel c stats
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
      R.constructorEntries H.entries outEnv H.outVEnv where
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
  let Hgenerated : GeneratedRecursors c.safety R.context.venv c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  exact Hgenerated.toCompletedBlockCertificate H.staged H.localWF H.bindings
    H.params R.typesWF R.ctorsWF hrules

end VerifyInductive
end Lean4Lean
