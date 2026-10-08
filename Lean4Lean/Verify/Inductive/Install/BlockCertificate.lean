import Lean4Lean.Verify.Inductive.Recursor.Check

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Installation certificate matching the executable order: mutual headers,
constructors, then recursors.  Header and constructor installation may be
ordinary (one validated constant at a time) or an atomic primitive batch; see
`FormationInstallation`.  Between the constructors and the recursors
the abstract environment registers the block's case eliminators and then its
projections (`VInductBlock.install`); both are abstract-only, so the
production environment is unchanged there.  Recursors always begin from the
completed valid constructor environment and use the ordinary validated
installation trace.  Reduction equations are not included here because their
validity depends on the independent iota schema. -/
structure BlockInstallation (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (projections : List VProjectionEntry)
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  formation : FormationInstallation safety env venv types
    envTypes venvTypes ctors envCtors venvCtors
  eliminators : List (Name × InductiveSignature.CaseSchema)
  casesWF : (venvCtors.addEliminators eliminators).WF
  projectedWF : ((venvCtors.addEliminators eliminators).addProjections projections).WF
  recursorsAdded : AddConstants safety envCtors
    ((venvCtors.addEliminators eliminators).addProjections projections) recursors
    outEnv outVEnv

def BlockInstallation.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : BlockInstallation checkSafety env venv types ctors recursors projections
      outEnv outVEnv) :
    BlockInstallation safety env venv types ctors recursors projections
      outEnv outVEnv where
  envTypes := H.envTypes
  venvTypes := H.venvTypes
  envCtors := H.envCtors
  venvCtors := H.venvCtors
  formation := H.formation.sf_mono hsafety
  eliminators := H.eliminators
  casesWF := H.casesWF
  projectedWF := H.projectedWF
  recursorsAdded := H.recursorsAdded.sf_mono hsafety

theorem BlockInstallation.abstract_types
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    venv.addConstVals (types.map Prod.snd) = some H.venvTypes :=
  H.formation.headerAbstract

theorem BlockInstallation.abstract_ctors
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    H.venvTypes.addConstVals (ctors.map Prod.snd) = some H.venvCtors :=
  H.formation.constructorAbstract

theorem BlockInstallation.abstract_recursors
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    ((H.venvCtors.addEliminators H.eliminators).addProjections projections).addConstVals
      (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- Collapse the completed formation prefix and ordinary recursor suffix into
one atomic trace. This exposes whole-block provenance without manufacturing
a validity judgment for a primitive header prefix. -/
theorem BlockInstallation.atomic
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    AtomicAddConstants safety env
      ((venv.addEliminators H.eliminators).addProjections projections) (types ++ ctors ++ recursors)
      outEnv outVEnv := by
  have Hformation' : AtomicAddConstants safety env
      ((venv.addEliminators H.eliminators).addProjections projections) (types ++ ctors) H.envCtors
      ((H.venvCtors.addEliminators H.eliminators).addProjections projections) := by
    exact H.formation.atomic.addEliminators.addProjections
  simpa [List.append_assoc] using
    Hformation'.append
      (AtomicAddConstants.ofAddConstants H.recursorsAdded)

theorem BlockInstallation.quotInit_eq
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) : outEnv.quotInit = env.quotInit :=
  H.recursorsAdded.quotInit_eq.trans H.formation.quotInit_eq

/-- The staged installation preserves the local checking invariants. -/
theorem BlockInstallation.validCore
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv :=
  H.recursorsAdded.validCore
    (((H.formation.validCore hvalid).addEliminators H.casesWF).addProjections
      H.projectedWF)

/-- The staged installation adds no stored equation. -/
theorem BlockInstallation.defeqs
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    ∀ df, outVEnv.defeqs df → venv.defeqs df := by
  intro df hdf
  have h1 := H.recursorsAdded.defeqs df hdf
  rw [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs] at h1
  exact H.formation.atomic.defeqs df h1

theorem BlockInstallation.le
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    venv ≤ outVEnv :=
  H.formation.atomic.le.trans
    (VEnv.addEliminators_addProjections_le.trans H.recursorsAdded.le)

theorem BlockInstallation.aligned
    (H : BlockInstallation checkSafety env venv types ctors recursors
      projections outEnv outVEnv)
    (Halign : Aligned checkSafety env.constants venv) :
    Aligned checkSafety outEnv.constants outVEnv :=
  H.atomic.aligned (.projections (Aligned.addEliminators Halign))

theorem BlockInstallation.trEnvIgnore
    (H : BlockInstallation checkSafety prodEnv venv types ctors recursors
      projections outEnv outVEnv)
    (htypes : ∀ entry ∈ types, ¬ observerSafety ≤ entry.1.safety)
    (hctors : ∀ entry ∈ ctors, ¬ observerSafety ≤ entry.1.safety)
    (hrecursors : ∀ entry ∈ recursors,
      ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv := by
  apply H.recursorsAdded.trEnvIgnore hrecursors
  apply H.formation.atomic.trEnvIgnore _ htr
  intro entry hentry
  rcases List.mem_append.mp hentry with htype | hctor
  · exact htypes entry htype
  · exact hctors entry hctor

theorem BlockInstallation.deltaConservative
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (Halign : Aligned safety env.constants venv) :
    ∀ {name ci}, outEnv.constants.find? name = some ci →
      ci.deltaValue?.isSome → env.constants.find? name = some ci :=
  H.atomic.deltaConservative (.projections (Aligned.addEliminators Halign))

/-- The complete semantic certificate for the block assembled by the three
executable installation stages, whose formation prefix may be ordinary or an
atomic primitive batch.  The installation trace records the per-step checking
environment; the `*WF` fields deliberately record the stronger stage-wide
facts required by the independent `VInductBlock.WF` specification.  This
distinction matters for mutual declarations: typing a later header only after
installing an earlier sibling would not establish formation of the mutual
block.  Well-formedness depends only on the three abstract `addConstVals`
equations, never on partial-batch validity. -/
structure BlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  projections : List VProjectionEntry
  installation : BlockInstallation safety env venv types ctors recursors
    projections outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF installation.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF ((installation.venvCtors.addEliminators installation.eliminators).addProjections
      projections)
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def BlockCertificate.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : BlockCertificate checkSafety env venv types ctors recursors
      rules outEnv outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := H.projections
  installation := H.installation.sf_mono hsafety
  typesWF := H.typesWF
  ctorsWF := H.ctorsWF
  recursorsWF := H.recursorsWF
  rulesWF := H.rulesWF

def BlockCertificate.block
    (_H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules
  projections := _H.projections
  eliminators := _H.installation.eliminators

def BlockCertificate.installedVEnv
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VEnv :=
  outVEnv.addDefEqRules rules

/-- The header environment of a completed block is below its final model. -/
theorem BlockCertificate.typesLe
    (H : BlockCertificate safety env venv types ctors recursors rules outEnv outVEnv)
    (htypes : venv.addConstVals (types.map Prod.snd) = some venvH) :
    venvH ≤ H.installedVEnv := by
  rw [H.installation.abstract_types] at htypes
  cases htypes
  exact (VEnv.addConstVals_le H.installation.abstract_ctors).trans
    (VEnv.addEliminators_addProjections_le.trans
      (H.installation.recursorsAdded.le.trans VEnv.addDefEqRules_le))

theorem BlockCertificate.block_eq_of_projections_eq
    (H₁ : BlockCertificate safety₁ env₁ venv₁ types ctors recursors
      rules outEnv₁ outVEnv₁)
    (H₂ : BlockCertificate safety₂ env₂ venv₂ types ctors recursors
      rules outEnv₂ outVEnv₂)
    (h : H₁.projections = H₂.projections)
    (he : H₁.installation.eliminators = H₂.installation.eliminators) : H₁.block = H₂.block := by
  simp [BlockCertificate.block, h, he]

theorem BlockCertificate.wf
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.installation.venvTypes, H.installation.venvCtors,
    outVEnv,
    H.installation.abstract_types, H.installation.abstract_ctors,
    H.installation.abstract_recursors, H.typesWF, H.ctorsWF,
    H.recursorsWF, H.rulesWF⟩

theorem BlockCertificate.install
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some H.installedVEnv := by
  simp [BlockCertificate.block, VInductBlock.install,
    BlockCertificate.installedVEnv,
    H.installation.abstract_types, H.installation.abstract_ctors,
    H.installation.abstract_recursors]

theorem BlockCertificate.names
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    List.Nodup
      ((H.block.types ++ H.block.ctors ++ H.block.recursors).map
        (·.name)) := by
  have hall : ((venv.addEliminators H.installation.eliminators).addProjections H.projections).addConstVals
      (types.map Prod.snd ++ ctors.map Prod.snd ++ recursors.map Prod.snd) =
      some outVEnv := by
    simpa [List.map_append, List.append_assoc] using
      H.installation.atomic.abstract
  simpa [BlockCertificate.block, List.map_append] using
    VEnv.addConstVals_names_nodup hall

/-- Replay a completed block in a larger abstract source model.  Formation is
replayed with the sound completed-prefix theorem, so the atomic primitive case
never requires a valid header-only environment. -/
theorem BlockCertificate.rebaseCertificate
    {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv base types ctors
      recursors rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety <= checkSafety)
    (hbase : base <= largerBase)
    (Hdecl : decl.WF base)
    (Hcompile : decl.CompilesTo base H.block)
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate safety prodEnv largerBase types
        ctors recursors rules outEnv largerOutBase,
      outBase ≤ largerOutBase ∧ Hlarger.projections = H.projections ∧
        Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.installation.formation.rebase Hvalid.tr hsafety hbase with
    ⟨largerTypes, largerCtors, ⟨Hformation⟩, htypes, hctors⟩
  have HcheckingCtors : CheckingEnv safety H.installation.envCtors largerCtors :=
    Hformation.checking Hvalid.tr
  have htypes' : largerBase.addConstVals decl.typeConstants = some largerTypes := by
    rw [← Hcompile.types]
    exact Hformation.headerAbstract
  have hctors' : largerTypes.addConstVals decl.constructorConstants = some largerCtors := by
    rw [← Hcompile.ctors]
    exact Hformation.constructorAbstract
  have Hcases := Hreplay _ _ htypes' hctors'
  have hcasesWF : (largerCtors.addEliminators H.installation.eliminators).WF :=
    Hcases.elimWF Hvalid.tr.wf (Hdecl.1.mono_of_addConstVals hbase htypes' hctors')
      Hcompile.types Hcompile.ctors Hformation.headerAbstract Hformation.constructorAbstract
  have hprojectedWF :
      ((largerCtors.addEliminators H.installation.eliminators).addProjections H.projections).WF := by
    obtain ⟨_, _, _, _, hc⟩ := Hcases
    rcases hc with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, _⟩
    · have hP' : H.projections = [] :=
        Hcompile.projections.trans (VInductDecl.projectionEntries_eq_nil hT)
      have hcasesWF' := hcasesWF
      generalize H.installation.eliminators = es at hcasesWF' ⊢
      rw [hP']
      exact hcasesWF'
    apply VEnv.WF.inductProjections
        (base := largerBase) (envTypes := largerTypes)
        (decl := decl) (block := H.block)
    · exact Hvalid.tr.wf
    · exact hcasesWF
    · exact ⟨key, schema, hE, hreg⟩
    · exact Hcompile.sourceNames
    · exact fun type member => (Hdecl.1.originalTypes type member).mono hbase
    · exact Hdecl.1.2.2.2.1
    · rcases Hdecl.1.originalConstructors with ⟨baseTypes, hbaseTypes, hwf⟩
      have hle : baseTypes ≤ largerTypes :=
        VEnv.addConstVals_mono hbase hbaseTypes htypes'
      exact fun ctor hctor => (hwf ctor hctor).mono hle
    · rcases Hdecl.1.originalConstructors with ⟨baseTypes, hbaseTypes, _⟩
      exact (Hdecl.sourceParameterWF hbaseTypes).mono_of_addConstVals hbase htypes'
    · rcases Hdecl.1.originalConstructors with ⟨baseTypes, hbaseTypes, _⟩
      exact (Hdecl.sourceParameterWF hbaseTypes).rawCtorShape
    · exact Hcompile.types
    · exact Hcompile.ctors
    · exact Hcompile.projections
    · exact Hformation.headerAbstract
    · exact Hformation.constructorAbstract
  have HcheckingProjected : CheckingEnv safety H.installation.envCtors
      ((largerCtors.addEliminators H.installation.eliminators).addProjections H.projections) :=
    (HcheckingCtors.addEliminators hcasesWF).addProjections hprojectedWF
  have hctorsProjected :
      (H.installation.venvCtors.addEliminators H.installation.eliminators).addProjections H.projections ≤
        (largerCtors.addEliminators H.installation.eliminators).addProjections H.projections :=
    VEnv.addProjections_mono (VEnv.addEliminators_mono hctors)
  rcases H.installation.recursorsAdded.rebase HcheckingProjected hsafety
      hctorsProjected with ⟨largerOutBase, Hrecursors, hout⟩
  let Hlarger : BlockCertificate safety prodEnv largerBase types
      ctors recursors rules outEnv largerOutBase := {
    projections := H.projections
    installation := {
      envTypes := H.installation.envTypes
      venvTypes := largerTypes
      envCtors := H.installation.envCtors
      venvCtors := largerCtors
      formation := Hformation
      eliminators := H.installation.eliminators
      casesWF := hcasesWF
      projectedWF := hprojectedWF
      recursorsAdded := Hrecursors }
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := fun ci hci => (H.ctorsWF ci hci).mono htypes
    recursorsWF := fun ci hci =>
      (H.recursorsWF ci hci).mono hctorsProjected
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hout }
  exact ⟨largerOutBase, Hlarger, hout, rfl, rfl⟩

/-- Concrete executable-to-specification boundary for a completed block.
Whole-block alignment and delta conservation use the atomic trace, which is
valid for ordinary and primitive formation alike. -/
theorem BlockCertificate.addInduct
    (H : BlockCertificate checkSafety prodEnv venv types ctors
      recursors rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      venv outEnv.constants H.installedVEnv)
    (hsourceAligned : Aligned checkSafety prodEnv.constants venv)
    (helim : VInductBlock.EliminatorsWF venv decl H.block) :
    AddInduct checkSafety prodEnv.constants venv decl outEnv.constants
      H.installedVEnv := by
  apply AddInduct.intro H.block hdecl hcompile H.wf H.install
  · exact horigins
  · intro name ci hfind
    have hfindEnv : prodEnv.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?,
        hsourceAligned.map_wf.find?'_eq_find?]
      exact hfind
    have hout := H.installation.atomic.preservesSourceFind
      hsourceAligned.map_wf hfindEnv
    have houtWF := H.installation.atomic.targetMapWF
      hsourceAligned.map_wf
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hout
    exact hout
  · intro Haligned
    exact aligned_addDefEqs
      (H.installation.atomic.aligned (.projections (Aligned.addEliminators Haligned))) rules
  · exact H.installation.atomic.deltaConservative
      (.projections (Aligned.addEliminators hsourceAligned))
  · exact hprovenance.ofUnsafe
  · exact helim

/-- Replay a safe completed block into one observer model and construct the
corresponding concrete `AddInduct` witness. -/
theorem BlockCertificate.rebaseAddInductSafe
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid targetSafety prodEnv largerBase)
    (hbase : base <= largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      base outEnv.constants H.installedVEnv)
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate targetSafety prodEnv largerBase
        types ctors recursors rules outEnv largerOutBase,
      AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
        (largerOutBase.addDefEqRules rules) ∧
      H.installedVEnv ≤
        (largerOutBase.addDefEqRules rules) ∧
      Hlarger.projections = H.projections ∧
      Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.rebaseCertificate Hvalid DefinitionSafety.le_safe hbase hdecl
      hcompile Hreplay with
    ⟨largerOutBase, Hlarger, houtBase, hprojections, heliminators⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hblock := Hlarger.block_eq_of_projections_eq H hprojections heliminators
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    by
      rw [← hblock] at hcompile
      exact hcompile.mono hbase Hlarger.wf
  have helimLarger : VInductBlock.EliminatorsWF largerBase decl Hlarger.block :=
    (Hreplay.congr_block hblock).eliminatorsWF hdeclLarger.1
  have hprovenanceLarger := hprovenance.rebaseBlock hbase
    (VEnv.addDefEqRules_mono houtBase) H.install Hlarger.install rfl
  have hadd : AddInduct targetSafety prodEnv.constants largerBase decl
      outEnv.constants
        (largerOutBase.addDefEqRules rules) := by
    simpa [BlockCertificate.installedVEnv, hprojections] using
      Hlarger.addInduct hdeclLarger hcompileLarger horigins hprovenanceLarger Hvalid.tr.aligned
        helimLarger
  exact ⟨largerOutBase, Hlarger, hadd,
    VEnv.addDefEqRules_mono houtBase, hprojections, heliminators⟩

theorem BlockCertificate.hasPrimitives
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hprimitives : venv.HasPrimitives) :
    H.installedVEnv.HasPrimitives := by
  apply hasPrimitives_addDefEqs
  exact H.installation.recursorsAdded.hasPrimitives
    (H.installation.formation.hasPrimitives Hprimitives).addEliminators.addProjections

/-- Validate the completed staging trace from its source, for ordinary and
primitive formation alike.  The projection-stage well-formedness proof is part
of the trace, so callers do not have to reconstruct it from a separate
compilation witness. -/
theorem BlockCertificate.validCore
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv :=
  H.installation.validCore Hvalid

/-- Replay a complete inductive refinement in a larger safety-indexed model.
The fresh block supplies the source-installation facts that plain weakening
cannot preserve, while source well-formedness and compilation semantics are
transported from the original model. -/
theorem BlockCertificate.rebaseAddInduct
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate safety prodEnv largerBase types ctors
        recursors rules outEnv largerOutBase,
      Hlarger.projections = H.projections ∧
      VEnv.AddInduct largerBase decl Hlarger.installedVEnv ∧
      H.installedVEnv ≤ Hlarger.installedVEnv ∧
      Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.rebaseCertificate Hvalid hsafety hbase hdecl hcompile Hreplay with
    ⟨largerOutBase, Hlarger, houtBase, hprojections, heliminators⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hblock := Hlarger.block_eq_of_projections_eq H hprojections heliminators
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    by
      rw [← hblock] at hcompile
      exact hcompile.mono hbase Hlarger.wf
  have helimLarger : VInductBlock.EliminatorsWF largerBase decl Hlarger.block :=
    (Hreplay.congr_block hblock).eliminatorsWF hdeclLarger.1
  refine ⟨largerOutBase, Hlarger, hprojections, ?_, ?_, heliminators⟩
  · simpa [BlockCertificate.installedVEnv, hprojections] using
      VEnv.AddInduct.intro hdeclLarger hcompileLarger Hlarger.wf helimLarger Hlarger.install
  · exact VEnv.addDefEqRules_mono houtBase

/-- A batch whose production entries are all tagged unsafe supplies the
exact hidden-header certificate required by the safety-indexed extension. -/
theorem BlockCertificate.newFamiliesUnsafe
    (H : BlockCertificate .unsafe prodEnv unsafeBase types ctors recursors
      rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe) :
    NewFamiliesUnsafe prodEnv outEnv := by
  intro familyName familyInfo hfamily hfresh
  rcases H.installation.atomic.entryOrigin hwf hfamily with hold | hnew
  · rw [hfresh] at hold
    contradiction
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafety : (ConstantInfo.inductInfo familyInfo).safety =
        DefinitionSafety.unsafe := by
      rw [hinfo]
      exact hunsafe entry hentry
    cases h : familyInfo.isUnsafe
    · have heq : DefinitionSafety.safe = DefinitionSafety.unsafe := by
        simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial, h] using hsafety
      contradiction
    · rfl

/-- Constructor semantics for an unchanged observer of an unsafe block.
Every visible old family is transported through the production installation;
a genuinely new family is unsafe and hence cannot be visible to a partial or
safe observer. -/
theorem BlockCertificate.hiddenUnsafeConstructorTyping
    (H : BlockCertificate .unsafe prodEnv unsafeBase types ctors recursors
      rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : CtorParamsAgree
      observer prodEnv observerBase)
    (hobserver : observer ≠ .unsafe)
    (Hhidden : NewFamiliesUnsafe prodEnv outEnv) :
    CtorParamsAgree observer outEnv observerBase := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := H.installation.atomic
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.rebaseKernel
      (Hinstall.preservesSourceFind hwf C.lookup) VEnv.LE.rfl⟩
  · rcases hnew with ⟨_entry, _hentry, _hname, _hinfo⟩
    cases hold : prodEnv.find? familyName with
    | some oldInfo =>
      have hpreserved := Hinstall.preservesSourceFind hwf hold
      rw [hfamily] at hpreserved
      cases hpreserved
      rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
      exact ⟨C.rebaseKernel
        (Hinstall.preservesSourceFind hwf C.lookup) VEnv.LE.rfl⟩
    | none =>
      have hunsafe := Hhidden familyName familyInfo hfamily hold
      have hobserverUnsafe : observer ≤ DefinitionSafety.unsafe := by
        simpa [hunsafe] using hvisible
      have heq : observer = DefinitionSafety.unsafe :=
        DefinitionSafety.le_antisymm hobserverUnsafe
          DefinitionSafety.unsafe_le
      exact False.elim (hobserver heq)

/-- Lift one unsafe block installation to the three safety-indexed abstract
environments.  Partial and safe translation traces normally come from
ignoring the newly installed unsafe production constants; every other field
is derived from the block certificate and the source `VEnvs.WFCore`. -/
theorem BlockCertificate.extendUnsafeExact
    {ves : VEnvs}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WFCore prodEnv)
    (htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      H.installedVEnv)
    (htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial))
    (htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe))
    (hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      CtorParamsAgree .unsafe outEnv
        H.installedVEnv)
    (hinductiveProvenance : ∀ safety,
      InductFamiliesInstalled safety outEnv.constants
        (match safety with
        | .unsafe => H.installedVEnv
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe))
    (hheadersUnsafe : NewFamiliesUnsafe prodEnv outEnv) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .unsafe = H.installedVEnv := by
  apply Lean4Lean.VEnvs.WFCore.extendUnsafeExact wf
    H.installedVEnv
    htrUnsafe htrPartial htrSafe
  · exact H.hasPrimitives wf.hasPrimitives
  · exact hsafePrimitives
  · exact hclosed
  · exact hconstructorOwners
  · intro safety
    cases safety with
    | «unsafe» => exact hconstructorSemantics
    | «partial» =>
      exact H.hiddenUnsafeConstructorTyping
        (wf.tr (safety := .unsafe)).map_wf
        (wf.ctorParamsAgree (safety := .partial)) (by decide)
        hheadersUnsafe
    | safe =>
      exact H.hiddenUnsafeConstructorTyping
        (wf.tr (safety := .unsafe)).map_wf
        (wf.ctorParamsAgree (safety := .safe)) (by decide)
        hheadersUnsafe
  · exact hinductiveProvenance
  · exact VInductBlock.install_le H.install

/-- Reconstruct constructor semantics for one replay of a safe block.  Old
families are transported from the corresponding source safety model.  A new
family is necessarily safe because the original batch was checked at
`.safe`, so its already-completed output witness transports along the replay
monotonicity proof. -/
theorem BlockCertificate.replaySafeConstructorTyping
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hreplay : BlockCertificate observer prodEnv observerBase types ctors
      recursors rules outEnv replayBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : CtorParamsAgree
      observer prodEnv observerBase)
    (Hcompleted : CtorParamsAgree .safe outEnv
      H.installedVEnv)
    (hreplay : H.installedVEnv ≤ Hreplay.installedVEnv) :
    CtorParamsAgree observer outEnv
      Hreplay.installedVEnv := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := Hreplay.installation.atomic
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    have hlookup := Hinstall.preservesSourceFind hwf C.lookup
    have hle : observerBase ≤ Hreplay.installedVEnv :=
      VEnv.addEliminators_addProjections_le.trans (Hinstall.le.trans VEnv.addDefEqRules_le)
    exact ⟨C.rebaseKernel hlookup hle⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafe : .safe ≤ (ConstantInfo.inductInfo familyInfo).safety := by
      rw [hinfo]
      exact H.installation.atomic.entrySafety hentry
    have hsafe' : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hsafe
    have hfamilySafe : familyInfo.isUnsafe = false := by
      cases h : familyInfo.isUnsafe
      · rfl
      · have hsafeUnsafe : DefinitionSafety.safe ≤
            DefinitionSafety.unsafe := by simpa [h] using hsafe'
        have heq : DefinitionSafety.safe = DefinitionSafety.unsafe :=
          DefinitionSafety.le_antisymm hsafeUnsafe DefinitionSafety.unsafe_le
        contradiction
    have hsafeVisible : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simp [hfamilySafe, DefinitionSafety.le_rfl]
    rcases Hcompleted familyName familyInfo hfamily hsafeVisible i hi with ⟨C⟩
    exact ⟨C.mono hreplay⟩

/-- A safe executable block, ordinary or primitive, extends all three abstract
safety models.  Each model is replayed independently, while monotonicity of
the resulting family is recovered from the shared abstract block
installation.  For a primitive Bool/Nat block `HasPrimitives` is restored only
at the complete formation batch (`FormationInstallation.hasPrimitives`). -/
theorem BlockCertificate.extendSafeExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WFCore prodEnv) (htels : ∀ safety, CtorTelescopes safety prodEnv (ves.venv safety))
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      (ves.venv .safe) outEnv.constants H.installedVEnv)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      CtorParamsAgree .safe outEnv
        H.installedVEnv)
    (Hreplay : ∀ safety, VInductBlock.EliminatorsReplay (ves.venv safety) decl H.block) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) ∧
      H.installedVEnv ≤ ves'.venv .safe := by
  have valid (safety : DefinitionSafety) :
      CheckingEnv.Valid safety prodEnv (ves.venv safety) :=
    (wf.tr (safety := safety)).toCheckingValid
      (wf.hasPrimitives (safety := safety)) wf.safePrimitives
      wf.constructorOwners wf.projectionRegistryCoherent ((htels _))
  rcases H.rebaseAddInductSafe (valid .unsafe)
      (wf.mono DefinitionSafety.unsafe_le) hdecl hcompile horigins hprovenance
      (Hreplay .unsafe) with
    ⟨unsafeBase, Hunsafe, HunsafeAdd, hunsafeLE, hunsafeProj, hunsafeElim⟩
  rcases H.rebaseAddInductSafe (valid .partial)
      (wf.mono DefinitionSafety.le_safe) hdecl hcompile horigins hprovenance
      (Hreplay .partial) with
    ⟨partialBase, Hpartial, HpartialAdd, hpartialLE, hpartialProj, hpartialElim⟩
  rcases H.rebaseAddInductSafe (valid .safe) VEnv.LE.rfl
      hdecl hcompile horigins hprovenance (Hreplay .safe) with
    ⟨safeBase, Hsafe, HsafeAdd, hsafeLE, hsafeProj, hsafeElim⟩
  let pre : DefinitionSafety → VEnv
    | .unsafe => unsafeBase
    | .partial => partialBase
    | .safe => safeBase
  let next (safety : DefinitionSafety) :=
    (pre safety).addDefEqRules rules
  let cert : ∀ safety,
      BlockCertificate safety prodEnv (ves.venv safety) types ctors
        recursors rules outEnv (pre safety)
    | .unsafe => Hunsafe
    | .partial => Hpartial
    | .safe => Hsafe
  have certProjections : ∀ safety, (cert safety).projections = H.projections
    | .unsafe => hunsafeProj
    | .partial => hpartialProj
    | .safe => hsafeProj
  have certEliminators : ∀ safety, (cert safety).installation.eliminators = H.installation.eliminators
    | .unsafe => hunsafeElim
    | .partial => hpartialElim
    | .safe => hsafeElim
  let adds : ∀ safety,
      AddInduct safety prodEnv.constants (ves.venv safety) decl outEnv.constants
        (next safety)
    | .unsafe => HunsafeAdd
    | .partial => HpartialAdd
    | .safe => HsafeAdd
  let outputLE : ∀ safety,
      H.installedVEnv ≤ next safety
    | .unsafe => hunsafeLE
    | .partial => hpartialLE
    | .safe => hsafeLE
  have hprimitives : ∀ safety, (next safety).HasPrimitives := by
    intro safety
    simpa [next, BlockCertificate.installedVEnv, certProjections safety] using
      (cert safety).hasPrimitives (wf.hasPrimitives (safety := safety))
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] :=
    (Hsafe.validCore (valid .safe).toValidCore).safePrimitives
  have hsemantics : ∀ safety,
      CtorParamsAgree safety outEnv
        (next safety) := by
    intro safety
    have hreplay : H.installedVEnv ≤ (cert safety).installedVEnv := by
      simpa [next, BlockCertificate.installedVEnv, certProjections safety] using
        outputLE safety
    simpa [next, BlockCertificate.installedVEnv, certProjections safety] using
      H.replaySafeConstructorTyping (cert safety)
        (wf.tr (safety := safety)).map_wf
        (wf.ctorParamsAgree (safety := safety)) hconstructorSemantics
        hreplay
  have hmono : ∀ {safety safety'}, safety ≤ safety' →
      next safety' ≤ next safety := by
    intro safety safety' hle
    have hblock' := (cert safety').block_eq_of_projections_eq H
      (certProjections safety') (certEliminators safety')
    have hblock := (cert safety).block_eq_of_projections_eq H
      (certProjections safety) (certEliminators safety)
    have hi' : H.block.install (ves.venv safety') = some (next safety') := by
      simpa [next, BlockCertificate.installedVEnv, hblock', certProjections safety'] using
        (cert safety').install
    have hi : H.block.install (ves.venv safety) = some (next safety) := by
      simpa [next, BlockCertificate.installedVEnv, hblock, certProjections safety] using
        (cert safety).install
    exact VInductBlock.install_mono (wf.mono hle)
      hi' hi
  rcases wf.extendInductExact decl next adds H.installation.quotInit_eq
      hprimitives hsafePrimitives hclosed hconstructorOwners hsemantics hmono with
    ⟨ves', wf', hsourceLE, hexact⟩
  refine ⟨ves', wf', hsourceLE, ?_, ?_⟩
  rw [hexact .safe]
  exact (adds .safe).toVEnv
  rw [hexact .safe]
  exact outputLE .safe

/-- Install a certified inductive block directly into the concrete
environment-refinement judgment.  This is the abstract/executable seam used
by the inductive branch of declaration verification. -/
theorem BlockCertificate.trEnv'
    {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      venv outEnv.constants H.installedVEnv)
    (hsource : TrEnv' checkSafety prodEnv.constants quotInit venv)
    (helim : VInductBlock.EliminatorsWF venv decl H.block) :
    TrEnv' checkSafety outEnv.constants quotInit
      H.installedVEnv :=
  .induct hdecl
    (H.addInduct hdecl hcompile horigins hprovenance hsource.aligned helim) hsource

/-- Unsafe inductives extend only the unsafe abstract model; partial and safe
models replay the concrete additions through `TrEnv'.ignore`. -/
theorem BlockCertificate.extendUnsafeOfHiddenExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WFCore prodEnv) (htels : ∀ safety, CtorTelescopes safety prodEnv (ves.venv safety))
    (hdecl : decl.WF (ves.venv .unsafe))
    (hcompile : decl.CompilesTo (ves.venv .unsafe) H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      (ves.venv .unsafe) outEnv.constants H.installedVEnv)
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      CtorParamsAgree .unsafe outEnv
        H.installedVEnv)
    (helim : VInductBlock.EliminatorsWF (ves.venv .unsafe) decl H.block) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnv.AddInduct (ves.venv .unsafe) decl (ves'.venv .unsafe) ∧
      H.installedVEnv ≤ ves'.venv .unsafe := by
  have validUnsafe : CheckingEnv.Valid .unsafe prodEnv
      (ves.venv .unsafe) :=
    (wf.tr (safety := .unsafe)).toCheckingValid
      (wf.hasPrimitives (safety := .unsafe)) wf.safePrimitives
      wf.constructorOwners wf.projectionRegistryCoherent ((htels _))
  have hiddenPartial : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.partial ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have hiddenSafe : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.safe ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      H.installedVEnv := by
    rw [H.installation.quotInit_eq]
    exact H.trEnv' hdecl hcompile horigins hprovenance
      (wf.tr (safety := .unsafe)) helim
  have htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial) := by
    rw [H.installation.quotInit_eq]
    apply H.installation.trEnvIgnore
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · exact wf.tr (safety := .partial)
  have htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe) := by
    rw [H.installation.quotInit_eq]
    apply H.installation.trEnvIgnore
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · exact wf.tr (safety := .safe)
  have hheadersUnsafe := H.newFamiliesUnsafe
    (wf.tr (safety := .unsafe)).map_wf hunsafe
  have haddUnsafe : AddInduct .unsafe prodEnv.constants
      (ves.venv .unsafe) decl outEnv.constants
      H.installedVEnv :=
    H.addInduct hdecl hcompile horigins hprovenance
      (wf.tr (safety := .unsafe)).aligned helim
  have houtMapWF := H.installation.atomic.targetMapWF
    (wf.tr (safety := .unsafe)).map_wf
  have hiddenProvenance (observer : DefinitionSafety)
      (hobserver : observer ≠ .unsafe) :
      InductFamiliesInstalled observer outEnv.constants
        (ves.venv observer) := by
    apply VerifyInductive.InductFamiliesInstalled.rebaseHidden
      (wf.inductFamiliesInstalled (safety := observer))
      haddUnsafe.preservesSourceFind
    intro familyName familyInfo hfamily hfresh
    have hfamilyEnv : outEnv.find? familyName =
        some (.inductInfo familyInfo) := by
      rw [Lean.Kernel.Environment.find?, houtMapWF.find?'_eq_find?]
      exact hfamily
    have hfreshEnv : prodEnv.find? familyName = none := by
      rw [Lean.Kernel.Environment.find?,
        (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
      exact hfresh
    have hunsafeFamily := hheadersUnsafe familyName familyInfo
      hfamilyEnv hfreshEnv
    have hobserverNotLE : ¬ observer ≤ DefinitionSafety.unsafe := by
      intro hle
      exact hobserver (DefinitionSafety.le_antisymm hle
        DefinitionSafety.unsafe_le)
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, hunsafeFamily] using hobserverNotLE
  have hinductiveProvenance : ∀ safety,
      InductFamiliesInstalled safety outEnv.constants
        (match safety with
        | .unsafe => H.installedVEnv
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe)
    | .unsafe => InductFamiliesInstalled.addInduct
        (wf.inductFamiliesInstalled (safety := .unsafe)) haddUnsafe
    | .partial => hiddenProvenance .partial (by decide)
    | .safe => hiddenProvenance .safe (by decide)
  rcases H.extendUnsafeExact wf htrUnsafe htrPartial htrSafe
      (H.validCore validUnsafe.toValidCore).safePrimitives hclosed hconstructorOwners
      hconstructorSemantics hinductiveProvenance hheadersUnsafe with
    ⟨ves', wf', hle, hexact⟩
  refine ⟨ves', wf', hle, ?_, hexact ▸ VEnv.LE.rfl⟩
  rw [hexact]
  exact haddUnsafe.toVEnv



def GeneratedRecursors.toBlockCertificate
    (projections : List VProjectionEntry)
    (installation : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (H : GeneratedRecursors safety
      ((installation.venvCtors.addEliminators installation.eliminators).addProjections projections)
      lparams elimLevel c stats
      indTypes recInfos recursors)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (htypes : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv)
    (hctors : ∀ ci ∈ ctors.map Prod.snd,
      ci.toVConstant.WF installation.venvTypes)
    (hrules : ∀ df ∈ rules, df.WF outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := projections
  installation := installation
  typesWF := htypes
  ctorsWF := hctors
  recursorsWF := H.recursorsWF Hc Hbindings Hparams
  rulesWF := hrules

theorem ConstructorCheck.typesWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
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

theorem ConstructorCheck.ctorsWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
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

def RecursorCheck.installation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    BlockInstallation c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries decl.projectionEntries outEnv H.outVEnv where
  envTypes := R.headerEnv
  venvTypes := R.headerVEnv
  envCtors := ctorEnv
  venvCtors := R.ctorVEnv
  formation := R.installation
  eliminators := R.eliminators
  casesWF := R.casesWF
  projectedWF := R.projectedWF
  recursorsAdded := by
    rw [← R.contextVEnv]
    simpa [H.localExtends.safety_eq, H.localExtends.env_eq] using H.installed

def RecursorCheck.blockCertificate
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    BlockCertificate c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries rules outEnv H.outVEnv := by
  let Hgenerated : GeneratedRecursors c.safety
      ((R.ctorVEnv.addEliminators R.eliminators).addProjections decl.projectionEntries) c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
    rw [← R.contextVEnv]
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  exact Hgenerated.toBlockCertificate decl.projectionEntries H.installation
    H.localWF H.bindings H.params R.typesWF R.ctorsWF hrules

@[simp] theorem RecursorCheck.blockCertificate_projections
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    (H.blockCertificate rules hrules).projections = decl.projectionEntries := by
  rfl

/-- The completed block registers the declaration's certified case eliminators. -/
theorem RecursorCheck.blockEliminatorsWF
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    VInductBlock.EliminatorsWF sourceEnv decl (H.blockCertificate rules hrules).block :=
  R.eliminatorsWF.congr_block R.headerValues R.constructorValues rfl rfl

/-- The completed block's case eliminators are certified over every larger environment in
which its families and constructors install. -/
theorem RecursorCheck.blockEliminatorsReplay
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) {env' : VEnv} (hle : sourceEnv ≤ env') :
    VInductBlock.EliminatorsReplay env' decl (H.blockCertificate rules hrules).block :=
  R.eliminatorsCertified.replay hle (fun _ h => h.elim) R.headerValues R.constructorValues rfl rfl

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem RecursorCheck.minorPrefixLength_eq
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (owner : Nat)
    (howner : owner ≤ H.recInfos.size) :
    ((H.recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < H.recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos H.recInfos owner hrec,
        getElem!_pos indTypes owner hind] using H.minorCounts owner hrec

theorem RecursorCheck.outVEnvWF
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : H.outVEnv.WF := by
  have hvalid : CheckingEnv.ValidCore H.localContext.safety
      H.localContext.env
        R.context.venv := by
    rw [H.localExtends.safety_eq, H.localExtends.env_eq]
    exact R.context.checking.toValidCore
  exact (H.installed.validCore hvalid).tr.wf

/-- Recursor installation preserves the constructor semantics established at
the completed formation boundary. -/
theorem RecursorCheck.ctorParamsAgree
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (Hsource : CtorParamsAgree
      safety c.env sourceEnv) :
    CtorParamsAgree safety outEnv H.outVEnv := by
  apply H.installed.preservesConstructorTyping
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · rw [H.localExtends.env_eq]
    exact (R.ctorParamsAgree Hsource).mono R.ctorLE
  · exact H.generated.nonInductive

theorem RecursorCheck.inductInfosFromDecl
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants decl := by
  have hctorOrigins : InductInfosFromDecl c.env.constants
      H.localContext.env.constants decl := by
    simpa [H.localExtends.env_eq] using R.inductInfosFromDecl
  apply InductInfosFromDecl.addConstants hctorOrigins H.installed
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · exact H.generated.nonInductive

theorem RecursorCheck.constructorTyping
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (Hsource : CtorParamsAgree
      safety c.env sourceEnv) (rules : List VDefEq) :
    CtorParamsAgree safety outEnv
      (H.outVEnv.addDefEqRules rules) :=
  (H.ctorParamsAgree Hsource).mono
    VEnv.addDefEqRules_le

theorem RecursorCheck.generatedTelescopeTranslations
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    RecursorTypeTelescopes
      R.context.venv stats
      H.recInfos H.entries := by
  intro ownerIdx hentry
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [← H.generated.length]
    exact hentry
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    ownerIdx hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  refine ⟨E.info, E.source_eq, ?_⟩
  exact E.telescopeTranslation selections hrecInfo hnoalias

theorem RecursorCheck.generatedRecursorCommonPrefixBinderDomainAt
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (i : Nat)
    (hi : i < stats.params.size +
      (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size)
    {domain₁ domain₂ : Expr}
    (Hbinder₁ : Expr.ForallBinderAt
      (H.generated.entry owner₁ howner₁).info.type i domain₁)
    (Hbinder₂ : Expr.ForallBinderAt
      (H.generated.entry owner₂ howner₂).info.type i domain₂) :
    domain₁ = domain₂ := by
  have hrecInfo₁ : owner₁ < H.recInfos.size := by
    simpa [H.generated.length] using howner₁
  have hrecInfo₂ : owner₂ < H.recInfos.size := by
    simpa [H.generated.length] using howner₂
  let E₁ := H.generated.entry owner₁ howner₁
  let E₂ := H.generated.entry owner₂ howner₂
  let S₁ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₁ hrecInfo₁
  let S₂ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₂ hrecInfo₂
  have hnoalias₁ : S₁.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₁ hrecInfo₁
  have hnoalias₂ : S₂.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₂ hrecInfo₂
  by_cases hparam : i < stats.params.size
  · rcases H.params.declarationAt H.localWF i hparam with ⟨D⟩
    have Hcanonical₁ := S₁.parameterBinderAt hnoalias₁ D
    have Hcanonical₂ := S₂.parameterBinderAt hnoalias₂ D
    dsimp only at Hcanonical₁ Hcanonical₂
    rw [← E₁.type] at Hcanonical₁
    rw [← E₂.type] at Hcanonical₂
    exact (Hbinder₁.unique Hcanonical₁).trans
      (Hbinder₂.unique Hcanonical₂).symm
  · let motiveIdx := i - stats.params.size
    by_cases hmotive : motiveIdx < (H.recInfos.map (·.motive)).size
    · rcases H.bindings.motives.declarationAt H.localWF motiveIdx hmotive with
        ⟨D⟩
      have Hcanonical₁ := S₁.motiveBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.motiveBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size + motiveIdx = i := by
        dsimp [motiveIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm
    · let minorIdx := i - stats.params.size -
        (H.recInfos.map (·.motive)).size
      have hminor : minorIdx <
          (H.recInfos.flatMap (·.minors)).size := by
        dsimp [motiveIdx, minorIdx] at hmotive ⊢
        omega
      rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx hminor with
        ⟨D⟩
      have Hcanonical₁ := S₁.minorBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.minorBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size +
          (H.recInfos.map (·.motive)).size + minorIdx = i := by
        dsimp [minorIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm

end VerifyInductive
end Lean4Lean
