import Lean4Lean.Verify.Inductive.Primitive.BatchInstallation
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two sound installation histories that can reach the completed
constructor boundary.  Ordinary declarations preserve validity after every
constant; primitive Bool/Nat declarations instead regain it only after the
whole header/constructor batch, which is why the primitive case records that
the batch is exactly the canonical Bool or Nat batch and that its primitive
production names are safe and universe-monomorphic. -/
inductive CompletedFormationInstallation (safety : DefinitionSafety)
    (sourceEnv : Environment) (sourceVEnv : VEnv)
    (headerEntries : List (ConstantInfo × VConstVal))
    (headerEnv : Environment) (headerVEnv : VEnv)
    (ctorEntries : List (ConstantInfo × VConstVal))
    (ctorEnv : Environment) (ctorVEnv : VEnv) : Prop
  | ordinary :
    AddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv
  | primitive :
    AtomicAddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AtomicAddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    (headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd = primitiveBoolConstants ∨
      headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd = primitiveNatConstants) ->
    (∀ entry ∈ headerEntries ++ ctorEntries,
      Kernel.Environment.primitives.contains entry.1.name →
      entry.1.safety = .safe ∧ entry.1.levelParams = []) ->
    CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv

def CompletedFormationInstallation.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : CompletedFormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    CompletedFormationInstallation safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv := by
  cases H with
  | ordinary Hheaders Hctors =>
      exact .ordinary (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
  | primitive Hheaders Hctors hconstants hsafe =>
      exact .primitive (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
        hconstants hsafe

theorem CompletedFormationInstallation.headerLE
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv <= headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.le
  | primitive Htypes _ _ _ => exact Htypes.le

theorem CompletedFormationInstallation.constructorLE
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv <= ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.le
  | primitive _ Hctors _ _ => exact Hctors.le

theorem CompletedFormationInstallation.headerAbstract
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv.addConstVals (headerEntries.map Prod.snd) = some headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.abstract
  | primitive Htypes _ _ _ => exact Htypes.abstract

theorem CompletedFormationInstallation.constructorAbstract
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv.addConstVals (ctorEntries.map Prod.snd) = some ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.abstract
  | primitive _ Hctors _ _ => exact Hctors.abstract

/-- The complete formation endpoint always carries the local checker
invariant. In the primitive case the header-only prefix is used only as a
`CheckingEnv`, never as `CheckingEnv.Valid`. -/
theorem CompletedFormationInstallation.checking
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : CheckingEnv safety sourceEnv sourceVEnv) :
    CheckingEnv safety ctorEnv ctorVEnv := by
  cases H with
  | ordinary Htypes Hctors =>
      exact (AtomicAddConstants.ofAddConstants Hctors).checking
        ((AtomicAddConstants.ofAddConstants Htypes).checking Hsource)
  | primitive Htypes Hctors _ _ =>
      exact Hctors.checking (Htypes.checking Hsource)

theorem CompletedFormationInstallation.quotInit_eq
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    ctorEnv.quotInit = sourceEnv.quotInit := by
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq
  | primitive Htypes Hctors _ _ =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq

/-- Replay a complete formation prefix in a larger abstract environment.
Primitive headers and constructors are replayed with only `CheckingEnv`; the
primitive invariant is not asserted at the invalid header-only intermediate
state. -/
theorem CompletedFormationInstallation.rebase
    (H : CompletedFormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hvalid : CheckingEnv safety sourceEnv largerSource)
    (hsafety : safety <= checkSafety)
    (hsource : sourceVEnv <= largerSource) :
    exists largerHeader largerCtors,
      Nonempty (CompletedFormationInstallation safety sourceEnv largerSource
        headerEntries headerEnv largerHeader ctorEntries ctorEnv largerCtors) /\
      headerVEnv <= largerHeader /\ ctorVEnv <= largerCtors := by
  cases H with
  | ordinary Htypes Hctors =>
      rcases Htypes.rebase Hvalid hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.checking Hvalid) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.ordinary Htypes' Hctors'⟩, hheader, hctors⟩
  | primitive Htypes Hctors hconstants hsafe =>
      rcases Htypes.rebase Hvalid hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.checking Hvalid) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.primitive Htypes' Hctors' hconstants hsafe⟩, hheader, hctors⟩

theorem CompletedFormationInstallation.headerMapWF
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF) : headerEnv.constants.WF := by
  cases H with
  | ordinary Htypes _ => exact Htypes.targetMapWF hwf
  | primitive Htypes _ _ _ => exact Htypes.targetMapWF hwf

/-- A retained header entry is visible at the completed constructor endpoint
for both ordinary and atomic primitive histories. -/
theorem CompletedFormationInstallation.findHeaderEntry
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hentry : (info, value) ∈ headerEntries) :
    ctorEnv.find? info.name = some info := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)
  | primitive Htypes Hctors _ _ =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)

/-- Every constant of the completed constructor environment is old or an installed entry. -/
theorem CompletedFormationInstallation.entryOrigin
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : ctorEnv.find? name = some found) :
    sourceEnv.find? name = some found ∨ (∃ e ∈ headerEntries, found = e.1) ∨
      ∃ e ∈ ctorEntries, found = e.1 := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
    rcases (AtomicAddConstants.ofAddConstants Hctors).entryOrigin hheaderWF hfind with
      h | ⟨e, he, -, rfl⟩
    · rcases (AtomicAddConstants.ofAddConstants Htypes).entryOrigin hwf h with
        h | ⟨e, he, -, rfl⟩
      · exact .inl h
      · exact .inr (.inl ⟨e, he, rfl⟩)
    · exact .inr (.inr ⟨e, he, rfl⟩)
  | primitive Htypes Hctors _ _ =>
    rcases Hctors.entryOrigin hheaderWF hfind with h | ⟨e, he, -, rfl⟩
    · rcases Htypes.entryOrigin hwf h with h | ⟨e, he, -, rfl⟩
      · exact .inl h
      · exact .inr (.inl ⟨e, he, rfl⟩)
    · exact .inr (.inr ⟨e, he, rfl⟩)

/-- The header and constructor prefix as one atomic lockstep batch, for either
installation history. -/
theorem CompletedFormationInstallation.atomic
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    AtomicAddConstants safety sourceEnv sourceVEnv (headerEntries ++ ctorEntries)
      ctorEnv ctorVEnv := by
  cases H with
  | ordinary Htypes Hctors =>
      exact (AtomicAddConstants.ofAddConstants Htypes).append
        (AtomicAddConstants.ofAddConstants Hctors)
  | primitive Htypes Hctors _ _ => exact Htypes.append Hctors

/-- The completed formation prefix restores `HasPrimitives`: ordinary
installation never touches a primitive name, and a primitive batch is the
complete canonical Bool or Nat bootstrap. -/
theorem CompletedFormationInstallation.hasPrimitives
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : sourceVEnv.HasPrimitives) : ctorVEnv.HasPrimitives := by
  cases H with
  | ordinary Htypes Hctors => exact Hctors.hasPrimitives (Htypes.hasPrimitives Hsource)
  | primitive Htypes Hctors hconstants _ =>
      have hadd := VEnv.addConstVals_append Htypes.abstract Hctors.abstract
      rcases hconstants with hbool | hnat
      · rw [hbool] at hadd
        exact VEnv.HasPrimitives.addBoolBootstrap Hsource hadd
      · rw [hnat] at hadd
        exact VEnv.HasPrimitives.addNatBootstrap Hsource hadd

/-- The completed formation endpoint carries the local checking invariants,
for both installation histories. -/
theorem CompletedFormationInstallation.validCore
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : CheckingEnv.ValidCore safety sourceEnv sourceVEnv) :
    CheckingEnv.ValidCore safety ctorEnv ctorVEnv := by
  have hprimitives := H.hasPrimitives Hsource.hasPrimitives
  have hchecking := H.checking Hsource.tr
  cases H with
  | ordinary Htypes Hctors => exact Hctors.validCore (Htypes.validCore Hsource)
  | primitive Htypes Hctors _ hsafe =>
      exact ⟨hchecking, hprimitives,
        (Htypes.append Hctors).safePrimitives Hsource.tr.map_wf
          Hsource.safePrimitives hsafe⟩

theorem InductiveHeaderEntries.not_ctor (H : InductiveHeaderEntries infos entries) :
    ∀ e ∈ entries, ∀ info : ConstructorVal, e.1 ≠ .ctorInfo info := by
  induction H with
  | nil => simp
  | cons _ ih =>
    intro e he info heq
    rcases List.mem_cons.mp he with rfl | he
    · cases heq
    · exact ih e he info heq

theorem ConstructorListEntries.mem_info
    {mkInfo : Nat → Constructor → ConstructorVal}
    (H : ConstructorListEntries mkInfo start ctors entries) :
    ∀ e ∈ entries, ∃ ctor ∈ ctors, ∃ i, e.1 = .ctorInfo (mkInfo i ctor) := by
  induction H with
  | nil => simp
  | @cons start ctors tail ctor value _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨ctor, List.mem_cons_self, _, rfl⟩
    · obtain ⟨c, hc, i, h⟩ := ih e he
      exact ⟨c, List.mem_cons_of_mem _ hc, i, h⟩

theorem ConstructorTypeEntries.mem_info
    {mkInfo : InductiveType → Nat → Constructor → ConstructorVal}
    (H : ConstructorTypeEntries mkInfo owners entries) :
    ∀ e ∈ entries, ∃ owner ∈ owners, ∃ ctor ∈ owner.ctors, ∃ i,
      e.1 = .ctorInfo (mkInfo owner i ctor) := by
  induction H with
  | nil => simp
  | cons Hhead _ ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨c, hc, i, h⟩ := Hhead.mem_info e he
      exact ⟨_, List.mem_cons_self, c, hc, i, h⟩
    · obtain ⟨o, ho, c, hc, i, h⟩ := ih e he
      exact ⟨o, List.mem_cons_of_mem _ ho, c, hc, i, h⟩

/-- Stable input boundary for recursor generation.  It contains only facts
available after every constructor is installed and the final checking context
is valid.  No field requires a valid header-only context. -/
structure CompletedConstructorPhases (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool) (depth : Nat)
    (sourceEnv : VEnv) (indTypes : Array InductiveType)
    (ctorEnv : Environment) extends
    ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes where
  headerEnv : Environment
  headerEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  headerValues : headerEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  context : ContextWF { c with env := ctorEnv }
  contextMLCtx : context.mlctx = headerMLCtx
  checked : CheckedConstructorCertificate sourceEnv decl headerVEnv
    params
  parameterPrefixes : CheckedRecursorParameterPrefixes stats indTypes
  ownerNormalForms : CheckedConstructorOwnerNormalForms stats indTypes
  /-- The telescope certificates of the source constructor types. -/
  telescopes : SourceCtorsCertified headerVEnv c.lparams indTypes.toList
  headerSourceAligned : exists numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList headerEntries
  constructorSourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList constructorEntries
  constructorProduction : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    exists info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  constructorNonInductive : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    forall value : InductiveVal,
      entry.1 ≠ ConstantInfo.inductInfo value
  /-- The declaration's certified case eliminator, registered over the constructors. -/
  eliminators : List (Name × InductiveSignature.CaseSchema)
  eliminatorsWF : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock eliminators)
  eliminatorsCertified : decl.CaseEliminators sourceEnv (fun _ => False) eliminators
  eliminatorsOwn : decl.OwnCaseEliminators sourceEnv eliminators
  /-- The eliminators are those of a constructor boundary of the declaration. -/
  eliminatorsBoundary : ∃ B : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv
    indTypes, eliminators = B.caseEliminators ∧ B.params = params ∧
      B.parameterScope = parameterScope
  /-- The retained checking context carries the declaration's case eliminator and projection
  entries: every checker run after the constructor stage happens in this environment. -/
  contextVEnv : context.venv =
    (ctorVEnv.addEliminators eliminators).addProjections decl.projectionEntries
  installation : CompletedFormationInstallation c.safety c.env sourceEnv
    headerEntries headerEnv headerVEnv constructorEntries ctorEnv ctorVEnv
  productionInductiveOrigins :
    ProductionInductiveOrigins c.env.constants ctorEnv.constants decl
  constructorSemantics : forall {safety},
    InductiveConstructorsSemanticallyCoherent safety c.env sourceEnv ->
    InductiveConstructorsSemanticallyCoherent safety ctorEnv ctorVEnv

/-- Every constructor of the completed constructor environment is old, or a new constructor of
the declaration, with the declaration's safety flag and a certified type. -/
theorem CompletedConstructorPhases.ctorOrigin
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hfind : ctorEnv.find? name = some (.ctorInfo ci)) :
    c.env.find? name = some (.ctorInfo ci) ∨
      (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt R.headerVEnv ci) := by
  rcases R.installation.entryOrigin R.sourceContext.checking.tr.map_wf hfind with
    h | ⟨e, he, heq⟩ | ⟨e, he, heq⟩
  · exact .inl h
  · obtain ⟨_, hH⟩ := R.headerSourceAligned
    exact absurd heq.symm (hH.not_ctor e he ci)
  · obtain ⟨owner, howner, ctor, hctor, i, he1⟩ :=
      R.constructorSourceAligned.mem_info e he
    rw [he1] at heq
    cases heq
    refine .inr ⟨by simp [AddInductive.constructorInfo], ?_⟩
    obtain ⟨T, hT⟩ := R.telescopes owner howner ctor hctor
    exact ⟨T, by simpa [AddInductive.constructorInfo] using hT⟩

/-- The constructor-complete abstract environment admits the exact projection
prefix of this declaration as a genuine staged well-formed environment. -/
theorem CompletedConstructorPhases.projectedWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ((R.ctorVEnv.addEliminators R.eliminators).addProjections decl.projectionEntries).WF := by
  rw [← R.contextVEnv]
  exact R.context.checking.tr.wf

/-- The constructor-complete abstract environment with the declaration's case eliminators is
well formed. -/
theorem CompletedConstructorPhases.casesWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    (R.ctorVEnv.addEliminators R.eliminators).WF := by
  have hsourceWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  exact R.eliminatorsWF.casesWF hsourceWF
    (Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF R.core hsourceWF)
    R.core.typesAdded R.core.ctorsAdded

theorem CompletedConstructorPhases.ctorLE
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.ctorVEnv ≤ R.context.venv := by
  rw [R.contextVEnv]
  exact VEnv.addEliminators_addProjections_le

/-- The exact header/constructor installation trace preserves the persistent
constructor-owner invariant.  New constructor metadata obtains its owner from
the family-major constructor trace, and that owner's header is found in the
matching generated-header trace. -/
theorem CompletedConstructorPhases.constructorOwnersPresent
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hsource : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent ctorEnv := by
  rcases R.headerSourceAligned with ⟨numNested, Hheaders⟩
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, R.materialized.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  apply R.installation.atomic.constructorOwnersPresent
    R.sourceContext.checking.tr.map_wf hsource
  intro entry hentry info hinfo
  rcases List.mem_append.mp hentry with hheader | hctor
  · rcases Hheaders.originInfo hheader with ⟨familyInfo, _, heq⟩
    rw [heq] at hinfo
    cases hinfo
  · rcases R.constructorSourceAligned.ownerOfEntry hctor with
      ⟨owner, howner, installedInfo, hentryInfo, hownerName⟩
    have hinfoEq : info = installedInfo := by
      rw [hentryInfo] at hinfo
      exact ConstantInfo.ctorInfo.inj hinfo.symm
    subst info
    rcases inductiveTypeInfos_owner stats nparams indTypes numNested isUnsafe
        c.lparams hindicesSize howner with ⟨ownerInfo, hownerInfo, hname⟩
    rcases Hheaders.findInfo hownerInfo with ⟨value, hentry⟩
    refine ⟨ownerInfo, ?_⟩
    rw [hownerName, ← hname]
    exact R.installation.findHeaderEntry
      R.sourceContext.checking.tr.map_wf hentry

/-- Transport the retained header materialization to the final valid
constructor environment only when recursor checking begins. -/
def CompletedConstructorPhases.materializedFinal
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      R.context.venv c.lparams R.context.mlctx.vlctx stats decl depth := by
  let M := R.materialized.mono (R.installation.constructorLE.trans R.ctorLE)
  exact {
    headers := M.headers
    isNotZero := M.isNotZero
    commonLevel := M.commonLevel
    levels := M.levels
    levelParams := M.levelParams
    uvars := M.uvars
    consts := M.consts
    indices := M.indices
    params := by simpa only [R.contextMLCtx] using M.params
    paramFVars := M.paramFVars
    parameterScope := M.parameterScope
    normalizedSources := M.normalizedSources
    normalizedShapes := M.normalizedShapes
    ambientScope := M.ambientScope
    scopeDecomposition := by
      simpa only [R.contextMLCtx] using M.scopeDecomposition
    ambientLength := M.ambientLength
    cachedScope := M.cachedScope
    runtimeScope := by simpa only [R.contextMLCtx] using M.runtimeScope
    paramsContext := M.paramsContext
    narrowParams := M.narrowParams }

theorem CompletedConstructorPhases.materializedFinal_parameterScope
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.materializedFinal.parameterScope = R.parameterScope := by
  simp [CompletedConstructorPhases.materializedFinal,
    checkInductiveTypes.loopInd.MaterializedHeaderResult.mono,
    R.materializedParameterScope]

/-- Embed the ordinary formation result into the completed constructor
boundary while retaining its staged installation traces. -/
def ConstructorPhasesResult.completed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H ctorEnv) :
    CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceMaterialized := H.sourceMaterialized
  context := R.declared.context
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.materialized.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  materialized := H.materialized
  materializedParams := H.headerParams
  materializedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  telescopes := R.telescopes
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorProduction := R.declared.production
  constructorNonInductive := R.declared.nonInductive
  ctorVEnv := R.declared.venvCtors
  eliminators := R.declared.eliminators
  eliminatorsWF := R.declared.eliminatorsWF
  eliminatorsCertified := R.declared.eliminatorsCertified
  eliminatorsOwn := R.declared.eliminatorsOwn
  eliminatorsBoundary := R.declared.eliminatorsBoundary
  contextVEnv := R.declared.contextVEnv
  installation := .ordinary H.installed R.declared.installed
  formation := R.formation
  core := R.core
  productionInductiveOrigins := R.productionInductiveOrigins
  constructorSemantics := fun Hsource => R.constructorSemantics Hsource

/-- The constructor boundary of a completed primitive formation run. -/
noncomputable def PrimitiveConstructorPhasesResult.boundary
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorPhasesResult H ctorEnv) :
    ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes where
  headerVEnv := H.context.venv
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceMaterialized := H.sourceMaterialized
  headerMLCtx := H.context.mlctx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.materialized.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  materialized := H.materialized
  materializedParams := H.headerParams
  materializedParameterScope := rfl
  constructorTails := R.constructorTails
  ctorVEnv := R.declared.venvCtors
  formation := R.formation
  core := R.core

/-- The primitive constructor context, with the declaration's case eliminators and
projections. -/
theorem PrimitiveConstructorPhasesResult.projectedChecking
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorPhasesResult H ctorEnv) :
    CheckingEnv.Valid c.safety ctorEnv
      ((R.declared.venvCtors.addEliminators R.boundary.caseEliminators).addProjections
        decl.projectionEntries) := by
  have hchecking : CheckingEnv.Valid c.safety ctorEnv R.declared.venvCtors := by
    rw [← R.declared.contextVEnv]
    exact R.declared.context.checking
  exact (hchecking.addEliminators R.boundary.casesWF).addProjections R.boundary.projectedWF

/-- The atomic primitive formation pipeline embeds into the same completed
recursor boundary. -/
noncomputable def PrimitiveConstructorPhasesResult.completed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorPhasesResult H ctorEnv) :
    CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceMaterialized := H.sourceMaterialized
  context := R.declared.context.withEnv R.projectedChecking (by
    rw [R.declared.contextVEnv]
    exact VEnv.addEliminators_addProjections_le)
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.materialized.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  materialized := H.materialized
  materializedParams := H.headerParams
  materializedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  telescopes := R.telescopes
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorProduction := R.declared.production
  constructorNonInductive := R.declared.nonInductive
  ctorVEnv := R.declared.venvCtors
  eliminators := R.boundary.caseEliminators
  eliminatorsWF := R.boundary.caseEliminatorsWF
  eliminatorsCertified := R.boundary.caseEliminatorsCertified
  eliminatorsOwn := R.boundary.caseEliminatorsOwn
  eliminatorsBoundary := ⟨R.boundary, rfl, rfl, rfl⟩
  contextVEnv := rfl
  installation := .primitive H.installed R.declared.installed
    (by simpa [H.values, R.declared.values] using R.declared.primitiveConstants)
    R.declared.safeEntries
  formation := R.formation
  core := R.core
  productionInductiveOrigins := R.productionInductiveOrigins
  constructorSemantics := fun Hsource => R.constructorSemantics Hsource

end VerifyInductive
end Lean4Lean
