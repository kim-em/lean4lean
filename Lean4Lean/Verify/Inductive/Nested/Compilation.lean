import Lean4Lean.Verify.Inductive.Nested.Restoration

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Installing an operationally restored auxiliary recursor advances the
independent auxiliary-name certificate. Translation identifies the production
`RecursorVal` name with the abstract constant name; no semantic claim about
its restored rules is hidden in this naming step. -/
theorem AuxiliaryRestorationPrefix.pushRestoredRecursor
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName oldInfo newInfo)
    (Htr : TrConstVal safety trEnv (.recInfo newInfo) recursor)
    (hnewName : newRecName =
      (decl.recursorName main).appendIndexAfter (recursors.length + 1)) :
    AuxiliaryRestorationPrefix decl block main
      (recursors ++ [recursor]) rules := by
  apply H.pushRecursor
  calc
    recursor.name = newInfo.name := Htr.2.symm
    _ = newRecName := Hrestore.name
    _ = (decl.recursorName main).appendIndexAfter
        (recursors.length + 1) := hnewName

/-- Restored-rule guardedness is deliberately supplied independently of
`RuleRestoration`: the latter is a syntactic executable refinement, whereas
this premise is the semantic fact required by `NestedCompilation`. -/
theorem AuxiliaryRestorationPrefix.appendRestoredRules
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (Hrestore : RulesRestoration result prodEnv auxRec oldRecName newRecName
      sourceRules restoredRules)
    (htranslated : abstractRules.length = restoredRules.length)
    (hguarded : ∀ i (hsource : i < sourceRules.length)
      (hrestored : i < restoredRules.length)
      (habstract : i < abstractRules.length),
      RuleRestoration result prodEnv auxRec oldRecName newRecName
        sourceRules[i] restoredRules[i] →
      ∃ fieldVars, abstractRules[i].rhs.GuardedIota
        (block.recursors.map (·.name)) fieldVars 0) :
    AuxiliaryRestorationPrefix decl block main recursors
      (rules ++ abstractRules) := by
  apply H.appendRules
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hrestored : i < restoredRules.length := by
    rw [← htranslated]
    simpa using hi
  have hsource : i < sourceRules.length := by
    rw [← Hrestore.length]
    exact hrestored
  have Hentry := Hrestore.entry i hsource hrestored
  exact hguarded i hsource hrestored hi Hentry

/-- Independent semantic interpretation of one operational auxiliary
recursor step. The syntactic restoration relation comes from the executable
trace; translation, sequential naming, and guardedness are supplied here. -/
structure RestoredAuxiliaryStepSemantics
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv)
    (priorRecursors : List VConstVal) where
  recursor : VConstVal
  rules : List VDefEq
  translated : TrConstVal safety trEnv
    (.recInfo Hstep.restored.newInfo) recursor
  sequentialName : Hstep.restored.newRecName =
    (decl.recursorName main).appendIndexAfter (priorRecursors.length + 1)
  rulesLength : rules.length = Hstep.restored.newInfo.rules.length
  guarded : ∀ i (hsource : i < Hstep.oldInfo.rules.length)
    (hrestored : i < Hstep.restored.newInfo.rules.length)
    (habstract : i < rules.length),
    RuleRestoration result loweredEnv auxRec oldRecName
      Hstep.restored.newRecName Hstep.oldInfo.rules[i]
      Hstep.restored.newInfo.rules[i] →
    ∃ fieldVars, rules[i].rhs.GuardedIota
      (block.recursors.map (·.name)) fieldVars 0

theorem RestoredAuxiliaryStepSemantics.advance
    (H : RestoredAuxiliaryStepSemantics decl block main safety trEnv Hstep
      priorRecursors)
    (Hprefix : AuxiliaryRestorationPrefix decl block main priorRecursors
      priorRules) :
    AuxiliaryRestorationPrefix decl block main
      (priorRecursors ++ [H.recursor]) (priorRules ++ H.rules) := by
  have Hrecursor := Hprefix.pushRestoredRecursor
    Hstep.restored.restoration H.translated H.sequentialName
  exact Hrecursor.appendRestoredRules Hstep.restored.restoration.rules
    H.rulesLength H.guarded

/-- Trace-aligned semantic interpretation of an auxiliary restoration fold.
Unlike a callback over arbitrary prefixes, this object records the exact
abstract recursor and rule batch chosen for every operational step. -/
inductive RestoredAuxiliarySemanticTrace
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv : VEnv) :
    ∀ {names sourceEnv targetEnv},
      StateForMTrace
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv →
      List VConstVal → List VDefEq →
      List VConstVal → List VDefEq → Prop
  | nil (sourceEnv) (recursors rules) :
      RestoredAuxiliarySemanticTrace decl block main safety trEnv
        (StateForMTrace.nil (P :=
          RestoredRecursorStep result loweredEnv auxRec allIndNames)
          (source := sourceEnv)) recursors rules recursors rules
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : StateForMTrace
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hsemantic : RestoredAuxiliaryStepSemantics decl block main safety trEnv
        Hstep priorRecursors)
      (Hrest : RestoredAuxiliarySemanticTrace decl block main safety trEnv
        Htail (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules) :
      RestoredAuxiliarySemanticTrace decl block main safety trEnv
        (.cons Hstep Htail) priorRecursors priorRules
          finalRecursors finalRules

theorem RestoredAuxiliarySemanticTrace.prefix
    (H : RestoredAuxiliarySemanticTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules)
    (Hprefix : AuxiliaryRestorationPrefix decl block main priorRecursors
      priorRules) :
    AuxiliaryRestorationPrefix decl block main finalRecursors finalRules := by
  induction H with
  | nil => exact Hprefix
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact ih (Hsemantic.advance Hprefix)

theorem RestoredAuxiliarySemanticTrace.recursorsLength
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    (H : RestoredAuxiliarySemanticTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules) :
    finalRecursors.length = priorRecursors.length + names.length := by
  induction H with
  | nil => simp
  | cons Hstep Htail Hsemantic Hrest ih =>
    simp only [List.length_cons]
    rw [ih]
    simp
    omega

/-- Sequential abstract installation payload for one exact operational
recursor-restoration step.  This is intentionally separate from guarded iota
semantics: it concerns translation, typing, and environment extension only. -/
structure RestoredRecursorInstallationSemantics
    (safety : DefinitionSafety)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (sourceVEnv targetVEnv : VEnv) where
  recursor : VConstVal
  translated : TrConstVal safety sourceVEnv
    (.recInfo Hstep.restored.newInfo) recursor
  wf : recursor.toVConstant.WF sourceVEnv
  installed : sourceVEnv.addConst recursor.name recursor.toVConstant =
    some targetVEnv

theorem RestoredRecursorInstallationSemantics.checking
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv targetProdEnv : Environment}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {oldRecName : Name}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv}
    (H : RestoredRecursorInstallationSemantics safety Hstep sourceVEnv
      targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Hadd : sourceVEnv.addConst Hstep.restored.newInfo.name
      H.recursor.toVConstant = some targetVEnv := by
    have hname : Hstep.restored.newInfo.name = H.recursor.name := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        H.translated.2
    rw [hname]
    exact H.installed
  have Hnext := CheckingEnv.add
    (ci := .recInfo Hstep.restored.newInfo)
    (ci' := H.recursor.toVConstant) Hvalid hprodFresh H.translated.1
    H.wf Hadd rfl
  have htarget : targetProdEnv = sourceProdEnv.add
      (.recInfo Hstep.restored.newInfo) :=
    congrArg Prod.snd Hstep.restored.output
  rwa [htarget]

theorem RestoredRecursorStep.installationOfMetadata
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (recursor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = recursor.uvars)
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type recursor.type)
    (hname : recursor.name = Hstep.restored.newRecName)
    (Hwf : recursor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredRecursorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Htranslated := Hstep.restored.restoration.translatedOfMetadata
    Hsafety Huvars Htype hname
  rcases CheckingEnv.exists_addConst Hvalid hprodFresh
      recursor.toVConstant with ⟨targetVEnv, Hinstalled⟩
  have Hinstalled' : sourceVEnv.addConst recursor.name
      recursor.toVConstant = some targetVEnv := by
    rw [← Htranslated.2]
    exact Hinstalled
  exact ⟨targetVEnv, ⟨{
    recursor := recursor
    translated := Htranslated
    wf := Hwf
    installed := Hinstalled' }⟩⟩

/-- Compatibility form for callers which already have a translation of the
lowered recursor.  New nested-restoration proofs should use
`installationOfMetadata`, since the lowered type can mention auxiliary
constants absent from the restored environment. -/
theorem RestoredRecursorStep.installation
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (recursor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv (.recInfo Hstep.oldInfo)
      { recursor with name := oldRecName })
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type recursor.type)
    (hname : recursor.name = Hstep.restored.newRecName)
    (Hwf : recursor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredRecursorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid recursor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · exact Htype
  · exact hname
  · exact Hwf

/-- Specification-facing payload for one restored primary recursor.  The
translated concrete telescope and independent abstract `NestedRecursorShape` live
in the same object, preventing installation correctness from being proved
against a recursor unrelated to the source declaration. -/
structure RestoredPrimaryRecursorSemantics
    (decl : VInductDecl) (owner : VInductiveType)
    (safety : DefinitionSafety)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (sourceVEnv : VEnv) where
  recursor : VConstVal
  safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type
  name : recursor.name = Hstep.restored.newRecName
  wf : recursor.toVConstant.WF sourceVEnv
  shape : Nonempty (decl.NestedRecursorShape owner recursor)

/-- The genuinely canonical-environment obligations left after a restored
primary recursor has been matched to its generated production entry. -/
structure RestoredPrimaryRecursorCanonicalInputs
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (recursor : VConstVal) (canonicalEnv : VEnv) : Prop where
  type : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type
  name : recursor.name = Hstep.restored.newRecName
  wf : recursor.toVConstant.WF canonicalEnv

/-- Independent source-level meaning of one primary recursor.  In particular,
this object mentions neither the lowered declaration nor any production
restoration step: it is the abstract specification which the executable
recursor construction must refine. -/
structure SourcePrimaryRecursorSemantics
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (canonicalEnv : VEnv) where
  recursor : VConstVal
  name : recursor.name = sourceDecl.recursorName owner
  isType : canonicalEnv.IsType recursor.uvars [] recursor.type
  shape : Nonempty (sourceDecl.NestedRecursorShape owner recursor)

/-- Executable-to-specification refinement for a restored primary recursor.
The source recursor is fixed by `SourcePrimaryRecursorSemantics`; this record
states that the concrete restoration step has exactly its universe arity and
translates its restored telescope to exactly its abstract type. -/
structure RestoredPrimaryRecursorRefinement
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) : Prop where
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type

/-- One abstract source recursor realized by a particular restored concrete
recursor.  The equality field prevents the source witness and refinement
proof from drifting to different constants. -/
structure SourcePrimaryRecursorRealization
    (sourceDecl : VInductDecl) (sourceOwner : VInductiveType)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) where
  source : SourcePrimaryRecursorSemantics sourceDecl sourceOwner canonicalEnv
  recursor_eq : source.recursor = recursor
  refinement : RestoredPrimaryRecursorRefinement Hstep canonicalEnv recursor

/-- A joint source realization supplies the specification, canonical typing,
and executable refinement needed by the restored installation layer. -/
def SourcePrimaryRecursorRealization.toRestoredSemantics
    (H : SourcePrimaryRecursorRealization sourceDecl sourceOwner Hstep
      canonicalEnv recursor)
    (safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety)
    (hname : recursor.name = Hstep.restored.newRecName) :
    RestoredPrimaryRecursorSemantics sourceDecl sourceOwner safety Hstep
      canonicalEnv where
  recursor := recursor
  safety_le := safety_le
  uvars := H.refinement.uvars
  type := H.refinement.type
  name := hname
  wf := by
    rw [← H.recursor_eq]
    exact H.source.isType
  shape := by
    rw [← H.recursor_eq]
    exact H.source.shape

theorem SourcePrimaryRecursorRealization.installation
    {sourceProdEnv targetProdEnv : Environment}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv}
    (H : SourcePrimaryRecursorRealization sourceDecl sourceOwner Hstep
      canonicalEnv recursor)
    (safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety)
    (hname : recursor.name = Hstep.restored.newRecName)
    (Hvalid : CheckingEnv safety sourceProdEnv canonicalEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredRecursorInstallationSemantics safety Hstep
        canonicalEnv targetVEnv) :=
  Hstep.installationOfMetadata Hvalid recursor safety_le H.refinement.uvars
    H.refinement.type hname (by
      rw [← H.recursor_eq]
      exact H.source.isType)

/-- Discharge both source-recursion callbacks from one canonical restored
recursor once lowering has supplied the declarative compatibility facts.  In
particular, the abstract recursor is not chosen independently of the concrete
restoration step: its translated type and well-formedness come from
`Hcanonical`, while its source shape is transported from the expanded
lowered declaration. -/
def RestoredPrimaryRecursorCanonicalInputs.sourceSemanticsOfCompatible
    {loweredDecl sourceDecl : VInductDecl}
    {loweredOwner sourceOwner : VInductiveType}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv}
    {recursor : VConstVal} {canonicalEnv : VEnv}
    (Hcanonical : RestoredPrimaryRecursorCanonicalInputs Hstep recursor
      canonicalEnv)
    (Hshape : loweredDecl.NestedRecursorShape loweredOwner recursor)
    (howner : Hshape.ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[Hshape.ownerIdx] = sourceOwner)
    (hsourceName : Hstep.restored.newRecName =
      sourceDecl.recursorName sourceOwner)
    (hsourceUvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (holdUvars : Hstep.oldInfo.levelParams.length = recursor.uvars)
    (hnparams : sourceDecl.nparams = loweredDecl.nparams)
    (hmotives : sourceDecl.types.length ≤ Hshape.motives.length)
    (hminors : sourceDecl.ownedConstructors.length ≤ Hshape.minors.length)
    (hindices : sourceOwner.numIndices = loweredOwner.numIndices) :
    SourcePrimaryRecursorRealization sourceDecl sourceOwner Hstep canonicalEnv
      recursor where
  source := ⟨recursor, Hcanonical.name.trans hsourceName, Hcanonical.wf,
    ⟨Hshape.ofCompatible howner hownerEq
      (Hcanonical.name.trans hsourceName) hsourceUvars hnparams hmotives
      hminors hindices⟩⟩
  recursor_eq := rfl
  refinement := ⟨holdUvars, Hcanonical.type⟩

/-- For an ordinary block, the verified production recursor certificate
already supplies the independent source-level recursor semantics.  Nested
lowering cannot use this theorem directly for an original source family,
because its generated entries are indexed by the expanded lowered
declaration; that remaining distinction is intentional. -/
theorem GeneratedRecursors.sourcePrimaryRecursorSemantics
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {sourceEnv envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (ownerIdx : Nat) (hentry : ownerIdx < entries.length) :
    Nonempty (SourcePrimaryRecursorSemantics decl
      (decl.types[ownerIdx]'(by
        have howner : ownerIdx < recInfos.size := by
          simpa [H.length] using hentry
        simpa [Hcard.records] using howner)) env) := by
  have howner : ownerIdx < recInfos.size := by
    simpa [H.length] using hentry
  have hdeclOwner : ownerIdx < decl.types.length := by
    simpa [Hcard.records] using howner
  let recursor := entries[ownerIdx].2
  have hrecursor : recursor ∈ entries.map Prod.snd := by
    rw [List.mem_iff_getElem]
    refine ⟨ownerIdx, ?_, ?_⟩
    · simpa using hentry
    · simp [recursor]
  have Hshape :=
    (H.recursorCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl).shapes
      ownerIdx hdeclOwner (by simpa using hentry)
  rw [List.getElem_map] at Hshape
  change Nonempty (decl.RecursorShape
    (decl.types[ownerIdx]'hdeclOwner) recursor) at Hshape
  rcases Hshape with ⟨Hshape⟩
  refine ⟨{
    recursor := recursor
    name := Hshape.name
    isType := ?_
    shape := ⟨Hshape.toNested⟩ }⟩
  exact H.recursorsWF Hc Hbindings Hparams recursor hrecursor

theorem RestoredPrimaryRecursorSemantics.installation
    {oldRecName : Name} {sourceProdEnv targetProdEnv : Environment}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv}
    {sourceVEnv : VEnv}
    (H : RestoredPrimaryRecursorSemantics decl owner safety Hstep sourceVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredRecursorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) :=
  Hstep.installationOfMetadata Hvalid H.recursor H.safety_le H.uvars H.type
    H.name H.wf

/-- Primary recursor semantics indexed directly by the operational family
restoration trace, but interpreted in the single canonical abstract
post-constructor environment.  This separation is essential for mutual
inductives: production restoration is family-interleaved, whereas abstract
typing requires all mutual headers and constructors to be present first. -/
inductive RestoredPrimaryRecursorSemanticTrace
    (decl : VInductDecl) (safety : DefinitionSafety)
    (canonicalEnv : VEnv) :
    ∀ {types sourceProdEnv targetProdEnv},
      StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredPrimaryRecursorSemanticTrace decl safety canonicalEnv
        (StateForMTrace.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hsemantic : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor canonicalEnv)
      (Hrest : RestoredPrimaryRecursorSemanticTrace decl safety canonicalEnv
        Htail owners recursors) :
      RestoredPrimaryRecursorSemanticTrace decl safety canonicalEnv
        (.cons Hstep Htail) (owner :: owners)
        (Hsemantic.recursor :: recursors)

theorem RestoredPrimaryRecursorSemanticTrace.forall₂
    (H : RestoredPrimaryRecursorSemanticTrace decl safety canonicalEnv
      Htrace owners recursors) :
    List.Forall₂ (fun owner recursor =>
      Nonempty (decl.NestedRecursorShape owner recursor)) owners recursors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact .cons Hsemantic.shape ih

theorem RestoredPrimaryRecursorSemanticTrace.recursorCertificate
    (H : RestoredPrimaryRecursorSemanticTrace decl safety canonicalEnv
      Htrace owners recursors)
    (htypes : decl.types = owners) :
    NestedRecursorCertificate decl recursors := by
  have Hshapes := H.forall₂
  rw [← htypes] at Hshapes
  refine {
    length := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hshapes |>.symm
    shapes := ?_ }
  intro i htype hrec
  exact Lean4Lean.VerifyInductive.List.Forall₂.getElem Hshapes i htype hrec

/-- Trace-aligned installation semantics for a fold of restored recursors.
The abstract environment advances at exactly the same step boundaries as the
production environment. -/
inductive RestoredRecursorInstallationTrace
    (safety : DefinitionSafety) :
    ∀ {names sourceProdEnv targetProdEnv},
      StateForMTrace
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceProdEnv targetProdEnv →
      VEnv → List VConstVal → VEnv → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredRecursorInstallationTrace safety
        (StateForMTrace.nil (P :=
          RestoredRecursorStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) sourceVEnv [] sourceVEnv
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleProdEnv targetProdEnv)
      (Hsemantic : RestoredRecursorInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredRecursorInstallationTrace safety Htail middleVEnv
        recursors targetVEnv) :
      RestoredRecursorInstallationTrace safety (.cons Hstep Htail)
        sourceVEnv (Hsemantic.recursor :: recursors) targetVEnv

/-- Forget a trace-aligned recursor interpretation to the generic translated
freshness trace used by restored-block assembly. -/
theorem RestoredRecursorInstallationTrace.translatedFresh
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {recursors : List VConstVal}
    (H : RestoredRecursorInstallationTrace safety Htrace sourceVEnv
      recursors targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries targetProdEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv recursors
          targetVEnv := by
  induction H with
  | nil => exact ⟨[], .nil, .nil _ _⟩
  | @cons oldRecName sourceProdEnv middleProdEnv names targetProdEnv
      sourceVEnv middleVEnv recursors targetVEnv Hstep Htail Hsemantic
      Hrest ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh : sourceProdEnv.find? ci.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.fresh
    have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middleProdEnv.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
    rcases ih hmiddleWF with
      ⟨entries, Hfresh, Htranslated⟩
    have HtranslatedTail :
        ∃ Hfresh' : FreshConstantTrace (sourceProdEnv.add ci) entries
            targetProdEnv,
          TranslatedFreshConstantTrace safety Hfresh' middleVEnv recursors
            targetVEnv := by
      exact hmiddle ▸ ⟨Hfresh, Htranslated⟩
    rcases HtranslatedTail with ⟨Hfresh', Htranslated'⟩
    exact ⟨ci :: entries, .cons hfresh Hfresh',
      .cons hfresh Hfresh' Hsemantic.translated Hsemantic.wf
        Hsemantic.installed Htranslated'⟩

theorem RestoredRecursorInstallationTrace.checking
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {recursors : List VConstVal}
    (H : RestoredRecursorInstallationTrace safety Htrace sourceVEnv
      recursors targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  induction H with
  | nil => exact Hvalid
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact ih (Hsemantic.checking Hvalid)

structure RestoredConstructorInstallationSemantics
    (safety : DefinitionSafety)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (sourceVEnv targetVEnv : VEnv) where
  constructor : VConstVal
  translated : TrConstVal safety sourceVEnv
    (.ctorInfo Hstep.restored.newInfo) constructor
  wf : constructor.toVConstant.WF sourceVEnv
  installed : sourceVEnv.addConst constructor.name constructor.toVConstant =
    some targetVEnv

theorem RestoredConstructorInstallationSemantics.checking
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv targetProdEnv : Environment}
    {ctorName : Name}
    {Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv}
    (H : RestoredConstructorInstallationSemantics safety Hstep sourceVEnv
      targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Hadd : sourceVEnv.addConst Hstep.restored.newInfo.name
      H.constructor.toVConstant = some targetVEnv := by
    have hname : Hstep.restored.newInfo.name = H.constructor.name := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        H.translated.2
    rw [hname]
    exact H.installed
  have Hnext := CheckingEnv.add
    (ci := .ctorInfo Hstep.restored.newInfo)
    (ci' := H.constructor.toVConstant) Hvalid hprodFresh H.translated.1
    H.wf Hadd rfl
  have htarget : targetProdEnv = sourceProdEnv.add
      (.ctorInfo Hstep.restored.newInfo) :=
    congrArg Prod.snd Hstep.restored.output
  rwa [htarget]

/-- Build the installation payload for a restored constructor.  All metadata
and freshness facts are derived; the only restoration-specific semantic
premise is translation of the restored concrete type to the original
abstract constructor type. -/
theorem RestoredConstructorStep.installationOfMetadata
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Htranslated := Hstep.restored.restoration.translatedOfMetadata
    Hsafety Huvars Hname Htype
  rcases CheckingEnv.exists_addConst Hvalid hprodFresh
      constructor.toVConstant with ⟨targetVEnv, Hinstalled⟩
  have Hinstalled' : sourceVEnv.addConst constructor.name
      constructor.toVConstant = some targetVEnv := by
    rw [← Htranslated.2]
    exact Hinstalled
  exact ⟨targetVEnv, ⟨{
    constructor := constructor
    translated := Htranslated
    wf := Hwf
    installed := Hinstalled' }⟩⟩

/-- Compatibility form for non-nested callers which already translate the
old constructor in the target environment. -/
theorem RestoredConstructorStep.installation
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv
      (.ctorInfo Hstep.oldInfo) constructor)
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid constructor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hold.2
  · exact Htype
  · exact Hwf

inductive RestoredConstructorInstallationTrace
    (safety : DefinitionSafety) :
    ∀ {names sourceProdEnv targetProdEnv},
      StateForMTrace (RestoredConstructorStep result loweredEnv)
        names sourceProdEnv targetProdEnv →
      VEnv → List VConstVal → VEnv → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredConstructorInstallationTrace safety
        (StateForMTrace.nil (P := RestoredConstructorStep result loweredEnv)
          (source := sourceProdEnv)) sourceVEnv [] sourceVEnv
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace (RestoredConstructorStep result loweredEnv)
        names middleProdEnv targetProdEnv)
      (Hsemantic : RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredConstructorInstallationTrace safety Htail middleVEnv
        constructors targetVEnv) :
      RestoredConstructorInstallationTrace safety (.cons Hstep Htail)
        sourceVEnv (Hsemantic.constructor :: constructors) targetVEnv

theorem RestoredConstructorInstallationTrace.translatedFresh
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constructors : List VConstVal}
    (H : RestoredConstructorInstallationTrace safety Htrace sourceVEnv
      constructors targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries targetProdEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv constructors
          targetVEnv := by
  induction H with
  | nil => exact ⟨[], .nil, .nil _ _⟩
  | @cons ctorName sourceProdEnv middleProdEnv names targetProdEnv
      sourceVEnv middleVEnv constructors targetVEnv Hstep Htail Hsemantic
      Hrest ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh : sourceProdEnv.find? ci.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.fresh
    have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middleProdEnv.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
    rcases ih hmiddleWF with
      ⟨entries, Hfresh, Htranslated⟩
    have HtranslatedTail :
        ∃ Hfresh' : FreshConstantTrace (sourceProdEnv.add ci) entries
            targetProdEnv,
          TranslatedFreshConstantTrace safety Hfresh' middleVEnv constructors
            targetVEnv := by
      exact hmiddle ▸ ⟨Hfresh, Htranslated⟩
    rcases HtranslatedTail with ⟨Hfresh', Htranslated'⟩
    exact ⟨ci :: entries, .cons hfresh Hfresh',
      .cons hfresh Hfresh' Hsemantic.translated Hsemantic.wf
        Hsemantic.installed Htranslated'⟩

theorem RestoredConstructorInstallationTrace.checking
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constructors : List VConstVal}
    (H : RestoredConstructorInstallationTrace safety Htrace sourceVEnv
      constructors targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  induction H with
  | nil => exact Hvalid
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact ih (Hsemantic.checking Hvalid)

/-- One source constructor paired with the exact operational restoration
step that installs it.  Source translation is stated in the canonical
post-header environment, not the production interleaved environment. -/
structure RestoredSourceConstructorSemantics
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (source : Constructor) where
  constructor : VConstVal
  sourceTranslation : TrSourceConst canonicalEnv lparams source.name
    source.type constructor
  restoredTranslation : TrConstVal safety canonicalEnv
    (.ctorInfo Hstep.restored.newInfo) constructor

/-- Positional source-constructor semantics for the exact constructor
restoration fold of one family. -/
inductive RestoredSourceConstructorTrace
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv) :
    List Name → Environment → Environment →
      List Constructor → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredSourceConstructorTrace lparams safety canonicalEnv
        [] sourceProdEnv sourceProdEnv [] []
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Hsemantic : RestoredSourceConstructorSemantics lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredSourceConstructorTrace lparams safety canonicalEnv
        names middleProdEnv targetProdEnv sources constructors) :
      RestoredSourceConstructorTrace lparams safety canonicalEnv
        (ctorName :: names) sourceProdEnv targetProdEnv (source :: sources)
        (Hsemantic.constructor :: constructors)

theorem RestoredSourceConstructorTrace.forall₂
    (H : RestoredSourceConstructorTrace lparams safety canonicalEnv names
      sourceProdEnv targetProdEnv sources constructors) :
    List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Hsemantic Hrest ih =>
    exact .cons Hsemantic.sourceTranslation ih

/-- Source-family semantics indexed by the production restoration trace but
staged in the canonical abstract environments required by mutual typing. -/
inductive RestoredSourceInductiveSemanticTrace
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety)
    (sourceVEnv envTypes envCtors : VEnv) :
    ∀ {types sourceProdEnv targetProdEnv},
      StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors
        (StateForMTrace.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredSourceConstructorTrace lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors) :
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors (.cons Hstep Htail) (owner :: owners)
        (Hrecursor.recursor :: recursors)

/-- All canonical-stage semantic data for one exact operational family
restoration step.  Bundling the fields keeps mutual-trace assembly independent
of how headers, constructors, and primary recursors are proved. -/
structure RestoredSourceInductiveSemantics
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety) (sourceVEnv envTypes envCtors : VEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  owner : VInductiveType
  header : TrSourceConst sourceVEnv lparams indType.name indType.type
    owner.toVConstVal
  constructors : RestoredSourceConstructorTrace lparams safety envTypes
    Hstep.oldInfo.ctors Hstep.restored.headerEnv
      Hstep.restored.constructorEnv indType.ctors owner.ctors
  recursor : RestoredPrimaryRecursorSemantics decl owner safety
    Hstep.restored.recursor envCtors

/-- Assemble per-family semantic payloads over the exact executable mutual
restoration trace.  This discharges all ordering and state-threading work and
returns the source owners and primary recursors selected by those payloads. -/
theorem StateForMTrace.sourceInductiveSemanticTrace
    (Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv)
    (Hsemantics : ∀ indType stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ types →
      Nonempty (RestoredSourceInductiveSemantics decl lparams safety
        sourceVEnv envTypes envCtors Hstep)) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors := by
  induction Htrace with
  | nil => exact ⟨[], [], .nil _⟩
  | cons Hstep Htail ih =>
    rcases Hsemantics _ _ _ Hstep (by simp) with ⟨Hhead⟩
    rcases ih (fun indType stepSource stepTarget Hstep hmem =>
      Hsemantics indType stepSource stepTarget Hstep (by simp [hmem])) with
      ⟨owners, recursors, Hrest⟩
    exact ⟨Hhead.owner :: owners, Hhead.recursor.recursor :: recursors,
      .cons Hstep Htail Hhead.header Hhead.constructors Hhead.recursor Hrest⟩

theorem RestoredSourceInductiveSemanticTrace.types
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (TrInductiveType sourceVEnv envTypes lparams)
      sourceTypes owners := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hheader, Hconstructors.forall₂⟩ ih

theorem RestoredSourceInductiveSemanticTrace.primaryRecursors
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    RestoredPrimaryRecursorSemanticTrace decl safety envCtors Htrace owners
      recursors := by
  induction H with
  | nil => exact .nil _
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons Hstep Htail Hrecursor ih

/-- Reconstruct the independent source declaration translation from the
canonical-stage semantic trace.  The executable restoration trace fixes all
pointwise source/target correspondences; only the canonical abstract stage
extensions and declaration metadata are supplied separately. -/
theorem RestoredSourceInductiveSemanticTrace.core
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners)
    (huvars : decl.uvars = lparams.length)
    (hnparams : decl.nparams = nparams)
    (hisUnsafe : decl.isUnsafe = isUnsafe)
    (htypesAdded : sourceVEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors) :
    TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe decl
      envTypes envCtors := by
  refine {
    uvars := huvars
    nparams := hnparams
    isUnsafe := hisUnsafe
    typesAdded := htypesAdded
    ctorsAdded := hctorsAdded
    types := ?_ }
  rw [htypes]
  exact H.types

theorem RestoredSourceInductiveSemanticTrace.recursorCertificate
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners) :
    NestedRecursorCertificate decl recursors :=
  H.primaryRecursors.recursorCertificate htypes

/-- Installation semantics for one complete restored source family: header,
its exact constructor fold, and its primary recursor. -/
structure RestoredInductiveInstallationSemantics
    (safety : DefinitionSafety)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv)
    (sourceVEnv targetVEnv : VEnv) where
  headerVEnv : VEnv
  constructorVEnv : VEnv
  header : VConstVal
  constructors : List VConstVal
  headerTranslated : TrConstVal safety sourceVEnv
    (.inductInfo Hstep.restored.header.newInfo) header
  headerWF : header.toVConstant.WF sourceVEnv
  headerInstalled : sourceVEnv.addConst header.name header.toVConstant =
    some headerVEnv
  constructorTrace : RestoredConstructorInstallationTrace safety
    Hstep.restored.constructors headerVEnv constructors constructorVEnv
  recursor : RestoredRecursorInstallationSemantics safety
    Hstep.restored.recursor constructorVEnv targetVEnv

/-- Header translation and abstract installation are inherited directly from
the unchanged lowered header.  Restoration's production freshness check and
the source checking-environment alignment determine the fresh abstract
target; no restoration-specific expression proof is required. -/
theorem RestoredInductiveStep.headerInstallation
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (header : VConstVal)
    (Htr : TrConstVal safety sourceVEnv
      (.inductInfo Hstep.oldInfo) header)
    (Hwf : header.toVConstant.WF sourceVEnv) :
    ∃ headerVEnv,
      TrConstVal safety sourceVEnv
        (.inductInfo Hstep.restored.header.newInfo) header ∧
      header.toVConstant.WF sourceVEnv ∧
      sourceVEnv.addConst header.name header.toVConstant =
        some headerVEnv := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.header.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf
      Hstep.restored.header.fresh
  have Htranslated := Hstep.restored.header.translated Htr
  rcases CheckingEnv.exists_addConst Hvalid hprodFresh
      header.toVConstant with ⟨headerVEnv, Hinstalled⟩
  have Hinstalled' : sourceVEnv.addConst header.name header.toVConstant =
      some headerVEnv := by
    rw [← Htranslated.2]
    exact Hinstalled
  exact ⟨headerVEnv, Htranslated, Hwf, Hinstalled'⟩

theorem RestoredInductiveInstallationSemantics.translatedFresh
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv targetProdEnv : Environment}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {indType : InductiveType}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv}
    (H : RestoredInductiveInstallationSemantics safety Hstep sourceVEnv
      targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries targetProdEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv
          (H.header :: H.constructors ++ [H.recursor.recursor])
          targetVEnv := by
  let headerInfo : ConstantInfo :=
    .inductInfo Hstep.restored.header.newInfo
  have hheaderFresh : sourceProdEnv.find? headerInfo.name = none :=
    find?_none_of_contains_false hsourceWF Hstep.restored.header.fresh
  have hheaderEnv : Hstep.restored.headerEnv =
      sourceProdEnv.add headerInfo :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderProdWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
  rcases H.constructorTrace.translatedFresh hheaderProdWF with
    ⟨constructorEntries, HconstructorFresh, HconstructorTranslated⟩
  have hconstructorProdWF :=
    HconstructorFresh.targetWF hheaderProdWF
  let HrecTrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      [Lean.mkRecName indType.name] Hstep.restored.constructorEnv
        targetProdEnv :=
    .cons Hstep.restored.recursor .nil
  let HrecInstall : RestoredRecursorInstallationTrace safety HrecTrace
      H.constructorVEnv [H.recursor.recursor] targetVEnv :=
    .cons Hstep.restored.recursor .nil H.recursor (.nil _ _)
  rcases HrecInstall.translatedFresh hconstructorProdWF with
    ⟨recursorEntries, HrecursorFresh, HrecursorTranslated⟩
  have HheaderPair :
      ∃ Hfresh : FreshConstantTrace sourceProdEnv [headerInfo]
          Hstep.restored.headerEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv [H.header]
          H.headerVEnv := by
    have Hfresh₀ : FreshConstantTrace sourceProdEnv [headerInfo]
        (sourceProdEnv.add headerInfo) := .cons hheaderFresh .nil
    have Htranslated₀ : TranslatedFreshConstantTrace safety Hfresh₀
        sourceVEnv [H.header] H.headerVEnv :=
      .cons hheaderFresh .nil H.headerTranslated H.headerWF
        H.headerInstalled (.nil _ _)
    exact hheaderEnv.symm ▸ ⟨Hfresh₀, Htranslated₀⟩
  rcases HheaderPair with ⟨HheaderFresh, HheaderTranslated⟩
  let HprimaryFresh :=
    (HheaderFresh.append HconstructorFresh).append HrecursorFresh
  have HprimaryTranslated : TranslatedFreshConstantTrace safety HprimaryFresh
      sourceVEnv ([H.header] ++ H.constructors ++ [H.recursor.recursor])
        targetVEnv :=
    (HheaderTranslated.append HconstructorTranslated).append
      HrecursorTranslated
  exact ⟨[headerInfo] ++ constructorEntries ++ recursorEntries,
    HprimaryFresh, by simpa only [List.singleton_append] using
      HprimaryTranslated⟩

theorem RestoredInductiveInstallationSemantics.checking
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv targetProdEnv : Environment}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {indType : InductiveType}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv}
    (H : RestoredInductiveInstallationSemantics safety Hstep sourceVEnv
      targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  let headerInfo : ConstantInfo :=
    .inductInfo Hstep.restored.header.newInfo
  have hprodFresh : sourceProdEnv.find? headerInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.header.fresh
  have hname : headerInfo.name = H.header.name := H.headerTranslated.2
  have Hadd : sourceVEnv.addConst headerInfo.name H.header.toVConstant =
      some H.headerVEnv := by
    rw [hname]
    exact H.headerInstalled
  have HheaderChecking : CheckingEnv safety Hstep.restored.headerEnv
      H.headerVEnv := by
    have Hnext := CheckingEnv.add (ci := headerInfo)
      (ci' := H.header.toVConstant) Hvalid hprodFresh H.headerTranslated.1
      H.headerWF Hadd rfl
    have htarget : Hstep.restored.headerEnv = sourceProdEnv.add headerInfo :=
      congrArg Prod.snd Hstep.restored.header.output
    rwa [htarget]
  have HconstructorChecking :=
    H.constructorTrace.checking HheaderChecking
  exact H.recursor.checking HconstructorChecking

inductive RestoredInductiveInstallationTrace
    (safety : DefinitionSafety) :
    ∀ {types sourceProdEnv targetProdEnv},
      StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      VEnv → List VConstVal → VEnv → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredInductiveInstallationTrace safety
        (StateForMTrace.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) sourceVEnv [] sourceVEnv
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hsemantic : RestoredInductiveInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredInductiveInstallationTrace safety Htail middleVEnv
        constants targetVEnv) :
      RestoredInductiveInstallationTrace safety (.cons Hstep Htail)
        sourceVEnv
          ((Hsemantic.header :: Hsemantic.constructors ++
            [Hsemantic.recursor.recursor]) ++ constants)
          targetVEnv

/-- A list is exactly the primary-recursor projection of an operational
restoration trace.  This relation deliberately ignores the interleaved
headers and constructors in the installation list; it is relational because
the trace itself is proof-valued. -/
inductive RestoredPrimaryRecursors
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (safety : DefinitionSafety) :
    ∀ {types : List InductiveType}
      {sourceProdEnv targetProdEnv : Environment}
      {Htrace : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv}
      {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal},
      RestoredInductiveInstallationTrace safety Htrace sourceVEnv constants
        targetVEnv →
      List VConstVal → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredPrimaryRecursors result loweredEnv auxRec allIndNames safety
        (RestoredInductiveInstallationTrace.nil (safety := safety)
          (result := result) (loweredEnv := loweredEnv) (auxRec := auxRec)
          (allIndNames := allIndNames) sourceProdEnv sourceVEnv) []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hsemantic : RestoredInductiveInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredInductiveInstallationTrace safety Htail middleVEnv
        constants targetVEnv)
      (HrestRecursors : RestoredPrimaryRecursors result loweredEnv auxRec
        allIndNames safety Hrest recursors) :
      RestoredPrimaryRecursors result loweredEnv auxRec allIndNames safety
        (RestoredInductiveInstallationTrace.cons (safety := safety)
          Hstep Htail Hsemantic Hrest)
        (Hsemantic.recursor.recursor :: recursors)

theorem RestoredInductiveInstallationTrace.existsPrimaryRecursors
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal}
    (H : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv) :
    ∃ recursors, RestoredPrimaryRecursors result loweredEnv auxRec
      allIndNames safety H recursors := by
  induction H with
  | nil => exact ⟨[], .nil _ _⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
    rcases ih with ⟨recursors, Hrecursors⟩
    exact ⟨Hsemantic.recursor.recursor :: recursors,
      .cons Hstep Htail Hsemantic Hrest Hrecursors⟩

theorem RestoredPrimaryRecursors.length
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constants recursors : List VConstVal}
    {Hinstall : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv}
    (H : RestoredPrimaryRecursors result loweredEnv auxRec allIndNames safety
      Hinstall recursors) :
    recursors.length = types.length := by
  induction H with
  | nil => rfl
  | cons Hstep Htail Hsemantic Hrest HrestRecursors ih =>
    simp only [List.length_cons]
    rw [ih]

/-- Pointwise source recursor shapes accumulated in the same order as the
exact restored-family installation trace. -/
inductive RestoredPrimaryRecursorShapes
    (decl : VInductDecl)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (safety : DefinitionSafety) :
    ∀ {types : List InductiveType}
      {sourceProdEnv targetProdEnv : Environment}
      {Htrace : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv}
      {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal},
      RestoredInductiveInstallationTrace safety Htrace sourceVEnv constants
        targetVEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredPrimaryRecursorShapes decl result loweredEnv auxRec allIndNames
        safety
        (RestoredInductiveInstallationTrace.nil (safety := safety)
          (result := result) (loweredEnv := loweredEnv) (auxRec := auxRec)
          (allIndNames := allIndNames) sourceProdEnv sourceVEnv) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hsemantic : RestoredInductiveInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredInductiveInstallationTrace safety Htail middleVEnv
        constants targetVEnv)
      (Hshape : Nonempty
        (decl.NestedRecursorShape owner Hsemantic.recursor.recursor))
      (HrestShapes : RestoredPrimaryRecursorShapes decl result loweredEnv
        auxRec allIndNames safety Hrest owners recursors) :
      RestoredPrimaryRecursorShapes decl result loweredEnv auxRec allIndNames
        safety
        (RestoredInductiveInstallationTrace.cons (safety := safety)
          Hstep Htail Hsemantic Hrest)
        (owner :: owners) (Hsemantic.recursor.recursor :: recursors)

theorem RestoredPrimaryRecursorShapes.trace
    (H : RestoredPrimaryRecursorShapes decl result loweredEnv auxRec
      allIndNames safety Hinstall owners recursors) :
    RestoredPrimaryRecursors result loweredEnv auxRec allIndNames safety
      Hinstall recursors := by
  induction H with
  | nil => exact .nil _ _
  | cons Hstep Htail Hsemantic Hrest Hshape HrestShapes ih =>
    exact .cons Hstep Htail Hsemantic Hrest ih

theorem RestoredPrimaryRecursorShapes.forall₂
    (H : RestoredPrimaryRecursorShapes decl result loweredEnv auxRec
      allIndNames safety Hinstall owners recursors) :
    List.Forall₂ (fun owner recursor =>
      Nonempty (decl.NestedRecursorShape owner recursor)) owners recursors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hsemantic Hrest Hshape HrestShapes ih =>
    exact .cons Hshape ih

/-- Abstract recursor shapes aligned with the exact operational restoration
trace.  This is the specification-facing certificate for primary restored
recursors; no independently chosen list can be substituted for the values
actually installed by the trace. -/
structure RestoredPrimaryRecursorCertificate
    (decl : VInductDecl)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (safety : DefinitionSafety)
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    (Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv)
    {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal}
    (H : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv)
    (recursors : List VConstVal) : Prop where
  trace : RestoredPrimaryRecursors result loweredEnv auxRec allIndNames safety
    H recursors
  shapes : List.Forall₂ (fun owner recursor =>
    Nonempty (decl.NestedRecursorShape owner recursor))
    decl.types recursors

theorem RestoredPrimaryRecursorCertificate.recursorCertificate
    (H : RestoredPrimaryRecursorCertificate decl result loweredEnv auxRec
      allIndNames safety Htrace Hinstall recursors) :
    NestedRecursorCertificate decl recursors := by
  refine {
    length := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.shapes |>.symm
    shapes := ?_ }
  intro i htype hrec
  exact Lean4Lean.VerifyInductive.List.Forall₂.getElem H.shapes i htype hrec

theorem RestoredPrimaryRecursorShapes.certificate
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal}
    {Hinstall : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv}
    (H : RestoredPrimaryRecursorShapes decl result loweredEnv auxRec
      allIndNames safety Hinstall owners recursors)
    (htypes : decl.types = owners) :
    RestoredPrimaryRecursorCertificate decl result loweredEnv auxRec
      allIndNames safety Htrace Hinstall recursors := by
  refine ⟨H.trace, ?_⟩
  rw [htypes]
  exact H.forall₂

theorem RestoredInductiveInstallationTrace.translatedFresh
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal}
    (H : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries targetProdEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv constants
          targetVEnv := by
  induction H with
  | nil => exact ⟨[], .nil, .nil _ _⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
    rcases Hsemantic.translatedFresh hsourceWF with
      ⟨familyEntries, HfamilyFresh, HfamilyTranslated⟩
    rcases ih (HfamilyFresh.targetWF hsourceWF) with
      ⟨tailEntries, HtailFresh, HtailTranslated⟩
    exact ⟨familyEntries ++ tailEntries,
      HfamilyFresh.append HtailFresh,
      HfamilyTranslated.append HtailTranslated⟩

theorem RestoredInductiveInstallationTrace.checking
    {types : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constants : List VConstVal}
    (H : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  induction H with
  | nil => exact Hvalid
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact ih (Hsemantic.checking Hvalid)

private theorem perm_group_familyConstants
    (header recursor : VConstVal)
    (tailTypes familyCtors tailCtors tailRecursors : List VConstVal) :
    (header :: tailTypes) ++ (familyCtors ++ tailCtors) ++
        (recursor :: tailRecursors) ~
      (header :: familyCtors ++ [recursor]) ++
        (tailTypes ++ tailCtors ++ tailRecursors) := by
  apply List.Perm.cons header
  have htypes : tailTypes ++ familyCtors ~ familyCtors ++ tailTypes :=
    List.perm_append_comm
  have hfirst :
      tailTypes ++ familyCtors ++ tailCtors ++ recursor :: tailRecursors ~
        familyCtors ++ tailTypes ++ tailCtors ++ recursor :: tailRecursors := by
    simpa only [List.append_assoc] using
      htypes.append_right (tailCtors ++ recursor :: tailRecursors)
  have hrecursor :
      tailTypes ++ tailCtors ++ [recursor] ~
        [recursor] ++ tailTypes ++ tailCtors := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm :
        (tailTypes ++ tailCtors) ++ [recursor] ~
          [recursor] ++ (tailTypes ++ tailCtors))
  have hsecond :
      familyCtors ++ tailTypes ++ tailCtors ++ recursor :: tailRecursors ~
        familyCtors ++
          (recursor :: (tailTypes ++ tailCtors ++ tailRecursors)) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      (List.Perm.refl familyCtors).append
        (hrecursor.append_right tailRecursors)
  have h := hfirst.trans hsecond
  have hleft :
      (tailTypes.append (familyCtors ++ tailCtors)).append
          (recursor :: tailRecursors) =
        ((tailTypes.append familyCtors).append tailCtors).append
          (recursor :: tailRecursors) := by
    exact congrArg (· ++ (recursor :: tailRecursors))
      (List.append_assoc tailTypes familyCtors tailCtors).symm
  have hright :
      (familyCtors.append [recursor]).append
          (tailTypes ++ tailCtors ++ tailRecursors) =
        familyCtors ++
          (recursor :: (tailTypes ++ tailCtors ++ tailRecursors)) := by
    exact (List.append_assoc familyCtors [recursor]
      (tailTypes ++ tailCtors ++ tailRecursors)).trans <|
        congrArg (familyCtors ++ ·) List.singleton_append
  exact hleft.symm ▸ hright.symm ▸ h

structure RestoredPrimaryConstantLayout (constants : List VConstVal) where
  types : List VConstVal
  ctors : List VConstVal
  recursors : List VConstVal
  grouped : types ++ ctors ++ recursors ~ constants

theorem RestoredInductiveInstallationTrace.primaryLayout
    (H : RestoredInductiveInstallationTrace safety Htrace sourceVEnv
      constants targetVEnv) :
    Nonempty (RestoredPrimaryConstantLayout constants) := by
  induction H with
  | nil => exact ⟨⟨[], [], [], .refl []⟩⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
    rcases ih with ⟨layout⟩
    refine ⟨{
      types := Hsemantic.header :: layout.types
      ctors := Hsemantic.constructors ++ layout.ctors
      recursors := Hsemantic.recursor.recursor :: layout.recursors
      grouped := ?_ }⟩
    exact (perm_group_familyConstants Hsemantic.header
      Hsemantic.recursor.recursor layout.types Hsemantic.constructors
      layout.ctors layout.recursors).trans <|
        (List.Perm.refl
          (Hsemantic.header :: Hsemantic.constructors ++
            [Hsemantic.recursor.recursor])).append layout.grouped

theorem RestoredNestedDeclarationsResult.translatedFreshOfInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceVEnv primaryConstants primaryVEnv)
    (Hauxiliary : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries out.2,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv
          (primaryConstants ++ auxiliaryConstants) outVEnv := by
  rcases Hprimary.translatedFresh hsourceWF with
    ⟨primaryEntries, HprimaryFresh, HprimaryTranslated⟩
  rcases Hauxiliary.translatedFresh
      (HprimaryFresh.targetWF hsourceWF) with
    ⟨auxiliaryEntries, HauxiliaryFresh, HauxiliaryTranslated⟩
  exact ⟨primaryEntries ++ auxiliaryEntries,
    HprimaryFresh.append HauxiliaryFresh,
    HprimaryTranslated.append HauxiliaryTranslated⟩

theorem RestoredNestedDeclarationsResult.checkingOfInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceVEnv primaryConstants primaryVEnv)
    (Hauxiliary : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety out.2 outVEnv :=
  Hauxiliary.checking (Hprimary.checking Hvalid)

/-- Compositional restored-block assembly.  Unlike
`restoredBlockCertificate`, this endpoint takes exact per-family and
per-auxiliary installation traces, so no whole-restoration semantic callback
remains. -/
theorem RestoredNestedDeclarationsResult.restoredBlockCertificateOfInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceVEnv primaryConstants primaryVEnv)
    (Hauxiliary : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Horder : block.types ++ block.ctors ++ block.recursors ~
      primaryConstants ++ auxiliaryConstants)
    (HtypesWF : ∀ ci ∈ block.types, ci.toVConstant.WF sourceVEnv)
    (HctorsWF : ∀ envTypes,
      sourceVEnv.addConstVals block.types = some envTypes →
      ∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ envTypes envCtors,
      sourceVEnv.addConstVals block.types = some envTypes →
      envTypes.addConstVals block.ctors = some envCtors →
      ∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors)
    (HrulesWF : ∀ df ∈ block.rules, df.WF outVEnv) :
    Nonempty (RestoredBlockCertificate sourceVEnv block) := by
  rcases H.translatedFreshOfInstallation Hprimary Hauxiliary hsourceWF with
    ⟨_entries, _Hfresh, Htranslated⟩
  exact ⟨{
    constants := primaryConstants ++ auxiliaryConstants
    outVEnv := outVEnv
    order := Horder
    installed := Htranslated.abstract
    typesWF := HtypesWF
    ctorsWF := HctorsWF
    recursorsWF := HrecursorsWF
    rulesWF := HrulesWF }⟩

/-- Layout-specialized restored-block assembly.  Interleaving is proved once
by `primaryLayout`; callers identify only the three canonical component
lists, rather than supplying an opaque permutation of the full block. -/
theorem RestoredNestedDeclarationsResult.restoredBlockCertificateOfLayout
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceVEnv primaryConstants primaryVEnv)
    (Hauxiliary : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (layout : RestoredPrimaryConstantLayout primaryConstants)
    (htypes : block.types = layout.types)
    (hctors : block.ctors = layout.ctors)
    (hrecursors : block.recursors = layout.recursors ++ auxiliaryConstants)
    (hsourceWF : sourceProdEnv.constants.WF)
    (HtypesWF : ∀ ci ∈ block.types, ci.toVConstant.WF sourceVEnv)
    (HctorsWF : ∀ envTypes,
      sourceVEnv.addConstVals block.types = some envTypes →
      ∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ envTypes envCtors,
      sourceVEnv.addConstVals block.types = some envTypes →
      envTypes.addConstVals block.ctors = some envCtors →
      ∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors)
    (HrulesWF : ∀ df ∈ block.rules, df.WF outVEnv) :
    Nonempty (RestoredBlockCertificate sourceVEnv block) := by
  apply H.restoredBlockCertificateOfInstallation Hprimary Hauxiliary
    hsourceWF
  · rw [htypes, hctors, hrecursors]
    simpa only [List.append_assoc] using
      layout.grouped.append_right auxiliaryConstants
  · exact HtypesWF
  · exact HctorsWF
  · exact HrecursorsWF
  · exact HrulesWF

/-- Interpret the exact auxiliary-recursors state trace into the independent
append-oriented restoration specification. The callback must justify both the
translated recursor and its guarded abstract rules from each operational
step; this theorem supplies all fold ordering and cardinality bookkeeping. -/
theorem StateForMTrace.auxiliaryRestorationPrefix
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (Hadvance : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      recursors rules,
      AuxiliaryRestorationPrefix decl block main recursors rules →
      ∃ recursor : VConstVal, ∃ newRules : List VDefEq,
        AuxiliaryRestorationPrefix decl block main
          (recursors ++ [recursor]) (rules ++ newRules))
    (recursors : List VConstVal) (rules : List VDefEq)
    (Hprefix : AuxiliaryRestorationPrefix decl block main recursors rules) :
    ∃ finalRecursors finalRules,
      AuxiliaryRestorationPrefix decl block main finalRecursors finalRules ∧
      finalRecursors.length = recursors.length + names.length := by
  induction Htrace generalizing recursors rules with
  | nil => exact ⟨recursors, rules, Hprefix, by simp⟩
  | cons Hstep Htail ih =>
    rcases Hadvance _ _ _ Hstep recursors rules
      Hprefix with ⟨recursor, newRules, Hnext⟩
    rcases ih (recursors ++ [recursor]) (rules ++ newRules) Hnext with
      ⟨finalRecursors, finalRules, Hfinal, hlength⟩
    exact ⟨finalRecursors, finalRules, Hfinal, by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength⟩

/-- Empty-start specialization used by nested compilation assembly. -/
theorem StateForMTrace.auxiliaryRestoration
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (Hadvance : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      recursors rules,
      AuxiliaryRestorationPrefix decl block main recursors rules →
      ∃ recursor : VConstVal, ∃ newRules : List VDefEq,
        AuxiliaryRestorationPrefix decl block main
          (recursors ++ [recursor]) (rules ++ newRules)) :
    ∃ auxiliaryRecursors auxiliaryRules,
      AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
        auxiliaryRules ∧
      auxiliaryRecursors.length = names.length := by
  simpa using Htrace.auxiliaryRestorationPrefix Hadvance [] []
    (AuxiliaryRestorationPrefix.empty decl block main)

/-- Semantic-callback specialization of `auxiliaryRestoration`: each exact
operational step is interpreted through `RestoredAuxiliaryStepSemantics`. -/
theorem StateForMTrace.auxiliaryRestorationOfSemantics
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (Hsemantics : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      recursors rules,
      AuxiliaryRestorationPrefix decl block main recursors rules →
      Nonempty (RestoredAuxiliaryStepSemantics decl block main safety trEnv
        Hstep recursors)) :
    ∃ auxiliaryRecursors auxiliaryRules,
      AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
        auxiliaryRules ∧
      auxiliaryRecursors.length = names.length := by
  apply Htrace.auxiliaryRestoration
  intro oldRecName stepSource stepTarget Hstep recursors rules Hprefix
  rcases Hsemantics oldRecName stepSource stepTarget Hstep recursors rules
    Hprefix with ⟨Hsemantic⟩
  exact ⟨Hsemantic.recursor, Hsemantic.rules, Hsemantic.advance Hprefix⟩

theorem RestoredNestedDeclarationsResult.auxiliaryRestorationOfSemantics
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (Hsemantics : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      recursors rules,
      AuxiliaryRestorationPrefix decl block main recursors rules →
      Nonempty (RestoredAuxiliaryStepSemantics decl block main safety trEnv
        Hstep recursors)) :
    ∃ auxiliaryRecursors auxiliaryRules,
      AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
        auxiliaryRules ∧
      auxiliaryRecursors.length = auxRecNames.length :=
  H.auxiliaries.auxiliaryRestorationOfSemantics Hsemantics

/-- Source-shaped block determined by restored primary declarations and the
trace-aligned auxiliary suffix. -/
def canonicalRestoredBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  recursors := primaryRecursors ++ auxiliaryRecursors
  rules := primaryRules ++ auxiliaryRules

/-- Canonical nested-compilation endpoint.  All block layout equations are
definitional; the exact auxiliary semantic trace supplies guardedness and
sequential names. Production restoration supplies name uniqueness, with only
an order-insensitive correspondence required because restoration installs
family members interleaved rather than in abstract block order. -/
theorem RestoredNestedDeclarationsResult.canonicalNestedCompilation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (envTypes envCtors : VEnv) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : NestedRecursorCertificate decl primaryRecursors)
    (HprimaryRules : IotaBuildCertificate envCtors decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      ((canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).types ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).ctors ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).recursors).map (·.name) ~
        entries.map (·.name)) :
    Nonempty (NestedCompilationCertificate sourceEnv decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules)) := by
  let block := canonicalRestoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  have Haux : AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
      auxiliaryRules := by
    exact Hauxiliary.prefix (AuxiliaryRestorationPrefix.empty decl block main)
  rcases H.freshTrace hsourceWF with ⟨entries, Hentries⟩
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) :=
    (Hnames entries Hentries).nodup_iff.mpr
      (Hentries.namesNodup hsourceWF)
  exact ⟨NestedCompilationCertificate.ofRestoration sourceEnv envTypes
    envCtors decl block main rest
    htypesSource primaryRecursors auxiliaryRecursors primaryRules
    auxiliaryRules HprimaryRecursors HprimaryRules hprimaryLength Haux rfl rfl
    htypesAdded hctorsAdded
    rfl rfl hnames⟩

/-- Mutual-safe canonical endpoint.  The operational restoration trace fixes
the primary recursor list, while all primary recursors are interpreted in the
canonical environment containing every source constructor.  No abstract
environment is advanced in the production family-interleaved order. -/
theorem RestoredNestedDeclarationsResult.canonicalNestedCompilationOfSemanticTrace
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (envTypes envCtors : VEnv) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RestoredPrimaryRecursorSemanticTrace decl safety
      canonicalCtorEnv H.inductives (main :: rest) primaryRecursors)
    (HprimaryRules : IotaBuildCertificate envCtors decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      ((canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).types ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).ctors ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).recursors).map (·.name) ~
        entries.map (·.name)) :
    Nonempty (NestedCompilationCertificate sourceEnv decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules)) := by
  apply H.canonicalNestedCompilation envTypes envCtors rest htypesSource
    primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  · exact HprimaryRecursors.recursorCertificate htypesSource
  · exact HprimaryRules
  · exact hprimaryLength
  · exact htypesAdded
  · exact hctorsAdded
  · exact Hauxiliary
  · exact hsourceWF
  · exact Hnames

/-- Joint implementation/specification boundary for a restored nested block.
One canonical-stage semantic trace reconstructs the original source
declaration translation and certifies the exact restored primary recursors;
the auxiliary trace supplies the guarded restoration-only suffix. -/
theorem RestoredNestedDeclarationsResult.sourceCoreAndNestedCompilation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames out)
    (main : VInductiveType) (rest : List VInductiveType)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors H.inductives (main :: rest)
      primaryRecursors)
    (htypesSource : decl.types = main :: rest)
    (huvars : decl.uvars = lparams.length)
    (hnparams : decl.nparams = nparams)
    (hisUnsafe : decl.isUnsafe = isUnsafe)
    (htypesAdded : sourceVEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (HprimaryRules : IotaBuildCertificate envCtors decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      ((canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).types ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).ctors ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).recursors).map (·.name) ~
        entries.map (·.name)) :
    TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe decl
        envTypes envCtors ∧
      Nonempty (NestedCompilationCertificate sourceVEnv decl
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules)) := by
  refine ⟨Hsource.core htypesSource huvars hnparams hisUnsafe htypesAdded
    hctorsAdded, ?_⟩
  apply H.canonicalNestedCompilation envTypes envCtors rest htypesSource
    primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  · exact Hsource.recursorCertificate htypesSource
  · exact HprimaryRules
  · exact hprimaryLength
  · exact htypesAdded
  · exact hctorsAdded
  · exact Hauxiliary
  · exact hsourceWF
  · exact Hnames

/-- Trace-aligned form of `canonicalNestedCompilation`.  The primary
recursor certificate is derived from the exact restored installation trace,
so the abstract `NestedRecursorShape` witnesses cannot describe a detached
list. -/
theorem RestoredNestedDeclarationsResult.canonicalNestedCompilationOfInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceEnv primaryConstants primaryVEnv)
    (envTypes envCtors : VEnv) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RestoredPrimaryRecursorCertificate decl result
      loweredEnv auxRec allIndNames safety H.inductives Hprimary
      primaryRecursors)
    (HprimaryRules : IotaBuildCertificate envCtors decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      ((canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).types ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).ctors ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).recursors).map (·.name) ~
        entries.map (·.name)) :
    Nonempty (NestedCompilationCertificate sourceEnv decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules)) := by
  exact H.canonicalNestedCompilation envTypes envCtors rest htypesSource
    primaryRecursors auxiliaryRecursors primaryRules auxiliaryRules
    HprimaryRecursors.recursorCertificate HprimaryRules hprimaryLength
    htypesAdded hctorsAdded Hauxiliary hsourceWF Hnames

/-- Fully structural primary-recursor specialization.  The family-indexed
shape fold itself supplies both trace alignment and the indexed
`RecursorCertificate` consumed by nested compilation. -/
theorem RestoredNestedDeclarationsResult.canonicalNestedCompilationOfShapes
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceEnv primaryConstants primaryVEnv)
    (envTypes envCtors : VEnv) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryShapes : RestoredPrimaryRecursorShapes decl result loweredEnv
      auxRec allIndNames safety Hprimary (main :: rest) primaryRecursors)
    (HprimaryRules : IotaBuildCertificate envCtors decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      ((canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).types ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).ctors ++
        (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
          primaryRules auxiliaryRules).recursors).map (·.name) ~
        entries.map (·.name)) :
    Nonempty (NestedCompilationCertificate sourceEnv decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules)) := by
  apply H.canonicalNestedCompilationOfInstallation Hprimary envTypes envCtors
    rest htypesSource primaryRecursors auxiliaryRecursors primaryRules
    auxiliaryRules
  · exact HprimaryShapes.certificate htypesSource
  · exact HprimaryRules
  · exact hprimaryLength
  · exact htypesAdded
  · exact hctorsAdded
  · exact Hauxiliary
  · exact hsourceWF
  · exact Hnames

/-- Assemble the independent nested-compilation certificate from the exact
restoration trace. Primary recursors/rules retain their ordinary certificates;
the operational auxiliary suffix is interpreted by `Hsemantics`. -/
theorem RestoredNestedDeclarationsResult.nestedCompilationCertificate
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hsemantics : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      recursors rules,
      AuxiliaryRestorationPrefix decl block main recursors rules →
      Nonempty (RestoredAuxiliaryStepSemantics decl block main safety trEnv
        Hstep recursors))
    (envTypes envCtors : VEnv) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors : List VConstVal) (primaryRules : List VDefEq)
    (HprimaryRecursors : NestedRecursorCertificate decl primaryRecursors)
    (HprimaryRules : IotaBuildCertificate envCtors decl block primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (htypesAdded : sourceEnv.addConstVals block.types = some envTypes)
    (hctorsAdded : envTypes.addConstVals block.ctors = some envCtors)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hlayout : ∀ auxiliaryRecursors auxiliaryRules,
      AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
        auxiliaryRules →
      block.recursors = primaryRecursors ++ auxiliaryRecursors ∧
      block.rules = primaryRules ++ auxiliaryRules)
    (Hnames : ∀ entries,
      FreshConstantTrace sourceProdEnv entries out.2 →
      (block.types ++ block.ctors ++ block.recursors).map (·.name) =
        entries.map (·.name)) :
    Nonempty (NestedCompilationCertificate sourceEnv decl block) := by
  rcases H.auxiliaryRestorationOfSemantics Hsemantics with
    ⟨auxiliaryRecursors, auxiliaryRules, Haux, _hlength⟩
  rcases Hlayout auxiliaryRecursors auxiliaryRules Haux with
    ⟨hrecursors, hrules⟩
  rcases H.freshTrace hsourceWF with ⟨entries, Hentries⟩
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    rw [Hnames entries Hentries]
    exact Hentries.namesNodup hsourceWF
  exact ⟨NestedCompilationCertificate.ofRestoration sourceEnv envTypes
    envCtors decl block main rest
    htypesSource primaryRecursors auxiliaryRecursors primaryRules
    auxiliaryRules HprimaryRecursors HprimaryRules hprimaryLength Haux htypes
    hctors htypesAdded hctorsAdded hrecursors hrules hnames⟩

/-- Syntactic facts that must hold before an expression can be treated as a
nested occurrence. The environment lookup and parameter scan are certified
separately, at the point where their reader/state effects are exposed. -/
structure NestedAppShape (e : Expr) : Prop where
  isApp : e.isApp = true
  constHead : ∃ fn levels, e.getAppFn = .const fn levels

theorem isNestedInductiveApp_shape
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.1.isSome → NestedAppShape e := by
  intro out hout hsome
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp only [happ, Bool.not_false, if_true] at hout
    change Except.ok (none, state) = .ok out at hout
    cases hout
    simp at hsome
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      exact ⟨happTrue, ⟨fn, levels, hhead⟩⟩
    | _ =>
      simp [happTrue, hhead, ReaderT.pure, StateT.pure] at hout
      cases hout
      simp at hsome

/-- Independent specification of the occurrence test used while scanning
parameters of a previously declared inductive application. -/
def MentionsNestedNewType
    (newTypes : Array InductiveType) (e : Expr) : Prop :=
  (e.find? fun
    | .const name _ => newTypes.any fun type => name == type.name
    | _ => false).isSome

theorem mentionsNestedNewType_iff
    (newTypes : Array InductiveType) (e : Expr) :
    Lean4Lean.ElimNestedInductive.mentionsNestedNewType newTypes e = true ↔
      MentionsNestedNewType newTypes e := by
  rfl

theorem nestedParamFlags_fst
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).1 = true ↔
      ∃ i, i < n ∧ MentionsNestedNewType newTypes args[i]! := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_true, ih, mentionsNestedNewType_iff]
    constructor
    · rintro (⟨i, hi, hmentions⟩ | hmentions)
      · exact ⟨i, by omega, hmentions⟩
      · exact ⟨n, by omega, hmentions⟩
    · rintro ⟨i, hi, hmentions⟩
      by_cases h : i = n
      · subst i; exact Or.inr hmentions
      · exact Or.inl ⟨i, by omega, hmentions⟩

theorem nestedParamFlags_snd_false
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).2 = false ↔
      ∀ i, i < n → args[i]!.hasLooseBVars = false := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hprev, hn⟩ i hi
      by_cases h : i = n
      · simpa [h] using hn
      · exact hprev i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall n (by omega)⟩

/-- Abstract contract for the parameter scan in
`isNestedInductiveApp?`: the application has enough arguments, at least one
parameter mentions a family currently being lowered, and every scanned
parameter is closed with respect to bound variables. -/
structure NestedParameterScan
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) : Prop where
  arity : n ≤ args.size
  nested : ∃ i, i < n ∧ MentionsNestedNewType newTypes args[i]!
  closed : ∀ i, i < n → args[i]!.hasLooseBVars = false

theorem NestedParameterScan.noLoose
    (H : NestedParameterScan newTypes args n) (hi : i < n) :
    args[i]!.hasLooseBVars = false :=
  H.closed i hi

theorem NestedParameterScan.hasOccurrence
    (H : NestedParameterScan newTypes args n) :
    ∃ i, i < args.size ∧ MentionsNestedNewType newTypes args[i]! := by
  rcases H.nested with ⟨i, hi, hmentions⟩
  exact ⟨i, Nat.lt_of_lt_of_le hi H.arity, hmentions⟩

/-- Full abstract acceptance contract for nested-application recognition.
This is deliberately stated without reference to the executable loop, so its
eventual refinement theorem cannot silently inherit an implementation bug. -/
structure NestedAppCandidate (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (e : Expr) (info : InductiveVal) : Prop where
  shape : NestedAppShape e
  headFound : ∃ fn levels, e.getAppFn = .const fn levels ∧
    env.find? fn = some (.inductInfo info)
  parameters : NestedParameterScan state.newTypes e.getAppArgs info.numParams

/-- Recognition is maximal over an application spine: adding trailing
arguments preserves a nested-family candidate because only its leading
parameter prefix is inspected. -/
theorem NestedAppCandidate.app
    (H : NestedAppCandidate env state fn info) (arg : Expr) :
    NestedAppCandidate env state (.app fn arg) info := by
  have hargs : (Expr.app fn arg).getAppArgs = fn.getAppArgs.push arg := by
    rw [Expr.getAppArgs_eq, Expr.getAppArgs_eq, Expr.getAppArgsList_app]
    simp
  refine {
    shape := ⟨rfl, ?_⟩
    headFound := ?_
    parameters := ?_ }
  · rcases H.shape.constHead with ⟨name, levels, hhead⟩
    exact ⟨name, levels, by simpa [Expr.getAppFn] using hhead⟩
  · rcases H.headFound with ⟨name, levels, hhead, hfound⟩
    exact ⟨name, levels, by simpa [Expr.getAppFn] using hhead, hfound⟩
  · refine {
      arity := by
        rw [hargs]
        exact Nat.le_trans H.parameters.arity (by simp)
      nested := ?_
      closed := ?_ }
    · rcases H.parameters.nested with ⟨i, hi, hmentions⟩
      refine ⟨i, hi, ?_⟩
      have hiOld : i < fn.getAppArgs.size :=
        Nat.lt_of_lt_of_le hi H.parameters.arity
      have hiPush : i < (fn.getAppArgs.push arg).size := by simp; omega
      have hbang : (fn.getAppArgs.push arg)[i]! = fn.getAppArgs[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hiPush, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hargs, hbang]
      exact hmentions
    · intro i hi
      have hiOld : i < fn.getAppArgs.size :=
        Nat.lt_of_lt_of_le hi H.parameters.arity
      have hiPush : i < (fn.getAppArgs.push arg).size := by simp; omega
      have hbang : (fn.getAppArgs.push arg)[i]! = fn.getAppArgs[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hiPush, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hargs, hbang]
      exact H.parameters.closed i hi

theorem isNestedInductiveApp_candidate
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => ∀ info, out.1 = some info →
        NestedAppCandidate env state e info := by
  intro out hout info hinfo
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    simp at hinfo
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        change Except.ok (none, state) = .ok out at hout
        cases hout
        simp at hinfo
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            simp at hinfo
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              simp at hinfo
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                simp only [Option.some.injEq] at hinfo
                subst info
                refine {
                  shape := ⟨happTrue, ⟨fn, levels, hhead⟩⟩
                  headFound := ⟨fn, levels, hhead, hfound⟩
                  parameters := ?_ }
                refine {
                  arity := by omega
                  nested := (nestedParamFlags_fst
                    state.newTypes e.getAppArgs ci.numParams).mp hnestedTrue
                  closed := (nestedParamFlags_snd_false
                    state.newTypes e.getAppArgs ci.numParams).mp hlooseFalse }
        | _ =>
          simp [hfound] at hout
          change Except.ok (none, state) = .ok out at hout
          cases hout
          simp at hinfo
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      simp at hinfo

/-- Completeness of the independent recognition contract: every abstract
candidate is returned by the executable recognizer. -/
theorem NestedAppCandidate.recognized
    (H : NestedAppCandidate env state e info) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.1 = some info := by
  intro out hout
  rcases H.headFound with ⟨fn, levels, hhead, hfound⟩
  have hnested :
      (Lean4Lean.ElimNestedInductive.nestedParamFlags state.newTypes
        e.getAppArgs info.numParams).1 = true :=
    (nestedParamFlags_fst state.newTypes e.getAppArgs info.numParams).mpr
      H.parameters.nested
  have hloose :
      (Lean4Lean.ElimNestedInductive.nestedParamFlags state.newTypes
        e.getAppArgs info.numParams).2 = false :=
    (nestedParamFlags_snd_false state.newTypes e.getAppArgs
      info.numParams).mpr H.parameters.closed
  have harity : ¬ e.getAppArgs.size < info.numParams :=
    Nat.not_lt_of_ge H.parameters.arity
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  simp only [H.shape.isApp, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hhead, Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
  simp [hfound, harity, hnested, hloose] at hout
  cases hout
  rfl

def NoNestedAppCandidate (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) (e : Expr) : Prop :=
  ∀ info, ¬ NestedAppCandidate env state e info

theorem isNestedInductiveApp_preservesState
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.2 = state := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    rfl
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        cases hout
        rfl
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            rfl
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              rfl
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                rfl
        | _ =>
          simp [hfound] at hout
          cases hout
          rfl
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      rfl

/-- Reader/state bind specialized to nested lowering. -/
theorem nestedBind.WF
    {α β : Type} {P : α × Lean4Lean.ElimNestedInductive.State → Prop}
    {Q : β × Lean4Lean.ElimNestedInductive.State → Prop}
    {x : Lean4Lean.ElimNestedInductive.M α}
    {f : α → Lean4Lean.ElimNestedInductive.M β}
    (Hx : (x env state).WF P)
    (Hf : ∀ a nextState, P (a, nextState) →
      (f a env nextState).WF Q) :
    ((x >>= f) env state).WF Q := by
  exact Hx.bind fun result hresult => Hf result.1 result.2 hresult

/-- A reviewable trace of the mutual-family generation loop.  Each list member
has one certified fresh-generation step, and the accumulator passed to the
tail is exactly the executable `Option.or` update. -/
inductive GeneratedAuxiliaryBatch
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) : Option Expr → List Name →
      Lean4Lean.ElimNestedInductive.State →
      Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | nil (hresult : result.isSome = true) :
      GeneratedAuxiliaryBatch env lctx params As targetName levels nparams args
        result [] state (result, state)
  | cons :
      GeneratedAuxiliary env lctx params As targetName levels nparams args
        sourceName sourceInfo state step →
      GeneratedAuxiliaryBatch env lctx params As targetName levels nparams args
        (step.1.or result) sourceNames step.2 out →
      GeneratedAuxiliaryBatch env lctx params As targetName levels nparams args
        result (sourceName :: sourceNames) state out

theorem GeneratedAuxiliaryBatch.resultSome
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : out.1.isSome = true := by
  induction H with
  | nil hresult => exact hresult
  | cons _ _ ih => exact ih

theorem GeneratedAuxiliaryBatch.appendSizes
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) :
    out.2.nestedAux.size = state.nestedAux.size + sourceNames.length ∧
    out.2.newTypes.size = state.newTypes.size + sourceNames.length := by
  induction H with
  | nil => simp
  | cons Hstep Htail ih =>
    rcases Hstep.generated with
      ⟨auxName, nextIdx, data, Hfresh, Hdata, hresult, hstate⟩
    constructor
    · rw [ih.1, hstate]
      simp only [Array.size_push, List.length_cons]
      omega
    · rw [ih.2, hstate]
      simp only [Array.size_push, List.length_cons]
      omega

theorem GeneratedAuxiliaryBatch.auxFVarsIn
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (HAs : LocalForallSelection lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih =>
    exact ih (Hstep.auxFVarsIn HAs hnparams Hlevels Hargs Hparams Hstate)

theorem GeneratedAuxiliaryBatch.pendingNewTypesClosed
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih =>
    exact ih (Hstep.pendingNewTypesClosed Henv Hclosing Hlevels Hargs Hstate)

private theorem generateAuxiliariesLoop_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (hsize : As.size = params.size)
    (sourceNames : List Name) (infos : InductiveMemberInfos env sourceNames)
    (result : Option Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hready : result.isSome = true ∨ targetName ∈ sourceNames) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop lctx params As
      targetName levels nparams args result sourceNames env state).WF fun out =>
        GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
          args result sourceNames state out := by
  induction infos generalizing result state with
  | nil =>
    rcases hready with hsome | hmem
    · simp only [Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop,
        hsome, ↓reduceIte, pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure (.nil hsome)
    · simp at hmem
  | @cons sourceName sourceInfo sourceNames hlookup infos ih =>
    rw [Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop]
    refine nestedBind.WF
      (generateAuxiliary_refines env lctx params As targetName levels nparams
        args sourceName sourceInfo state hlookup hsize) ?_
    intro found nextState Hstep
    have hnext : (found.or result).isSome = true ∨
        targetName ∈ sourceNames := by
      rcases hready with hsome | hmem
      · left
        cases found <;> cases result <;> simp_all
      · simp only [List.mem_cons] at hmem
        rcases hmem with heq | htail
        · subst sourceName
          left
          rcases Hstep.generated with
            ⟨auxName, nextIdx, data, Hfresh, Hdata, hfound, hstate⟩
          simp only [beq_self_eq_true, if_true] at hfound
          rw [hfound]
          simp
        · exact Or.inr htail
    exact (ih (result := found.or result) (state := nextState) hnext).mono
      fun _ Htail => .cons Hstep Htail

theorem generateAuxiliaries_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (value : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (infos : InductiveMemberInfos env value.all)
    (htarget : targetName ∈ value.all) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliaries lctx params As targetName
      levels nparams args value env state).WF fun out =>
        GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
          args none value.all state out := by
  unfold Lean4Lean.ElimNestedInductive.generateAuxiliaries
  exact generateAuxiliariesLoop_refines env lctx params As targetName levels
    nparams args hsize value.all infos none state (Or.inr htarget)

theorem addConstant_find_self
    (env : Environment) (info : ConstantInfo)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none) :
    (Lean4Lean.AddInductive.addConstant env info).find? info.name = some info := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change (env.constants.insert info.name info).find?' info.name = some info
  rw [(hwf.insert info.name info hfresh).find?'_eq_find?, hwf.find?_insert]
  simp

theorem addConstant_find_of_ne
    (env : Environment) (info : ConstantInfo) (name : Name)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none)
    (hne : info.name ≠ name) (hfind : env.find? name = some found) :
    (Lean4Lean.AddInductive.addConstant env info).find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh hfind
  change (env.constants.insert info.name info).find?' name = some found
  rw [(hwf.insert info.name info hfresh).find?'_eq_find?, hwf.find?_insert]
  split
  · rename_i heq
    exact False.elim (hne (by simpa using heq))
  · exact hfind

theorem addConstant_find_cases
    (env : Environment) (info : ConstantInfo) (name : Name)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none)
    (hfind : (Lean4Lean.AddInductive.addConstant env info).find? name =
      some found) :
    (name = info.name ∧ found = info) ∨ env.find? name = some found := by
  have hfreshMap : env.constants.find? info.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change (env.constants.insert info.name info).find?' name = some found at hfind
  rw [(hwf.insert info.name info hfreshMap).find?'_eq_find?,
    hwf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    left
    simp only [Option.some.injEq] at hfind
    have hEq : info.name = name := by simpa using heq
    exact ⟨hEq.symm, hfind.symm⟩
  · right
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

/-- A lockstep installation preserves every lookup from its source production
environment. -/
theorem AddConstants.preservesFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    outEnv.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hfind] at hn
      contradiction
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    apply ih hnextWF
    change (Lean4Lean.AddInductive.addConstant envHead ci).find? name = some found
    exact addConstant_find_of_ne envHead ci name hwf hn hne hfind

/-- Every lookup in the target of a lockstep installation either came from
the source environment or is one of the exact newly installed production
entries. -/
theorem AddConstants.origin
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : outEnv.find? name = some found) :
    env.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.1.name ∧ found = entry.1 := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · rcases addConstant_find_cases envHead ci name hwf hn hnext with
        ⟨hname, hfound⟩ | hold
      · exact Or.inr ⟨(ci, ci'), by simp, hname, hfound⟩
      · exact Or.inl hold
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

theorem AddConstants.entryNames
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hentry : entry ∈ entries) : entry.1.name = entry.2.name := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact htr.2
    · exact ih htail

theorem AddConstants.entrySafety
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hentry : entry ∈ entries) : safety ≤ entry.1.safety := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact htr.1.1
    · exact ih htail

/-- A successful lockstep installation makes every constructor recognized as
belonging to a fresh auxiliary family absent from the original abstract
environment. -/
theorem AddConstants.restoreAuxConstructorsFresh
    (H : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (Hfamilies : RestoreAuxFamiliesFresh result sourceProdEnv) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  intro name nested auxFamily hrecognized
  rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
      hrecognized with ⟨⟨info, hlookup, hfamily, hmap⟩⟩
  rcases H.origin hwf hlookup with hold | hnew
  · rcases Howners name info hold with ⟨owner, howner⟩
    have hfresh := Hfamilies info.induct nested hmap
    rw [howner] at hfresh
    contradiction
  · rcases hnew with ⟨entry, hentry, hname, hfound⟩
    have habstractFresh := (VEnv.addConstVals_names_fresh H.abstract).2
      entry.2 (List.mem_map.mpr ⟨entry, hentry, rfl⟩)
    have hentryNames := H.entryNames hentry
    rw [hname, hentryNames]
    exact habstractFresh

/-- Every production entry named by an `AddConstants` certificate is present
with its exact metadata in the final environment. -/
theorem AddConstants.findOfMem
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    outEnv.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons] at hentry
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases hentry with hhead | htail
    · have hinstalled : outProd.find? ci.name = some ci := by
        apply Htail.preservesFind hnextWF
        change (Lean4Lean.AddInductive.addConstant envHead ci).find? ci.name = some ci
        exact addConstant_find_self envHead ci hwf hn
      have hi : info = ci := congrArg Prod.fst hhead
      simpa [hi] using hinstalled
    · exact ih hnextWF htail

/-- Exact lookup effect of the executable mutual-header installation fold. -/
structure DeclaredInductiveInfos
    (source : Environment) (infos : List InductiveVal)
    (target : Environment) : Prop where
  mapWF : target.constants.WF
  preserves : ∀ {name found}, source.find? name = some found →
    target.find? name = some found
  origin : ∀ {name found}, target.find? name = some found →
    source.find? name = some found ∨
      ∃ info ∈ infos, name = info.name ∧ found = .inductInfo info
  installed : ∀ info ∈ infos,
    target.find? info.name = some (.inductInfo info)
  sourceFresh : ∀ info ∈ infos, source.find? info.name = none
  namesNodup : (infos.map (fun info => info.name)).Nodup

theorem declareInductiveTypeInfos_refines
    (allowPrimitive : Bool) (infos : List InductiveVal) (env : Environment)
    (hwf : env.constants.WF) :
    (Lean4Lean.AddInductive.declareInductiveTypeInfos
      allowPrimitive infos env).WF fun out =>
        DeclaredInductiveInfos env infos out := by
  induction infos generalizing env with
  | nil =>
    simp only [Lean4Lean.AddInductive.declareInductiveTypeInfos]
    exact Except.WF.pure ⟨hwf, fun h => h, fun h => Or.inl h,
      by simp, by simp, by simp⟩
  | cons info infos ih =>
    rw [Lean4Lean.AddInductive.declareInductiveTypeInfos]
    exact (checkName.WF hwf info.name allowPrimitive).bind fun _ hchecked => by
      have hfresh := hchecked.1
      have hfreshMap : env.constants.find? info.name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
      let nextEnv := Lean4Lean.AddInductive.addConstant env (.inductInfo info)
      have hnextWF : nextEnv.constants.WF := by
        change (env.constants.insert info.name (.inductInfo info)).WF
        exact hwf.insert info.name (.inductInfo info) hfreshMap
      exact (ih nextEnv hnextWF).mono fun out Htail => by
        refine ⟨Htail.mapWF, ?_, ?_, ?_, ?_, ?_⟩
        · intro name found hfind
          have hne : info.name ≠ name := by
            intro heq
            subst name
            rw [hfind] at hfresh
            contradiction
          exact Htail.preserves
            (addConstant_find_of_ne env (.inductInfo info) name hwf
              hfresh hne hfind)
        · intro name found hfind
          rcases Htail.origin hfind with hnext | ⟨tail, htail, hname, hfound⟩
          · rcases addConstant_find_cases env (.inductInfo info) name hwf
                hfresh hnext with hhead | hold
            · right
              exact ⟨info, by simp, hhead.1, hhead.2⟩
            · exact Or.inl hold
          · right
            exact ⟨tail, by simp [htail], hname, hfound⟩
        · have hinstalledHead := Htail.preserves
            (addConstant_find_self env (.inductInfo info) hwf hfresh)
          intro member hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact hinstalledHead
          · exact Htail.installed member htail
        · intro member hmember
          simp only [List.mem_cons] at hmember
          rcases hmember with rfl | htail
          · exact hfresh
          · have hnextFresh := Htail.sourceFresh member htail
            by_cases hsame : info.name = member.name
            · have hnextFind :
                  nextEnv.find? info.name = some (.inductInfo info) := by
                have hself :=
                  addConstant_find_self env (.inductInfo info) hwf hfresh
                change (Lean4Lean.AddInductive.addConstant env
                  (.inductInfo info)).find? info.name =
                    some (.inductInfo info) at hself
                simpa only [nextEnv] using hself
              rw [← hsame, hnextFind] at hnextFresh
              contradiction
            · by_contra hsource
              cases hsourceFind : env.find? member.name with
              | none => exact hsource hsourceFind
              | some found =>
                have hnextFind := addConstant_find_of_ne env
                  (.inductInfo info) member.name hwf hfresh hsame hsourceFind
                rw [hnextFind] at hnextFresh
                contradiction
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, Htail.namesNodup⟩
          intro hmemberName
          rcases List.mem_map.mp hmemberName with
            ⟨member, hmember, hname⟩
          have hnextFresh := Htail.sourceFresh member hmember
          have hnextFind :
              nextEnv.find? info.name = some (.inductInfo info) := by
            have hself :=
              addConstant_find_self env (.inductInfo info) hwf hfresh
            change (Lean4Lean.AddInductive.addConstant env
              (.inductInfo info)).find? info.name =
                some (.inductInfo info) at hself
            simpa only [nextEnv] using hself
          rw [hname, hnextFind] at hnextFresh
          contradiction

theorem InductiveMemberInfos.mapEnvironment
    (H : InductiveMemberInfos source names)
    (hpreserves : ∀ {name found}, source.find? name = some found →
      target.find? name = some found) :
    InductiveMemberInfos target names := by
  induction H with
  | nil => exact .nil
  | cons hlookup Htail ih => exact .cons (hpreserves hlookup) ih

private theorem inductiveMemberInfos_of_forall
    (infos : List InductiveVal)
    (hlookup : ∀ info ∈ infos,
      env.find? info.name = some (.inductInfo info)) :
    InductiveMemberInfos env (infos.map (fun info => info.name)) := by
  induction infos with
  | nil => exact .nil
  | cons info infos ih =>
    exact .cons (hlookup info (by simp))
      (ih fun member hmem => hlookup member (by simp [hmem]))

theorem DeclaredInductiveInfos.newMembers
    (H : DeclaredInductiveInfos source infos target) :
    InductiveMemberInfos target (infos.map (fun info => info.name)) :=
  inductiveMemberInfos_of_forall infos H.installed

/-- A lockstep installation consisting only of constructors, recursors, or
other non-inductive constants preserves closure of all mutual blocks. -/
theorem AddConstants.closesMutuals
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env)
    (hnind : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
      ∀ (value : InductiveVal),
      entry.1 ≠ ConstantInfo.inductInfo value) :
    MutualInductivesClosed outEnv := by
  induction H with
  | nil => exact hclosed
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn _ _ _ _ _ Htail ih =>
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (env.add ci).constants.WF := by
      change (env.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    have hclosedNext : MutualInductivesClosed (env.add ci) := by
      change MutualInductivesClosed
        (Lean4Lean.AddInductive.addConstant env ci)
      exact hclosed.addNonInductive hwf hn
        (fun value => hnind (ci, ci') (by simp) value)
    exact ih hnextWF hclosedNext fun entry hentry value =>
      hnind entry (by simp [hentry]) value

theorem DeclaredConstructorsResult.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : DeclaredConstructorsResult H outEnv)
    (hclosed : MutualInductivesClosed headerEnv) :
    MutualInductivesClosed outEnv :=
  R.installed.closesMutuals H.context.checking.tr.map_wf hclosed
    R.nonInductive

theorem GeneratedRecursors.closesMutuals
    (H : GeneratedRecursors safety sourceEnv lparams elimLevel c stats
      indTypes recInfos entries)
    (Hinstalled : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env) :
    MutualInductivesClosed outEnv := by
  apply Hinstalled.closesMutuals hwf hclosed
  intro entry hmem inductiveValue
  rcases entry with ⟨info, value⟩
  exact H.nonInductive info value hmem inductiveValue

/-- Add the lookup invariant to an already verified constructor phase without
replaying either executable fold. -/
theorem constructorPhasesAndClosure
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (Hphases :
      ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
        AddInductive.declareConstructors stats indTypes isUnsafe)
        { c with env := headerEnv }).WF fun outEnv =>
          ∃ _ : ConstructorPhasesResult H outEnv, True)
    (hclosed : MutualInductivesClosed headerEnv) :
    ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : ConstructorPhasesResult H outEnv,
          MutualInductivesClosed outEnv := by
  intro outEnv hout
  rcases Hphases outEnv hout with ⟨R, _⟩
  exact ⟨R, R.declared.closesMutuals hclosed⟩

/-- Add the lookup invariant to the public recursor-installation refinement.
The generated-recursors certificate supplies the required non-inductive
shape of every installed production entry. -/
theorem declareRecursorsAndClosure
    (k : Bool)
    (Hrecursors :
      (AddInductive.declareRecursors stats indTypes elimLevel recInfos k c).WF
        fun outEnv =>
          ∃ outVEnv : VEnv,
          ∃ entries : List (ConstantInfo × VConstVal),
            Nonempty (GeneratedRecursors c.safety venv c.lparams elimLevel c
              stats indTypes recInfos entries) ∧
            AddConstants c.safety c.env venv entries outEnv outVEnv)
    (hwf : c.env.constants.WF)
    (hclosed : MutualInductivesClosed c.env) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety venv c.lparams elimLevel c
            stats indTypes recInfos entries) ∧
          AddConstants c.safety c.env venv entries outEnv outVEnv ∧
          MutualInductivesClosed outEnv := by
  intro outEnv hout
  rcases Hrecursors outEnv hout with
    ⟨outVEnv, entries, ⟨Hgenerated⟩, Hinstalled⟩
  exact ⟨outVEnv, entries, ⟨Hgenerated⟩, Hinstalled,
    Hgenerated.closesMutuals Hinstalled hwf hclosed⟩

theorem DeclaredInductiveInfos.closesMutuals
    (H : DeclaredInductiveInfos source infos target)
    (hold : MutualInductivesClosed source)
    (huniform : ∀ info ∈ infos,
      info.all = infos.map (fun member => member.name)) :
    MutualInductivesClosed target := by
  intro targetName value hfind
  rcases H.origin hfind with holdLookup |
      ⟨info, hinfo, hname, hvalue⟩
  · have Hclosure := hold targetName value holdLookup
    exact ⟨Hclosure.members.mapEnvironment H.preserves, Hclosure.target,
      Hclosure.names⟩
  · cases hvalue
    have hmembers := H.newMembers
    rw [← huniform value hinfo] at hmembers
    exact ⟨hmembers, by
      rw [hname]
      rw [huniform value hinfo]
      exact List.mem_map.mpr ⟨value, hinfo, rfl⟩, by
        rw [huniform value hinfo]
        exact H.namesNodup⟩

private theorem property_of_mem_zipWith
    (f : α → β → γ) (P : γ → Prop)
    (hproperty : ∀ a b, P (f a b)) :
    ∀ {as : List α} {bs : List β} {value : γ},
      value ∈ List.zipWith f as bs → P value := by
  intro as
  induction as with
  | nil => simp
  | cons a as ih =>
    intro bs value hmem
    cases bs with
    | nil => simp at hmem
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact hproperty a b
      · exact ih htail

private theorem zipWith_left_projection
    (g : α → γ) {as : List α} {bs : List β}
    (hlength : bs.length = as.length) :
    List.zipWith (fun a _ => g a) as bs = as.map g := by
  induction as generalizing bs with
  | nil => simpa using hlength
  | cons a as ih =>
    cases bs with
    | nil => simp at hlength
    | cons b bs =>
      have hlength' : bs.length = as.length := by
        simp only [List.length_cons] at hlength
        omega
      simp [ih hlength']

theorem inductiveTypeInfos_uniformAll
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size) :
    ∀ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
      numNested isUnsafe lparams).toList,
      info.all =
        (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
          isUnsafe lparams).toList.map (fun member => member.name) := by
  intro info hinfo
  simp [AddInductive.inductiveTypeInfos, hsize] at hinfo ⊢
  have hall := property_of_mem_zipWith
    (fun (indType : InductiveType) (numIndices : Nat) =>
      show InductiveVal from {
        name := indType.name
        levelParams := lparams
        type := indType.type
        numParams := numParams
        numIndices := numIndices
        all := indTypes.toList.map (fun type => type.name)
        numNested := numNested
        isUnsafe := isUnsafe
        ctors := indType.ctors.map (fun ctor => ctor.name)
        isRec := AddInductive.isRec indTypes stats.indConsts
        isReflexive := AddInductive.isReflexive indTypes stats.indConsts })
    (fun generated =>
      generated.all = indTypes.toList.map (fun type => type.name))
    (by intro _a _b; rfl) hinfo
  have hlength : stats.nindices.toList.length = indTypes.toList.length := by
    simpa using hsize
  exact hall.trans (zipWith_left_projection
    (fun type : InductiveType => type.name) hlength).symm

theorem inductiveTypeInfos_source_mem
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size)
    (howner : owner ∈ indTypes.toList) :
    ∃ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
        numNested isUnsafe lparams).toList,
      info.name = owner.name ∧
      info.ctors = owner.ctors.map (fun ctor => ctor.name) ∧
      info.all = indTypes.toList.map (fun type => type.name) := by
  rcases List.mem_iff_getElem.mp howner with ⟨i, hi, rfl⟩
  have hinfosSize :
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).size = indTypes.size := by
    simp [AddInductive.inductiveTypeInfos, hsize]
  let info := (AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe lparams)[i]'(by simpa [hinfosSize] using hi)
  refine ⟨info, ?_, ?_, ?_, ?_⟩
  · simpa [info] using Array.getElem_mem (xs :=
      AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams) (by simpa [hinfosSize] using hi)
  · simp [info, AddInductive.inductiveTypeInfos, hsize]
  · simp [info, AddInductive.inductiveTypeInfos, hsize]
  · simp [info, AddInductive.inductiveTypeInfos, hsize]

/-- Installing the production metadata headers closes every new mutual block
and preserves closure of the inductive blocks already present. -/
theorem declareInductiveTypes_closesMutuals
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (hwf : c.env.constants.WF)
    (hold : MutualInductivesClosed c.env)
    (hsize : stats.nindices.size = indTypes.size) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF MutualInductivesClosed := by
  unfold AddInductive.declareInductiveTypes
  exact (declareInductiveTypeInfos_refines c.allowPrimitive
    (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
      isUnsafe c.lparams).toList c.env hwf).mono fun _ Hdeclared =>
        Hdeclared.closesMutuals hold
          (inductiveTypeInfos_uniformAll stats numParams indTypes numNested
            isUnsafe c.lparams hsize)

/-- Pair the existing semantic header refinement with the independently
proved production lookup invariant for the very same executable result. -/
theorem declareInductiveTypes_headersAndClosure
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (Hheaders :
      (AddInductive.declareInductiveTypes stats numParams indTypes numNested
        isUnsafe c).WF fun outEnv =>
          ∃ _ : DeclaredHeadersResult c stats decl numParams isUnsafe depth
            sourceEnv indTypes outEnv, True)
    (hwf : c.env.constants.WF)
    (hold : MutualInductivesClosed c.env)
    (hsize : stats.nindices.size = indTypes.size) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : DeclaredHeadersResult c stats decl numParams isUnsafe depth
          sourceEnv indTypes outEnv,
          MutualInductivesClosed outEnv := by
  intro outEnv hout
  rcases Hheaders outEnv hout with ⟨Hresult, _⟩
  exact ⟨Hresult,
    declareInductiveTypes_closesMutuals stats numParams indTypes numNested
      isUnsafe c hwf hold hsize outEnv hout⟩

/-- Compositional form of the executable header/constructor prefix carrying
the mutual-lookup invariant across both environment-changing phases. -/
theorem formationCoreAndClosure
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (Htypes :
      (AddInductive.declareInductiveTypes stats numParams indTypes numNested
        isUnsafe c).WF fun headerEnv =>
          ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
            depth sourceEnv indTypes headerEnv,
            MutualInductivesClosed headerEnv)
    (Hphases : ∀ headerEnv
      (Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe depth
        sourceEnv indTypes headerEnv),
      ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
        AddInductive.declareConstructors stats indTypes isUnsafe)
        { c with env := headerEnv }).WF fun outEnv =>
          ∃ _ : ConstructorPhasesResult Hheaders outEnv, True) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv =>
        ∃ headerEnv : Environment,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth sourceEnv indTypes headerEnv,
        ∃ _ : ConstructorPhasesResult Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  exact Htypes.bind fun headerEnv Hheader => by
    rcases Hheader with ⟨Hheaders, hclosed⟩
    exact (constructorPhasesAndClosure (Hphases headerEnv Hheaders)
      hclosed).mono fun outEnv Hresult => by
        rcases Hresult with ⟨R, hclosedOut⟩
        exact ⟨headerEnv, Hheaders, R, hclosedOut⟩

/-- Formation/core specialization of `formationCoreAndClosure`, deriving the
metadata cardinality needed for mutual closure from the independently
translated headers. -/
theorem AddInductive.formationCore.closedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hnprimCtors : ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ headerEnv : Environment,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ _ : ConstructorPhasesResult Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hdecl.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, Hmaterialized.indices, List.length_map]
    exact htypesLength.symm
  have Hheaders := AddInductive.declareInductiveTypes.headersWF Hc Hdecl
    Hmaterialized hvisible hnprimTypes
  have HheadersClosed := declareInductiveTypes_headersAndClosure stats
    numParams indTypes numNested isUnsafe c Hheaders
    Hc.checking.tr.map_wf Hclosed hsize
  apply formationCoreAndClosure stats numParams indTypes numNested isUnsafe c
    HheadersClosed
  intro headerEnv Hheader
  exact AddInductive.constructorPhases.WF Hheader hconsume hlit hproj
    hunsafe hvisible hnprimCtors


end VerifyInductive
end Lean4Lean
