import Lean4Lean.Verify.Inductive.Nested.CompilationAssembly
import Lean4Lean.Verify.Inductive.Nested.OrderInsensitiveAlignment
import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.Nested.FormationEvidence
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaTrace
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryFinalTrace
import Lean4Lean.Verify.Inductive.Nested.CanonicalRestorationReplay
import Lean4Lean.Verify.Inductive.Nested.HeaderNativeEvidence
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterNativeReplay
import Lean4Lean.Verify.Inductive.Nested.FormationExpansionTrace
import Lean4Lean.Verify.Inductive.Nested.SourceCoreNativeEvidence
import Lean4Lean.Verify.Inductive.Run.SemanticRun

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

private theorem List.nodup_of_map_nodup
    {l : List α} (f : α → β) (H : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at H ⊢
    exact ⟨fun ha => H.1 (List.mem_map_of_mem ha), ih H.2⟩

private theorem List.Forall₂.right_ne_nil
    (H : List.Forall₂ R left right) (hleft : left ≠ []) : right ≠ [] := by
  cases H <;> simp_all

/-- A fresh insertion trace between fixed endpoints has a unique finite
payload up to order.  Consequently final assembly needs to align just one
exact restoration trace with canonical dependency order; every other trace
witness for the same successful run follows automatically. -/
theorem FreshConstantTrace.permOfSameTarget
    (Hleft : FreshConstantTrace source leftEntries target)
    (Hright : FreshConstantTrace source rightEntries target)
    (hsourceWF : source.constants.WF) : leftEntries ~ rightEntries := by
  have leftNodup : leftEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hleft.namesNodup hsourceWF)
  have rightNodup : rightEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hright.namesNodup hsourceWF)
  apply List.Subperm.antisymm
  · apply List.subperm_of_subset leftNodup
    intro ci hci
    have hfind := Hleft.findEntry hsourceWF hci
    rcases Hright.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hleft.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry
  · apply List.subperm_of_subset rightNodup
    intro ci hci
    have hfind := Hright.findEntry hsourceWF hci
    rcases Hleft.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hright.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry

/-- Primary restored-iota shape is independent of the block's equation
payload; only the installed recursor list occurs in `NestedIotaRule`. -/
def VInductDecl.NestedIotaRule.rebaseRecursors
    {decl : VInductDecl} {source target : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule source owner ctor rule)
    (hrecursors : source.recursors = target.recursors) :
    decl.NestedIotaRule target owner ctor rule where
  recursor := H.recursor
  recursor_mem := by rw [← hrecursors]; exact H.recursor_mem
  recursor_shape := H.recursor_shape
  rule_uvars := H.rule_uvars
  domains := H.domains
  lhsBody := H.lhsBody
  rhsBody := H.rhsBody
  typeBody := H.typeBody
  lhs_wrapped := H.lhs_wrapped
  rhs_wrapped := H.rhs_wrapped
  type_wrapped := H.type_wrapped
  recursorLevels := H.recursorLevels
  leadingArgs := H.leadingArgs
  ctorLevels := H.ctorLevels
  ctorArgs := H.ctorArgs
  lhs_pattern := H.lhs_pattern
  recursor_levels := H.recursor_levels
  ctor_levels := H.ctor_levels
  leading_arity := H.leading_arity
  constructor_arity := H.constructor_arity
  parameter_args := H.parameter_args
  domains_arity := H.domains_arity
  recursiveFields := H.recursiveFields
  fieldPositions := H.fieldPositions
  fieldPositions_eq := H.fieldPositions_eq
  fieldPositions_ordered := H.fieldPositions_ordered
  fields_at_positions := H.fields_at_positions
  recursiveArgs := H.recursiveArgs
  recursiveArgs_eq := H.recursiveArgs_eq
  recursive_args := H.recursive_args
  fieldVars := H.fieldVars
  fieldVars_eq := H.fieldVars_eq
  fields_in_scope := H.fields_in_scope
  minorVar := H.minorVar
  minor_in_scope := H.minor_in_scope
  rhsArgs := H.rhsArgs
  rhs_spine := H.rhs_spine
  field_args := H.field_args
  recursive_results := H.recursive_results
  rhs_guarded := by rw [← hrecursors]; exact H.rhs_guarded

theorem NestedIotaBuildCertificate.rebaseRecursors
    {decl : VInductDecl} {source target : VInductBlock}
    {rules : List VDefEq}
    (H : NestedIotaBuildCertificate decl source rules)
    (hrecursors : source.recursors = target.recursors) :
    NestedIotaBuildCertificate decl target rules where
  covered := H.covered
  shapes i hrule hctor := by
    rcases H.shapes i hrule hctor with ⟨Hrule⟩
    exact ⟨VInductDecl.NestedIotaRule.rebaseRecursors Hrule hrecursors⟩

/-- Rule-free block used while the primary restoration fold discovers the
actual primary rule list. -/
def canonicalRestoredShapeBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal) : VInductBlock :=
  canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors [] []

/-- The final result of nested restoration, relating the returned production
environment to the constant stage of the abstract extension and retaining the
complete independent `AddInduct` judgment (including its restored rules). -/
structure NestedFinalEnvironmentResult (sourceEnv : VEnv)
    (decl : VInductDecl) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (safety : DefinitionSafety) (outEnv : Environment) where
  envTypes : VEnv
  envCtors : VEnv
  sourceCore : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  baseVEnv : VEnv
  rules : List VDefEq
  checking : CheckingEnv safety outEnv baseVEnv
  valid : CheckingEnv.Valid safety outEnv baseVEnv
  addInduct : VEnv.AddInduct sourceEnv decl (baseVEnv.addDefEqRules rules)

/-- Exact semantic payload still needed after the executable restoration fold
has completed.  The actual production trace supplies only freshness and its
family-interleaved order.  Semantic typing and abstract installation occur in
the canonical dependency order, where every mutual header precedes every
constructor.  `productionOrder` is the exact finite join between them.

This separation is essential for mutual nested declarations: asking the
abstract environment to follow production's per-family order would require a
constructor to typecheck before later sibling headers existed. -/
structure NestedFinalAssemblyCertificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety) where
  production : NestedInstalledProduction loweredEnv
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  canonicalProdEnv : Environment
  finalBaseVEnv : VEnv
  canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
    constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
  productionOrder : ∀ actualEntries,
    FreshConstantTrace sourceProdEnv actualEntries outEnv →
    actualEntries ~
      (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  main : VInductiveType
  rest : List VInductiveType
  typesSource : decl.types = main :: rest
  primaryRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  primaryRules : List VDefEq
  auxiliaryRules : List VDefEq
  sourceSemantics : RestoredSourceInductiveSemanticTrace decl lparams safety
    sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      (main :: rest)
      primaryRecursors
  primaryIota : RestoredPrimaryIotaSemanticTrace decl
    (canonicalRestoredShapeBlock decl primaryRecursors auxiliaryRecursors)
      finalBaseVEnv production sourceSemantics
      (main :: rest) primaryRules
  auxiliarySemantics : RestoredAuxiliarySemanticTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonical.venvCtors H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  typeValues : typeEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  recursorValues : recursorEntries.map Prod.snd =
    primaryRecursors ++ auxiliaryRecursors
  formationAssembly : NestedFormationAssembly sourceEnv decl
  formationExpanded : formationAssembly.expanded = production.loweredDecl
  materialized : MaterializedInductivePrefix decl production.loweredDecl
  uvars : decl.uvars = lparams.length
  numParams : decl.nparams = nparams
  unsafeEq : decl.isUnsafe = isUnsafe
  sourceNonempty : sourceTypes ≠ []
  auxiliaryWF : RestoredAuxiliaryFinalWFTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonical.venvCtors
      canonical.venvCtors
      finalBaseVEnv auxiliarySemantics [] [] auxiliaryRecursors auxiliaryRules

/-- Assemble the final certificate around the canonical replay proved from the
exact executable restoration trace.  All concrete layout, production order,
and restored constant-value equations are projections of `replay`; only the
semantic rule/formation judgments remain downstream of installation. -/
noncomputable def NestedFinalAssemblyCertificate.ofCanonicalReplay
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {envTypes envCtors : VEnv}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {canonicalProdEnv : Environment} {finalBaseVEnv : VEnv}
    (P : NestedInstalledProduction loweredEnv)
    (replay : CanonicalRestorationReplay safety sourceProdEnv outEnv sourceEnv
      envTypes envCtors decl.types primaryRecursors auxiliaryRecursors)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv replay.typeEntries
      replay.constructorEntries replay.recursorEntries canonicalProdEnv
        finalBaseVEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (main : VInductiveType) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRules auxiliaryRules : List VDefEq)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
        (main :: rest) primaryRecursors)
    (Hprimary : RestoredPrimaryIotaSemanticTrace decl
      (canonicalRestoredShapeBlock decl primaryRecursors auxiliaryRecursors)
        finalBaseVEnv P Hsource (main :: rest) primaryRules)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety canonical.venvCtors
          H.auxiliaries
          [] [] auxiliaryRecursors auxiliaryRules)
    (Hformation : NestedFormationAssembly sourceEnv decl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
    (Hmaterialized : MaterializedInductivePrefix decl P.loweredDecl)
    (huvars : decl.uvars = lparams.length)
    (hnumParams : decl.nparams = nparams)
    (hunsafeEq : decl.isUnsafe = isUnsafe)
    (hsourceNonempty : sourceTypes ≠ [])
    (HauxiliaryWF : RestoredAuxiliaryFinalWFTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety canonical.venvCtors
          canonical.venvCtors
          finalBaseVEnv Hauxiliary [] [] auxiliaryRecursors auxiliaryRules) :
    NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams isUnsafe
      safety where
  production := P
  typeEntries := replay.typeEntries
  constructorEntries := replay.constructorEntries
  recursorEntries := replay.recursorEntries
  canonicalProdEnv := canonicalProdEnv
  finalBaseVEnv := finalBaseVEnv
  canonical := canonical
  productionOrder := by
    intro actualEntries Hactual
    exact (Hactual.permOfSameTarget replay.fresh hsourceWF).trans
      replay.productionOrder
  main := main
  rest := rest
  typesSource := htypesSource
  primaryRecursors := primaryRecursors
  auxiliaryRecursors := auxiliaryRecursors
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  sourceSemantics := Hsource
  primaryIota := Hprimary
  auxiliarySemantics := Hauxiliary
  typeValues := replay.typeValues
  constructorValues := replay.constructorValues
  recursorValues := replay.recursorValues
  formationAssembly := Hformation
  formationExpanded := hformationExpanded
  materialized := Hmaterialized
  uvars := huvars
  numParams := hnumParams
  unsafeEq := hunsafeEq
  sourceNonempty := hsourceNonempty
  auxiliaryWF := HauxiliaryWF

/-- Residual final-layout evidence after the source-family and primary-iota
semantic traces have been constructed from their exact producers.  Keeping
this separate prevents the executable boundary from replacing either
semantic aggregate with an unrelated witness. -/
structure NestedFinalAssemblyRemainder
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : NestedInstalledProduction loweredEnv)
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (main : VInductiveType) (rest : List VInductiveType)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv) where
  productionOrder : ∃ actualEntries,
    FreshConstantTrace sourceProdEnv actualEntries outEnv ∧
      actualEntries ~
        (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  sourceMapWF : sourceProdEnv.constants.WF
  auxiliarySemantics : RestoredAuxiliarySemanticTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonical.venvCtors H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  recursorValues : recursorEntries.map Prod.snd =
    primaryRecursors ++ auxiliaryRecursors
  auxiliaryWF : RestoredAuxiliaryFinalWFTrace decl
    (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules) main safety canonical.venvCtors
      canonical.venvCtors
      finalBaseVEnv auxiliarySemantics [] [] auxiliaryRecursors auxiliaryRules

/-- Construct the entire post-primary remainder from the exact canonical
restoration replay and the exact auxiliary semantic/WF trace.  In
particular, production order and the recursor-value split are no longer
caller-supplied equalities. -/
noncomputable def NestedFinalAssemblyRemainder.ofCanonicalReplay
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {main : VInductiveType} {rest : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {primaryRules auxiliaryRules : List VDefEq}
    (P : NestedInstalledProduction loweredEnv)
    (replay : CanonicalRestorationReplay safety sourceProdEnv outEnv sourceEnv
      envTypes envCtors (main :: rest) primaryRecursors auxiliaryRecursors)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv replay.typeEntries
      replay.constructorEntries replay.recursorEntries canonicalProdEnv
        finalBaseVEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety canonical.venvCtors
          H.auxiliaries
          [] [] auxiliaryRecursors auxiliaryRules)
    (HauxiliaryWF : RestoredAuxiliaryFinalWFTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety canonical.venvCtors
          canonical.venvCtors
          finalBaseVEnv Hauxiliary [] [] auxiliaryRecursors auxiliaryRules) :
    NestedFinalAssemblyRemainder P H sourceEnv decl lparams nparams isUnsafe
      safety main rest primaryRecursors auxiliaryRecursors primaryRules
        auxiliaryRules replay.typeEntries replay.constructorEntries
          replay.recursorEntries canonicalProdEnv finalBaseVEnv canonical where
  productionOrder := ⟨replay.actualEntries, replay.fresh,
    replay.productionOrder⟩
  sourceMapWF := hsourceWF
  auxiliarySemantics := Hauxiliary
  recursorValues := replay.recursorValues
  auxiliaryWF := HauxiliaryWF

/-- Assemble the full certificate after its two producer-indexed semantic
traces have been built. -/
noncomputable def NestedFinalAssemblyRemainder.certificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {P : NestedInstalledProduction loweredEnv}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {main : VInductiveType} {rest : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {primaryRules auxiliaryRules : List VDefEq}
    {typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal)}
    {canonicalProdEnv : Environment} {finalBaseVEnv : VEnv}
    {canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv}
    (R : NestedFinalAssemblyRemainder (sourceTypes := sourceTypes) P H
      sourceEnv decl lparams nparams
      isUnsafe safety main rest primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules typeEntries constructorEntries
      recursorEntries canonicalProdEnv finalBaseVEnv canonical)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      (main :: rest) primaryRecursors)
    (Hprimary : RestoredPrimaryIotaSemanticTrace decl
      (canonicalRestoredShapeBlock decl primaryRecursors auxiliaryRecursors)
        finalBaseVEnv P Hsource
      (main :: rest) primaryRules)
    (htypeValues : typeEntries.map Prod.snd = decl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      decl.constructorConstants)
    (Hformation : NestedFormationAssembly sourceEnv decl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
    (Hmaterialized : MaterializedInductivePrefix decl P.loweredDecl)
    (huvars : decl.uvars = lparams.length)
    (hnumParams : decl.nparams = nparams)
    (hunsafeEq : decl.isUnsafe = isUnsafe)
    (htypesSource : decl.types = main :: rest)
    (hsourceNonempty : sourceTypes ≠ []) :
    NestedFinalAssemblyCertificate (sourceTypes := sourceTypes) H sourceEnv
      decl lparams nparams isUnsafe safety where
  production := P
  typeEntries := typeEntries
  constructorEntries := constructorEntries
  recursorEntries := recursorEntries
  canonicalProdEnv := canonicalProdEnv
  finalBaseVEnv := finalBaseVEnv
  canonical := canonical
  productionOrder := by
    intro actualEntries Hactual
    rcases R.productionOrder with
      ⟨witnessEntries, Hwitness, hwitnessOrder⟩
    exact (Hactual.permOfSameTarget Hwitness R.sourceMapWF).trans
      hwitnessOrder
  main := main
  rest := rest
  typesSource := htypesSource
  primaryRecursors := primaryRecursors
  auxiliaryRecursors := auxiliaryRecursors
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  sourceSemantics := Hsource
  primaryIota := Hprimary
  auxiliarySemantics := R.auxiliarySemantics
  typeValues := htypeValues
  constructorValues := hconstructorValues
  recursorValues := R.recursorValues
  formationAssembly := Hformation
  formationExpanded := hformationExpanded
  materialized := Hmaterialized
  uvars := huvars
  numParams := hnumParams
  unsafeEq := hunsafeEq
  sourceNonempty := hsourceNonempty
  auxiliaryWF := R.auxiliaryWF

/-- Fold primary equations while retaining membership of both the concrete
source family and its exact restored source recursor in the two aggregate
lists.  These are the two positional facts needed to connect a pointwise
restoration step back to its generated production entry and final block. -/
theorem RestoredSourceInductiveSemanticTrace.primaryIotaSemanticTraceOfMemberships
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {block : VInductBlock}
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (targetVEnv : VEnv)
    (Hfamilies : ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (_Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      (_Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors) →
      (_Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors) →
      _Hrecursor.recursor ∈ recursors →
      Nonempty (RestoredPrimaryIotaFamilySemantics decl block targetVEnv owner
        P Hstep)) :
    ∃ rules, RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource
      owners rules := by
  induction Hsource with
  | nil sourceProdEnv => exact ⟨[], .nil sourceProdEnv⟩
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    rcases Hfamilies _ _ _ _ Hstep (by simp) Hheader Hconstructors Hrecursor
        (by simp) with ⟨Hhead⟩
    rcases ih (fun indType stepSource stepTarget owner Hstep hmem Hheader
        Hconstructors Hrecursor hrecursor =>
      Hfamilies indType stepSource stepTarget owner Hstep (by simp [hmem])
        Hheader Hconstructors Hrecursor (by simp [hrecursor])) with
      ⟨tailRules, Hrules⟩
    exact ⟨Hhead.rules ++ tailRules,
      .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead.trace
        Hrules⟩

/-- Exact producer-indexed inputs for final assembly.  Source declaration
semantics and primary iota semantics are supplied one actual restoration step
at a time; neither aggregate trace nor the final certificate can be replaced
by an unrelated witness.  The residual `finish` callback begins only after
both folds have exposed their exact owner, recursor, and rule lists. -/
structure NestedFinalAssemblyProducerEvidence
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
  sourceNonempty : sourceTypes ≠ []
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
    restoredRules
    (Hprimary : RestoredPrimaryIotaSemanticTrace decl
      (canonicalRestoredShapeBlock decl primaryRecursors
        auxiliaryRecursors) finalBaseVEnv P Hsource (main :: rest)
          restoredRules),
    Nonempty (NestedFinalAssemblyRemainder P H sourceEnv decl lparams
      nparams isUnsafe safety main rest primaryRecursors
      auxiliaryRecursors restoredRules auxiliaryRules typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
      canonical)

/-- Assemble directly from a source semantic trace whose owner list is the
independently specified declaration's literal type list.  The core assembly
step therefore neither chooses an existential owner list nor accepts a
post-hoc callback identifying such a list. -/
theorem RestoredNestedDeclarationsResult.finalAssemblyOfExactSource
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (P : NestedInstalledProduction loweredEnv)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv)
    (auxiliaryRecursors : List VConstVal) (auxiliaryRules : List VDefEq)
    (htypeValues : typeEntries.map Prod.snd = decl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      decl.constructorConstants)
    (Hformation : NestedFormationAssembly sourceEnv decl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
    (Hmaterialized : MaterializedInductivePrefix decl P.loweredDecl)
    (huvars : decl.uvars = lparams.length)
    (hnumParams : decl.nparams = nparams)
    (hunsafeEq : decl.isUnsafe = isUnsafe)
    (hsourceNonempty : sourceTypes ≠ [])
    (primaryRecursors : List VConstVal)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
      decl.types primaryRecursors)
    (HprimaryFamilies : ∀ indType stepSource stepTarget owner
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
          auxiliaryRecursors) finalBaseVEnv owner P Hstep))
    (Hfinish : ∀ main rest
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
        (main :: rest) primaryRecursors)
      restoredRules
      (Hprimary : RestoredPrimaryIotaSemanticTrace decl
        (canonicalRestoredShapeBlock decl primaryRecursors
          auxiliaryRecursors) finalBaseVEnv P Hsource (main :: rest)
          restoredRules),
      Nonempty (NestedFinalAssemblyRemainder P H sourceEnv decl lparams
        nparams isUnsafe safety main rest primaryRecursors
        auxiliaryRecursors restoredRules auxiliaryRules typeEntries
        constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
        canonical)) :
    Nonempty { C : NestedFinalAssemblyCertificate H sourceEnv decl lparams
        nparams isUnsafe safety // C.production = P } := by
  have hownersNonempty : decl.types ≠ [] :=
    List.Forall₂.right_ne_nil Hsource.types hsourceNonempty
  cases htypes : decl.types with
  | nil => exact (hownersNonempty htypes).elim
  | cons main rest =>
      have Hsource' : RestoredSourceInductiveSemanticTrace decl lparams safety
          sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
          (main :: rest) primaryRecursors := by
        simpa only [htypes] using Hsource
      rcases Hsource'.primaryIotaSemanticTraceOfMemberships P finalBaseVEnv
          HprimaryFamilies with ⟨restoredRules, Hprimary⟩
      rcases Hfinish main rest Hsource' restoredRules Hprimary with ⟨R⟩
      exact ⟨⟨R.certificate Hsource' Hprimary htypeValues
        hconstructorValues Hformation hformationExpanded Hmaterialized huvars
        hnumParams hunsafeEq htypes hsourceNonempty, rfl⟩⟩

/-- Fold pointwise source-family semantics and pointwise primary-equation
semantics over the exact restoration trace, then attach only the residual
layout/auxiliary evidence.  Mutual-family order, the primary recursor list,
and the primary rule list are all outputs of the two trace folds. -/
theorem RestoredNestedDeclarationsResult.finalAssemblyOfFamilies
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (P : NestedInstalledProduction loweredEnv)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : StagedBlock safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv)
    (auxiliaryRecursors : List VConstVal) (auxiliaryRules : List VDefEq)
    (htypeValues : typeEntries.map Prod.snd = decl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      decl.constructorConstants)
    (Hformation : NestedFormationAssembly sourceEnv decl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
    (Hmaterialized : MaterializedInductivePrefix decl P.loweredDecl)
    (huvars : decl.uvars = lparams.length)
    (hnumParams : decl.nparams = nparams)
    (hunsafeEq : decl.isUnsafe = isUnsafe)
    (hsourceNonempty : sourceTypes ≠ [])
    (HexactSource : ∃ primaryRecursors,
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceEnv
        canonical.venvTypes canonical.venvCtors H.inductives decl.types
          primaryRecursors)
    (HprimaryFamilies : ∀ primaryRecursors
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
          auxiliaryRecursors) finalBaseVEnv owner P Hstep))
    (Hfinish : ∀ main rest primaryRecursors
      (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceEnv canonical.venvTypes canonical.venvCtors H.inductives
        (main :: rest) primaryRecursors)
      restoredRules
      (Hprimary : RestoredPrimaryIotaSemanticTrace decl
        (canonicalRestoredShapeBlock decl primaryRecursors
          auxiliaryRecursors) finalBaseVEnv P Hsource (main :: rest)
          restoredRules),
      Nonempty (NestedFinalAssemblyRemainder P H sourceEnv decl lparams
        nparams isUnsafe safety main rest primaryRecursors
        auxiliaryRecursors restoredRules auxiliaryRules typeEntries
        constructorEntries recursorEntries canonicalProdEnv finalBaseVEnv
        canonical)) :
    Nonempty { C : NestedFinalAssemblyCertificate H sourceEnv decl lparams
        nparams isUnsafe safety // C.production = P } := by
  rcases HexactSource with ⟨primaryRecursors, Hsource'⟩
  exact H.finalAssemblyOfExactSource P sourceEnv decl lparams nparams
    isUnsafe safety typeEntries constructorEntries recursorEntries
    canonicalProdEnv finalBaseVEnv canonical auxiliaryRecursors auxiliaryRules
    htypeValues hconstructorValues Hformation hformationExpanded Hmaterialized
    huvars hnumParams hunsafeEq hsourceNonempty primaryRecursors Hsource'
    (HprimaryFamilies primaryRecursors Hsource')
    (fun main rest Hsource restoredRules Hprimary =>
      Hfinish main rest primaryRecursors Hsource restoredRules Hprimary)

theorem NestedFinalAssemblyProducerEvidence.certificate
    (E : NestedFinalAssemblyProducerEvidence P H sourceEnv decl lparams
      nparams isUnsafe safety) :
    Nonempty { C : NestedFinalAssemblyCertificate H sourceEnv decl lparams
        nparams isUnsafe safety // C.production = P } :=
  H.finalAssemblyOfFamilies P sourceEnv decl lparams nparams isUnsafe safety
    E.typeEntries E.constructorEntries E.recursorEntries E.canonicalProdEnv
    E.finalBaseVEnv E.canonical E.auxiliaryRecursors E.auxiliaryRules
    E.typeValues E.constructorValues E.formationAssembly E.formationExpanded
    E.materialized E.uvars E.numParams E.unsafeEq E.sourceNonempty
    E.exactSource E.primaryFamilies E.finish

theorem NestedFinalAssemblyCertificate.typesAdded
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    sourceEnv.addConstVals decl.typeConstants = some C.canonical.venvTypes := by
  rw [← C.typeValues]
  exact C.canonical.typesAdded.abstract

theorem NestedFinalAssemblyCertificate.constructorsAdded
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    C.canonical.venvTypes.addConstVals decl.constructorConstants =
      some C.canonical.venvCtors := by
  rw [← C.constructorValues]
  exact C.canonical.ctorsAdded.abstract

theorem NestedFinalAssemblyCertificate.primaryIotaBuild
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    NestedIotaBuildCertificate decl
      (canonicalRestoredBlock decl C.primaryRecursors C.auxiliaryRecursors
        C.primaryRules C.auxiliaryRules) C.primaryRules :=
  (C.primaryIota.build C.typesSource).rebaseRecursors (by
    simp [canonicalRestoredShapeBlock, canonicalRestoredBlock])

/-- Assemble the final independent nested judgment and the concrete restored
environment alignment from the same trace-indexed certificate. -/
noncomputable def NestedFinalAssemblyCertificate.finalEnvironment
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
    (Hvalid : CheckingEnv.Valid safety sourceProdEnv sourceEnv) :
    NestedFinalEnvironmentResult sourceEnv decl lparams nparams sourceTypes
      isUnsafe safety outEnv := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl C.canonical.venvTypes C.canonical.venvCtors :=
    C.sourceSemantics.core C.typesSource C.uvars C.numParams C.unsafeEq
      C.typesAdded C.constructorsAdded
  let primaryConstants :=
    decl.typeConstants ++ decl.constructorConstants ++ C.primaryRecursors
  let layout : RestoredPrimaryConstantLayout primaryConstants := {
    types := decl.typeConstants
    ctors := decl.constructorConstants
    recursors := C.primaryRecursors
    grouped := by rfl }
  have hcanonicalValues :
      (C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map
          Prod.snd = primaryConstants ++ C.auxiliaryRecursors := by
    rw [List.map_append, List.map_append, C.typeValues,
      C.constructorValues, C.recursorValues]
    simp only [primaryConstants, List.append_assoc]
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshConstantTrace sourceProdEnv entries outEnv } := by
    rcases H.freshTrace Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  let HrestoredValid : CheckingEnv.Valid safety outEnv C.finalBaseVEnv :=
    C.canonical.combined.validOfFreshPermutation actual.property
      (C.productionOrder actual.val actual.property) Hvalid
  refine {
    envTypes := C.canonical.venvTypes
    envCtors := C.canonical.venvCtors
    sourceCore := Hsource
    baseVEnv := C.finalBaseVEnv
    rules := C.primaryRules ++ C.auxiliaryRules
    checking := HrestoredValid.tr
    valid := HrestoredValid
    addInduct := ?_ }
  exact H.addInductOfCanonicalInstallation C.canonical.combined
    primaryConstants C.auxiliaryRecursors hcanonicalValues layout
    C.canonical.venvTypes C.canonical.venvCtors
    C.main C.rest C.typesSource C.primaryRecursors C.auxiliaryRecursors
    C.primaryRules C.auxiliaryRules C.sourceSemantics.primaryRecursors
    C.primaryIotaBuild (C.primaryIota.length C.typesSource)
    C.auxiliarySemantics
    rfl rfl rfl rfl C.formationAssembly.formation Hsource C.sourceNonempty
    (C.sourceSemantics.typeConstantsWF C.typesSource)
    (C.sourceSemantics.constructorConstantsWF C.typesSource)
    (by
      intro ci hci
      rcases List.mem_append.mp hci with hprimary | hauxiliary
      · exact C.sourceSemantics.primaryRecursorsWF ci hprimary
      · exact C.auxiliaryWF.recursorsWF (by simp) ci hauxiliary)
    (by
      intro df hdf
      rcases List.mem_append.mp hdf with hprimary | hauxiliary
      · exact C.primaryIota.rulesWF df hprimary
      · exact C.auxiliaryWF.rulesWF (by simp) df hauxiliary)

/-- All proof-relevant data produced by a successful nested execution before
final certificate assembly.  Keeping this result independent of the final
certificate breaks the old circular API in which execution could expose its
validation traces only after a caller had already supplied an assembly. -/
structure NestedValidatedRunResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) where
  loweredEnv : Environment
  production : NestedInstalledProduction loweredEnv
  productionContext : AddInductive.Context
  productionContextWF : ContextWF productionContext
  productionContext_env : productionContext.env = sourceProdEnv
  productionContext_lparams : productionContext.lparams = lparams
  productionContext_safety : productionContext.safety = safety
  productionContext_allowPrimitive : productionContext.allowPrimitive = false
  productionContext_venv : productionContextWF.venv = sourceEnv
  production_c : production.c = productionContext
  production_nparams : production.nparams = nparams
  production_isUnsafe : production.isUnsafe =
    (productionContext.safety != .safe)
  production_isUnsafe_source : production.isUnsafe = isUnsafe
  production_initialEnv : production.initialEnv = sourceEnv
  production_indTypes : production.indTypes = res.types.toArray
  stats : AddInductive.InductiveStats
  depth : Nat
  commonParams : List VExpr
  commonLevel : VLevel
  sourceHeaderSemantics :
    checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
      productionContextWF.venv productionContext.lparams nparams commonParams
        commonLevel res.types.toArray.toList
  validationFuel : FuelConfig
  productionContext_fuel : productionContext.fuel = validationFuel
  lowering : NestedLoweringResultClosed sourceProdEnv
    validationFuel.inductiveFuel nparams sourceTypes
    { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res
  restoration : RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
    (sourceTypes.map (·.name)) sourceTypes
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv)
  primitiveSafe : ∃ entries,
    PrimitiveSafeFreshConstantTrace false sourceProdEnv entries outEnv
  validationEnv : Environment
  validationEnvironment :
    RestoredConstructorValidationEnvironment res loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) false sourceTypes validationEnv
  recursorTypeValidation :
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
      lparams safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run outEnv loweredEnv lparams
      safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  auxiliaryHeaderEnv : Environment
  headerValidationEnvironment :
    RestoredHeaderValidationEnvironment loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv
  parameterValidation :
    Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
      lparams safety validationFuel sourceTypes res = .ok ()
  auxiliaryVEnv : VEnv
  auxiliaryMLCtx : TypeChecker.MLCtx
  auxiliaryMLCtx_lctx : auxiliaryMLCtx.lctx = res.lctx
  auxiliaryMLCtxWF : auxiliaryMLCtx.WF auxiliaryVEnv lparams
  validatedAuxiliaries : ValidatedNestedAuxiliaries auxiliaryVEnv lparams
    auxiliaryMLCtx.vlctx res
  auxiliarySelection : LocalForallSelection res.lctx res.params
  auxiliaryTranslations : ClosedNestedAuxiliaryTranslations auxiliaryVEnv
    lparams res auxiliarySelection
  nativeSource : NativeNestedSourceCoreResult sourceEnv lparams nparams
    sourceTypes isUnsafe production.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  nativeSourceDecl_eq : nativeSource.sourceDecl = decl
  auxiliaryVEnv_eq_native : auxiliaryVEnv = nativeSource.envTypes

/-- Rich final nested result retaining the exact ordinary installation,
restoration trace, and assembly certificate that produced the public final
environment model.  Downstream declaration dispatch needs these witnesses to
derive closure, safety tags, and constructor coherence for this exact run. -/
structure NestedExactFinalRunResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) where
  loweredEnv : Environment
  production : NestedInstalledProduction loweredEnv
  productionContext : AddInductive.Context
  productionContextWF : ContextWF productionContext
  productionContext_env : productionContext.env = sourceProdEnv
  productionContext_lparams : productionContext.lparams = lparams
  productionContext_safety : productionContext.safety = safety
  production_c : production.c = productionContext
  production_nparams : production.nparams = nparams
  production_isUnsafe : production.isUnsafe =
    (productionContext.safety != .safe)
  production_initialEnv : production.initialEnv = sourceEnv
  production_indTypes : production.indTypes = res.types.toArray
  validationFuel : FuelConfig
  lowering : NestedLoweringResultClosed sourceProdEnv
    validationFuel.inductiveFuel nparams sourceTypes
    { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res
  restoration : RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
    (sourceTypes.map (·.name)) sourceTypes
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv)
  primitiveSafe : ∃ entries,
    PrimitiveSafeFreshConstantTrace false sourceProdEnv entries outEnv
  validationEnv : Environment
  validationEnvironment :
    RestoredConstructorValidationEnvironment res loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) productionContext.allowPrimitive sourceTypes
      validationEnv
  recursorTypeValidation :
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
      lparams safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run outEnv loweredEnv lparams
      safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  auxiliaryHeaderEnv : Environment
  headerValidationEnvironment :
    RestoredHeaderValidationEnvironment loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv
  parameterValidation :
    Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
      lparams safety validationFuel sourceTypes res = .ok ()
  auxiliaryVEnv : VEnv
  auxiliaryMLCtx : TypeChecker.MLCtx
  auxiliaryMLCtx_lctx : auxiliaryMLCtx.lctx = res.lctx
  auxiliaryMLCtxWF : auxiliaryMLCtx.WF auxiliaryVEnv lparams
  validatedAuxiliaries : ValidatedNestedAuxiliaries auxiliaryVEnv lparams
    auxiliaryMLCtx.vlctx res
  auxiliarySelection : LocalForallSelection res.lctx res.params
  auxiliaryTranslations : ClosedNestedAuxiliaryTranslations auxiliaryVEnv
    lparams res auxiliarySelection
  nativeSource : NativeNestedSourceCoreResult sourceEnv lparams nparams
    sourceTypes isUnsafe production.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  nativeSourceDecl_eq : nativeSource.sourceDecl = decl
  assembly : NestedFinalAssemblyCertificate restoration sourceEnv decl lparams
    nparams isUnsafe safety
  production_eq : assembly.production = production
  finalResult : NestedFinalEnvironmentResult sourceEnv decl lparams nparams
    sourceTypes isUnsafe safety outEnv

/-- Exact final run with its independently specified source declaration
chosen only after the concrete production/restoration trace is known.
`AcceptSource` lets fixed-declaration consumers recover the previous theorem
while declaration dispatch may use `True` and retain the produced witness. -/
structure NestedExistentialFinalRunResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (isUnsafe : Bool) (safety : DefinitionSafety)
    (AcceptSource : VInductDecl → Prop) (outEnv : Environment) where
  sourceDecl : VInductDecl
  accepted : AcceptSource sourceDecl
  exact : NestedExactFinalRunResult res sourceProdEnv sourceTypes sourceEnv
    sourceDecl lparams nparams isUnsafe safety outEnv

/-- Existential source selection for the pre-assembly validated run. -/
structure NestedExistentialValidatedRunResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (isUnsafe : Bool) (safety : DefinitionSafety)
    (AcceptSource : VInductDecl → Prop) (outEnv : Environment) where
  sourceDecl : VInductDecl
  accepted : AcceptSource sourceDecl
  validated : NestedValidatedRunResult res sourceProdEnv sourceTypes sourceEnv
    sourceDecl lparams nparams isUnsafe safety outEnv

/-- The checker context used by the production post-lowering pipeline. -/
def nestedAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := allowPrimitive, fuel := fuel }

/-- Fully executable validated nested run.  The lowered ordinary run is
discharged by `AddInductive.run.semanticWF`; its existential semantic context
and complete recursor phases are retained because restoration needs the
latter, whereas `semanticAddInductWF` intentionally projects them away. -/
theorem Environment.addInductiveAfterLowering.nestedValidatedExistentialSourceSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (Hc : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel))
    (Hclosed : MutualInductivesClosed env)
    (Howners : ConstructorOwnersPresent env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < res.types.toArray.size)
    (HnotPartial :
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
        fuel).safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = allowPrimitive →
      c'.fuel = fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety != .safe) Hc')
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hallowFalse : allowPrimitive = false)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res).WF fun outEnv =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = env ∧
          c'.safety =
            (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
              fuel).safety ∧
          c'.lparams = lparams ∧
          c'.allowPrimitive = allowPrimitive ∧
          c'.fuel = fuel ∧
          Hc'.venv = Hc.venv ∧
          ∃ sourceDecl, Nonempty (NestedValidatedRunResult res env sourceTypes
            Hc'.venv sourceDecl lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe) outEnv) := by
  let c := nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel
  have Hrun := AddInductive.run.semanticSourceAlignedWF
    (types := res.types) nparams res.aux2nested.size Hc (by
      simpa [c, nestedAddInductiveContext] using Hclosed) hctx hnonempty
      HnotPartial
      (fun Hc' hallowPrimitive hfuel Hsemantic =>
        Hinputs Hc' hallowPrimitive hfuel Hsemantic)
  unfold Environment.addInductiveAfterLowering
  exact Hrun.bind fun loweredEnv Hinstalled => by
    simp only [hnested, ↓reduceIte]
    rcases Hinstalled with
      ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
        hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hphases⟩
    have henv' : c'.env = env := by
      simpa [c, nestedAddInductiveContext] using henv
    have hsafety' : c'.safety = c.safety := hsafety
    have hlparams' : c'.lparams = lparams := by
      simpa [c, nestedAddInductiveContext] using hlparams
    have hallowPrimitive' : c'.allowPrimitive = allowPrimitive := by
      simpa [c, nestedAddInductiveContext] using hallowPrimitive
    have hfuel' : c'.fuel = fuel := by
      simpa [c, nestedAddInductiveContext] using hfuel
    have hvenv' : Hc'.venv = Hc.venv := hvenv
    rcases Hphases with
      ⟨loweredDecl, headerEnv, ctorEnv, Hheaders, R, ⟨Hprod⟩⟩
    let P : NestedInstalledProduction loweredEnv := {
      c := c'
      stats := stats
      loweredDecl := loweredDecl
      nparams := nparams
      depth := depth
      isUnsafe := c.safety != .safe
      initialEnv := Hc'.venv
      indTypes := res.types.toArray
      headerEnv := headerEnv
      ctorEnv := ctorEnv
      headers := Hheaders
      constructors := R
      production := Hprod }
    have Hlower' : NestedLoweringResultClosed c'.env fuel.inductiveFuel
        nparams sourceTypes
        { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res := by
      rw [henv']
      exact Hlower
    have HlowerInitial : NestedLoweringResultClosed c'.env fuel.inductiveFuel
        nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res := by
      simpa using Hlower'
    rcases HlowerInitial.sourceHeaderPrefix R.core rfl with
      ⟨sourceTypesVEnv, HsourceTypesAdded, HsourceHeaders⟩
    have hsourceTypesWF : sourceTypesVEnv.WF := by
      apply VEnv.WF.addConstVals Hc'.checking.tr.wf _ HsourceTypesAdded
      intro ci hci
      simp only [List.mem_map] at hci
      rcases hci with ⟨target, htarget, rfl⟩
      rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceHeaders target
          htarget with
        ⟨_source, _hsource, Htarget⟩
      exact Htarget.wf
    have Hfirst : ∀ first rest, sourceTypes = first :: rest →
        ∃ target, TrExprS sourceTypesVEnv c'.lparams [] first.type target := by
      intro first rest htypes
      have hsource : 0 < sourceTypes.length := by simp [htypes]
      have htarget : 0 <
          (loweredDecl.types.take sourceTypes.length).length := by
        rw [← Lean4Lean.List.Forall₂.length_eq HsourceHeaders]
        exact hsource
      have Hhead := Lean4Lean.VerifyInductive.List.Forall₂.getElem
        HsourceHeaders 0 hsource htarget
      have hfirst : sourceTypes[0] = first := by simp [htypes]
      rw [hfirst] at Hhead
      exact ⟨_, Hhead.type.mono
        (VEnv.addConstVals_le HsourceTypesAdded)⟩
    rcases HlowerInitial with
      ⟨finalLoweringState, HlowerRun, HauxFVars, HparamsNodup⟩
    have HlowerInitial' : NestedLoweringResultClosed c'.env
        fuel.inductiveFuel nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res :=
      ⟨finalLoweringState, HlowerRun, HauxFVars, HparamsNodup⟩
    rcases HlowerRun.resultParameterMLCtx hsourceTypesWF Hfirst rfl with
      ⟨auxiliaryMLCtx, hauxiliaryLctx, hauxiliaryWF,
        hauxiliaryFresh⟩
    have hvisible : c'.safety ≤
        (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
      rw [hsafety']
      simp [c, nestedAddInductiveContext]
    have HheaderValid : ∀ auxiliaryHeaderEnv,
        Nonempty (RestoredHeaderValidationEnvironment loweredEnv c'.env
          (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv) →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          auxiliaryHeaderEnv sourceTypesVEnv := by
      intro auxiliaryHeaderEnv HheaderValidation
      rcases HheaderValidation with ⟨HheaderValidation⟩
      rcases HheaderValidation.validOfLowering HlowerInitial' Hc' Hprod rfl
          hvisible with
        ⟨headerVEnv, HheaderAdded, HheaderValid⟩
      have hheaderVEnv : headerVEnv = sourceTypesVEnv :=
        Option.some.inj (HheaderAdded.symm.trans HsourceTypesAdded)
      subst headerVEnv
      simpa [c, nestedAddInductiveContext, hsafety'] using HheaderValid
    let Validated := fun restoredEnv =>
      ∃ sourceDecl, Nonempty (NestedValidatedRunResult res env sourceTypes
        Hc'.venv sourceDecl lparams nparams isUnsafe
          (if isUnsafe then .unsafe else .safe) restoredEnv)
    have Hrestore' := Environment.restoreNestedAfterInstall.ofLoweringClosedWF
      (initialState := { lvls := lparams.map .param, newTypes := #[] })
      Hc' Hprod HlowerInitial' Hc'.checking.tr.map_wf lparams
      (if isUnsafe then .unsafe else .safe) allowPrimitive fuel
      sourceTypesVEnv HheaderValid auxiliaryMLCtx
      (by simpa only [hlparams'] using hauxiliaryWF)
      hauxiliaryLctx hauxiliaryFresh
    have Hrestore :
        (Environment.restoreNestedAfterInstall env loweredEnv lparams
          sourceTypes (if isUnsafe then .unsafe else .safe) allowPrimitive
          fuel res).WF fun outEnv =>
            RestoredAfterInstallResult res env loweredEnv
              (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
              (sourceTypes.map (·.name)) sourceTypes
              lparams (if isUnsafe then .unsafe else .safe) allowPrimitive fuel
              (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
              Validated
              outEnv := by
      have HrestoreEnv := Hrestore'
      rw [henv'] at HrestoreEnv
      refine HrestoreEnv.mono ?_
      intro restoredEnv Hrestored
      rcases Hrestored.restoration with ⟨Htrace⟩
      rcases Hrestored.recursorTypeValidation with
        ⟨validationEnv, ⟨Hvalidation⟩, HrecursorTypes⟩
      have HrecursorRules := Hrestored.recursorRuleValidation
      rcases Hrestored.auxiliaryHeaderValidation with
        ⟨auxiliaryHeaderEnv, ⟨HheaderValidation⟩, Hparameters,
          HauxiliaryRun⟩
      rcases Hrestored.validated with
        ⟨Hvalidated, selection, Htranslations⟩
      have Howners' : ConstructorOwnersPresent c'.env := by
        simpa only [henv'] using Howners
      have Htrace' : RestoredNestedDeclarationsResult res loweredEnv c'.env
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          ((), restoredEnv) := by
        simpa only [henv'] using Htrace
      have Hvalidation' : RestoredConstructorValidationEnvironment res
          loweredEnv c'.env (sourceTypes.map (·.name)) false sourceTypes
          validationEnv := by
        simpa only [henv', hallowFalse] using Hvalidation
      have HheaderValidation' : RestoredHeaderValidationEnvironment loweredEnv
          c'.env (sourceTypes.map (·.name)) sourceTypes
          auxiliaryHeaderEnv := by
        simpa only [henv'] using HheaderValidation
      have Hparameters' :
          Lean4Lean.validateRestoredConstructorParameters.run
            auxiliaryHeaderEnv c'.lparams c'.safety fuel sourceTypes res =
              .ok () := by
        simpa only [hlparams', hsafety', c, nestedAddInductiveContext] using
          Hparameters
      have hproducerUnsafe : (c.safety != .safe) = isUnsafe := by
        simp [c, nestedAddInductiveContext]
        cases isUnsafe <;> decide
      have Hnative := HlowerInitial'.nativeSourceCore Hc' Hprod Hsources
        Howners' rfl Htrace' Hvalidation' HheaderValidation' Hparameters'
        hvisible
      have Hnative' : Nonempty (NativeNestedSourceCoreResult Hc'.venv lparams
          nparams sourceTypes isUnsafe loweredDecl
          (if isUnsafe then .unsafe else .safe) validationEnv
            auxiliaryHeaderEnv) := by
        rw [hproducerUnsafe] at Hnative
        simpa only [hlparams', hsafety', c, nestedAddInductiveContext] using
          Hnative
      rcases Hnative' with ⟨N⟩
      exact {
        restoration := ⟨Htrace⟩
        primitiveSafe := Hrestored.primitiveSafe
        constructorParameterValidation := ⟨validationEnv, ⟨Hvalidation⟩⟩
        recursorTypeValidation :=
          ⟨validationEnv, ⟨Hvalidation⟩, HrecursorTypes⟩
        recursorRuleValidation := HrecursorRules
        auxiliaryHeaderValidation :=
          ⟨auxiliaryHeaderEnv, ⟨HheaderValidation⟩, Hparameters,
            HauxiliaryRun⟩
        validated := ⟨N.sourceDecl, ⟨{
            loweredEnv := loweredEnv
            production := P
            productionContext := c'
            productionContextWF := Hc'
            productionContext_env := henv'
            productionContext_lparams := hlparams'
            productionContext_safety := by
              simpa [c, nestedAddInductiveContext] using hsafety'
            productionContext_allowPrimitive := by
              exact hallowPrimitive'.trans hallowFalse
            productionContext_venv := rfl
            production_c := rfl
            production_nparams := rfl
            production_isUnsafe := by
              change (c.safety != .safe) = (c'.safety != .safe)
              rw [hsafety']
            production_isUnsafe_source := hproducerUnsafe
            production_initialEnv := rfl
            production_indTypes := rfl
            stats := stats
            depth := depth
            commonParams := commonParams
            commonLevel := commonLevel
            sourceHeaderSemantics := Hsemantic
            lowering := Hlower
            productionContext_fuel := hfuel'
            restoration := Htrace
            primitiveSafe := by
              simpa only [hallowFalse] using Hrestored.primitiveSafe
            validationEnv := validationEnv
            validationFuel := fuel
            validationEnvironment := by
              simpa only [hallowPrimitive', hallowFalse] using Hvalidation
            recursorTypeValidation := HrecursorTypes
            recursorRuleValidation := HrecursorRules
            auxiliaryHeaderEnv := auxiliaryHeaderEnv
            headerValidationEnvironment := HheaderValidation
            parameterValidation := Hparameters
            auxiliaryVEnv := sourceTypesVEnv
            auxiliaryMLCtx := auxiliaryMLCtx
            auxiliaryMLCtx_lctx := hauxiliaryLctx
            auxiliaryMLCtxWF := by
              simpa only [hlparams'] using hauxiliaryWF
            validatedAuxiliaries := by
              simpa only [hlparams'] using Hvalidated
            auxiliarySelection := selection
            auxiliaryTranslations := by
              simpa only [hlparams'] using Htranslations
            nativeSource := N
            nativeSourceDecl_eq := rfl
            auxiliaryVEnv_eq_native :=
              Option.some.inj (HsourceTypesAdded.symm.trans N.sourceAdded)
          }⟩⟩ }
    exact Hrestore.mono fun restoredEnv Hrestored => by
      exact ⟨c', Hc', henv',
        by simpa [c, nestedAddInductiveContext] using hsafety',
        hlparams',
        hallowPrimitive', hfuel', hvenv',
        Hrestored.validated⟩

/-- Legacy internal compatibility lift retained only for proofs below this
module; public dispatch uses the unconditional validated-run assembly. -/
private theorem Environment.addInductiveAfterLowering.nestedFinalExistentialSourceSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (AcceptSource : VInductDecl → Prop)
    (Hc : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel))
    (Hclosed : MutualInductivesClosed env)
    (Howners : ConstructorOwnersPresent env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < res.types.toArray.size)
    (HnotPartial :
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
        fuel).safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') → c'.allowPrimitive = allowPrimitive →
      c'.fuel = fuel →
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      SemanticRunVerificationInputs c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety != .safe) Hc')
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hallowFalse : allowPrimitive = false)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams
      sourceTypes
      ({ lvls := lparams.map .param, newTypes := sourceTypes.toArray } :
        Lean4Lean.ElimNestedInductive.State) res)
    (hnested : res.aux2nested.size ≠ 0)
    (Hassembly : ∀ (c' : AddInductive.Context)
      (stats : AddInductive.InductiveStats) (depth : Nat)
      (commonParams : List VExpr) (commonLevel : VLevel)
      (Hc' : ContextWF c'), c'.env = env →
      c'.safety = (nestedAddInductiveContext env lparams isUnsafe
        allowPrimitive fuel).safety → c'.lparams = lparams →
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      ∀ loweredEnv, (P : NestedInstalledProduction loweredEnv) →
      ∀ restoredEnv
        (Hrestored : RestoredNestedDeclarationsResult res loweredEnv env
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          ((), restoredEnv)),
        ∀ sourceDecl, AcceptSource sourceDecl ∧
          Nonempty (NestedFinalAssemblyProducerEvidence P Hrestored Hc'.venv
            sourceDecl lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe))) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res).WF fun outEnv =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = env ∧
          c'.safety = (nestedAddInductiveContext env lparams isUnsafe
            allowPrimitive fuel).safety ∧
          c'.lparams = lparams ∧ c'.allowPrimitive = allowPrimitive ∧
          c'.fuel = fuel ∧ Hc'.venv = Hc.venv ∧
          Nonempty (NestedExistentialFinalRunResult res env sourceTypes
            Hc'.venv lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe) AcceptSource outEnv) := by
  exact (Environment.addInductiveAfterLowering.nestedValidatedExistentialSourceSemanticWF
      env lparams nparams
      sourceTypes isUnsafe allowPrimitive fuel res Hc Hclosed Howners hctx
      hnonempty HnotPartial Hinputs Hsources hallowFalse Hlower hnested).mono
    fun _ Hout => by
      rcases Hout with ⟨c', Hc', henv, hsafety, hlparams, hallow, hfuel,
        hvenv, sourceDecl, ⟨V⟩⟩
      have HsourceHeader :
          checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
            Hc'.venv c'.lparams nparams V.commonParams V.commonLevel
              res.types.toArray.toList := by
        simpa only [V.productionContext_venv, V.productionContext_lparams,
          hlparams] using V.sourceHeaderSemantics
      rcases Hassembly c' V.stats V.depth V.commonParams V.commonLevel Hc'
          henv hsafety hlparams HsourceHeader V.loweredEnv
          V.production _ V.restoration sourceDecl with
        ⟨haccepted, ⟨A⟩⟩
      rcases A.certificate with ⟨⟨C, hproduction⟩⟩
      have Hvalid : CheckingEnv.Valid
          (if isUnsafe then .unsafe else .safe) env Hc'.venv := by
        have Hchecking := Hc'.checking
        rw [henv, hsafety] at Hchecking
        simpa [nestedAddInductiveContext] using Hchecking
      exact ⟨c', Hc', henv, hsafety, hlparams, hallow, hfuel, hvenv,
        ⟨{
          sourceDecl := sourceDecl
          accepted := haccepted
          exact := {
            loweredEnv := V.loweredEnv
            production := V.production
            productionContext := V.productionContext
            productionContextWF := V.productionContextWF
            productionContext_env := V.productionContext_env
            productionContext_lparams := V.productionContext_lparams
            productionContext_safety := V.productionContext_safety
            production_c := V.production_c
            production_nparams := V.production_nparams
            production_isUnsafe := V.production_isUnsafe
            production_initialEnv := V.production_initialEnv
            production_indTypes := V.production_indTypes
            validationFuel := V.validationFuel
            lowering := V.lowering
            restoration := V.restoration
            primitiveSafe := V.primitiveSafe
            validationEnv := V.validationEnv
            validationEnvironment := by
              simpa only [V.productionContext_allowPrimitive] using
                V.validationEnvironment
            recursorTypeValidation := V.recursorTypeValidation
            recursorRuleValidation := V.recursorRuleValidation
            auxiliaryHeaderEnv := V.auxiliaryHeaderEnv
            headerValidationEnvironment := V.headerValidationEnvironment
            parameterValidation := V.parameterValidation
            auxiliaryVEnv := V.auxiliaryVEnv
            auxiliaryMLCtx := V.auxiliaryMLCtx
            auxiliaryMLCtx_lctx := V.auxiliaryMLCtx_lctx
            auxiliaryMLCtxWF := V.auxiliaryMLCtxWF
            validatedAuxiliaries := V.validatedAuxiliaries
            auxiliarySelection := V.auxiliarySelection
            auxiliaryTranslations := V.auxiliaryTranslations
            nativeSource := V.nativeSource
            nativeSourceDecl_eq := V.nativeSourceDecl_eq
            assembly := C
            production_eq := hproduction
            finalResult := C.finalEnvironment Hvalid }
        }⟩⟩

/- The former fixed-source/final-environment wrappers lived here.  They were
conditional on a caller-supplied final-assembly callback and are intentionally
retired while the validated run is assembled internally downstream.

/-- Fixed-source specialization of the existential exact-run theorem. -/
theorem Environment.addInductiveAfterLowering.nestedFinalExactSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceDecl : VInductDecl)
    (Hc : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel))
    (Hclosed : MutualInductivesClosed env)
    (Howners : ConstructorOwnersPresent env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < res.types.toArray.size)
    (HnotPartial :
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
        fuel).safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = allowPrimitive →
      c'.fuel = fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety != .safe) Hc')
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hallowFalse : allowPrimitive = false)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0)
    (Hassembly : ∀ (c' : AddInductive.Context)
      (stats : AddInductive.InductiveStats) (depth : Nat)
      (commonParams : List VExpr) (commonLevel : VLevel)
      (Hc' : ContextWF c'),
      c'.env = env →
      c'.safety =
        (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety →
      c'.lparams = lparams →
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      ∀ loweredEnv,
      (P : NestedInstalledProduction loweredEnv) →
      ∀ restoredEnv
        (Hrestored : RestoredNestedDeclarationsResult res loweredEnv env
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          ((), restoredEnv)),
        ∀ actualSource, actualSource = sourceDecl ∧
          Nonempty (NestedFinalAssemblyProducerEvidence P Hrestored Hc'.venv
            actualSource lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe))) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res).WF fun outEnv =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = env ∧
          c'.safety =
            (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
              fuel).safety ∧
          c'.lparams = lparams ∧
          c'.allowPrimitive = allowPrimitive ∧
          c'.fuel = fuel ∧
          Hc'.venv = Hc.venv ∧
          Nonempty (NestedExactFinalRunResult res env sourceTypes Hc'.venv
            sourceDecl lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe) outEnv) := by
  exact (Environment.addInductiveAfterLowering.nestedFinalExistentialSourceSemanticWF
      env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res (fun decl => decl = sourceDecl) Hc
      Hclosed Howners hctx hnonempty HnotPartial Hinputs Hsources hallowFalse
      Hlower hnested
      (fun c' stats depth commonParams commonLevel Hc' henv hsafety hlparams
          Hsemantic loweredEnv P restoredEnv Hrestored actualSource =>
        Hassembly c' stats depth commonParams commonLevel Hc' henv hsafety
          hlparams Hsemantic loweredEnv P restoredEnv Hrestored
          actualSource)).mono
    fun _ Hout => by
      rcases Hout with ⟨c', Hc', henv, hsafety, hlparams, hallow, hfuel,
        hvenv, ⟨R⟩⟩
      rcases R with ⟨decl, hdecl, Hexact⟩
      subst decl
      exact ⟨c', Hc', henv, hsafety, hlparams, hallow, hfuel, hvenv,
        ⟨Hexact⟩⟩

/-- Compatibility projection of `nestedFinalExactSemanticWF` for consumers
that need only the public final environment model. -/
theorem Environment.addInductiveAfterLowering.nestedFinalSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceDecl : VInductDecl)
    (Hc : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel))
    (Hclosed : MutualInductivesClosed env)
    (Howners : ConstructorOwnersPresent env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < res.types.toArray.size)
    (HnotPartial :
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
        fuel).safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = allowPrimitive →
      c'.fuel = fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety != .safe) Hc')
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hallowFalse : allowPrimitive = false)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0)
    (Hassembly : ∀ (c' : AddInductive.Context)
      (stats : AddInductive.InductiveStats) (depth : Nat)
      (commonParams : List VExpr) (commonLevel : VLevel)
      (Hc' : ContextWF c'),
      c'.env = env →
      c'.safety =
        (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety →
      c'.lparams = lparams →
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      ∀ loweredEnv,
      (P : NestedInstalledProduction loweredEnv) →
      ∀ restoredEnv
        (Hrestored : RestoredNestedDeclarationsResult res loweredEnv env
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          ((), restoredEnv)),
        ∀ actualSource, actualSource = sourceDecl ∧
          Nonempty (NestedFinalAssemblyProducerEvidence P Hrestored Hc'.venv
            actualSource lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe))) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res).WF fun outEnv =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = env ∧
          c'.safety =
            (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
              fuel).safety ∧
          c'.lparams = lparams ∧
          Nonempty (NestedFinalEnvironmentResult Hc'.venv sourceDecl lparams
            nparams sourceTypes isUnsafe
              (if isUnsafe then .unsafe else .safe) outEnv) := by
  exact (Environment.addInductiveAfterLowering.nestedFinalExactSemanticWF
    env lparams nparams sourceTypes isUnsafe allowPrimitive fuel res sourceDecl
    Hc Hclosed Howners hctx hnonempty HnotPartial Hinputs Hsources
    hallowFalse Hlower hnested Hassembly).mono fun _ Hout => by
      rcases Hout with
        ⟨c', Hc', henv, hsafety, hlparams, _hallow, _hfuel, _hvenv, ⟨R⟩⟩
      exact ⟨c', Hc', henv, hsafety, hlparams, ⟨R.finalResult⟩⟩
-/

end VerifyInductive
end Lean4Lean
