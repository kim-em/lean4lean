import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Lowering.Run
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.SourceIotaFamilies
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Rules.Alignment




namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The production lookup used by a primary restoration step is the exact
generated recursor entry at the corresponding source-family position.  The
ordinary equation proof and the restoration trace can therefore be indexed by
one shared rule list. -/
theorem RecursorCheck.restoredPrimaryInfo_eq_generated
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv)
    (owner : Nat) (hentry : owner < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[owner]!.name) :
    Hstep.oldInfo = (H.generated.entry owner hentry).info := by
  let E := H.generated.entry owner hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[owner].1.name =
      some H.entries[owner].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have hstepLookup : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo Hstep.oldInfo) := by
    simpa [holdRecName] using Hstep.lookup
  exact ConstantInfo.recInfo.inj
    (Option.some.inj (hstepLookup.symm.trans hlookupE))

/-- A complete restored-primary nested rule list supplies the append-facing
certificate used by restoration assembly. -/
theorem NestedIotaListCertificate.toBuild
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : NestedIotaListCertificate decl block rules) :
    NestedIotaBuildCertificate decl block rules where
  covered := Nat.le_of_eq H.length
  shapes i hrule hctor := H.rules i hctor hrule

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Ordered flattened restored-primary equation trace.  The left list is the
independent source declaration's owner/constructor traversal, so this
relation fixes both order and cardinality rather than accepting a separate
indexing callback. -/
abbrev RestoredPrimaryIotaListTrace
    (decl : VInductDecl) (block : VInductBlock)
    (owned : List (VInductiveType × VConstVal))
    (rules : List VDefEq) : Prop :=
  List.Forall₂ (fun ownerCtor rule =>
    Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
    owned rules

/-- An exact trace over `ownedConstructors` is precisely the ordered
`NestedIotaListCertificate` consumed by nested compilation. -/
theorem NestedIotaListCertificate.ofForall₂
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : RestoredPrimaryIotaListTrace decl block
      decl.ownedConstructors rules) :
    NestedIotaListCertificate decl block rules where
  length :=
    (Lean4Lean.List.Forall₂.length_eq H).symm
  rules i hctor hrule :=
    Lean4Lean.List.forall₂_getElem H i hctor hrule

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Owner-indexed constructor order used while restored primary equations are
assembled one family at a time. -/
def ownedConstructorsFor (owners : List VInductiveType) :
    List (VInductiveType × VConstVal) :=
  owners.flatMap fun owner => owner.ctors.map (owner, ·)

theorem ownedConstructorsFor_eq
    (decl : VInductDecl) :
    ownedConstructorsFor decl.types = decl.ownedConstructors :=
  rfl

/-- Exact family-by-family restored-primary equation batch.  Each head batch
is indexed by the constructors of the corresponding source owner, and the
result list is definitionally the concatenation in mutual-family order. -/
inductive RestoredPrimaryIotaFamilyTrace
    (decl : VInductDecl) (block : VInductBlock) :
    List VInductiveType → List VDefEq → Prop
  | nil : RestoredPrimaryIotaFamilyTrace decl block [] []
  | cons {owner owners head tail}
      (Hhead : List.Forall₂ (fun ownerCtor rule =>
        Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
        (owner.ctors.map (owner, ·)) head)
      (Htail : RestoredPrimaryIotaFamilyTrace decl block owners tail) :
      RestoredPrimaryIotaFamilyTrace decl block (owner :: owners)
        (head ++ tail)

/-- Family-local batches flatten to the single ordered trace consumed by the
independent nested-iota specification. -/
theorem RestoredPrimaryIotaFamilyTrace.forall₂
    (H : RestoredPrimaryIotaFamilyTrace decl block owners rules) :
    RestoredPrimaryIotaListTrace decl block
      (ownedConstructorsFor owners) rules := by
  induction H with
  | nil => exact .nil
  | @cons owner owners head tail Hhead Htail ih =>
    simpa [ownedConstructorsFor] using
      _root_.List.Forall₂.append' Hhead ih

/-- Once source restoration has fixed the declaration's owner list, the
family-local batches give the complete ordered primary iota certificate.
Mutual flattening, coverage, and cardinality are therefore not separate
callbacks at compilation assembly. -/
theorem RestoredPrimaryIotaFamilyTrace.certificate
    (Hrules : RestoredPrimaryIotaFamilyTrace decl block owners rules)
    (htypes : decl.types = owners)
    :
    NestedIotaListCertificate decl block rules := by
  apply NestedIotaListCertificate.ofForall₂
  rw [← ownedConstructorsFor_eq decl, htypes]
  exact Hrules.forall₂

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Semantic interpretation of the exact executable rule-restoration list
for one primary recursor.  The abstract output list is forced to consist of
the restored RHS endpoints of these very production rules. -/
inductive RestoredPrimaryIotaRuleTrace
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (P : NestedInstalledProduction prodEnv)
    (targetVEnv : VEnv) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ {oldRules newRules},
      RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules →
      List VConstVal → List VDefEq → Prop
  | nil : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName (.nil) [] []
  | cons
      (Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
        oldRule newRule)
      (Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules)
      (abstractRule : VDefEq)
      (Hshape : decl.NestedIotaRule block owner ctor abstractRule)
      (Hwf : abstractRule.WF targetVEnv)
      (Hrest : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
        P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
      RestoredPrimaryIotaRuleTrace decl block owner result prodEnv P
        targetVEnv auxRec oldRecName newRecName (.cons Hrule Hrules) (ctor :: ctors)
        (abstractRule :: rules)

theorem RestoredPrimaryIotaRuleTrace.forall₂
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    List.Forall₂ (fun ctor rule =>
      Nonempty (decl.NestedIotaRule block owner ctor rule)) ctors rules := by
  induction H with
  | nil => exact .nil
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    exact .cons ⟨Hshape⟩ ih

theorem RestoredPrimaryIotaRuleTrace.rulesWF
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    rcases List.mem_cons.mp hrule with rfl | hrule
    · exact Hwf
    · exact ih hrule

/-- The exact abstract rule batch interpreting one restored primary recursor.
Keeping the batch existential here lets a trace fold determine the final
abstract rule list rather than asking final assembly to guess it in advance. -/
structure RestoredPrimaryIotaFamilySemantics
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    (owner : VInductiveType)
    (P : NestedInstalledProduction loweredEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  rules : List VDefEq
  trace : RestoredPrimaryIotaRuleTrace decl block owner result loweredEnv
    P targetVEnv auxRec (Lean.mkRecName indType.name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.restored.restoration.rules owner.ctors rules

/-- Mutual-family primary equation semantics, indexed simultaneously by the
canonical source-family interpretation and the exact operational restoration
trace.  Consequently family order, constructor order, and rule cardinality
are consequences rather than final-assembly assumptions. -/
inductive RestoredPrimaryIotaSemanticTrace
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv)
    {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {sourceTypes : List InductiveType}
        {sourceProdEnv targetProdEnv : Environment}
        {Htrace : StateForMTrace
          (RestoredInductiveStep result loweredEnv auxRec allIndNames)
          sourceTypes sourceProdEnv targetProdEnv}
        {owners : List VInductiveType} {recursors : List VConstVal},
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors →
      List VInductiveType → List VDefEq → Prop
  | nil {lparams safety sourceVEnv envTypes envCtors result loweredEnv auxRec
      allIndNames} (sourceProdEnv : Environment) :
      RestoredPrimaryIotaSemanticTrace decl block targetVEnv
        P
        (RestoredSourceInductiveSemanticTrace.nil
          (decl := decl) (lparams := lparams) (safety := safety)
          (sourceVEnv := sourceVEnv) (envTypes := envTypes)
          (envCtors := envCtors) (result := result) (loweredEnv := loweredEnv)
          (auxRec := auxRec) (allIndNames := allIndNames) sourceProdEnv) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors)
      (Hhead : RestoredPrimaryIotaRuleTrace decl block owner result loweredEnv
        P targetVEnv auxRec (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName
        Hstep.restored.recursor.restored.restoration.rules owner.ctors
        headRules)
      (Hrules : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hrest
        owners tailRules) :
      RestoredPrimaryIotaSemanticTrace decl block targetVEnv P
        (.cons Hstep Htail Hheader Hconstructors Hrecursor Hrest)
        (owner :: owners) (headRules ++ tailRules)

theorem RestoredPrimaryIotaSemanticTrace.familyTrace
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules) :
    RestoredPrimaryIotaFamilyTrace decl block owners rules :=
  match H with
  | .nil _ => .nil
  | .cons _ _ _ _ _ _ Hhead Hrules =>
    .cons (by simpa using Hhead.forall₂) Hrules.familyTrace

/-- The exact restoration-indexed semantic trace is the complete primary
iota certificate required by nested compilation. -/
theorem RestoredPrimaryIotaSemanticTrace.certificate
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaListCertificate decl block rules :=
  H.familyTrace.certificate htypes

theorem RestoredPrimaryIotaSemanticTrace.build
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaBuildCertificate decl block rules :=
  (H.certificate htypes).toBuild

theorem RestoredPrimaryIotaSemanticTrace.length
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    rules.length = decl.ownedConstructors.length :=
  (H.certificate htypes).length

theorem RestoredPrimaryIotaSemanticTrace.rulesWF
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead Hrules ih =>
    rcases List.mem_append.mp hrule with hrule | hrule
    · exact Hhead.rulesWF rule hrule
    · exact ih hrule

end VerifyInductive
end Lean4Lean
