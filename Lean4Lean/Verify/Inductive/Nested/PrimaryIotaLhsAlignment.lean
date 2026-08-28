import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaLhsApplication
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaShapeAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Pointwise restored-primary LHS telescope alignment

Restoration changes the recursor and constructor constant types, so the
generated typing derivation cannot be weakened into the source environment.
The operationally meaningful invariant is instead that both restored heads
consume the equation's existing arguments through the same dependent domains
as independently typed reference applications in that environment.
-/

/-- Exact pointwise alignment sufficient to reconstruct a restored primary
LHS application.  The producer retains only same-domain telescope relations
and independently typed reference applications; the dependent argument
typings consumed by `LhsApplicationCertificate` are derived below. -/
structure RecursorPhasesResult.GeneratedNestedIotaSource.RestoredPrimaryLhsSpineAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    (targetEnv : VEnv) : Type where
  targetEnvWF : targetEnv.WF
  contextWF : OnCtx G.translation.domains.reverse
    (targetEnv.IsType generatedRule.uvars)
  recursorLookup : targetEnv.constants S.source.recursor.name =
    some S.source.recursor.toVConstant
  constructorLookup : targetEnv.constants sourceCtor.name =
    some sourceCtor.toVConstant
  recursorLevelsWF : ∀ level ∈ S.source.recursorLevels,
    level.WF generatedRule.uvars
  constructorLevelsWF : ∀ level ∈ S.source.ctorLevels,
    level.WF generatedRule.uvars
  recursorLevelsLength : S.source.recursorLevels.length =
    S.source.recursor.uvars
  constructorLevelsLength : S.source.ctorLevels.length = sourceCtor.uvars
  leadingReference : VExpr
  leadingReferenceType : VExpr
  leadingReferenceTyping : targetEnv.HasType generatedRule.uvars
    G.translation.domains.reverse leadingReference leadingReferenceType
  leadingReferenceApplication : VExpr.WF targetEnv generatedRule.uvars
    G.translation.domains.reverse
    (VExpr.mkApps leadingReference S.source.leadingArgs)
  leadingDomains : SameTelescopeDomains S.source.leadingArgs.length
    (S.source.recursor.type.instL S.source.recursorLevels)
    leadingReferenceType
  constructorReference : VExpr
  constructorReferenceType : VExpr
  constructorReferenceTyping : targetEnv.HasType generatedRule.uvars
    G.translation.domains.reverse constructorReference
      constructorReferenceType
  constructorReferenceApplication : VExpr.WF targetEnv generatedRule.uvars
    G.translation.domains.reverse
    (VExpr.mkApps constructorReference S.source.ctorArgs)
  constructorDomains : SameTelescopeDomains S.source.ctorArgs.length
    (sourceCtor.type.instL S.source.ctorLevels) constructorReferenceType
  constructorResult : VExpr.applyForallType
    (sourceCtor.type.instL S.source.ctorLevels) S.source.ctorArgs =
      S.source.leadingSplit.majorDomain
  resultType : S.source.leadingSplit.resultBody.inst
    (VExpr.mkApps (.const sourceCtor.name S.source.ctorLevels)
      S.source.ctorArgs) = G.translation.typeBody

/-- Same-domain operational alignment reconstructs the exact dependent
application certificate; no typing judgment crosses environments. -/
noncomputable def RecursorPhasesResult.GeneratedNestedIotaSource.RestoredPrimaryLhsSpineAlignment.certificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    {S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor}
    {targetEnv : VEnv}
    (A : S.RestoredPrimaryLhsSpineAlignment targetEnv) :
    S.LhsApplicationCertificate targetEnv := by
  have Hrecursor : targetEnv.HasType generatedRule.uvars
      G.translation.domains.reverse
      (.const S.source.recursor.name S.source.recursorLevels)
      (S.source.recursor.type.instL S.source.recursorLevels) :=
    VEnv.HasType.const A.recursorLookup A.recursorLevelsWF
      A.recursorLevelsLength
  have Hleading := VEnv.TypedApplicationSpine.ofSameTelescopeDomains
    A.targetEnvWF A.contextWF A.leadingDomains Hrecursor
      A.leadingReferenceTyping A.leadingReferenceApplication
  have Hconstructor : targetEnv.HasType generatedRule.uvars
      G.translation.domains.reverse
      (.const sourceCtor.name S.source.ctorLevels)
      (sourceCtor.type.instL S.source.ctorLevels) :=
    VEnv.HasType.const A.constructorLookup A.constructorLevelsWF
      A.constructorLevelsLength
  have HctorArgs := VEnv.TypedApplicationSpine.ofSameTelescopeDomains
    A.targetEnvWF A.contextWF A.constructorDomains Hconstructor
      A.constructorReferenceTyping A.constructorReferenceApplication
  exact {
    recursorLookup := A.recursorLookup
    constructorLookup := A.constructorLookup
    recursorLevelsWF := A.recursorLevelsWF
    constructorLevelsWF := A.constructorLevelsWF
    recursorLevelsLength := A.recursorLevelsLength
    constructorLevelsLength := A.constructorLevelsLength
    majorDomain := S.source.leadingSplit.majorDomain
    resultBody := S.source.leadingSplit.resultBody
    leadingArguments := by
      rw [S.source.leadingSplit.eq] at Hleading
      exact Hleading.toTypedArguments
    constructorArguments := by
      rw [A.constructorResult] at HctorArgs
      exact HctorArgs.toTypedArguments
    resultType := A.resultType }

end VerifyInductive
end Lean4Lean
