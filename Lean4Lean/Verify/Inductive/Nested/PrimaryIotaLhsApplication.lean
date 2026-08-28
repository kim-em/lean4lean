import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Restored primary-iota left-hand-side applications

The generated equation is typed in the lowered environment, whereas its
source reinterpretation is checked after the source recursor and constructor
have been restored. These environments are not ordered. This file records the
exact dependent application spine needed to type the same LHS syntax from the
restored constant lookups.
-/

/-- Typing evidence for a dependent argument spine, independent of the
function to which it will eventually be applied. Each argument is checked
against the domain exposed after instantiating all preceding arguments. -/
inductive VEnv.TypedArguments (env : VEnv) (uvars : Nat)
    (ctx : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | nil (type : VExpr) : TypedArguments env uvars ctx type [] type
  | cons
      (argumentTyping : env.HasType uvars ctx argument domain)
      (rest : TypedArguments env uvars ctx (body.inst argument)
        arguments result) :
      TypedArguments env uvars ctx (.forallE domain body)
        (argument :: arguments) result

/-- Apply a function to an independently checked dependent argument spine. -/
theorem VEnv.TypedArguments.apply
    (H : VEnv.TypedArguments env uvars ctx functionType arguments resultType)
    (Hfunction : env.HasType uvars ctx function functionType) :
    env.HasType uvars ctx (VExpr.mkApps function arguments) resultType := by
  induction H generalizing function with
  | nil => simpa [VExpr.mkApps] using Hfunction
  | cons Hargument Hrest ih =>
    simpa [VExpr.mkApps] using ih (Hfunction.app Hargument)

/-- Forget the repeated function typings in a conventional typed application
spine, retaining exactly the dependent argument obligations. Thus a producer
which already constructs `TypedApplicationSpine` need not rebuild the new
certificate argument-by-argument. -/
theorem VEnv.TypedApplicationSpine.toTypedArguments
    (H : VEnv.TypedApplicationSpine env uvars ctx function functionType
      arguments resultType) :
    VEnv.TypedArguments env uvars ctx functionType arguments resultType := by
  induction H with
  | nil _ => exact .nil _
  | cons _ Hargument _ ih => exact .cons Hargument ih

/-- Recover the complete dependent argument spine for a function from a
well-typed reference application with the same telescope domains.  This is
the evidence-retaining counterpart of `HasType.mkApps_sameTelescopeDomains`:
it is useful when restoration changes the constant head and result, but the
canonical application arguments still consume pointwise aligned domains. -/
theorem VEnv.TypedApplicationSpine.ofSameTelescopeDomains
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hdomains : SameTelescopeDomains args.length leftType rightType)
    (Hleft : env.HasType uvars ctx left leftType)
    (Hright : env.HasType uvars ctx right rightType)
    (HrightApps : VExpr.WF env uvars ctx (VExpr.mkApps right args)) :
    VEnv.TypedApplicationSpine env uvars ctx left leftType args
      (VExpr.applyForallType leftType args) := by
  induction args generalizing left right leftType rightType with
  | nil =>
    cases Hdomains with
    | zero => simpa [VExpr.applyForallType] using
        (VEnv.TypedApplicationSpine.nil Hleft)
  | cons arg args ih =>
    cases Hdomains with
    | @succ domain leftBody rightBody arity Htail =>
      have Harg := VEnv.HasType.mkApps_head henv hctx Hright HrightApps
      have HleftApp := Hleft.app Harg
      have HrightApp := Hright.app Harg
      have Htail' := Htail.instN arg 0
      have HrightRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app right arg) args) := by
        simpa [VExpr.mkApps] using HrightApps
      have Hrest := ih Htail' HleftApp HrightApp HrightRest
      simpa [VExpr.applyForallType] using
        (VEnv.TypedApplicationSpine.cons Hleft Harg Hrest)

/-- Exact generated-to-restored LHS application certificate.

The lookup fields select the source recursor and constructor installed in the
target environment. The two argument fields consume their exact dependent
telescopes and meet at the major domain. The final equality identifies the
dependent result after applying the major with the generated equation's
retained type body. -/
structure RecursorPhasesResult.GeneratedNestedIotaSource.LhsApplicationCertificate
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
  majorDomain : VExpr
  resultBody : VExpr
  leadingArguments : VEnv.TypedArguments targetEnv generatedRule.uvars
    G.translation.domains.reverse
    (S.source.recursor.type.instL S.source.recursorLevels)
    S.source.leadingArgs (.forallE majorDomain resultBody)
  constructorArguments : VEnv.TypedArguments targetEnv generatedRule.uvars
    G.translation.domains.reverse
    (sourceCtor.type.instL S.source.ctorLevels)
    S.source.ctorArgs majorDomain
  resultType : resultBody.inst
    (VExpr.mkApps (.const sourceCtor.name S.source.ctorLevels)
      S.source.ctorArgs) = G.translation.typeBody

/-- Reconstruct target LHS typing by consuming the exact restored recursor
and constructor application spines. No judgment is transported from the
lowered environment. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.LhsApplicationCertificate.targetTyping
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
    (C : S.LhsApplicationCertificate targetEnv) :
    targetEnv.HasType generatedRule.uvars G.translation.domains.reverse
      G.translation.lhsBody G.translation.typeBody := by
  have Hrecursor : targetEnv.HasType generatedRule.uvars
      G.translation.domains.reverse
      (.const S.source.recursor.name S.source.recursorLevels)
      (S.source.recursor.type.instL S.source.recursorLevels) :=
    VEnv.HasType.const C.recursorLookup C.recursorLevelsWF
      C.recursorLevelsLength
  have Hprefix := C.leadingArguments.apply Hrecursor
  have Hconstructor : targetEnv.HasType generatedRule.uvars
      G.translation.domains.reverse
      (.const sourceCtor.name S.source.ctorLevels)
      (sourceCtor.type.instL S.source.ctorLevels) :=
    VEnv.HasType.const C.constructorLookup C.constructorLevelsWF
      C.constructorLevelsLength
  have Hmajor := C.constructorArguments.apply Hconstructor
  have Hlhs := Hprefix.app Hmajor
  rw [C.resultType] at Hlhs
  have hlhs : G.translation.lhsBody =
      VExpr.mkApps (.const S.source.recursor.name S.source.recursorLevels)
        (S.source.leadingArgs ++
          [VExpr.mkApps (.const sourceCtor.name S.source.ctorLevels)
            S.source.ctorArgs]) := by
    rw [S.lhsBody]
    exact S.source.lhs_pattern
  rw [hlhs]
  simpa [VExpr.mkApps_append, VExpr.mkApps] using Hlhs

end VerifyInductive
end Lean4Lean
