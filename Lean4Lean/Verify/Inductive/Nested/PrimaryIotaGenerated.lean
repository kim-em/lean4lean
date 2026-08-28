import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIotaStructural
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSeedAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A canonical generated equation, reinterpreted as the corresponding source
nested equation.  The three body equalities are retained explicitly because
they are the exact bridge used to transport the generated equation's context
and LHS typing; no independent typing premise is needed downstream. -/
structure RecursorPhasesResult.GeneratedNestedIotaSource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {generatedRule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor generatedRule)
    (sourceDecl : VInductDecl) (sourceBlock : VInductBlock)
    (sourceOwner : VInductiveType) (sourceCtor : VConstVal) where
  source : sourceDecl.NestedIotaRule sourceBlock sourceOwner sourceCtor
    generatedRule
  domains : G.translation.domains = source.domains
  lhsBody : G.translation.lhsBody = source.lhsBody
  typeBody : G.translation.typeBody = source.typeBody
  uvars : Us.length = generatedRule.uvars

/-- Ordinary generated-rule semantics plus the explicit lowering
compatibilities construct the source nested equation without any equation
shape or typing assumptions. -/
def RecursorPhasesResult.GeneratedNestedIotaSource.ofOrdinaryCompatible
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {generatedRule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor generatedRule)
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    {ordinaryEnv : VEnv} {loweredBlock : VInductBlock}
    {loweredOwner : VInductiveType} {loweredCtor : VConstVal}
    (Hordinary : loweredDecl.IotaRule ordinaryEnv loweredBlock loweredOwner
      loweredCtor generatedRule)
    (sourceRecursor : VConstVal)
    (Hshape : sourceDecl.NestedRecursorShape sourceOwner sourceRecursor)
    (hrecursorMem : sourceRecursor ∈ sourceBlock.recursors)
    (hrecursorNames : sourceBlock.recursors.map (·.name) =
      loweredBlock.recursors.map (·.name))
    (hrecursorName : sourceRecursor.name = Hordinary.recursor.name)
    (hrecursorUvars : sourceRecursor.uvars = Hordinary.recursor.uvars)
    (huvars : sourceDecl.uvars = loweredDecl.uvars)
    (hnparams : sourceDecl.nparams = loweredDecl.nparams)
    (hindices : sourceOwner.numIndices = loweredOwner.numIndices)
    (hmotives : Hshape.motives.length = loweredDecl.types.length)
    (hminors : Hshape.minors.length = loweredDecl.ownedConstructors.length)
    (hctorName : sourceCtor.name = loweredCtor.name)
    (hdomains : G.translation.domains = Hordinary.domains)
    (hlhsBody : G.translation.lhsBody = Hordinary.lhsBody)
    (htypeBody : G.translation.typeBody = Hordinary.typeBody)
    (hlevels : Us.length = generatedRule.uvars) :
    H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor := by
  let Hsource := Hordinary.toNestedOfCompatible sourceRecursor Hshape
    hrecursorMem hrecursorNames hrecursorName hrecursorUvars huvars hnparams
    hindices hmotives hminors hctorName
  exact {
    source := Hsource
    domains := hdomains
    lhsBody := hlhsBody
    typeBody := htypeBody
    uvars := hlevels }

/-- Data-valued package for the exact completed recursor phase selected by a
successful semantic run.  Unlike `SemanticRunWithStatsResult`, this retains
the existential witnesses as data and can therefore index later certificates
without proof-irrelevance erasing run identity. -/
structure NestedInstalledProduction (outEnv : Environment) where
  c : AddInductive.Context
  stats : AddInductive.InductiveStats
  loweredDecl : VInductDecl
  nparams : Nat
  depth : Nat
  isUnsafe : Bool
  initialEnv : VEnv
  indTypes : Array InductiveType
  headerEnv : Environment
  ctorEnv : Environment
  headers : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
    initialEnv indTypes headerEnv
  constructors : ConstructorPhasesResult headers ctorEnv
  production : RecursorPhasesResult constructors outEnv

/-- Exact production origin of one source nested equation.  The concrete old
rule is fixed by a completed generated-recursor entry, while the abstract
equation is the canonical witness for the same family/constructor index and
is explicitly reinterpreted as the source nested rule. -/
structure RestoredPrimaryGeneratedSource
    {prodEnv : Environment} (P : NestedInstalledProduction prodEnv)
    (oldRecName : Name) (oldRule : RecursorRule)
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (sourceRule : VDefEq)
    (Hsource : decl.NestedIotaRule block owner ctor sourceRule)
    (Us : List Name) where
  generatedOwner : Nat
  ownerEntry : generatedOwner < P.production.entries.length
  ctorIndex : Nat
  ctorBound : ctorIndex < P.indTypes[generatedOwner]!.ctors.length
  witness : P.production.GeneratedEquationWitness Us generatedOwner
    ownerEntry ctorIndex ctorBound sourceRule
  nested : P.production.GeneratedNestedIotaSource witness decl block owner ctor
  source_eq : nested.source = Hsource
  recursorName : oldRecName =
    Lean.mkRecName P.indTypes[generatedOwner]!.name
  ruleBound : ctorIndex <
    (P.production.generated.entry generatedOwner ownerEntry).info.rules.length
  concreteRule : oldRule = (P.production.generated.entry generatedOwner
    ownerEntry).info.rules[ctorIndex]'ruleBound

end VerifyInductive
end Lean4Lean
