import Lean4Lean.Verify.Inductive.Nested.PrimaryEquations
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Exact production origin of restored primary equations

This module joins the independently generated ordinary equation with the
concrete rule selected by executable recursor restoration.  In particular,
the family index, constructor index, recursor name, and old concrete rule are
all consequences of one completed production and one restored step.
-/

/-- Package a generated source equation at its exact production position.
All formerly independent metadata fields are definitionally fixed by the
indices and witness.  `restoredPrimaryGeneratedRuleAlignment` then proves
that this concrete rule is the one consumed by executable restoration. -/
def NestedInstalledProduction.primaryGeneratedSourceAt
    {prodEnv : Environment} (P : NestedInstalledProduction prodEnv)
    (generatedOwner : Nat)
    (ownerEntry : generatedOwner < P.production.entries.length)
    (ctorIndex : Nat)
    (ctorBound : ctorIndex < P.indTypes[generatedOwner]!.ctors.length)
    {Us : List Name} {sourceRule : VDefEq}
    (G : P.production.GeneratedEquationWitness Us generatedOwner ownerEntry
      ctorIndex ctorBound sourceRule)
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal}
    (S : P.production.GeneratedNestedIotaSource G decl block owner ctor) :
    let oldRecName := Lean.mkRecName P.indTypes[generatedOwner]!.name
    let oldRule :=
      getElem
        (P.production.generated.entry generatedOwner ownerEntry).info.rules
        ctorIndex G.alignment.sourceRule_lt
    RestoredPrimaryGeneratedSource P oldRecName oldRule decl block owner ctor
      sourceRule S.source Us := by
  exact {
    generatedOwner := generatedOwner
    ownerEntry := ownerEntry
    ctorIndex := ctorIndex
    ctorBound := ctorBound
    witness := G
    nested := S
    source_eq := rfl
    recursorName := rfl
    ruleBound := G.alignment.sourceRule_lt
    concreteRule := rfl }

/-- The concrete rule fixed by `primaryGeneratedSourceAt` is exactly the old
endpoint of the executable restoration entry at the same constructor index.
This is the proof-valued half of the production/source join. -/
theorem NestedInstalledProduction.primaryGeneratedSourceAt_restoration
    {prodEnv : Environment} (P : NestedInstalledProduction prodEnv)
    (generatedOwner : Nat)
    (ownerEntry : generatedOwner < P.production.entries.length)
    (Hstep : RestoredRecursorStep result prodEnv auxRec allIndNames
      (Lean.mkRecName P.indTypes[generatedOwner]!.name)
      sourceProdEnv targetProdEnv)
    (ctorIndex : Nat)
    (ctorBound : ctorIndex < P.indTypes[generatedOwner]!.ctors.length)
    (restoredBound : ctorIndex < Hstep.restored.newInfo.rules.length)
    {Us : List Name} {sourceRule : VDefEq}
    (G : P.production.GeneratedEquationWitness Us generatedOwner ownerEntry
      ctorIndex ctorBound sourceRule) :
    RuleRestoration result prodEnv auxRec
      (Lean.mkRecName P.indTypes[generatedOwner]!.name)
      Hstep.restored.newRecName
      (getElem
        (P.production.generated.entry generatedOwner ownerEntry).info.rules
        ctorIndex G.alignment.sourceRule_lt)
      (getElem Hstep.restored.newInfo.rules ctorIndex restoredBound) := by
  rcases P.production.restoredPrimaryGeneratedRuleAlignment generatedOwner
      ownerEntry Hstep rfl ctorIndex ctorBound restoredBound with
    ⟨sourceBound, _alignment, Hrule⟩
  have hsourceBound : sourceBound = G.alignment.sourceRule_lt :=
    Subsingleton.elim _ _
  subst sourceBound
  exact Hrule

end VerifyInductive
end Lean4Lean
