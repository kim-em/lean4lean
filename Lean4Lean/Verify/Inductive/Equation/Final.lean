import Lean4Lean.Verify.Inductive.Equation.Canonical
import Lean4Lean.Verify.Inductive.CompletedEquationFinal

/-! Ordinary equation reconstruction delegates to the completed producer.

Nested restoration still consumes the ordinary alignment/witness records.
This bridge converts those records without duplicating recursive RHS,
dependent-domain, LHS, or final equation-typing proofs.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive

/-- Reuse the shared completed equation construction for an ordinary run. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalEquationWitness
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ rule : VDefEq,
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule) := by
  rcases H.completed.generatedRuleAlignment owner howner i hctor with ⟨alignment⟩
  rcases alignment.finalCanonicalEquationWitness with ⟨rule, ⟨witness⟩⟩
  refine ⟨rule, ⟨{
    alignment := {
      sourceOwner_lt := witness.alignment.sourceOwner_lt
      sourceCtor_lt := witness.alignment.sourceCtor_lt
      abstractOwner_lt := witness.alignment.abstractOwner_lt
      abstractCtor_lt := witness.alignment.abstractCtor_lt
      ownerTranslation := witness.alignment.ownerTranslation
      ctorTranslation := witness.alignment.ctorTranslation
      sourceRule_lt := witness.alignment.sourceRule_lt
      rule := witness.alignment.rule
      semantics := witness.alignment.semantics
      parameterDecls_eq := witness.alignment.parameterDecls_eq
      motiveEvidence := witness.alignment.motiveEvidence
      originEvidence := witness.alignment.originEvidence
      semantic_owner := witness.alignment.semantic_owner }
    translation := witness.translation
    uvars := witness.uvars
    wf := witness.wf }⟩⟩

end VerifyInductive
end Lean4Lean
