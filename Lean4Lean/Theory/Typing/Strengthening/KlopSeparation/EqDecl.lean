import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.CanonicalEq

/-! # The inductive declaration of `Eq`, built by hand

First part of `exists_minimalKlopEnv` (`KlopSeparation/Statement.lean`): the signature of
`Eq`, the declaration generated from it, and the check that the generator produces exactly
the canonical type of `Eq`, of `Eq.refl`, of `Eq.rec` and the canonical ι rule
(`Theory/CanonicalEq.lean`). The well-formedness of the declaration (`VInductDecl.WF`) and
its installation are still to be proved, following `Tests/InductiveTheory.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- The signature of `Eq.{u} {α : Sort u} (a : α) : α → Prop` with its constructor
`Eq.refl : Eq a a`. -/
def eqSignature : InductiveSignature where
  uvars := 1
  params := [.sort (.param 0), .bvar 0]
  families := #[{ name := ``Eq, indices := [.bvar 1], resultLevel := .zero }]
  constructors :=
    #[{ name := ``Eq.refl, owner := ⟨0, by decide⟩, fields := [], indices := [.bvar 0] }]

/-- The recursor instance `Eq.rec.{u, u_1}`: motive universe `u = param 0`, the universe of
`α` is `u_1 = param 1`. -/
def eqInstance : InductiveSignature.Instance eqSignature where
  uvars := 2
  levels := [.param 1]
  targetLevel := .param 0
  recursorName := fun _ => ``Eq.rec

def eqRecursor : VConstVal := eqInstance.recursor ⟨0, by decide⟩

def eqRule : VDefEq := eqInstance.equation ⟨0, by decide⟩

theorem eqSignature_type :
    eqSignature.declaration.types.map (·.type) = [canonicalEqType] := rfl

theorem eqSignature_ctor :
    eqSignature.declaration.constructorConstants.map (·.type) = [canonicalEqReflType] := rfl

theorem eqRecursor_type : eqRecursor.type = canonicalEqRecType := rfl

theorem eqRecursor_name : eqRecursor.name = ``Eq.rec := rfl

theorem eqRecursor_uvars : eqRecursor.uvars = 2 := rfl

theorem eqRule_eq : eqRule = canonicalEqRecRule := rfl

end VEnv.Strengthening
end Lean4Lean
