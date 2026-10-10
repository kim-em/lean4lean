import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Inductive.AddInduct
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Typing.Lemmas

/-! Translation relations between the executable's recursor values, the generated recursors of
a signature instance, and the model's recursors (`VRecursor`, `VRecRule`):

* `TrRecursorRule`: a kernel rule is the generated equation of its constructor;
* `RecursorMetadata`, `TrRecursorVal`: a kernel recursor's metadata and rules are the
  generator's;
* the link to PR #43's `TrRecursor` (the `recs` field of `AddInduct`) and to
  `VRecRule.OfEquation` (the `rules` field of `VInductDecl.RecsOf`), which is how the
  recursor and rule phases discharge `VInductDecl.RecsCompiled`.

`TrConstVal` relates only a name, universe arity and type; it says nothing about rules,
parameter counts or the K flag. `TrRecursorVal` records those facts explicitly against the
signature generator (section 3.2 of the design notes). -/

namespace Lean4Lean
namespace InductiveSignature

/-- The source constructor indices owned by this recursor, in generation order. -/
def ownedConstructors (s : InductiveSignature) (owner : Fin s.families.size) :
    List (Fin s.constructors.size) :=
  (List.finRange s.constructors.size).filter fun i => s.constructors[i].owner == owner

/-- The concrete rule's constructor, field count, and RHS all correspond to
the same generated equation. Typing its RHS alone is insufficient. -/
structure TrRecursorRule {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (lparams : List Name) (index : Fin s.constructors.size)
    (rule : Lean.RecursorRule) : Prop where
  ctor : rule.ctor = s.constructors[index].name
  nfields : rule.nfields = s.constructors[index].fields.length
  rhs : TrExprS venv lparams [] rule.rhs (g.equation index).rhs

/-- The metadata of one concrete recursor, against the signature instance that generated
it: the name, universe arity, translated type, cardinalities, major premise, mutual block,
safety, and K flag. Everything recursor reduction consults except the rule list. `venv` is the
abstract environment of the block in which the type is translated. -/
structure RecursorMetadata {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size) (rec : Lean.RecursorVal) : Prop where
  name : rec.name = g.recursorName owner
  uvars : rec.levelParams.length = g.uvars
  type : TrExprS venv rec.levelParams [] rec.type (g.recursorType owner)
  numParams : rec.numParams = s.params.length
  numIndices : rec.numIndices = s.families[owner].indices.length
  numMotives : rec.numMotives = s.families.size
  numMinors : rec.numMinors = s.constructors.size
  major : rec.getMajorInduct = s.families[owner].name
  all : rec.all = s.families.toList.map (·.name)
  isUnsafe : rec.isUnsafe = s.isUnsafe
  k : rec.k = true →
    s.families.size = 1 ∧ s.constructors.size = 1 ∧
    s.families[owner].resultLevel ≈ .zero ∧
    ∀ ctor ∈ s.constructors.toList, ctor.fields = []

/-- All metadata consulted by recursor reduction is justified by the same signature as its
type and rules: the `RecursorMetadata` of the recursor together with its rule coverage. -/
structure TrRecursorVal {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size) (rec : Lean.RecursorVal) : Prop
    extends RecursorMetadata g venv owner rec where
  rules : List.Forall₂ (TrRecursorRule g venv rec.levelParams)
    (s.ownedConstructors owner) rec.rules

/-- An installed executable entry and its abstract constant are the executable and the
generated recursor of the same owner. -/
def TrRecursorEntry {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size)
    (entry : Lean.ConstantInfo × VConstVal) : Prop :=
  ∃ rec : Lean.RecursorVal, entry.1 = .recInfo rec ∧
    entry.2 = g.recursor owner ∧ TrRecursorVal g venv owner rec

/-! ### The model's recursors

A kernel recursor `rval` translating to the model's `r : VRecursor` (PR #43's `TrRecursor`,
`Verify/Environment/Basic.lean`) and to the generator's recursor (`TrRecursorVal`) makes `r`'s
rules the generated equations, reduct for reduct (`VRecRule.OfEquation`): `TrExprS` is
functional, so the two translations of a rule's reduct agree. This is the bridge from the
recursor and rule phases to `VInductDecl.RecsOf`, hence `RecsCompiled`. -/

/-- A model rule read off a kernel rule that is a generated equation is that equation's reduct
(`VRecRule.OfEquation`). -/
theorem VRecRule.OfEquation.ofTr {s : InductiveSignature} {g : Instance s}
    {venv venvR : VEnv} {lparams : List Name} {index : Fin s.constructors.size}
    {rule : Lean.RecursorRule} {r : VRecursor} {ru : VRecRule}
    (hrule : TrRecursorRule g venv lparams index rule)
    (hname : r.name = g.recursorName ⟨s.constructors[index].owner, s.constructors[index].owner.isLt⟩)
    (hctor : ru.ctor = rule.ctor) (hnfields : ru.nfields = rule.nfields)
    (hrhs : TrExprS venvR lparams [] rule.rhs ru.rhs)
    (hmajor : r.getMajorIdx = s.params.length + s.families.size + s.constructors.size +
      s.families[s.constructors[index].owner].indices.length)
    (hparams : ru.ctorParams = s.params.length) :
    VRecRule.OfEquation r ru (g.equation index) := by
  -- WAVE 2 STUB (Recursor/**): shape of `Instance.equation` (`Theory/Inductive/SignatureData`)
  -- plus `TrExprS.unique` for the reduct.
  have := hrule; have := hname; have := hctor; have := hnfields; have := hrhs; have := hmajor
  have := hparams; sorry

end InductiveSignature
end Lean4Lean
