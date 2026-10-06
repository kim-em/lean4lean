import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.InductiveShape

/-! Typed models and elimination admissibility for the pure signature generator. -/

namespace Lean4Lean
namespace InductiveSignature

/-- Exact family/constructor names and types modulo typed definitional equality.
The source constructor types are compared in the environment containing the
source family headers, before any recursor or equation is installed. -/
structure Models (s : InductiveSignature) (env : VEnv) (decl : VInductDecl) : Prop where
  uvars : s.uvars = decl.uvars
  nparams : s.params.length = decl.nparams
  safety : s.isUnsafe = decl.isUnsafe
  families : List.Forall₂ (fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
    normalized.numIndices = source.numIndices ∧
    normalized.resultLevel ≈ source.resultLevel ∧
    env.IsDefEqU decl.uvars [] normalized.type source.type ∧
    normalized.ctors.map VConstVal.name = source.ctors.map VConstVal.name)
    s.declaration.types decl.types
  constructors : ∃ envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    List.Forall₂ (fun normalized source =>
      normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] normalized.type source.type)
      s.declaration.constructorConstants decl.constructorConstants
  /-- Positivity checks a field after reduction, while generated minors retain
  its original domain. An external field may therefore contain source names
  erased by reduction; its checked normal form must be source-free. -/
  externalFields : s.isUnsafe = true ∨ ∃ envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length) type,
      ctor.fields[i] = Field.external type →
      ∃ normalized,
        envTypes.IsDefEqU decl.uvars
          (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
          type normalized ∧
        normalized.SourceConstFree (s.families.toList.map (·.name))
  recursiveDomains : s.isUnsafe = true ∨
    ∀ ctor ∈ s.constructors.toList, ∀ type r,
      Field.recursive type r ∈ ctor.fields →
      (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
      (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name)))
  /-- The checked constructor result has the owning family's exact index
  count. Normalization retains this finite syntactic fact independently of
  the typed correspondence between the selected and source telescopes. -/
  constructorArity : ∀ ctor ∈ s.constructors.toList,
    ctor.indices.length = s.families[ctor.owner].indices.length

/-- Singleton elimination is certified from the constructor fields. A field
is either a proof or is determined by an index of the constructor's result.
The test is made after universe specialization. -/
def SingletonElimination (s : InductiveSignature) (envTypes : VEnv)
    (uvars : Nat) (levels : List VLevel) : Prop :=
  s.families.size = 1 ∧ s.constructors.size ≤ 1 ∧
  ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
    envTypes.HasType uvars
      ((((s.fieldTypes ctor).take i).map (·.instL levels)).reverse ++
        (s.params.map (·.instL levels)).reverse)
      ((s.fieldType i ctor.fields[i]).instL levels) (.sort .zero) ∨
    VExpr.bvar (ctor.fields.length - 1 - i) ∈ ctor.indices

/-- Admissibility is checked at the instance's source universes. In particular,
a Sort-polymorphic family can acquire large elimination after specialization
without changing its native recursor's type. -/
structure Instance.Admissible {s : InductiveSignature} (g : Instance s)
    (envTypes : VEnv) : Prop where
  levels_length : g.levels.length = s.uvars
  levels_wf : ∀ level ∈ g.levels, level.WF g.uvars
  target_wf : g.targetLevel.WF g.uvars
  elimination :
    (∀ family ∈ s.families.toList, (family.resultLevel.inst g.levels).IsNeverZero) ∨
    g.targetLevel ≈ .zero ∨ s.SingletonElimination envTypes g.uvars g.levels

/-- Each generated induction hypothesis is a well-formed type in the context in
which the generated minor premise binds it: parameters, motives, earlier
minors, the constructor's fields and the earlier hypotheses.  This is the
typing fact the generated recursor needs from the recursive shapes.  It is
stated in the environment in which the recursors are declared, that is after
the family headers, the constructors and the declaration's projection entries,
since that is where the executable checks the generated types.  A
definitional-equality form in a smaller context is not derivable from the
checker's evidence without context strengthening of definitional equality,
which `docs/inductives/STRENGTHENING.md` refutes in general. -/
def Instance.RecursiveTypesWF {s : InductiveSignature} (g : Instance s) (env : VEnv) : Prop :=
  ∀ (index : Fin s.constructors.size) (j : Nat)
    (hj : j < (recursiveFields s.constructors[index]).length),
    env.IsType g.uvars (g.hypothesisContext s.constructors[index] index.val j)
      (g.hypothesis s.constructors[index] index.val j
        (recursiveFields s.constructors[index])[j].1
        (recursiveFields s.constructors[index])[j].2)

/-- Ordinary canonical generation fixes every motive, minor, recursive call,
and both sides of every equation. This certificate does not accept an
arbitrary list of equations on the strength of their typing. -/
structure Compiles (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop where
  generated : ∃ (s : InductiveSignature) (g : Instance s) (envTypes : VEnv),
    s.Models env decl ∧
    env.addConstVals decl.typeConstants = some envTypes ∧
    g.Admissible envTypes ∧
    (∃ envCtors, envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      g.RecursiveTypesWF (envCtors.addProjections decl.projectionEntries)) ∧
    (∀ owner, g.recursorName owner = s.families[owner].name.str "rec") ∧
    block.recursors = g.recursors ∧ block.rules = g.equations

end InductiveSignature
end Lean4Lean
