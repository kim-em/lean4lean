import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

/-! Concrete metadata needed to realize a generated ordinary recursor.

`TrConstVal` relates only a name, universe arity, and type. It cannot establish
any fact about rules, parameter counts, or the K flag. This relation retains
those facts explicitly, against the independent signature generator. It is a
producer target for the specification migration, not an inference from the
old `BlockCertificate`.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- The source constructor indices owned by this recursor, in generation order. -/
def ownedConstructors (s : InductiveSignature) (owner : Fin s.families.size) :
    List (Fin s.constructors.size) :=
  (List.finRange s.constructors.size).filter fun i => s.constructors[i].owner == owner

/-- The concrete rule's constructor, field count, and RHS all correspond to
the same generated equation. Typing its RHS alone is insufficient. -/
structure RuleRealization {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (lparams : List Name) (index : Fin s.constructors.size)
    (rule : Lean.RecursorRule) : Prop where
  ctor : rule.ctor = s.constructors[index].name
  nfields : rule.nfields = s.constructors[index].fields.length
  rhs : TrExprS venv lparams [] rule.rhs (g.equation index).rhs

/-- All metadata consulted by ordinary recursor reduction is justified by the
same signature as its type and rules. The environment here is the completed
abstract block; concrete installation may still be in progress. -/
structure RecursorRealization {s : InductiveSignature} (g : Instance s)
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
  rules : List.Forall₂ (RuleRealization g venv rec.levelParams)
    (s.ownedConstructors owner) rec.rules
  k : rec.k = true →
    s.families.size = 1 ∧ s.constructors.size = 1 ∧
    s.families[owner].resultLevel ≈ .zero ∧
    ∀ ctor ∈ s.constructors.toList, ctor.fields = []

/-- Rule coverage cannot survive replacing the concrete rule list by one of
a different length, even when the translated recursor type is unchanged. -/
theorem RecursorRealization.ruleCount
    {s : InductiveSignature} {g : Instance s}
    {rec : Lean.RecursorVal} {owner : Fin s.families.size} {venv : VEnv}
    (H : RecursorRealization g venv owner rec) :
    rec.rules.length = (s.ownedConstructors owner).length := by
  exact (Lean4Lean.List.Forall₂.length_eq H.rules).symm

/-- Parameter metadata is not erased by recursor realization. -/
theorem RecursorRealization.parameterCount_unique
    {s : InductiveSignature} {g : Instance s}
    {rec rec' : Lean.RecursorVal} {owner owner' : Fin s.families.size}
    {venv venv' : VEnv}
    (H : RecursorRealization g venv owner rec)
    (H' : RecursorRealization g venv' owner' rec') :
    rec.numParams = rec'.numParams := H.numParams.trans H'.numParams.symm

/-- An installed concrete entry and its abstract constant realize the same
owner. A type translation alone would erase the operational metadata. -/
def RecursorEntryRealization {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size)
    (entry : Lean.ConstantInfo × VConstVal) : Prop :=
  ∃ rec : Lean.RecursorVal, entry.1 = .recInfo rec ∧
    entry.2 = g.recursor owner ∧ RecursorRealization g venv owner rec

/-- The producer must choose one signature for both abstract compilation and
concrete execution. In particular it cannot certify the recursor types with
one signature and the rule list or metadata with another. `venv` is the
completed abstract constant environment in which the RHSs are translated. -/
structure CompilationRealization (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (venv : VEnv)
    (entries : List (Lean.ConstantInfo × VConstVal)) : Prop where
  generated : ∃ (s : InductiveSignature) (g : Instance s) (envTypes : VEnv),
    s.Models env decl ∧
    env.addConstVals decl.typeConstants = some envTypes ∧
    g.Admissible envTypes ∧ g.RecursiveTypesWF envTypes ∧
    (∀ owner, g.recursorName owner = s.families[owner].name.str "rec") ∧
    block.recursors = g.recursors ∧ block.rules = g.equations ∧
    List.Forall₂ (RecursorEntryRealization g venv)
      (List.finRange s.families.size) entries

theorem CompilationRealization.compiles
    (H : CompilationRealization env decl block venv entries) :
    Compiles env decl block := by
  rcases H.generated with ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he, _⟩
  exact ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he⟩

/-- The parameter count is fixed by the source declaration even when the
signature witness is existential. Choosing a different witness cannot repair
corrupted executable metadata. -/
theorem CompilationRealization.parameterCount
    (H : CompilationRealization env decl block venv entries)
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hmem : (Lean.ConstantInfo.recInfo rec, value) ∈ entries) :
    rec.numParams = decl.nparams := by
  rcases H.generated with ⟨s, g, _, hm, _, _, _, _, _, _, hentries⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r hentries _ hmem with
    ⟨owner, _, concrete, he, _, hrec⟩
  cases he
  exact hrec.numParams.trans hm.nparams

theorem RuleRealization.mono {s : InductiveSignature} {g : Instance s}
    {index : Fin s.constructors.size}
    (H : RuleRealization g venv Us index rule) (hle : venv ≤ venv') :
    RuleRealization g venv' Us index rule :=
  { H with rhs := H.rhs.mono hle }

theorem RecursorRealization.mono {s : InductiveSignature} {g : Instance s}
    {owner : Fin s.families.size}
    {rec : Lean.RecursorVal}
    (H : RecursorRealization g venv owner rec) (hle : venv ≤ venv') :
    RecursorRealization g venv' owner rec :=
  { H with
    type := H.type.mono hle
    rules := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.mono hle) H.rules }

theorem CompilationRealization.monoTarget
    (H : CompilationRealization env decl block venv entries) (hle : venv ≤ venv') :
    CompilationRealization env decl block venv' entries := by
  rcases H.generated with ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he, hentries⟩
  refine ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he, ?_⟩
  apply Lean4Lean.List.Forall₂.imp (l₁ := List.finRange s.families.size) _ hentries
  intro owner entry h
  rcases h with ⟨rec, hc, hv, hrec⟩
  exact ⟨rec, hc, hv, hrec.mono hle⟩

/-- Replaying the same declaration in a larger source model preserves the
joint witness, provided its source headers can still be installed. -/
theorem CompilationRealization.monoSource
    {env env' envTypes' : VEnv}
    (H : CompilationRealization env decl block venv entries) (hle : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes') :
    CompilationRealization env' decl block venv entries := by
  rcases H.generated with ⟨s, g, envTypes, hm, ht, ha, hrec, hrest⟩
  exact ⟨s, g, envTypes', hm.mono hle htypes, htypes,
    ha.mono (VEnv.addConstVals_mono hle ht htypes),
    hrec.mono (VEnv.addConstVals_mono hle ht htypes), hrest⟩

end InductiveSignature
end Lean4Lean
