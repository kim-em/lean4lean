import Lean4Lean.Verify.Inductive.Specification.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Indexed output certificate for one recursor per mutual-family member. -/
structure RecursorCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  length : recursors.length = decl.types.length
  shapes : ∀ i (htype : i < decl.types.length)
      (hrec : i < recursors.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

/-- Append-oriented invariant matching the recursor-generation loop. -/
structure RecursorBuildCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  covered : recursors.length ≤ decl.types.length
  shapes : ∀ i (hrec : i < recursors.length)
      (htype : i < decl.types.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

theorem RecursorBuildCertificate.empty (decl : VInductDecl) :
    RecursorBuildCertificate decl [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem RecursorBuildCertificate.push
    (H : RecursorBuildCertificate decl recursors)
    (hnext : recursors.length < decl.types.length)
    (hshape : Nonempty
      (decl.RecursorShape decl.types[recursors.length] recursor)) :
    RecursorBuildCertificate decl (recursors ++ [recursor]) where
  covered := by simp; omega
  shapes i hrec htype := by
    by_cases hi : i < recursors.length
    · simpa [List.getElem_append, hi] using H.shapes i hi htype
    · have hieq : i = recursors.length := by simp at hrec; omega
      subst i
      simpa using hshape

theorem RecursorBuildCertificate.complete
    (H : RecursorBuildCertificate decl recursors)
    (hcomplete : recursors.length = decl.types.length) :
    RecursorCertificate decl recursors where
  length := hcomplete
  shapes i htype hrec := H.shapes i hrec htype

theorem RecursorCertificate.forall₂
    (H : RecursorCertificate decl recursors) :
    List.Forall₂ (fun type recursor =>
      Nonempty (decl.RecursorShape type recursor))
      decl.types recursors := by
  apply List.forall₂_of_getElem H.length.symm
  intro i htype hrec
  exact H.shapes i htype hrec

/-- Indexed primary-recursor certificate for a restored nested block.  Its
motives and minors may include the auxiliary suffix produced by lowering. -/
structure NestedRecursorCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  length : recursors.length = decl.types.length
  shapes : ∀ i (htype : i < decl.types.length)
      (hrec : i < recursors.length),
    Nonempty (decl.NestedRecursorShape decl.types[i] recursors[i])

theorem NestedRecursorCertificate.forall₂
    (H : NestedRecursorCertificate decl recursors) :
    List.Forall₂ (fun type recursor =>
      Nonempty (decl.NestedRecursorShape type recursor))
      decl.types recursors := by
  apply List.forall₂_of_getElem H.length.symm
  intro i htype hrec
  exact H.shapes i htype hrec

theorem RecursorCertificate.toNested
    (H : RecursorCertificate decl recursors) :
    NestedRecursorCertificate decl recursors where
  length := H.length
  shapes i htype hrec := by
    rcases H.shapes i htype hrec with ⟨Hshape⟩
    exact ⟨Hshape.toNested⟩

/-- Indexed output certificate for exactly one iota rule per owned
constructor, in the same flattened order used for minors. -/
structure IotaCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) : Prop where
  length : block.rules.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < block.rules.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 block.rules[i])

theorem IotaCertificate.forall₂
    (H : IotaCertificate env decl block) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule env block owned.1 owned.2 rule))
      decl.ownedConstructors block.rules := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Rule-list certificate used when nested restoration appends auxiliary
rules after the primary rules corresponding to source constructors. -/
structure IotaListCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (ruleList : List VDefEq) : Prop where
  length : ruleList.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < ruleList.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 ruleList[i])

/-- Append-oriented iota invariant matching the per-family batches emitted by
`mkRecRules`. The rule list may later become either the complete ordinary
list or the primary prefix retained by nested restoration. -/
structure IotaBuildCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (rules : List VDefEq) : Prop where
  covered : rules.length ≤ decl.ownedConstructors.length
  shapes : ∀ i (hrule : i < rules.length)
      (hctor : i < decl.ownedConstructors.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 rules[i])

theorem IotaBuildCertificate.empty
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) :
    IotaBuildCertificate env decl block [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem IotaBuildCertificate.push
    (H : IotaBuildCertificate env decl block rules)
    (hnext : rules.length < decl.ownedConstructors.length)
    (hshape : Nonempty (decl.IotaRule env block
      decl.ownedConstructors[rules.length].1
      decl.ownedConstructors[rules.length].2 rule)) :
    IotaBuildCertificate env decl block (rules ++ [rule]) where
  covered := by simp; omega
  shapes i hrule hctor := by
    by_cases hold : i < rules.length
    · simpa [List.getElem_append, hold] using H.shapes i hold hctor
    · have hi : i = rules.length := by simp at hrule; omega
      subst i
      simpa using hshape

theorem IotaBuildCertificate.append
    (H : IotaBuildCertificate env decl block rules)
    (hlen : newRules.length + rules.length ≤
      decl.ownedConstructors.length)
    (hshapes : ∀ i (hi : i < newRules.length),
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[rules.length + i].1
        decl.ownedConstructors[rules.length + i].2 newRules[i])) :
    IotaBuildCertificate env decl block (rules ++ newRules) := by
  induction newRules generalizing rules with
  | nil => simpa using H
  | cons rule newRules ih =>
      have hnext : rules.length < decl.ownedConstructors.length := by
        simp at hlen
        omega
      have hhead := hshapes 0 (by simp)
      have Hpush := H.push hnext (by simpa using hhead)
      have Htail := ih Hpush (by
          simp at hlen ⊢
          omega) (by
          intro i hi
          have h := hshapes (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using h)
      simpa [List.append_assoc] using Htail

theorem IotaBuildCertificate.complete
    (H : IotaBuildCertificate env decl block rules)
    (hcomplete : rules.length = decl.ownedConstructors.length) :
    IotaListCertificate env decl block rules where
  length := hcomplete
  rules i hctor hrule := H.shapes i hrule hctor

theorem IotaBuildCertificate.completeBlock
    (H : IotaBuildCertificate env decl block block.rules)
    (hcomplete : block.rules.length = decl.ownedConstructors.length) :
    IotaCertificate env decl block where
  length := hcomplete
  rules i hctor hrule := H.shapes i hrule hctor

theorem IotaListCertificate.forall₂
    (H : IotaListCertificate env decl block ruleList) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule env block owned.1 owned.2 rule))
      decl.ownedConstructors ruleList := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Complete restored-primary equation list for a nested declaration.  Its
pointwise judgment permits the auxiliary motive/minor telescope retained by
the exact restored recursor shape and fields consumed by auxiliary recursors. -/
structure NestedIotaListCertificate (decl : VInductDecl)
    (block : VInductBlock) (ruleList : List VDefEq) : Prop where
  length : ruleList.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < ruleList.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 ruleList[i])

/-- Append-oriented form used while source primary batches are selected from
the expanded generated-rule traversal. -/
structure NestedIotaBuildCertificate (decl : VInductDecl)
    (block : VInductBlock) (rules : List VDefEq) : Prop where
  covered : rules.length ≤ decl.ownedConstructors.length
  shapes : ∀ i (hrule : i < rules.length)
      (hctor : i < decl.ownedConstructors.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 rules[i])

theorem NestedIotaBuildCertificate.empty
    (decl : VInductDecl) (block : VInductBlock) :
    NestedIotaBuildCertificate decl block [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem NestedIotaBuildCertificate.push
    (H : NestedIotaBuildCertificate decl block rules)
    (hnext : rules.length < decl.ownedConstructors.length)
    (hshape : Nonempty (decl.NestedIotaRule block
      decl.ownedConstructors[rules.length].1
      decl.ownedConstructors[rules.length].2 rule)) :
    NestedIotaBuildCertificate decl block (rules ++ [rule]) where
  covered := by simp; omega
  shapes i hrule hctor := by
    by_cases hold : i < rules.length
    · simpa [List.getElem_append, hold] using H.shapes i hold hctor
    · have hi : i = rules.length := by simp at hrule; omega
      subst i
      simpa using hshape

theorem NestedIotaBuildCertificate.append
    (H : NestedIotaBuildCertificate decl block rules)
    (hlen : newRules.length + rules.length ≤
      decl.ownedConstructors.length)
    (hshapes : ∀ i (hi : i < newRules.length),
      Nonempty (decl.NestedIotaRule block
        decl.ownedConstructors[rules.length + i].1
        decl.ownedConstructors[rules.length + i].2 newRules[i])) :
    NestedIotaBuildCertificate decl block (rules ++ newRules) := by
  induction newRules generalizing rules with
  | nil => simpa using H
  | cons rule newRules ih =>
      have hnext : rules.length < decl.ownedConstructors.length := by
        simp at hlen
        omega
      have hhead := hshapes 0 (by simp)
      have Hpush := H.push hnext (by simpa using hhead)
      have Htail := ih Hpush (by
          simp at hlen ⊢
          omega) (by
          intro i hi
          have h := hshapes (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using h)
      simpa [List.append_assoc] using Htail

theorem NestedIotaBuildCertificate.complete
    (H : NestedIotaBuildCertificate decl block rules)
    (hcomplete : rules.length = decl.ownedConstructors.length) :
    NestedIotaListCertificate decl block rules where
  length := hcomplete
  rules i hctor hrule := H.shapes i hrule hctor

theorem NestedIotaListCertificate.forall₂
    (H : NestedIotaListCertificate decl block ruleList) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.NestedIotaRule block owned.1 owned.2 rule))
      decl.ownedConstructors ruleList := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Generator-facing form of ordinary compilation. Its indexed fields match
the loops in `mkRecInfos` and `mkRecRules`; `ordinary` below converts them to
the independent list-relational specification. -/
structure OrdinaryCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  recursors : RecursorCertificate decl block.recursors
  rules : ∃ envTypes envCtors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    IotaCertificate envCtors decl block
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- The executable block-name check contains the original type and
constructor names as an exact prefix. Consequently its global freshness
certificate supplies precisely the name-uniqueness field of `SourceWF`. -/
theorem sourceNames_nodup_ofBlock
    {block : VInductBlock} {decl : VInductDecl}
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    decl.sourceNames.Nodup := by
  rw [htypes, hctors] at hnames
  simp only [List.map_append] at hnames
  exact (List.nodup_append.mp hnames).1

theorem OrdinaryCompilationCertificate.sourceNames_nodup
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.sourceNames.Nodup :=
  sourceNames_nodup_ofBlock H.types H.ctors H.names

theorem TrInductDeclCore.toTrInductDeclOfOrdinaryCompilation
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ [])
    (Hcompile : OrdinaryCompilationCertificate env decl block) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H
    (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty H hsource)
    Hcompile.sourceNames_nodup

theorem OrdinaryCompilationCertificate.ordinary
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.OrdinaryCompilation env block := by
  rcases H.rules with ⟨envTypes, envCtors, htypes, hctors, Hrules⟩
  exact {
  types := H.types
  ctors := H.ctors
  projections := H.projections
  recursors := H.recursors.forall₂
  rules := ⟨envTypes, envCtors, htypes, hctors, Hrules.forall₂⟩
  names := H.names }

theorem OrdinaryCompilationCertificate.compilesTo
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.CompilesTo env block :=
  .ordinary H.ordinary

/-- Indexed, generator-facing form of nested compilation. The primary
recursors and rules use the same certificates as ordinary compilation, while
the restoration-only suffix is isolated to deterministic names and guarded
right-hand sides. -/
structure NestedCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) where
  main : VInductiveType
  rest : List VInductiveType
  types_source : decl.types = main :: rest
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  envTypes : VEnv
  envCtors : VEnv
  types_added : env.addConstVals block.types = some envTypes
  ctors_added : envTypes.addConstVals block.ctors = some envCtors
  primaryRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  recursors_eq : block.recursors = primaryRecursors ++ auxiliaryRecursors
  primary_recursors : NestedRecursorCertificate decl primaryRecursors
  primaryRules : List VDefEq
  auxiliaryRules : List VDefEq
  rules_eq : block.rules = primaryRules ++ auxiliaryRules
  primary_rules : NestedIotaListCertificate decl block primaryRules
  auxiliary_guarded : ∀ rule ∈ auxiliaryRules,
    rule.rhs.GuardedRuleRhs (block.recursors.map (·.name))
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))

theorem NestedCompilationCertificate.sourceNames_nodup
    (H : NestedCompilationCertificate env decl block) :
    decl.sourceNames.Nodup :=
  sourceNames_nodup_ofBlock H.types H.ctors H.names

theorem TrInductDeclCore.toTrInductDeclOfNestedCompilation
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ [])
    (Hcompile : NestedCompilationCertificate env decl block) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H
    (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty H hsource)
    Hcompile.sourceNames_nodup

def NestedCompilationCertificate.nested
    (H : NestedCompilationCertificate env decl block) :
    decl.NestedCompilation env block where
  main := H.main
  rest := H.rest
  types_source := H.types_source
  types := H.types
  ctors := H.ctors
  projections := H.projections
  primaryRecursors := H.primaryRecursors
  auxiliaryRecursors := H.auxiliaryRecursors
  recursors_eq := H.recursors_eq
  primary_recursors := H.primary_recursors.forall₂
  primaryRules := H.primaryRules
  auxiliaryRules := H.auxiliaryRules
  rules_eq := H.rules_eq
  primary_rules := ⟨H.envTypes, H.envCtors, H.types_added, H.ctors_added,
    H.primary_rules.forall₂⟩
  auxiliary_guarded := H.auxiliary_guarded
  names := H.names

theorem NestedCompilationCertificate.compilesTo
    (H : NestedCompilationCertificate env decl block) :
    decl.CompilesTo env block := .nested H.nested

/-- Append-oriented restoration invariant for the auxiliary recursor/rule
suffix. It mirrors `processRec`: recursors receive consecutive `main.recN`
names, while restored auxiliary rules must retain a guarded RHS. -/
structure AuxiliaryRestorationPrefix (decl : VInductDecl)
    (block : VInductBlock) (main : VInductiveType)
    (recursors : List VConstVal) (rules : List VDefEq) : Prop where
  guarded : ∀ rule ∈ rules,
    rule.rhs.GuardedRuleRhs (block.recursors.map (·.name))

theorem AuxiliaryRestorationPrefix.empty
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType) :
    AuxiliaryRestorationPrefix decl block main [] [] where
  guarded _ h := by simp at h

theorem AuxiliaryRestorationPrefix.pushRecursor
    (H : AuxiliaryRestorationPrefix decl block main recursors rules) :
    AuxiliaryRestorationPrefix decl block main
      (recursors ++ [recursor]) rules where
  guarded := H.guarded

theorem AuxiliaryRestorationPrefix.appendRules
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (hnew : ∀ rule ∈ newRules,
      rule.rhs.GuardedRuleRhs (block.recursors.map (·.name))) :
    AuxiliaryRestorationPrefix decl block main recursors
      (rules ++ newRules) where
  guarded rule hrule := by
    rcases List.mem_append.mp hrule with hold | hnewRule
    · exact H.guarded rule hold
    · exact hnew rule hnewRule

/-- Final nested-compilation assembly for the actual restored primary
recursors and rules. Unlike the ordinary shortcut, these need not be the
lowered constants verbatim: restoration may rewrite their telescopes while
preserving the independent recursor/iota specifications. -/
def NestedCompilationCertificate.ofRestoration
    (env envTypes envCtors : VEnv) (decl : VInductDecl)
    (block : VInductBlock)
    (main : VInductiveType) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : NestedRecursorCertificate decl primaryRecursors)
    (HprimaryRules : NestedIotaBuildCertificate decl block primaryRules)
    (hprimaryLength : primaryRules.length =
      decl.ownedConstructors.length)
    (Haux : AuxiliaryRestorationPrefix decl block main
      auxiliaryRecursors auxiliaryRules)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypesAdded : env.addConstVals block.types = some envTypes)
    (hctorsAdded : envTypes.addConstVals block.ctors = some envCtors)
    (hrecursors : block.recursors =
      primaryRecursors ++ auxiliaryRecursors)
    (hrules : block.rules = primaryRules ++ auxiliaryRules)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    NestedCompilationCertificate env decl block where
  main := main
  rest := rest
  types_source := htypesSource
  types := htypes
  ctors := hctors
  projections := hprojections
  envTypes := envTypes
  envCtors := envCtors
  types_added := htypesAdded
  ctors_added := hctorsAdded
  primaryRecursors := primaryRecursors
  auxiliaryRecursors := auxiliaryRecursors
  recursors_eq := hrecursors
  primary_recursors := HprimaryRecursors
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  rules_eq := hrules
  primary_rules := HprimaryRules.complete hprimaryLength
  auxiliary_guarded := Haux.guarded
  names := hnames


end VerifyInductive
end Lean4Lean
