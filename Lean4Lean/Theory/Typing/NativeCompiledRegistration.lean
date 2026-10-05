import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.NativeRegistryInstallation
import Lean4Lean.Theory.Typing.NativeRuleRegistration

/-! A native table is extracted from the finite compilation retained by an
actual inductive installation. Abstract eliminator metadata is not needed.
The original compilation base is preserved across `CompiledInductive.replay`.
-/
namespace Lean4Lean
open InductiveSignature InductiveSignature.NativeRecursorData VEnv
set_option Elab.async false
set_option maxRecDepth 2048
variable {base installBase extended env : VEnv} {source expanded : VInductDecl}
  {block : VInductBlock} {equation : VDefEq}

/-- Every restored constructor equation belongs to the descriptor for its
actual owner. Both the descriptor and equation are computed from one instance. -/
theorem InductiveSignature.CompilationData.nativeEntries_equation
    (compilation : CompilationData base source expanded signature generated auxiliaries block)
    (member : equation ∈ block.rules) (key : Name) :
    ∃ data ∈ compilationEntries key source signature auxiliaries generated,
      ∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner ∧
        data.equation index = some equation := by
  obtain ⟨original, originalMember, restored⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp compilation.equations) _ member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp originalMember
  let data := ofInstance key (CaseSchema.ofCompilation source signature auxiliaries)
    generated signature.constructors[index].owner
  have instanceEq : data.nativeInstance = generated := by
    cases generated with
    | mk U levels target names =>
      change Instance.mk U levels target (fun owner => signature.families[owner].name.str "rec") =
        Instance.mk U levels target names
      congr 1
      exact funext fun owner => (compilation.recursorNames owner).symm
  refine ⟨data, List.mem_map.mpr ⟨signature.constructors[index].owner,
    List.mem_finRange _, rfl⟩, index, rfl, ?_⟩
  change (compilationRestoration source auxiliaries).equation (data.nativeInstance.equation index) = _
  rw [instanceEq]
  exact restored

/-- Actual block installation produces a finite native table with exact
recursor-name coverage, sound lookups, and coverage of every installed rule.
No separately supplied schema lookup, successful selection, or semantic
reduction answer is required. -/
theorem CompiledInductive.installedNativeEntries
    (compiled : CompiledInductive installBase source block)
    (installed : block.install installBase = some extended)
    (below : extended ≤ env) (key : Name) :
    ∃ entries : List NativeRecursorData,
      entries.map (·.name) = block.recursors.map (·.name) ∧
      (∀ name data, installEntries (fun _ => none) entries name = some data →
        NativeRecursorRegistered env data ∧ data.name = name) ∧
      (∀ old data, data ∈ entries → installEntries old entries data.name = some data) ∧
      (∀ equation ∈ block.rules, ∃ data ∈ entries,
        ∃ index : Fin data.schema.signature.constructors.size,
          data.schema.signature.constructors[index].owner = data.owner ∧
          data.equation index = some equation) := by
  obtain ⟨base, expanded, signature, generated, auxiliaries, baseBelow, compilation, specializations⟩ :=
    compiled.compilationOrigin
  refine ⟨compilationEntries key source signature auxiliaries generated,
    compilation.nativeEntries_names, ?_, ?_, ?_⟩
  · intro name data lookup
    exact NativeRecursorRegistered.installEntries
      (fun _ _ absent => by cases absent)
      (fun _ member => NativeRecursorRegistered.compilationEntries compilation specializations
        baseBelow installed below member) lookup
  · intro old data member
    exact compilation.nativeEntries_lookup member
  · intro equation member
    exact compilation.nativeEntries_equation member key

/-- Both public compilation paths retain the same finite origin; ordinary
`VDecl.WF.induct` can therefore populate its native table directly. -/
theorem VInductDecl.CompilesTo.installedNativeEntries
    (compiled : source.CompilesTo installBase block)
    (installed : block.install installBase = some extended)
    (below : extended ≤ env) (key : Name) :
    ∃ entries : List NativeRecursorData,
      entries.map (·.name) = block.recursors.map (·.name) ∧
      (∀ name data, installEntries (fun _ => none) entries name = some data →
        NativeRecursorRegistered env data ∧ data.name = name) ∧
      (∀ old data, data ∈ entries → installEntries old entries data.name = some data) ∧
      (∀ equation ∈ block.rules, ∃ data ∈ entries,
        ∃ index : Fin data.schema.signature.constructors.size,
          data.schema.signature.constructors[index].owner = data.owner ∧
          data.equation index = some equation) :=
  compiled.compiled.installedNativeEntries installed below key

end Lean4Lean
