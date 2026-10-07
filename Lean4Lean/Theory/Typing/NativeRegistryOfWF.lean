import Lean4Lean.Theory.Typing.NativeDeclarationProvenance
import Lean4Lean.Theory.Typing.NativeCompiledRegistration

/-! The actual `WF'` derivation constructs its native table. Every inductive
installation contributes the descriptors of its retained compilation, including
compilations replayed from an earlier base. Equation coverage is proved along
that same construction; it is not an input registry assumption. -/
namespace Lean4Lean.VEnv
open InductiveSignature NativeRecursorData
open private declaration_le definitionRegistry_decl_new definitionRegistry_decl_preserves
  from Lean4Lean.Theory.Typing.DefinitionHistory
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity
set_option Elab.async false
set_option maxRecDepth 2048
variable {env extended : VEnv} {declarations : List VDecl}
  {table : Name → Option NativeRecursorData} {equation : VDefEq}

/-- Exact syntactic coverage of an installed equation by the two generated
name tables or the fixed quotient rule. -/
def NativeRegistryEquationCovered (declarations : List VDecl)
    (table : Name → Option NativeRecursorData) (equation : VDefEq) : Prop :=
  (∃ value, definitionRegistry declarations value.name = some value ∧ equation = value.toDefEq) ∨
  (.quot ∈ declarations ∧ equation = quotDefEq) ∨
  ∃ data, table data.name = some data ∧
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.equation index = some equation

private theorem NativeRegistryEquationCovered.declaration
    (history : env.WF' declarations) (declaration : VDecl.WF env d extended)
    (covered : NativeRegistryEquationCovered declarations table equation) :
    NativeRegistryEquationCovered (d :: declarations) table equation := by
  rcases covered with ⟨value, lookup, equal⟩ | ⟨member, equal⟩ | native
  · exact .inl ⟨value, definitionRegistry_decl_preserves declaration
      (history.definitionRegistry_registered lookup).1 lookup, equal⟩
  · exact .inr (.inl ⟨List.mem_cons_of_mem _ member, equal⟩)
  · exact .inr (.inr native)

private theorem NativeRegistryEquationCovered.install
    {base installBase : VEnv} {source expanded : VInductDecl} {block : VInductBlock}
    (history : NativeRegistryHistory installBase declarations table)
    (compilation : CompilationData base source expanded signature generated auxiliaries block)
    (installed : block.install installBase = some extended)
    (covered : NativeRegistryEquationCovered declarations table equation) (key : Name) :
    NativeRegistryEquationCovered (.induct source :: declarations)
      (installEntries table (compilationEntries key source signature auxiliaries generated)) equation := by
  rcases covered with definition | quotient | ⟨data, lookup, index, owner, equationEq⟩
  · exact .inl definition
  · exact .inr (.inl ⟨List.mem_cons_of_mem _ quotient.1, quotient.2⟩)
  · exact .inr (.inr ⟨data,
      compilation.nativeEntries_preserves installed (history.registered lookup).1 lookup,
      index, owner, equationEq⟩)

/-- Every well-formed declaration history produces an actual native registry
history and exact coverage of all its installed equations. The construction
uses the original compilation base retained by `CompiledInductive.replay`.
No abstract eliminator-schema registration is required. -/
theorem WF'.nativeRegistry (formed : env.WF' declarations) :
    ∃ table : Name → Option NativeRecursorData,
      NativeRegistryHistory env declarations table ∧
      ∀ equation, env.defeqs equation → NativeRegistryEquationCovered declarations table equation := by
  induction formed with
  | empty => exact ⟨fun _ => none, .empty, fun _ absent => by cases absent⟩
  | decl declaration previous ih =>
    obtain ⟨table, history, covered⟩ := ih
    cases declaration with
    | «axiom» typed installed =>
      refine ⟨table, .decl history (.axiom typed installed), ?_⟩
      intro equation present
      exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
        previous (.axiom typed installed)
    | «opaque» typed installed =>
      refine ⟨table, .decl history (.opaque typed installed), ?_⟩
      intro equation present
      exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
        previous (.opaque typed installed)
    | «example» typed =>
      exact ⟨table, .decl history (.example typed), fun equation present =>
        (covered equation present).declaration previous (.example typed)⟩
    | «def» typed installed =>
      refine ⟨table, .decl history (.def typed installed), ?_⟩
      intro equation present
      rcases present with rfl | present
      · exact .inl ⟨_, definitionRegistry_decl_new (.def typed installed)
          (List.mem_singleton_self _), rfl⟩
      · exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
          previous (.def typed installed)
    | mutualDef headers installed bodies =>
      refine ⟨table, .decl history (.mutualDef headers installed bodies), ?_⟩
      intro equation present
      rw [addDefEqs_as_rules, defeqs_addRules] at present
      rcases present with member | present
      · obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
        exact .inl ⟨value, definitionRegistry_decl_new
          (.mutualDef headers installed bodies) valueMember, rfl⟩
      · exact (covered equation (by
          rwa [VEnv.addConstVals_defeqs (addConsts_as_values ▸ installed)] at present)).declaration
          previous (.mutualDef headers installed bodies)
    | quot ready installed =>
      refine ⟨table, .decl history (.quot ready installed), ?_⟩
      intro equation present
      have declaration := VDecl.WF.quot ready installed
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := installed
      rcases present with rfl | present
      · exact .inr (.inl ⟨List.mem_cons_self, rfl⟩)
      · exact (covered equation (by
          rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at present)).declaration previous declaration
    | induct original installed =>
      rename_i source
      cases installed with
      | intro _ compiled blockWF installed =>
        obtain ⟨base, expanded, signature, generated, auxiliaries, below, compilation, specializations⟩ :=
          compiled.compiled.compilationOrigin
        let key : Name := (source.types.head?.map (·.name)).getD `nativeRegistry
        refine ⟨installEntries table (compilationEntries key _ signature auxiliaries generated),
          .native history original compiled blockWF installed compilation specializations below, ?_⟩
        intro equation present
        have retain := NativeRegistryEquationCovered.install history compilation installed
          (key := key) (equation := equation)
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at installed
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := installed
        rw [defeqs_addRules] at present
        rcases present with member | present
        · obtain ⟨data, entry, index, owner, equationEq⟩ := compilation.nativeEntries_equation member key
          exact .inr (.inr ⟨data, compilation.nativeEntries_lookup entry, index, owner, equationEq⟩)
        · exact retain (covered equation (by
            rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at present))
  | inductEliminators baseHistory _ below certified keyEq constants fresh compat _ ih =>
    obtain ⟨table, history, covered⟩ := ih
    exact ⟨table, .eliminators history baseHistory below certified keyEq constants fresh compat,
      fun equation present => covered equation present⟩
  | inductProjections baseHistory _ sourceNames typeHeadersWF constructorUvars constructorsWF
      parameters shape types constructors projections addTypes addConstructors _ ih =>
    obtain ⟨table, history, covered⟩ := ih
    exact ⟨table, .projections history baseHistory sourceNames typeHeadersWF constructorUvars
      constructorsWF parameters shape types constructors projections addTypes addConstructors,
      fun equation present => covered equation
        (by simpa only [VEnv.addProjections_defeqs] using present)⟩

/-- Lookup soundness and original-stage provenance are consequences of the
same concrete table construction, together with full installed-rule coverage. -/
theorem WF.nativeRegistry (formed : env.WF) :
    ∃ declarations table, NativeRegistryHistory env declarations table ∧
      (∀ name data, table name = some data →
        NativeRecursorRegistered env data ∧ data.name = name ∧
        Nonempty (NativeDeclarationOrigin env declarations data)) ∧
      (∀ equation, env.defeqs equation → NativeRegistryEquationCovered declarations table equation) := by
  obtain ⟨declarations, history⟩ := formed
  obtain ⟨table, registered, covered⟩ := history.nativeRegistry
  exact ⟨declarations, table, registered, fun _ _ lookup =>
    ⟨(registered.registered lookup).1, registered.origin lookup⟩, covered⟩

end Lean4Lean.VEnv
