import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.RestorationNames
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ConstructorMajor

/-! # The constructor of a rule of a compiled block

What the rigidity of pattern constructors (`VEnv.WF.patCtor_rigid`,
`Theory/Typing/HeadInjectivity/Model/WFFacts.lean`) needs from the compilation of a block: the
constructor of every rule of every recursor read off a compiled block (`VInductDecl.RecsOf`)
is a constructor of the block itself or of a container whose own ι rules are registered in the
environment the block was compiled in (`ContainersInstalled`: the container was installed by
`VEnv.addInduct`, whose rule stage registers one ι rule per constructor of the container's
recursors). The second alternative is `VEnv.IsPatCtor env ru.ctor`
(`Theory/Typing/HeadInjectivity/Rules/ConstructorMajor.lean`).

WAVE 3 COMPAT, all named stubs (owner Restoration-B): the source branch's
`Instance.restored_equation_major` (`RecursorEquationHeads.lean`),
`CompilationData.constructor_name_cases` and `CompiledInductive.equation_major_cases`
(`ConstructorRigidity.lean`), with the stored-equation alternative replaced by a registered
pattern. -/

namespace Lean4Lean

namespace InductiveSignature

/-- The restored equation of constructor `index` has the restored constructor as the head of
its major argument. -/
theorem Instance.restored_equation_major {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {equation : VDefEq}
    (hrestore : (compilationRestoration source auxiliaries).equation
      (g.equation index) = some equation) :
    equation.HasConstructorMajor
      ((compilationRestoration source auxiliaries).headName s.constructors[index].name) := by
  -- WAVE 3 STUB (Restoration-B): `Instance.restored_equation_major` of the source branch's
  -- `Theory/Inductive/RecursorEquationHeads.lean` (`restored_common_telescope`).
  have := H; have := hrestore; sorry

/-- The restored constructor name of constructor `index` is a constructor of the source
declaration or of the container family of one of the auxiliaries. -/
theorem CompilationData.constructor_name_cases {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) :
    (∃ ctor ∈ source.constructorConstants,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name =
        ctor.name) ∨
    (∃ a ∈ auxiliaries, ∃ ctor ∈ a.source.ctors,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name =
        ctor.name) := by
  -- WAVE 3 STUB (Restoration-B): `CompilationData.constructor_name_cases` of the source
  -- branch's `RecursorEquationHeads.lean` (from `correspondence` and `recursorNamesFresh`).
  have := H; sorry

end InductiveSignature

/-- Every constructor of a container of an installed specialization list is the constructor of
a registered ι rule: the container's recursor has a rule on it, and the container was installed
by `VEnv.addInduct` below `env`. -/
theorem ContainersInstalled.constructor_isPatCtor {env : VEnv}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    (H : ContainersInstalled env auxiliaries) {a : InductiveSignature.ContainerSpecialization}
    (ha : a ∈ auxiliaries) {ctor : VConstVal} (hc : ctor ∈ a.source.ctors) :
    VEnv.IsPatCtor env ctor.name := by
  -- WAVE 3 STUB (Restoration-B): the container's compilation has one equation per
  -- constructor (`CompilationData.equations`, `Models`), `RecsOf.rules_total` turns it into a
  -- `VRecRule` on `ctor.name` (`VRecRule.OfEquation`), and the rule stage of `addInduct`
  -- registers it (`VEnv.addRules`), below `env`.
  have := H; have := ha; have := hc; sorry

/-- **The constructor of every rule of a compiled block** is a constructor of the block or the
constructor of a ι rule already registered in the compilation environment (the container's). -/
theorem CompiledInductive.rule_ctor_cases {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block)
    (hrecs : source.RecsOf block) {r : VRecursor} {ru : VRecRule} (hr : r ∈ source.recs)
    (hru : ru ∈ r.rules) :
    (∃ ctor ∈ source.constructorConstants, ru.ctor = ctor.name) ∨ VEnv.IsPatCtor env ru.ctor := by
  -- WAVE 3 STUB (Restoration-B): `CompiledInductive.equation_major_cases` of the source
  -- branch's `ConstructorRigidity.lean`, through `RecsOf.rules` (the rule is `OfEquation` of a
  -- block equation, whose major head is `ru.ctor`), `Instance.restored_equation_major`,
  -- `CompilationData.constructor_name_cases` and `ContainersInstalled.constructor_isPatCtor`;
  -- the `replay` case by `VEnv.LE.pats`.
  have := H; have := hrecs; have := hr; have := hru; sorry

end Lean4Lean
