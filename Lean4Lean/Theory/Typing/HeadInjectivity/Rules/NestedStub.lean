import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Compiled

/-! # Provenance of the rules of a nested block (wave 3)

The rules of a block compiled with container specializations (`auxiliaries ≠ []`) are the
*restored* generated equations (`Instance.restoredEquations`, `compilationRestoration`): the
generated equations of the expanded declaration with the auxiliary families and constructors
replaced by the containers' and the auxiliary recursors renamed. What the model needs of them
is their typing in the recursor stage of the block (`VDefEq.WF`): the ordinary case reads this
off the recursor types (`VInductDecl.WF.recs_wf`) and the generator's syntax
(`Instance.equation_rhs_containsAnyConst`), which the restoration does not preserve literally.

`VInductDecl.WF.nestedRules_wf` is the single statement wave 3 must provide for nested blocks
(the restoration lemmas live with the nested lowering, `Verify/Inductive/Nested/**`). -/

namespace Lean4Lean

/-- **WAVE 3 STUB.** The restored equations of a nested block are well-formed definitional
equations in the recursor stage of its installation (`VInductBlock.WF`'s `rules` clause,
transported from the compilation base to the installation environment). Wave 3 provides this
from the restoration of the expanded block's typing (the verified nested lowering records
`block.WF base`, see `VEnv.InstalledBelow` and `RuleTranslations.blockWF`). -/
theorem VInductDecl.WF.nestedRules_wf {env : VEnv} {decl : VInductDecl} (hdecl : decl.WF env)
    {block : VInductBlock} {base : VEnv} {expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {aux : List InductiveSignature.ContainerSpecialization}
    (hcomp : CompiledInductive env decl block) (hrecsOf : decl.RecsOf block) (hbase : base ≤ env)
    (C : InductiveSignature.CompilationData base decl expanded s g aux block)
    (hcont : ContainersInstalled base aux) (haux : aux ≠ [])
    {envR : VEnv} (hR : decl.addTypesCtorsProjsRecs env = some envR) :
    ∀ df ∈ block.rules, df.WF envR := by
  -- WAVE 3 STUB (model pat stubs): restored-equation typing of a nested block.
  have := hdecl; have := hcomp; have := hrecsOf; have := hbase; have := C; have := hcont
  have := haux; have := hR
  sorry

end Lean4Lean
