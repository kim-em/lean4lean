import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaHistory

/-! # Validity of the registered ι rules

A registered ι rule of a well-formed environment is valid in the model (`Model.PatValid`, the
`pat` case of `Model.sound`). Along the declaration history (`Model/EnvValid.lean`) the rule is
an ι rule registered by an inductive step (`addInduct_pats_origin'`), read off a generated
equation of the step's compiled block (`VInductDecl.WF.rule_block`):

* for an ordinary compilation (no container specializations) by `Model.PatValid.ordinary`
  (`Model/IotaHistory.lean`);
* for a nested compilation by `Model.PatValid.nested`, stated here.

Open: `PatValid.nested` is an open proof (`OPEN_PROOFS.md`). Its statement is that of `PatValid.ordinary` with the
compilation's container specializations `aux ≠ []` installed below the block
(`ContainersInstalled`). The generic part of the proof applies unchanged (`PatValid.of_rule`,
`PatValid.of_rule_empty`, `iotaArgRel_of`); what a nested block must supply is the static data
of a restored equation (`IotaStatic` of the restored recursor's type, the restored lead and the
restored constructor of an auxiliary family, which is a container constructor declared earlier),
the projection facts and the semantic sort of the major's family when it is a container
(`ProjMajor`, `FamSort`), and the relation of the container constructor's installed type to the
restored template's field domains (the hypotheses `hNS`, `hDP`, `hDF` of `iotaArgRel_of`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- **Validity of the ι rules of a nested block** (open). -/
theorem PatValid.nested {envF env0 env' : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (hpre : envF.WFPrefix env0) (h0 : env0.WF) (hdecl : decl.WF env0)
    (hadd : env0.addInduct decl = some env') (hle : env' ≤ envF)
    (V0 : EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → ProjValid envF S info)
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
      (∃ ci, env'.constants p.headConst = some ci) → env'.pats p r)
    (hdefs : ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      (∃ ci, env'.constants n = some ci) → env'.defeqs df)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (hc : ru.rhs.Closed)
    {block : VInductBlock} {base : VEnv} {expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {aux : List InductiveSignature.ContainerSpecialization}
    (haux : aux ≠ [])
    (hcomp : CompiledInductive env0 decl block)
    (hrecsOf : decl.RecsOf block) (hbwf : block.WF env0) (hbase : base ≤ env0)
    (C : InductiveSignature.CompilationData base decl expanded s g aux block)
    (hcont : ContainersInstalled base aux)
    {df : VDefEq} (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df) :
    PatValid envF
      (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
        rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  -- Open proof, see `OPEN_PROOFS.md`.
  sorry

end Model
end VEnv
end Lean4Lean
