import Lean4Lean.Theory.Typing.Strengthening.StructureIotaCoverage

/-! # Ordinary iota coverage from concrete pattern registration

The actual pattern table identifies its recursor registration. A typed major
then identifies any projection registration of its constructor with the owner
family, recovering the exact field count needed by closed structure replay.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions)

/-- A projection constructor typed at any rigid family identifies that family
and supplies its complete parameter/field telescope. -/
theorem projection_major_family {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hi : env.projections family info)
    (hF : env.Rigid F)
    (H : env.HasType U Γ (mkApps (.const info.ctorName levels) args)
      (mkApps (.const F ls) ps)) :
    family = F ∧ args.length = info.nparams + info.numFields := by
  have hlookup := henv.ordered.projectionConstructor hi
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, H⟩).const_inv henv hΓ
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hc := HasType.const (Γ := Γ) hlookup hw hl
  obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, hhead, harity⟩ := hraw.forallArity
  have hr : result = mkApps (.const family (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hname, ← hhead]
    exact (mkApps_getAppFnArgs_eq result).symm
  rw [← hctorType, hshape, hr, instL_wrapForalls, instL_mkApps] at hc
  simp only [VExpr.instL, VLevel.params_map_inst levels (hl.trans huvars.symm)] at hc
  obtain ⟨ha, hf⟩ := HasType.mkApps_rigid_family henv hΓ (henv.projectionRigid hi) hF hc H
  refine ⟨hf, ?_⟩
  change args.length = info.nparams + (info.ctorType.forallArity - info.nparams)
  rw [← hctorType, harity]
  simp only [List.length_map] at ha
  omega

namespace ClosedStructure
open Params ConstructorObservation

/-- All enabled concrete iota patterns enter the mixed head model from source
typing alone. Recursor registration, structure family, index count, telescope
arity, and projection admissibility are derived internally. -/
theorem concrete_iota_coverage {env : VEnv} (henv : env.WF)
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    {captures : (SimplePattern.iota recursor major ctor fields).toPattern.Path → VExpr}
    (hp : ConcretePattern env _ r)
    (hc : r.2.OK (env.IsDefEqU U Γ) levels captures)
    (hm : (SimplePattern.iota recursor major ctor fields).toPattern.Matches source levels captures)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ source) :
    @EtaCompute (henv.params U) (@definitions (henv.params U) D)
      source (r.1.apply levels captures) := by
  letI := henv.params U
  classical
  have hcheck : PureObservation.CheckFromTyping env U _ r levels := PureObservation.ConcretePattern.checkFromTyping henv hp hc
  by_cases hn : NotProjectionCtor ctor
  · exact .iota hp hcheck hm hn.notEtaCtor.testableMajor
  · simp only [NotProjectionCtor, ne_eq, Classical.not_forall, Classical.not_not] at hn
    obtain ⟨familyName, info, hi, rfl⟩ := hn
    rcases hp.recursor henv with ⟨data, hr, rfl, rfl, _, ⟨index, howner⟩, _⟩ | ⟨hq, _, _, he, _⟩
    · cases hm with
      | app hrec hctor =>
        obtain ⟨args, ha, rfl, _⟩ := Pattern.matches_varN_const_inv hrec
        obtain ⟨ctorArgs, hca, rfl, _⟩ := Pattern.matches_varN_const_inv hctor
        obtain ⟨T, ht⟩ := ht
        obtain ⟨_, _, ps, hmajor⟩ := hr.major_type henv hΓ ht ha
        obtain ⟨hfamily, hfields⟩ := projection_major_family henv hΓ hi
          (hr.family_head_rigid henv index howner).2 hmajor
        change familyName = family data at hfamily
        subst familyName
        have hf : fields = info.nparams + info.numFields := hca.symm.trans hfields
        subst hf
        exact iota_typed hr hi hp hcheck (.app hrec hctor) hΓ ⟨_, ht⟩
    · exact (QuotRegistered.not_struct henv hq hi he.symm).elim

end ClosedStructure
end Lean4Lean.VEnv.Strengthening
