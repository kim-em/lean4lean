import Lean4Lean.Theory.Typing.Strengthening.EtaConstructorExposure

/-! # Structure iota after finite eta expansion of its major

An existing constructor fires the original pattern before eta. A constructor
created by eta instead enables the closed projection unfolding, at the actual
recursor universe instance. In either case the result retains only eta
expansions of captures; arbitrary compatible interleavings remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A typed structure major transports its closed eta certificate between any
two family typings. Uniqueness aligns their universes, independently of the
parameter expressions. -/
theorem structure_eta_admissible_at (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hm' : env.HasType univs Γ major (mkApps (.const family levels') params'))
    (hz : ConstructorObservation.EtaAdmissible info levels) :
    ConstructorObservation.EtaAdmissible info levels' := by
  have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).2 hz
  obtain ⟨hw, hl, _, _⟩ := StructureReplay.constructor_levels henv hΓ hi
    (by simp [hp]) hc
  obtain ⟨_, hfamily⟩ := hm.isType henv hΓ
  have HE := ((hm.uniqU henv hΓ hm').structApp_inv henv hΓ hi hfamily).1
  obtain ⟨_, hfamily'⟩ := hm'.isType henv hΓ
  obtain ⟨_, _, hw', _⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hfamily'⟩).const_inv henv hΓ
  exact hz.level_congr hi hw hw' hl HE

end Lean4Lean.VEnv.Strengthening.PureObservation

namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params]

set_option backward.isDefEq.respectTransparency false in
/-- A registered structure-recursion root exchanges with arbitrary finite eta
expansion of its major and supplied arguments. Its source typing and the actual
pattern check supply all universe and admissibility data for an eta-created
constructor. The original pattern fires directly for an existing constructor. -/
theorem eta_iota_compute
    {r : (pattern data info).RHS × (pattern data info).Check}
    {recCaptures : ((Pattern.const data.name).varN data.majorOffset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : RecursorRegistered env data) (hi : env.projections (family data) info)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset)
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (HM : TypedEtaExpansion Γ major (mkApps (.const info.ctorName ctorLevels) ctorArgs))
    (ht : env.HasType univs Γ (.app (mkApps (.const data.name levels) args) major) T)
    (hrec : ((Pattern.const data.name).varN data.majorOffset).Matches
      (mkApps (.const data.name levels) args') levels recCaptures)
    (hlen : ctorArgs.length = info.nparams + info.numFields)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (mkApps (.const info.ctorName ctorLevels) ctorArgs) ctorLevels ctorCaptures) :
    ∃ out, PrefixCompute (definitions D) Γ (.app (mkApps (.const data.name levels) args) major) out ∧
      TypedEtaExpansion Γ out (Pattern.RHS.apply (p := pattern data info)
        levels (Sum.elim recCaptures ctorCaptures) r.1) := by
  obtain ⟨hw, hl, ps, hm⟩ := hr.major_type henv hΓ ht ha
  rcases HM.constructor_exposure hΓ hm with ⟨ctorArgs0, rfl, HC⟩ | HE
  · have ha' : args'.length = data.majorOffset := HA.length_eq.symm.trans ha
    have hc0 : ctorArgs0.length = info.nparams + info.numFields := HC.length_eq.trans hlen
    have hrecEq := (Pattern.matches_determ hrec (spineCaptures_match args' ha' levels)).2
    have hctorEq := (Pattern.matches_determ hctor (spineCaptures_match ctorArgs hlen ctorLevels)).2
    rw [hrecEq, hctorEq]
    refine ⟨_, .base (.pattern hp (.app (spineCaptures_match args ha levels)
      (spineCaptures_match ctorArgs0 hc0 ctorLevels)) hc), ?_⟩
    apply TypedEtaExpansion.apply_pat
    intro p
    cases p with
    | inl p => exact TypedEtaExpansion.spineCaptures HA ha ha' p
    | inr p => exact TypedEtaExpansion.spineCaptures HC hc0 hlen p
  · obtain ⟨family', info', ps', hi', hname, hparams, hx, hm', hz, _, HF⟩ := HE
    obtain ⟨hfamily, hinfo⟩ := henv.ordered.projectionConstructor_family hi' hi hname
    cases hinfo
    cases hfamily
    have hz' := structure_eta_admissible_at hΓ hi' hparams hx hm' hm hz
    have htake : (ctorArgs.take info.nparams).length = info.nparams := by simp [hlen]
    have hctor' : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
        (mkApps (.const info.ctorName ctorLevels)
          (ctorArgs.take info.nparams ++ ctorArgs.drop info.nparams)) ctorLevels ctorCaptures := by
      simpa only [List.take_append_drop] using hctor
    obtain ⟨out, RC, RE⟩ := iota_eta_exchange hr hw hl hi' hx hz' hp hc ha HA HF hrec htake hctor'
    exact ⟨out, .base (.base (.base RC)), RE⟩

end Lean4Lean.VEnv.Strengthening.ClosedStructure
