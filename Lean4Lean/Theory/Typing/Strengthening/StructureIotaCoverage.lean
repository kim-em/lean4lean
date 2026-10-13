import Lean4Lean.Theory.Typing.Strengthening.StructureUnfoldingSupply

/-! # Every typed registered structure-iota occurrence enters the head model

At indexed constructors, tuple tests suffice. At unindexed constructors, either
the recursor universe supports the closed projection equation or its actual
constructor instance is eta-inadmissible and permits a universe-tagged tuple
test. Typed family injectivity aligns the two universe instances. No projection
admissibility certificate is requested from the caller.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions CheckFromTyping)
open ConstructorObservation (EtaCompute EtaAdmissible NotEtaCtor NotEtaInstance TestableMajor)
variable [Params]

/-- The closed-equation/tuple-test split covers every typed iota match of a
registered structure recursor, at all source universes and index counts. Ordinary
rule enabling remains expressed by its uniform check certificate. -/
theorem iota_typed
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered env data) (hi : env.projections (family data) info)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (hm : (pattern data info).Matches source levels captures)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ source) :
    EtaCompute (definitions D) source (r.1.apply levels captures) := by
  classical
  by_cases hn : info.nindices = 0
  · cases hm with
    | app hrec hctor =>
      rename_i ctorLevels recCaptures ctorCaptures
      obtain ⟨args, ha, rfl, _⟩ := Pattern.matches_varN_const_inv hrec
      obtain ⟨ctorArgs, hca, rfl, _⟩ := Pattern.matches_varN_const_inv hctor
      obtain ⟨T, ht⟩ := ht
      obtain ⟨hw, hl, ps, hmajor⟩ := hr.major_type henv hΓ ht ha
      by_cases hz : Admissible env univs data info levels
      · exact .compute (iota_compute hr hw hl hi hn hz hp hc (.app hrec hctor))
      · have htest : NotEtaInstance info.ctorName ctorLevels := by
          apply NotEtaInstance.of_inadmissible hi
          intro hadm
          obtain ⟨hwc, hlc, hwf, he⟩ := StructureReplay.constructor_levels henv hΓ hi hca hmajor
          exact hz (hadm.level_congr hi hwc hwf hlc he)
        exact .iota hp hc (.app hrec hctor) (TestableMajor.of_instance htest)
  · exact .iota hp hc hm (NotEtaCtor.of_indexed hi hn).testableMajor

omit [Params] in
/-- Concrete enabled rules supply the uniform check; typed registered structure
sources supply the remaining split automatically. Mixed paths in the captures
are retained after the root computation. -/
theorem concrete_iota_typed {env : VEnv} (henv : env.WF)
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures captures' : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered env data) (hi : env.projections (family data) info)
    (hp : ConcretePattern env _ r)
    (hc : r.2.OK (env.IsDefEqU U Γ) levels captures)
    (hm : (pattern data info).Matches source levels captures)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ source)
    (H : ∀ p, @EtaCompute (henv.params U) (@definitions (henv.params U) D)
      (captures p) (captures' p)) :
    @EtaCompute (henv.params U) (@definitions (henv.params U) D)
      source (r.1.apply levels captures') := by
  letI := henv.params U
  exact (iota_typed hr hi hp (PureObservation.ConcretePattern.checkFromTyping henv hp hc) hm hΓ ht).trans
    (EtaCompute.apply_pat _ H)

end Lean4Lean.VEnv.Strengthening.ClosedStructure
