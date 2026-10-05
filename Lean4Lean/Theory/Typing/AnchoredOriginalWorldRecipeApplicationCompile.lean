import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeApplicationCompile
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private raiseQueryAnnotation from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Joint syntax/annotation assembly. Both actual child annotations survive
on the SAME destination application; only the argument program is grade-raised. -/
theorem RecipeVariableDemand.compileApplicationAnnotated
    {strata : EquationStratification env}
    (demand : RecipeVariableDemand env U registry target outerInput key.input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (fn : RichObs sourceEnv env U registry target function locals σ (Profile.fn key output) fnFootprint)
    (fnAvailable : fnFootprint.Available available)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available demand.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant))
    (fnAnnotation : WorldObsProvenance strata fn)
    (argAnnotation : WorldObsProvenance strata arg.observation) :
    ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output)
        (fnFootprint ++ arg.footprint),
    ∃ annotation : WorldCertProvenance strata certificate,
      (fnFootprint ++ arg.footprint).Available available ∧
      annotation.worlds = fnAnnotation.worlds ++ argAnnotation.worlds ∧
      ∀ policy, certificate.headDepth policy ≤ max (fn.headDepth policy) (arg.observation.headDepth policy) := by
  let replay := demand.replay henv hscoped formed arg
  obtain ⟨fnAnn, fnWorlds⟩ := raiseQueryAnnotation fn fnAnnotation (Nat.succ_le_succ replay.bound)
  have lifted : ∃ lifted : RichObs sourceEnv env U registry target function locals σ
      (.singleton (raiseAtom (replay.rank + 1) (Nat.succ_le_succ replay.bound) (.fn key output))) fnFootprint,
      ∃ annotation : WorldObsProvenance strata lifted,
        annotation.worlds = fnAnnotation.worlds ∧
        ∀ policy, lifted.headDepth policy = fn.headDepth policy := by
    have chosen : ∃ lifted : RichObs sourceEnv env U registry target function locals σ
        (raiseProfile (replay.rank + 1) (Nat.succ_le_succ replay.bound) (Profile.fn key output)) fnFootprint,
        ∃ annotation : WorldObsProvenance strata lifted,
          annotation.worlds = fnAnnotation.worlds ∧
          ∀ policy, lifted.headDepth policy = fn.headDepth policy :=
      ⟨fn.raise (Nat.succ_le_succ replay.bound), fnAnn, fnWorlds,
        fun policy => fn.headDepth_raise policy (Nat.succ_le_succ replay.bound)⟩
    change (∃ lifted : RichObs sourceEnv env U registry target function locals σ
        (raiseProfile (replay.rank + 1) (Nat.succ_le_succ replay.bound) (.singleton (.fn key output))) fnFootprint,
        ∃ annotation : WorldObsProvenance strata lifted,
          annotation.worlds = fnAnnotation.worlds ∧
          ∀ policy, lifted.headDepth policy = fn.headDepth policy) at chosen
    rw [raiseProfile_singleton] at chosen
    exact chosen
  obtain ⟨lifted, liftedAnn, liftedWorlds, liftedDepth⟩ := lifted
  let highFn := RichObs.view lifted (functionGradeView replay.bound key output)
  let highFnAnn := WorldObsProvenance.view liftedAnn (functionGradeView replay.bound key output)
  obtain ⟨argAnn, argWorlds⟩ := raiseQueryAnnotation arg.observation argAnnotation
    (Nat.le_max_left arg.rank demand.rank)
  let replayAnn : WorldObsProvenance strata replay.observation := argAnn
  let high := RichObs.app (domain := domain) (body := body) (result := result)
    hu hv highFn replay.observation replay.adapter (Admitted.raise henv replay.bound admitted)
  let highAnn : WorldObsProvenance strata high :=
    .app hu hv highFnAnn replayAnn replay.adapter (Admitted.raise henv replay.bound admitted)
  let profileEq := (raiseProfile_singleton replay.bound output).symm
  let highCast := (congrArg (fun p => RichObs sourceEnv env U registry target
    (.app hu hv domain body function argument result) locals σ p (fnFootprint ++ arg.footprint)) profileEq).mp high
  let highCastAnn : WorldObsProvenance strata highCast := .castProfile profileEq highAnn
  let certificate := RichCert.observe highCast.lowerRaised sorted
  let annotation : WorldCertProvenance strata certificate := .observe (.lowerRaised highCastAnn) sorted
  have worlds : annotation.worlds = fnAnnotation.worlds ++ argAnnotation.worlds := by
    change liftedAnn.worlds ++ argAnn.worlds = _
    rw [liftedWorlds, argWorlds]
  have depth : ∀ policy, certificate.headDepth policy ≤ max (fn.headDepth policy) (arg.observation.headDepth policy) := by
    intro policy
    simp only [certificate, RichCert.headDepth, RichObs.headDepth_lowerRaised]
    dsimp only [highCast]
    rw [RichObs.headDepth_mp policy rfl rfl profileEq rfl]
    simp only [high, highFn, RichObs.headDepth, liftedDepth]
    have argDepth : replay.observation.headDepth policy = arg.observation.headDepth policy := by
      simp only [replay, RecipeVariableDemand.replay, RichGradedResult.raiseTo]
      exact arg.observation.headDepth_raise policy _
    rw [argDepth]
    exact Nat.le_refl _
  refine ⟨certificate, annotation, ?_, worlds, depth⟩
  intro index need member
  rcases List.mem_append.mp member with member | member
  · exact fnAvailable index need member
  · exact arg.resources index need member

theorem RecipeVariableDemand.compileApplicationControlled
    {strata : EquationStratification env}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (demand : RecipeVariableDemand env U registry target outerInput key.input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (fn : RichObs sourceEnv env U registry target function locals σ (Profile.fn key output) fnFootprint)
    (fnAvailable : fnFootprint.Available available)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available demand.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant))
    (controls : OriginalWorldControls strata controlSource)
    (fnReady : ControlledStoredQuery controls frontier (.observation fn))
    (argReady : ControlledStoredQuery controls frontier (.observation arg.observation)) :
    ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output)
        (fnFootprint ++ arg.footprint),
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      (fnFootprint ++ arg.footprint).Available available ∧
      ready.annotation.worlds = fnReady.annotation.worlds ++ argReady.annotation.worlds ∧
      ∀ policy, certificate.headDepth policy ≤ max (fn.headDepth policy) (arg.observation.headDepth policy) := by
  obtain ⟨certificate, annotation, resources, worlds, depth⟩ :=
    demand.compileApplicationAnnotated henv hscoped formed hu hv fn fnAvailable arg admitted sorted
      fnReady.annotation argReady.annotation
  refine ⟨certificate, ⟨annotation, ?_, ?_⟩, resources, worlds, depth⟩
  · intro control active
    exact Nat.le_trans (depth _) (Nat.max_le.mpr ⟨fnReady.within control active, argReady.within control active⟩)
  · intro world member
    change world ∈ WorldCertProvenance.worlds annotation at member
    rw [worlds] at member
    rcases List.mem_append.mp member with member | member
    · exact fnReady.sponsored world member
    · exact argReady.sponsored world member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
