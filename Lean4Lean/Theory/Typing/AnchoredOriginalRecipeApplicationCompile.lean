import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableBodyCompile
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaGrades

/-! Assemble ordinary destination application code from an actual function
query and the computed argument demand. Grade changes retain the argument's
exact local footprint; no operand frame or frozen substitution is stored. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The function input will be the shared closed canonical leaf. This
assembler itself needs no new grammar: it exposes every argument demand using
ordinary application syntax, even when demand replay raises the grade. -/
theorem RecipeVariableDemand.compileApplication
    (demand : RecipeVariableDemand env U registry target outerInput key.input)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (fn : RichObs sourceEnv env U registry target function locals σ
      (Profile.fn key output) fnFootprint)
    (fnAvailable : fnFootprint.Available available)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available demand.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output)
        (fnFootprint ++ arg.footprint),
      (fnFootprint ++ arg.footprint).Available available ∧
      ∀ policy, certificate.headDepth policy ≤ max (fn.headDepth policy) (arg.observation.headDepth policy) := by
  let replay := demand.replay henv hscoped formed arg
  let highKey := raiseKey replay.rank replay.bound key
  let highOutput := raiseAtom replay.rank replay.bound output
  let highFn : RichObs sourceEnv env U registry target function locals σ
      (Profile.fn highKey highOutput) fnFootprint := by
    have raised := fn.raise (Nat.succ_le_succ replay.bound)
    change RichObs sourceEnv env U registry target function locals σ
      (raiseProfile (replay.rank + 1) (Nat.succ_le_succ replay.bound)
        (.singleton (.fn key output))) fnFootprint at raised
    rw [raiseProfile_singleton] at raised
    exact .view raised (functionGradeView replay.bound key output)
  have highAdmission := Admitted.raise henv replay.bound admitted
  let highCode : RichCert sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ relevant
      (raiseProfile replay.rank replay.bound (.singleton output)) (fnFootprint ++ arg.footprint) := by
    rw [raiseProfile_singleton]
    exact .observe (.app hu hv highFn replay.observation replay.adapter highAdmission)
      (by simpa only [raiseProfile_singleton] using Profile.HasType.raise_sort replay.bound sorted)
  refine ⟨highCode.lowerRaised replay.bound, ?_, ?_⟩
  · intro index need member
    rcases List.mem_append.mp member with member | member
    · exact fnAvailable index need member
    · exact arg.resources index need member
  · intro policy
    rw [RichCert.headDepth_lowerRaised]
    dsimp only [highCode]
    rw [RichCert.headDepth_mpr policy rfl rfl (raiseProfile_singleton replay.bound output).symm rfl]
    simp only [RichCert.headDepth, RichObs.headDepth]
    have fnDepth : highFn.headDepth policy = fn.headDepth policy := by
      dsimp only [highFn, id]
      rw [RichObs.headDepth]
      rw [RichObs.headDepth_mp policy rfl rfl
        (raiseProfile_singleton (Nat.succ_le_succ replay.bound) (.fn key output)) rfl]
      exact fn.headDepth_raise policy (Nat.succ_le_succ replay.bound)
    rw [fnDepth]
    have argDepth : replay.observation.headDepth policy = arg.observation.headDepth policy := by
      simp only [replay, RecipeVariableDemand.replay, RichGradedResult.raiseTo]
      exact arg.observation.headDepth_raise policy _
    rw [argDepth]
    exact Nat.le_refl _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
