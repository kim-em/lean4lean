import Lean4Lean.Theory.Typing.Strengthening.RegisteredStructureEquations

/-! # Joining a closed structure unfolding with its ordinary iota rule

Once the recursor head has unfolded, beta and constructor projections alone
reach the direct iota right-hand side. This closes the saturated root overlap
without eta expansion, normal comparison, confluence or a strengthening front.
It does not cover prefix overlaps or arbitrary compatible computational peaks.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params] {D : Definitions}

set_option backward.isDefEq.respectTransparency false in
/-- Applying the already unfolded projection program to a matching constructor
spine joins the direct iota result by beta and projections. The original
constant no longer occurs at the head of this outgoing path. -/
theorem unfolded_iota_join
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered env data) (hi : env.projections (family data) info)
    (hp : Pat _ r) (hm : (pattern data info).Matches source levels captures) :
    ProjectionCompute D
      (mkApps (value data info levels r.1 (domainsOf data levels)) source.getAppArgs)
      (r.1.apply levels captures) := by
  cases hm with
  | app hrec hctor =>
    rename_i ctorLevels recCaptures ctorCaptures
    obtain ⟨args, ha, rfl, _⟩ := Pattern.matches_varN_const_inv hrec
    obtain ⟨ctorArgs, hca, rfl, _⟩ := Pattern.matches_varN_const_inv hctor
    have hrecEq := (Pattern.matches_determ hrec (spineCaptures_match args ha levels)).2
    rw [hrecEq]
    let dummyArgs := List.replicate info.nparams (VExpr.sort .zero) ++ ctorArgs.drop info.nparams
    have hdlen : dummyArgs.length = info.nparams + info.numFields := by simp [dummyArgs, hca]
    have hdummy := spineCaptures_match (c := info.ctorName) dummyArgs hdlen []
    have hactual : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
        (mkApps (.const info.ctorName ctorLevels) (ctorArgs.take info.nparams ++ ctorArgs.drop info.nparams))
        ctorLevels ctorCaptures := by
      simpa only [List.take_append_drop] using hctor
    have he := (Params.pat_iota_params hp hi rfl hactual hdummy
      (by simp [hca]) (by simp)).1 levels (spineCaptures args ha)
    rw [he]
    obtain ⟨type, htype⟩ := hr.recursorType_exists
    have hdom := (type_shape (levels := levels) htype).2
    have HB := BetaRed.mkApps_wrapLams (domainsOf data levels) (body data info levels r.1)
      (args ++ [mkApps (.const info.ctorName ctorLevels) ctorArgs]) (by simp [ha, hdom])
    have R : Compute D
        (mkApps (value data info levels r.1 (domainsOf data levels))
          (args ++ [mkApps (.const info.ctorName ctorLevels) ctorArgs]))
        (suppliedBody data info levels r.1 args ha
          (mkApps (.const info.ctorName ctorLevels) ctorArgs)) := by
      have hlen : (domainsOf data levels).length =
          (args ++ [mkApps (.const info.ctorName ctorLevels) ctorArgs]).length := by simp [hdom, ha]
      simpa only [value, hlen, List.take_length, List.drop_length, mkApps_nil,
        body_instOuter ha] using (Compute.of_beta (D := D) HB)
    simp only [getAppArgs, getAppArgs_mkApps, List.nil_append]
    apply ProjectionCompute.trans (.base R)
    unfold suppliedBody
    apply projection_apply_pat
    intro p
    cases p with
    | inl => exact .base .refl
    | inr p =>
      exact projection_spineCaptures (projected_fields_compute hi hca) (by simp) hdlen p

/-- The chosen closed program and any registered RHS at its same pattern have
an exact computational join. Pattern uniqueness eliminates certificate choice. -/
theorem unfolded_iota_join_other
    {r r' : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered env data) (hi : env.projections (family data) info)
    (hp : Pat _ r) (hp' : Pat _ r')
    (hm : (pattern data info).Matches source levels captures) :
    ProjectionCompute D
      (mkApps (value data info levels r.1 (domainsOf data levels)) source.getAppArgs)
      (r'.1.apply levels captures) := by
  have he := (pat_uniq hp hp' .refl (Pattern.inter_self _)).2.2
  cases he
  exact unfolded_iota_join hr hi hp hm

end Lean4Lean.VEnv.Strengthening.ClosedStructure
