import Lean4Lean.Theory.Typing.Strengthening.StructureReconstruction
import Lean4Lean.Theory.Typing.Strengthening.PatternComputation

/-! # Typed replay of structure iota through projected fields

Constructor reconstruction allows a recursor to compute through the projections
of its major. The final RHS does not depend on the constructor's parameters or
levels, so its raw matching witness can use dummy ones. Typing the original major
at the registered family and satisfying the projection guards remain explicit.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (CheckFromTyping)
variable [Params]

/-- Replay a registered pattern after reconstructing a structure major. All
expanded-endpoint typing and pattern checks are recovered in the replay context. -/
theorem pattern_after_structure
    {p : Pattern} {r : p.RHS × p.Check} {captures : p.Path → VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (hinfo : env.projections family info)
    (hp : params.length = info.nparams) (hi : info.nindices = 0)
    (hmajor : HasType env univs Γ major (mkApps (.const family ctorLevels) params))
    (hsource : HasType env univs Γ (.app fn major) T)
    (hguard : (∀ index F u, index < info.numFields →
      info.fieldType family ctorLevels params index major = some F → HasType env univs Γ F (.sort u) →
      (info.resultLevel.inst ctorLevels).IsNeverZero ∨ u ≈ .zero) ∨
      ProofFields env univs info ctorLevels)
    (hpat : Pat p r) (hcheck : CheckFromTyping env univs p r levels)
    (hmatch : p.Matches (.app fn (structExpand family info ctorLevels params major)) levels captures) :
    IsDefEq env univs Γ (.app fn major) (r.1.apply levels captures) T := by
  have hc := structure_constructor henv hΓ hinfo hp hi hmajor hguard
  have heta := (IsDefEq.structEta hinfo hp hi hmajor hc).symm
  obtain ⟨A, B, hfn, hm⟩ := hsource.app_inv henv hΓ
  have hmEq := (show IsDefEqU env univs Γ major (structExpand family info ctorLevels params major)
    from ⟨_, heta⟩).of_l henv hΓ hm
  have happ := IsDefEq.trans_l henv hΓ hsource (IsDefEq.appDF hfn hmEq)
  have hstep := pat_wf hΓ hpat hmatch happ.hasType.2 (hcheck hΓ hmatch happ.hasType.2)
  exact happ.trans (hstep.of_l henv hΓ happ.hasType.2)

/-- The recursor RHS is unchanged if the projected constructor uses arbitrary
parameters and levels. They are replaced by the major's actual family parameters
only while reconstructing its typing. No typing or scope of the dummy data is needed. -/
theorem projected_iota
    {r : (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields))).RHS ×
      (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields))).Check}
    {recCaptures : ((Pattern.const recursor).varN offset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (hinfo : env.projections family info)
    (hp : params.length = info.nparams) (hi : info.nindices = 0)
    (hmajor : HasType env univs Γ major (mkApps (.const family ctorLevels) params))
    (hsource : HasType env univs Γ (.app fn major) T)
    (hguard : (∀ index F u, index < info.numFields →
      info.fieldType family ctorLevels params index major = some F → HasType env univs Γ F (.sort u) →
      (info.resultLevel.inst ctorLevels).IsNeverZero ∨ u ≈ .zero) ∨
      ProofFields env univs info ctorLevels)
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels)
    (hrec : ((Pattern.const recursor).varN offset).Matches fn levels recCaptures)
    (hdummy : dummyParams.length = info.nparams)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (mkApps (.const info.ctorName dummyLevels)
        (dummyParams ++ (List.range info.numFields).map (fun i => .proj family i major))) dummyLevels ctorCaptures) :
    IsDefEq env univs Γ (.app fn major) (Pattern.RHS.apply (p := (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)))) levels (Sum.elim recCaptures ctorCaptures) r.1) T := by
  obtain ⟨actualCaptures, hactual, _⟩ := Pattern.matches_varN_const
    (c := info.ctorName) (ls := ctorLevels) (info.nparams + info.numFields)
    (params ++ (List.range info.numFields).map (fun i => .proj family i major)) (by simp [hp])
  have he := (pat_iota_params hpat hinfo rfl hctor hactual hdummy hp).1 levels recCaptures
  rw [he]
  exact pattern_after_structure hΓ hinfo hp hi hmajor hsource hguard hpat hcheck (.app hrec hactual)

/-- In a never-zero source universe the projected iota replay needs no further
projection guard or expanded-constructor typing premise. -/
theorem projected_iota_neverZero
    {r : (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields))).RHS ×
      (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields))).Check}
    {recCaptures : ((Pattern.const recursor).varN offset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (hinfo : env.projections family info)
    (hp : params.length = info.nparams) (hi : info.nindices = 0)
    (hz : (info.resultLevel.inst ctorLevels).IsNeverZero)
    (hmajor : HasType env univs Γ major (mkApps (.const family ctorLevels) params))
    (hsource : HasType env univs Γ (.app fn major) T)
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels)
    (hrec : ((Pattern.const recursor).varN offset).Matches fn levels recCaptures)
    (hdummy : dummyParams.length = info.nparams)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (mkApps (.const info.ctorName dummyLevels)
        (dummyParams ++ (List.range info.numFields).map (fun i => .proj family i major))) dummyLevels ctorCaptures) :
    IsDefEq env univs Γ (.app fn major) (Pattern.RHS.apply (p := (Pattern.app ((Pattern.const recursor).varN offset)
      ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)))) levels (Sum.elim recCaptures ctorCaptures) r.1) T :=
  projected_iota hΓ hinfo hp hi hmajor hsource (.inl (fun _ _ _ _ _ _ => .inl hz))
    hpat hcheck hrec hdummy hctor

end Lean4Lean.VEnv.Strengthening.StructureReplay
