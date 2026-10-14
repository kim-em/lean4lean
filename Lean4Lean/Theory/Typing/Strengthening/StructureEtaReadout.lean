import Lean4Lean.Theory.Typing.Strengthening.EtaIotaExchange

/-! # Closed structure computation repairs neutral readout

On an exact structure expansion, the closed projection program is literally
the iota right-hand side, because the rule ignores constructor parameters.
Thus an identity-branch readout computes on the original neutral major once
these sound closed equations are included. No general phase composition or
strengthening is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params] {D : Definitions} {params : List VExpr}

set_option backward.isDefEq.respectTransparency false in
/-- The supplied projection program agrees exactly with iota on the original
major's eta expansion. Constructor parameters disappear by the registered
rule's parameter-independence law. -/
theorem suppliedBody_eq_eta_rhs
    {r : (pattern data info).RHS × (pattern data info).Check}
    {recCaptures : ((Pattern.const data.name).varN data.majorOffset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hp : Pat _ r) (hi : env.projections (family data) info)
    (ha : args.length = data.majorOffset) (hparams : params.length = info.nparams)
    (hrec : ((Pattern.const data.name).varN data.majorOffset).Matches
      (mkApps (.const data.name levels) args) levels recCaptures)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (structExpand (family data) info ctorLevels params major) ctorLevels ctorCaptures) :
    suppliedBody data info levels r.1 args ha major =
      Pattern.RHS.apply (p := pattern data info) levels (Sum.elim recCaptures ctorCaptures) r.1 := by
  have hrecEq := (Pattern.matches_determ hrec (spineCaptures_match args ha levels)).2
  rw [hrecEq]
  let fields := (List.range info.numFields).map (fun i => VExpr.proj (family data) i major)
  let dummy := List.replicate info.nparams (VExpr.sort .zero) ++ fields
  have hdlen : dummy.length = info.nparams + info.numFields := by simp [dummy, fields]
  have hdummy := spineCaptures_match (c := info.ctorName) dummy hdlen []
  have he := (pat_iota_params hp hi rfl hctor hdummy hparams (by simp)).1
    levels (spineCaptures args ha)
  exact he.symm

/-- A closed structure equation followed by beta performs the same field
readout on the original major, including a variable major with no computation. -/
theorem identity_branch_eta_readout
    {r : (pattern data info).RHS × (pattern data info).Check}
    {recCaptures : ((Pattern.const data.name).varN data.majorOffset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hr : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hl : levels.length = data.uvars) (hi : env.projections (family data) info)
    (hx : info.nindices = 0) (hz : Admissible env univs data info levels)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset) (hparams : params.length = info.nparams)
    (hrec : ((Pattern.const data.name).varN data.majorOffset).Matches
      (mkApps (.const data.name levels) args) levels recCaptures)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (structExpand (family data) info ctorLevels params major) ctorLevels ctorCaptures)
    (he : Pattern.RHS.apply (p := pattern data info) levels (Sum.elim recCaptures ctorCaptures) r.1 =
      .app (.lam A (.bvar 0)) (.proj (family data) index major)) :
    Compute (definitions D) (.app (mkApps (.const data.name levels) args) major)
      (.proj (family data) index major) := by
  have R := supplied_compute (D := D) hr hw hl hi hx hz hp hc ha (major := major)
  rw [suppliedBody_eq_eta_rhs hp hi ha hparams hrec hctor, he] at R
  have RB : Compute (definitions D) (.app (.lam A (.bvar 0)) (.proj (family data) index major))
      (.proj (family data) index major) := by
    simpa [VExpr.inst, instVar] using (Compute.beta (D := definitions D)
      (A := A) (b := .bvar 0) (a := VExpr.proj (family data) index major))
  exact R.trans RB

end Lean4Lean.VEnv.Strengthening.ClosedStructure
