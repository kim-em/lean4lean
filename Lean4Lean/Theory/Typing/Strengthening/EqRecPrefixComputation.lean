import Lean4Lean.Theory.Typing.Strengthening.StagedPrefixComputation

/-! # Indexed equality prefixes with finite alignment certificates

The prefix before the proof major unfolds using a finite comparison of its two
endpoints. With a proposition as carrier, even the prefix before the endpoint
unfolds: proof irrelevance certifies alignment with the fresh endpoint variable.
All remaining annotations are recovered from the canonical constant telescope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open InductiveSignature.RecursorData
variable [Params]

omit [Params] in
/-- The residual telescope after supplying the carrier, endpoint, motive and minor. -/
theorem eqRec_supply_four :
    supplyType [α, a, M, m] (canonicalEqRecType.instL [v, w]) =
      some (.forallE α (.forallE (eqApp w α.lift a.lift (.bvar 0))
        (.app (.app (M.liftN 2) (.bvar 1)) (.bvar 0)))) := by
  simp [supplyType, canonicalEqRecType, canonicalEqRecMotive, canonicalEqRecMinor,
    instL, VLevel.inst, inst, instVar, inst_liftN_lo, eqApp]

omit [Params] in
/-- Supplying the requested endpoint leaves exactly the equality-proof binder. -/
theorem eqRec_supply_five :
    supplyType [α, a, M, m, b] (canonicalEqRecType.instL [v, w]) =
      some (.forallE (eqApp w α a b) (.app (.app M.lift b.lift) (.bvar 0))) := by
  simp [supplyType, canonicalEqRecType, canonicalEqRecMotive, canonicalEqRecMinor,
    instL, VLevel.inst, inst, instVar, inst_liftN_lo, eqApp]

/-- Every endpoint comparison certificate enables the prefix before the major,
including a dependent motive. No proof major has yet been supplied. -/
theorem StagedEtaCompute.eqRec_before_major
    (heq : env.HasCanonicalEq) (hv : v.WF univs) (hw : w.WF univs)
    (H : ComputedComparison (StagedEtaCompute D kdepth stage) Γ a b) :
    StagedEtaCompute D kdepth (stage + 1) Γ
      (mkApps (.const ``Eq.rec [v, w]) [α, a, M, m, b])
      (.lam (eqApp w α a b) m.lift) := by
  have H' := H.weakN (StagedEtaCompute.computeWeakening stage)
    (Ctx.LiftN.one (A := eqApp w α a b))
  exact eqRec_prefix (n := 1) (domains := [eqApp w α a b]) heq hv hw
    eqRec_supply_five rfl rfl H'

/-- If the carrier is a proposition, its fresh endpoint is a proof too.
The prefix before the endpoint therefore unfolds using proof irrelevance. -/
theorem StagedEtaCompute.eqRec_proof_carrier
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hα : env.HasType univs Γ α (.sort .zero)) (ha : env.HasType univs Γ a α) :
    StagedEtaCompute D kdepth (stage + 1) Γ
      (mkApps (.const ``Eq.rec [v, .zero]) [α, a, M, m])
      (.lam α (.lam (eqApp .zero α.lift a.lift (.bvar 0)) (m.liftN 2))) := by
  let E := eqApp .zero α.lift a.lift (.bvar 0)
  have W : Ctx.LiftN 2 0 Γ (E :: α :: Γ) := .zero [E, α]
  have hα' := hα.weakN henv W
  have ha' := ha.weakN henv W
  have hb : env.HasType univs (E :: α :: Γ) (.bvar 1) (α.liftN 2) := by
    have h : env.HasType univs (E :: α :: Γ) (.bvar 1) α.lift.lift := .bvar (.succ .zero)
    simpa only [lift, liftN_liftN, Nat.zero_add] using h
  have H : ComputedComparison (StagedEtaCompute D kdepth stage) (E :: α :: Γ)
      (a.liftN 2) (.bvar 1) :=
    ⟨_, _, 0, .refl, .refl, .proofIrrel hα' ha' hb⟩
  exact eqRec_prefix (n := 2) (domains := [α, E]) heq hv (by trivial)
    eqRec_supply_four rfl rfl H

end Lean4Lean.VEnv.Strengthening
