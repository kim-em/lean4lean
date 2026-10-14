import Lean4Lean.Theory.Typing.Strengthening.StagedEtaComputation
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation

/-! # Recoverable telescope opening for guarded indexed prefixes

A declared constant's supplied prefix recovers its literal residual telescope.
Repeated recovered eta opens that telescope, after which a guarded computation
can run and be closed again. Applied to Eq.rec this handles partial prefixes
with a finite certificate for the opened endpoint comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open InductiveSignature.RecursorData
open PureObservation (Definitions)
variable [Params]

/-- Applying a literal dependent telescope recovers the residual type using
only the original recovery and the syntactic supply calculation. -/
theorem TypeRecoveryWith.supplyType (R : TypeRecoveryWith C Γ f T)
    (H : RecursorData.supplyType args T = some out) :
    TypeRecoveryWith C Γ (mkApps f args) out := by
  induction args generalizing f T with
  | nil => cases H; exact R
  | cons a args ih =>
    cases T <;> try contradiction
    exact ih (.app R) H

/-- Recovery opens a declared telescope with its fresh variables. -/
theorem TypeRecoveryWith.etaOpen (hw : ComputeWeakening C)
    (R : TypeRecoveryWith C Γ f (wrapForalls domains result)) :
    TypeRecoveryWith C (domains.reverse ++ Γ) (VEnv.etaOpen domains.length f) result := by
  induction domains generalizing Γ f with
  | nil => exact R
  | cons A domains ih =>
    have R' := TypeRecoveryWith.app (a := .bvar 0) (R.weakN hw (Ctx.LiftN.one (A := A)))
    simp only [inst_liftN_bvar] at R'
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, VEnv.etaOpen] using ih R'

/-- Compatible lambda formation at any stage. -/
theorem StagedEtaCompute.lam (RA : StagedEtaCompute D kdepth stage Γ A A')
    (Rb : StagedEtaCompute D kdepth stage (A :: Γ) b b') :
    StagedEtaCompute D kdepth stage Γ (.lam A b) (.lam A' b') := by
  cases stage with
  | zero => exact GuardedKCompute.lam RA Rb
  | succ stage => exact RecoveredEtaWith.lam RA Rb

/-- A staged path under a whole telescope closes under its displayed domains. -/
theorem StagedEtaCompute.wrapLams
    (R : StagedEtaCompute D kdepth stage (domains.reverse ++ Γ) b b') :
    StagedEtaCompute D kdepth stage Γ (VExpr.wrapLams domains b) (VExpr.wrapLams domains b') := by
  induction domains generalizing Γ with
  | nil => exact R
  | cons A domains ih =>
    apply StagedEtaCompute.lam .refl
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using R

/-- Any recovered telescope can be eta-opened at one further stage. The bound
is independent of the number of remaining binders. -/
theorem StagedEtaCompute.etaOpen
    (R : StagedTypeRecovery D kdepth stage Γ f (wrapForalls domains result)) :
    StagedEtaCompute D kdepth (stage + 1) Γ f
      (VExpr.wrapLams domains (VEnv.etaOpen domains.length f)) := by
  induction domains generalizing Γ f with
  | nil => exact .refl
  | cons A domains ih =>
    have R' := TypeRecoveryWith.app (a := .bvar 0)
      (R.weakN (Ctx.LiftN.one (A := A)))
    simp only [inst_liftN_bvar] at R'
    exact (StagedEtaCompute.eta R).trans (.lam .refl (ih R'))

/-- Open a recovered residual telescope, run a same-stage body computation,
and close it. This avoids copying arbitrary ambient eta annotations. -/
theorem StagedEtaCompute.prefix
    (R : StagedTypeRecovery D kdepth stage Γ f (wrapForalls domains result))
    (H : StagedEtaCompute D kdepth (stage + 1) (domains.reverse ++ Γ)
      (VEnv.etaOpen domains.length f) out) :
    StagedEtaCompute D kdepth (stage + 1) Γ f (VExpr.wrapLams domains out) :=
  (StagedEtaCompute.etaOpen R).trans H.wrapLams

/-- A partial Eq.rec prefix is computable whenever its fresh complete argument
spine has a preceding-stage endpoint comparison. Both the residual telescope
and the complete spine are exact syntactic calculations, not typing premises. -/
theorem StagedEtaCompute.eqRec_prefix
    (heq : env.HasCanonicalEq) (hv : v.WF univs) (hw : w.WF univs)
    (hsupply : RecursorData.supplyType args (canonicalEqRecType.instL [v, w]) = some residual)
    (htake : residual.takeForalls n = some (domains, result))
    (hargs : args.map (·.liftN n) ++ vars n 0 = [α, a, M, m, b, p])
    (H : ComputedComparison (StagedEtaCompute D kdepth stage) (domains.reverse ++ Γ) a b) :
    StagedEtaCompute D kdepth (stage + 1) Γ (mkApps (.const ``Eq.rec [v, w]) args)
      (VExpr.wrapLams domains m) := by
  have hc : StagedTypeRecovery D kdepth stage Γ (.const ``Eq.rec [v, w])
      (canonicalEqRecType.instL [v, w]) :=
    .const heq.2.2.1 (by simp_all) rfl
  have R := hc.supplyType hsupply
  rw [(takeForalls_eq_wrapForalls htake).1] at R
  apply StagedEtaCompute.prefix R
  rw [takeForalls_domains_length htake, etaOpen_spine, liftN_mkApps]
  simp only [liftN, ← mkApps_append]
  rw [hargs]
  exact StagedEtaCompute.eqRec H

end Lean4Lean.VEnv.Strengthening
