import Lean4Lean.Theory.Typing.Strengthening.ComparedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparisonLoop
import Lean4Lean.Theory.Typing.Strengthening.StagedEtaLoop

/-! # Direct loop comparison drives K and type recovery

The old example eta-computed both loops before comparing them. Recovered
application comparison can instead guard K directly at stage one, then drive
type recovery and variable eta at stage two. This is a shorter certificate;
it does not prove strict enlargement over the old union of all finite stages.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The original loop endpoints guard a stage-one K step directly. No endpoint
computation or normalization is used in this certificate. -/
theorem loopCast_direct_compute
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs)) :
    ComparedEtaCompute D kdepth 1 Γ (loopCast c p) resultType :=
  ComparedEtaCompute.eqRec_recovered
    (omega_recovered_comparison (depth := kdepth) (mode := true) hc hδ hd hΓ)

/-- The directly compared cast supplies a recovered Pi and then a stage-two
eta step. All typings are replayed in the original cast-typed context. -/
theorem loopCast_direct_variable_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c))
    (hΓ : OnCtx (loopCast c p :: Γ) (env.IsType univs)) :
    ComparedEtaCompute D kdepth 2 (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) ∧
    env.IsDefEq univs (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) (loopCast c p).lift := by
  have R := loopCast_direct_compute (kdepth := kdepth) (p := p.lift) hc hδ hd hΓ
  have R' : ComparedEtaCompute D kdepth 1 (loopCast c p :: Γ)
      (loopCast c p).lift resultType := by
    simpa [loopCast, eqRecApp, constantEqMotive, eqApp, omegaTerm, diagonal,
      etaOmega, etaDiagonal, selfBody, domain, resultType, prop, liftN] using R
  have hv : TypeRecoveryWith (ComparedEtaCompute D kdepth 1)
      (loopCast c p :: Γ) (.bvar 0) (loopCast c p).lift := .bvar .zero
  have RE : ComparedEtaCompute D kdepth 2 (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) := .eta (.convert hv R')
  exact ⟨RE, RE.simAt heq hs hΓ _ (.bvar .zero)⟩

omit [Params] in
/-- An actual canonical-Eq-preserving extension admits this two-stage cycle,
in the same well-formed cast context as the former three-stage certificate. -/
theorem canonical_compared_cast_eta (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    let henv := extended_wf hbase hfresh
    letI := henv.params 0
    let D := Definitions.ofEnv (extended base c) 0 henv
    (extended base c).HasCanonicalEq ∧
    OnCtx [loopCast c (.bvar 0), loopEquality c] ((extended base c).IsType 0) ∧
    ComparedEtaCompute D 0 2 [loopCast c (.bvar 0), loopEquality c] (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) ∧
    (extended base c).IsDefEq 0 [loopCast c (.bvar 0), loopEquality c] (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) (loopCast c (.bvar 0)).lift := by
  let henv := extended_wf hbase hfresh
  letI := henv.params 0
  let D := Definitions.ofEnv (extended base c) 0 henv
  obtain ⟨hEq, hΓ, _⟩ := canonical_staged_cast_eta hbase heq hfresh
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  exact ⟨hEq, hΓ, loopCast_direct_variable_eta hEq (Definitions.ofEnv_sound henv)
    hc hδ (PureObservation.guarded_definition henv 0) hΓ⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
