import Lean4Lean.Theory.Typing.Strengthening.StagedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaLoop
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # A recovered eta / K / type-recovery cycle

Stage one eta-aligns the recursive loop endpoints. Stage two uses that comparison
to contract a type-valued constant-motive recursor to a Pi. A variable at this
cast type can then be eta-expanded at stage three, using the recovered Pi.
The example is typed in a canonical-Eq-preserving recursive environment.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params] {D : Definitions}

/-- An equality assumption between the two well-typed recursive endpoints. -/
def loopEquality (c : Name) : VExpr :=
  eqApp (.succ .zero) resultType (omegaTerm c) (etaOmega c)

/-- The result is a function type, but its displayed head is a recursor. -/
def loopCast (c : Name) (p : VExpr) : VExpr :=
  eqRecApp (.succ (.succ .zero)) (.succ .zero) resultType (omegaTerm c)
    (constantEqMotive (.succ .zero) resultType (omegaTerm c) (.sort (.succ .zero)))
    resultType (etaOmega c) p

/-- Body eta at stage one supplies a finite endpoint certificate. -/
theorem loop_computed_comparison
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs)) :
    ComputedComparison (StagedEtaCompute D kdepth 1) Γ (omegaTerm c) (etaOmega c) := by
  have R : StagedEtaCompute D kdepth 1 Γ (omegaTerm c) (etaOmega c) :=
    .ofRecovered (recovered_omega_eta hd)
  exact R.comparison (R.simAt heq hs hΓ _ (omega_typed hc hδ)).hasType.2

/-- The stage-two K guard contains a genuine recovered body-eta computation. -/
theorem loopCast_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs)) :
    StagedEtaCompute D kdepth 2 Γ (loopCast c p) resultType :=
  .eqRec (loop_computed_comparison heq hs hc hδ hd hΓ)

/-- The cast is a type whenever its equality proof is supplied. -/
theorem loopCast_typed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (loopEquality c)) :
    env.HasType univs Γ (loopCast c p) (.sort (.succ .zero)) := by
  have R : RecoveredEtaCompute D 0 Γ (omegaTerm c) (etaOmega c) := recovered_omega_eta hd
  have hb := (R.simAt heq hs hΓ _ (omega_typed hc hδ)).hasType.2
  exact constant_eqRec_typed henv heq (by trivial) (by trivial) hΓ
    (result_typed env univs Γ) (omega_typed hc hδ) (.sort (by trivial))
    (result_typed env univs Γ) hb hp

/-- Recovery looks through the cast type before choosing this eta annotation.
Both the source's original cast typing and the displayed Pi typing are derived. -/
theorem loopCast_variable_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (loopEquality c)) :
    StagedEtaCompute D kdepth 3 (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) ∧
    env.IsDefEq univs (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) (loopCast c p).lift := by
  have hT := loopCast_typed heq hs hc hδ hd hΓ hp
  have hΓ' : OnCtx (loopCast c p :: Γ) (env.IsType univs) := ⟨hΓ, _, hT⟩
  have R := loopCast_compute (kdepth := kdepth) (p := p.lift) heq hs hc hδ hd hΓ'
  have R' : StagedEtaCompute D kdepth 2 (loopCast c p :: Γ) (loopCast c p).lift resultType := by
    simpa [loopCast, eqRecApp, constantEqMotive, eqApp, omegaTerm, diagonal,
      etaOmega, etaDiagonal, selfBody, domain, resultType, prop, liftN] using R
  have hv : StagedTypeRecovery D kdepth 2 (loopCast c p :: Γ) (.bvar 0) (loopCast c p).lift :=
    .bvar .zero
  have RE : StagedEtaCompute D kdepth 3 (loopCast c p :: Γ) (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) := .eta (.convert hv R')
  exact ⟨RE, RE.simAt heq hs hΓ' _ (.bvar .zero)⟩

omit [Params] in
/-- The three-stage interaction occurs in an actual well-formed environment
with canonical Eq; all proof and cast assumptions form a well-formed context. -/
theorem canonical_staged_cast_eta (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    let henv := extended_wf hbase hfresh
    letI := henv.params 0
    let D := Definitions.ofEnv (extended base c) 0 henv
    (extended base c).HasCanonicalEq ∧
    OnCtx [loopCast c (.bvar 0), loopEquality c] ((extended base c).IsType 0) ∧
    StagedEtaCompute D 0 3 [loopCast c (.bvar 0), loopEquality c] (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) ∧
    (extended base c).IsDefEq 0 [loopCast c (.bvar 0), loopEquality c] (.bvar 0)
      (.lam prop (.app (.bvar 1) (.bvar 0))) (loopCast c (.bvar 0)).lift := by
  let henv := extended_wf hbase hfresh
  letI := henv.params 0
  let D := Definitions.ofEnv (extended base c) 0 henv
  have hEq := extended_canonicalEq heq hfresh
  have hs : D.Sound Params.env univs := Definitions.ofEnv_sound henv
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  have hd : D.unfolds c [] (domainValue c) := PureObservation.guarded_definition henv 0
  have R : RecoveredEtaCompute D 0 [] (omegaTerm c) (etaOmega c) := recovered_omega_eta hd
  have heqTy := HasType.eqApp hEq (by trivial) (result_typed Params.env 0 [])
    (omega_typed hc hδ) (R.simAt hEq hs trivial _ (omega_typed hc hδ)).hasType.2
  have hΓ : OnCtx [loopEquality c] (Params.env.IsType univs) := ⟨trivial, _, heqTy⟩
  have hp : Params.env.HasType univs [loopEquality c] (.bvar 0) (loopEquality c) := by
    have h : Params.env.HasType univs [loopEquality c] (.bvar 0) (loopEquality c).lift := .bvar .zero
    simpa [loopEquality, eqApp, omegaTerm, diagonal, etaOmega, etaDiagonal,
      selfBody, domain, resultType, prop, liftN] using h
  exact ⟨hEq, ⟨hΓ, _, loopCast_typed hEq hs hc hδ hd hΓ hp⟩,
    loopCast_variable_eta hEq hs hc hδ hd hΓ hp⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
