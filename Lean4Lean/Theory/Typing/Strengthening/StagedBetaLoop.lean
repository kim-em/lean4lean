import Lean4Lean.Theory.Typing.Strengthening.StagedRecoverySubstitution
import Lean4Lean.Theory.Typing.Strengthening.StagedEtaLoop

/-! # Beta substitution of an argument recovered through eta-dependent K

The argument is a variable declared at the recursive cast type. Its recovery at
Prop → Prop requires the stage-two computation from StagedEtaLoop. Substituting
it into the stage-one eta path for an ordinary function variable produces the
stage-three beta/eta path, with exact output syntax and typed replay.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The additive bound is exercised with a stage-two argument and a stage-one
body. The resulting certificate is obtained by substitution, not re-synthesis. -/
theorem loopCast_beta_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (loopEquality c)) :
    StagedEtaCompute D kdepth 3 (loopCast c p :: Γ)
      (.app (.lam resultType (.bvar 0)) (.bvar 0))
      (.lam prop (.app (.bvar 1) (.bvar 0))) ∧
    env.IsDefEq univs (loopCast c p :: Γ)
      (.app (.lam resultType (.bvar 0)) (.bvar 0))
      (.lam prop (.app (.bvar 1) (.bvar 0))) resultType := by
  have hT := loopCast_typed heq hs hc hδ hd hΓ hp
  have hΓ' : OnCtx (loopCast c p :: Γ) (env.IsType univs) := ⟨hΓ, _, hT⟩
  have R := loopCast_compute (kdepth := kdepth) (p := p.lift) heq hs hc hδ hd hΓ'
  have R' : StagedEtaCompute D kdepth 2 (loopCast c p :: Γ) (loopCast c p).lift resultType := by
    simpa [loopCast, eqRecApp, constantEqMotive, eqApp, omegaTerm, diagonal,
      etaOmega, etaDiagonal, selfBody, domain, resultType, prop, liftN] using R
  have Rx : StagedTypeRecovery D kdepth 2 (loopCast c p :: Γ) (.bvar 0) resultType :=
    .convert (.bvar .zero) R'
  have hx := Rx.hasType heq hs hΓ' ⟨_, HasType.bvar Lookup.zero⟩
  have hΓ'' : OnCtx (resultType :: loopCast c p :: Γ) (env.IsType univs) :=
    ⟨hΓ', _, result_typed env univs _⟩
  have Rb : StagedEtaCompute D kdepth 1 (resultType :: loopCast c p :: Γ)
      (.bvar 0) (.lam prop (.app (.bvar 1) (.bvar 0))) := .eta (.bvar .zero)
  have RE := Rb.beta_inst heq hs hΓ'' hx Rx ⟨_, HasType.bvar Lookup.zero⟩
  have RE' : StagedEtaCompute D kdepth 3 (loopCast c p :: Γ)
      (.app (.lam resultType (.bvar 0)) (.bvar 0))
      (.lam prop (.app (.bvar 1) (.bvar 0))) := by
    simpa [prop, inst, instVar, liftN] using RE
  have hl : env.HasType univs (loopCast c p :: Γ)
      (.lam resultType (.bvar 0)) (.forallE resultType resultType) :=
    .lam (result_typed env univs _) (.bvar .zero)
  have hsource : env.HasType univs (loopCast c p :: Γ)
      (.app (.lam resultType (.bvar 0)) (.bvar 0)) resultType := HasType.app hl hx
  exact ⟨RE', RE'.simAt heq hs hΓ' _ hsource⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
