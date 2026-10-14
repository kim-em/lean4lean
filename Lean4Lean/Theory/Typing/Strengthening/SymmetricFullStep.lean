import Lean4Lean.Theory.Typing.Strengthening.SymmetricPrefixCompatibility

/-! # Every individual full step has a symmetric phase

All core, singleton, quotient, projection and eta roots are covered, as are
their compatible combinations. Finite full paths still require a mixed phase
composition theorem; terminal eta confluence alone does not supply that theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable {env : VEnv} {D : Definitions}

/-- Every typed full step is a symmetric computation/eta/normal join. The
singleton roots retain their actual prefix checks, without a coverage premise. -/
theorem fullStep_symmetric_phase (henv : env.WF) (hs : D.Sound env U)
    (hΓ : OnCtx Γ (env.IsType U)) (R : @FullStep (henv.params U) Γ a b)
    (ht : env.HasType U Γ a T) : @PrefixEtaJoin (henv.params U) D Γ a b := by
  letI := henv.params U
  induction R generalizing T with
  | core R => exact .compute hs hΓ (.base (PatternCompute.of_parRed henv R)) ht
  | delta R => exact .compute hs hΓ (.singleton R) ht
  | quotDelta R => exact .compute hs hΓ (.quotient R) ht
  | projIota hi hp hg _ =>
    obtain ⟨info', _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := hp.proj_inv henv hΓ
    obtain rfl := henv.ordered.projections_unique hi hi'
    have ha := (projection_major_family henv hΓ hi (henv.projectionRigid hi) hm.hasType.2).2
    exact .compute hs hΓ (.base (.base (.projIota hi ha hg))) ht
  | structEta hi hp hx hm hc =>
    exact .of_eta (EtaNormal.expansion hΓ (.structEta hi hp hx hm hc) ht).join
  | funEta hf => exact .of_eta (EtaNormal.expansion hΓ (.funEta hf) ht).join
  | app RF RA ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app hs hΓ hf (RF.hasType hΓ hf) ha (RA.hasType hΓ ha)
      (ihf hΓ hf) (iha hΓ ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj hs hΓ ht (ih hΓ hm.hasType.2)
  | lam RA RB _ ihb =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΔ : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hA⟩
    exact .lam hs hΓ hA (RA.defeq hΓ hA) hb (RB.hasType hΔ hb) (ihb hΔ hb)
  | forallE RA RB ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΔ : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hA⟩
    exact .forallE hs hΓ hA (RA.defeq hΓ hA) hB (RB.hasType hΔ hB)
      (ihA hΓ hA) (ihB hΔ hB)

end Lean4Lean.VEnv.Strengthening.PureObservation
