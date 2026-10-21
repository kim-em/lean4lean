import Lean4Lean.Theory.Typing.Strengthening.QuotPrefixConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion

/-! # Operational joins of repaired joint computations

Joint computation replays exactly into the now-confluent repaired prefix
relation. In particular, arbitrary typed instantiation has an operational join
without a recovery premise on the argument. The residual paths are actual
checked prefixes, not erased joint paths: their forward guards remain missing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]

/-- Two finite-stage joint paths from one typed erasure have typed original
representatives with a common actual computational reduct. No confluence of
the raw joint union, or forward coverage of residual guards, is assumed. -/
theorem proofErase_joint_operational_join
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RA : ProofShape.ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) sa)
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (RB : ProofShape.ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) sb)
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ a₀ b₀ out, env.HasType univs Γ a₀ T ∧ env.HasType univs Γ b₀ T ∧
      proofErase Γ a₀ = a ∧ proofErase Γ b₀ = b ∧
      PrefixCompute (ErasedQuotCore.definitions hq) Γ a₀ out ∧
      PrefixCompute (ErasedQuotCore.definitions hq) Γ b₀ out := by
  have hs := ErasedQuotCore.sound hq
  obtain ⟨a₀, HA, ha, EA⟩ := proofErase_joint_operational_replay heq hs hregistry hΓ ht RA
  obtain ⟨b₀, HB, hb, EB⟩ := proofErase_joint_operational_replay heq hs hregistry hΓ ht RB
  obtain ⟨out, JA, JB⟩ := ErasedQuotCore.prefix_confluent hq hcon hΓ ht HA HB
  exact ⟨a₀, b₀, out, ha, hb, EA, EB, JA, JB⟩

/-- Arbitrary typed instantiation of a joint body computation has an exact
operational join. The left endpoint is the original body instantiated by x;
the right representative erases literally to the raw output instantiated by
the erasure of x. No argument recovery or joint-confluence premise is needed.
Returning these residual paths to the raw joint grammar remains open. -/
theorem proofErase_joint_inst_operational_join
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RB : ProofShape.ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ∃ b' shared, env.HasType univs Γ b' (B.inst x) ∧
      proofErase Γ b' = out.inst (proofErase Γ x) ∧
      PrefixCompute (ErasedQuotCore.definitions hq) Γ (b.inst x) shared ∧
      PrefixCompute (ErasedQuotCore.definitions hq) Γ b' shared := by
  obtain ⟨b', HB, hb', EB⟩ := proofErase_joint_operational_replay heq
    (ErasedQuotCore.sound hq) hregistry hΓA hb RB
  obtain ⟨u, hA⟩ := hΓA.2
  have ht : env.HasType univs Γ (.app (.lam A b) x) (B.inst x) :=
    (hA.lam hb).app hx
  have HL : PrefixCompute (ErasedQuotCore.definitions hq) Γ
      (.app (.lam A b) x) (b.inst x) := .base (.base (.base .beta))
  have HR : PrefixCompute (ErasedQuotCore.definitions hq) Γ
      (.app (.lam A b) x) (b'.inst x) :=
    (PrefixCompute.app (.lam .refl HB) .refl).trans (.base (.base (.base .beta)))
  obtain ⟨shared, JL, JR⟩ := ErasedQuotCore.prefix_confluent hq hcon hΓA.1 ht HL HR
  refine ⟨b'.inst x, shared, hb'.instN henv Ctx.InstN.zero hx, ?_, JL, JR⟩
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb', EB]

end Lean4Lean.VEnv.Strengthening
