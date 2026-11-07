import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedContinuation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaGuard

/-! # Nonreplayable roots can be globally minimal before binder consumption

A one-primitive body followed by an actual consumption frame has total minimum
one whenever its short image cannot compute to the long image. Any competitor
with a zero-cost body would substitute by pure beta and contradict that fact.
For a non-lambda-headed output, the enclosing lambda application also has
minimum one: a pure beta competitor would give the forbidden short-image path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.beta_first_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta
open private beta_inst_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaGuard
variable [Params] {D : Definitions}

/-- Nonreplay excludes every zero-cost body prefix, even when the competitor
may change its endpoint, finite stage and arbitrarily costly continuation.
The actual one-root path therefore has a globally minimal typed consumption
continuation. This minimum alone cannot imply transport of its body root. -/
theorem pi_inert_nonreplay_typed_continuation_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource (A :: Δ) source)
    (HR : PiInertStage D n (A :: Δ) source target)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HN : ∀ later, ¬ ScopedCompute (PiInertStage D later) Δ (source.inst x) (target.inst x)) :
    (∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) []
        (fun e k => e = target.inst x ∧ k = 0) endpoint k → 1 ≤ j) ∧
    PiInertTypedContinuationMinimum D Δ (target.inst x) (A :: Δ) source 1 := by
  have HM : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) []
        (fun e k => e = target.inst x ∧ k = 0) endpoint k → 1 ≤ j := by
    rintro later j endpoint k RJ ⟨suffixStage, cs, e, ck, hc, RS, rfl, rfl⟩
    by_contra hj
    have hj0 : j = 0 := by omega
    subst j
    have RB : BetaRed (source.inst x) (endpoint.inst x) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        (RJ.zero_beta.subst (σ := ProofShape.Subst.one x))
    have RS' : ScopedCompute (PiInertStage D suffixStage) Δ (endpoint.inst x) (target.inst x) := by
      simpa only [ProofShape.mkApps, List.foldl_nil, ProofShape.inst_eq_subst,
        ProofShape.Subst.liftN] using RS.forget
    exact HN suffixStage ((ScopedCompute.beta RB).trans RS')
  have HTtarget := HT.pi_inert_compute heq hs (.base HR)
  have HTout : TypedSource Δ (target.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTtarget.subst W
  refine ⟨HM, PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) []
    (fun e k => e = target.inst x ∧ k = 0), n, 1, 0, target, HT, .base HR, ?_, rfl, ?_⟩
  · apply PiInertTypedContinuationRun.application (n := 0) (cs := 0) (ck := 0) (e' := target.inst x) HTtarget (.inst W)
    · simpa only [ProofShape.mkApps, List.foldl_nil, ProofShape.inst_eq_subst,
        ProofShape.Subst.liftN] using HTout
    · simpa only [ProofShape.mkApps, List.foldl_nil, ProofShape.inst_eq_subst,
        ProofShape.Subst.liftN] using
        (ScopedComputeCount.beta (Step := PiInertStage D 0) (Δ := Δ) (BetaRed.refl (e := target.inst x)))
    · exact .terminal HTout
  · intro later j endpoint k RJ RK
    have := HM later j endpoint k RJ RK
    omega

/-- Performing the root inside a lambda before beta has minimum count one
among all finite-stage paths to the same non-lambda-headed output. A zero-cost
competitor would contract beta after only beta changes to the body and argument,
thereby giving a forbidden path from the short instantiated body. -/
theorem pi_inert_nonreplay_lambda_application_minimum
    (HR : PiInertStage D n (A :: Δ) source target)
    (HN : ∀ later, ¬ ScopedCompute (PiInertStage D later) Δ (source.inst x) (target.inst x))
    (hout : ∀ B b y, target.inst x ≠ .app (.lam B b) y) :
    ScopedComputeCount (PiInertStage D n) 1 Δ (.app (.lam A source) x) (target.inst x) ∧
    ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.app (.lam A source) x) (target.inst x) → 1 ≤ j := by
  constructor
  · have R := ((ScopedComputeCount.beta (BetaRed.refl (e := A))).lam (.base HR)).app
      (ScopedComputeCount.beta (BetaRed.refl (e := x)))
    exact R.trans (.beta .beta)
  · intro later j RJ
    by_contra hj
    have hj0 : j = 0 := by omega
    subst j
    rcases ProofShape.beta_first_head RJ.zero_beta with ⟨A', b', x', E, RF, RX⟩ | ⟨A', b', x', RF, RX, RT⟩
    · exact hout A' b' x' E
    · obtain ⟨A'', b'', E, RA, RB⟩ := RF.lam_inv
      obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
      have RI : BetaRed (source.inst x) (b'.inst x) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
          (RB.subst (σ := ProofShape.Subst.one x))
      exact HN 0 (.beta ((RI.trans (beta_inst_image b' RX)).trans RT))

end Lean4Lean.VEnv.Strengthening
