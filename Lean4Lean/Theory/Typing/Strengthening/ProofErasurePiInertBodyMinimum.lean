import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCountedSpineComponents

/-! # Minimum body paths inside a consumed lambda

A competing body path is inserted below the original annotation, then the
original arguments, consuming beta and final suffix are replayed verbatim.
All finite stages can be raised to a common bound. Consequently a globally
minimum whole path forces a globally minimum body path and exact accounting.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Replace a body computation while retaining the exact whole-path output.
The source annotation fixes the body context even when the annotation changes.
No substitution closure of guarded primitives is used. -/
theorem pi_inert_counted_lambda_body_replace
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A body))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D later) j (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out) :
    ScopedComputeCount (PiInertStage D (max later n)) (cp+1+cd+j+ca+cs) Δ original out := by
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max later n) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_right later n)
  have RB' := RB.mono (pi_inert_stage_mono (Nat.le_max_left later n))
  have RF := (ScopedComputeCount.base (raise HR)).trans
    (ScopedComputeCount.lam (RD.mono raise) RB')
  have RBeta : ScopedComputeCount (PiInertStage D (max later n)) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs'))
      (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  simpa only [Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
    (RP.mono raise).trans ((RF.mkApps (RX.mono raise)).trans (RBeta.trans (RS.mono raise)))

/-- Global whole-path minimality is inherited by the body below the original
binder, even for competitors at larger stages. The reconstructed decomposition
uses every primitive in the minimum path, and its body has strictly lower cost.
This does not assert that the body endpoint itself exposes a carrier. -/
theorem pi_inert_counted_lambda_body_minimal
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A body))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out)
    (hcost : cp+1+cd+cb+ca+cs ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ original out → cost ≤ j) :
    cp+1+cd+cb+ca+cs = cost ∧ cb < cost ∧
      ∀ later j, ScopedComputeCount (PiInertStage D later) j (A :: Δ) body body' → cb ≤ j := by
  have HM := hmin _ _ (pi_inert_counted_lambda_body_replace RP HR RD RB RX RS)
  refine ⟨by omega, by omega, ?_⟩
  intro later j RJ
  have HJ := hmin _ _ (pi_inert_counted_lambda_body_replace RP HR RD RJ RX RS)
  omega

/-- Minimize the body together with its application continuation. A competitor
may change the body endpoint and the entire post-beta suffix, provided it
reaches the same final output. Both stages may increase independently. The
combined cost is strictly smaller than the enclosing minimum path's count. -/
theorem pi_inert_counted_lambda_continuation_minimal
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A body))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps (body'.inst x') xs') out)
    (hcost : cp+1+cd+cb+ca+cs ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ original out → cost ≤ j) :
    cb+cs < cost ∧ ∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j (A :: Δ) body endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Δ
        (ProofShape.mkApps (endpoint.inst x') xs') out → cb+cs ≤ j+k := by
  obtain ⟨hexact, _, _⟩ := pi_inert_counted_lambda_body_minimal RP HR RD RB RX RS hcost hmin
  refine ⟨by omega, ?_⟩
  intro later suffixStage j k endpoint RJ RK
  have raise : ∀ {Δ a b}, PiInertStage D n Δ a b → PiInertStage D (max n suffixStage) Δ a b :=
    pi_inert_stage_mono (Nat.le_max_left n suffixStage)
  have RR := pi_inert_counted_lambda_body_replace (RP.mono raise) (raise HR)
    (RD.mono raise) RJ (RX.mono raise)
    (RK.mono (pi_inert_stage_mono (Nat.le_max_right n suffixStage)))
  have HM := hmin _ _ RR
  omega

end Lean4Lean.VEnv.Strengthening
