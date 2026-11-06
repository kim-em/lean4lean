import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut

/-! # A non-level body root after a consumed eta

If a minimum body cannot merely compute its lifted function while retaining
the fresh eta slot, the counted constant-spine decomposition must reach a
non-level root. The exact prefix, root typing, and suffix are retained without
requiring the body endpoint to expose a carrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private eta_argument_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut
variable [Params]

/-- A counted first non-level root on the original constant spine, with
exact accounting, component ancestry, its actual source typing, and both
surrounding paths. This does not classify or eliminate the selected root. -/
def CountedNonlevelSpineRoot (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (ls : List VLevel) (args : List ProofShape) (out : ProofShape) (cost : Nat) : Prop :=
  ∃ ls' pre pending target cp ct, cp+1+ct = cost ∧
    List.Forall₂ (· ≈ ·) ls ls' ∧
    List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args (pre ++ pending) ∧
    ScopedComputeCount (PiInertStage D n) cp Δ
      (ProofShape.mkApps (.const c ls) args) (ProofShape.mkApps (.const c ls') (pre ++ pending)) ∧
    PiInertStage D n Δ (ProofShape.mkApps (.const c ls') pre) target ∧
    ¬ LevelPrimitive univs (ProofShape.mkApps (.const c ls') pre) target ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) out ∧
    TypedSource Δ (ProofShape.mkApps (.const c ls') pre)

/-- Excluding the retained fresh-slot form forces a non-level body-spine
root. Minimum count makes its decomposition exact. The output can be any
intermediate body endpoint, including a lambda awaiting its continuation. -/
theorem pi_inert_eta_body_spine_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource (A :: Δ)
      (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)))
    (RB : ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) body')
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) body' → cb ≤ j)
    (hretain : ∀ g cg, cg ≤ cb →
      ScopedComputeCount (PiInertStage D m) cg (A :: Δ)
        ((ProofShape.mkApps (.const c ls) pre).liftN 1) g →
      body' = .app g (etaArgument u) → False) :
    CountedNonlevelSpineRoot D m (A :: Δ) c ls (pre.map (·.liftN 1) ++ [etaArgument u]) body' cb := by
  have RBspine : ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
      (ProofShape.mkApps (.const c ls) (pre.map (·.liftN 1) ++ [etaArgument u])) body' := by
    simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RB
  rcases RBspine.const_spine_components_or_cut (U := univs) with
    ⟨ls', rawArgs, ch, cc, hcomponents, EO, _, RH, RA⟩ |
    ⟨ls', bodyPre, bodyPending, target, cp, ct, hcut, HL, HA, RP, HR, HN, RT⟩
  · obtain ⟨pre', slot', cp', cx', rfl, hargs, Rpre, Rslot⟩ := RA.snoc_inv
    obtain rfl := eta_argument_fixed Rslot.forget
    have RG : ScopedComputeCount (PiInertStage D m) (ch+cp') (A :: Δ)
        ((ProofShape.mkApps (.const c ls) pre).liftN 1) (ProofShape.mkApps (.const c ls') pre') := by
      simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using RH.mkApps Rpre
    exact (hretain _ _ (by omega) RG (by simpa only [ProofShape.mkApps_snoc] using EO)).elim
  · have RT' := ((ScopedComputeCount.base HR).mkApps ScopedArgumentsCount.refl).trans RT
    rw [← ProofShape.mkApps_append] at RT'
    have HM := hmin m (cp+1+ct) (by
      simpa only [Nat.add_zero, ← Nat.add_assoc, ProofShape.mkApps_snoc,
        ProofShape.liftN_mkApps, ProofShape.liftN] using RP.trans RT')
    refine ⟨ls', bodyPre, bodyPending, target, cp, ct, by omega, HL, HA, RP, HR, HN, RT, ?_⟩
    apply RP.forget.spine_cut_source_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs m))
    simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using HT

end Lean4Lean.VEnv.Strengthening
