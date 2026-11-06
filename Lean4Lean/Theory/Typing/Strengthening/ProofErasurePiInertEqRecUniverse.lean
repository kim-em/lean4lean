import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUniverseConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecCarrier

/-! # Reversible guarded conversion at universe-valued Eq recursors

The earlier Eq computation supplies the backward carrier prefix. Universe
exposure supplies forward transport from an arbitrary completed history.
Together they give an equivalence, not just construction from a minor history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Increasing the stage of interpreted evidence preserves its typed output
and its ordinary-core tails, or all independently computed comparison pairs. -/
theorem PiInertInterpret.raise (hle : n ≤ m) (H : PiInertInterpret D n kind Δ a b) :
    PiInertInterpret D m kind Δ a b := by
  cases kind with
  | compute =>
    refine ⟨H.1, ?_⟩
    intro out R
    obtain ⟨shared, RA, RB⟩ := H.2 R
    exact ⟨shared, RA.mono (fun R => pi_inert_stage_mono hle R), RB⟩
  | compare mode =>
    intro left right RA RB
    exact (H RA RB).mono (fun R => pi_inert_stage_mono hle R)

/-- Raising the guard bound retains every future typed substitution. -/
theorem PiInertEvidence.raise (hle : n ≤ m) (H : PiInertEvidence D n kind Δ a b) :
    PiInertEvidence D m kind Δ a b :=
  ⟨PiInertInterpret.raise hle H.base, fun W => PiInertInterpret.raise hle (H.future W)⟩

/-- At any stage containing the directed computation, universe exposure gives
equivalent whole histories before and after it. The forward direction consumes
an arbitrary completed old history; the reverse uses the certified prefix. -/
theorem pi_inert_guarded_universe_histories_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (hv : v.WF univs)
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (RC : PiInertEvidence D k .compute (proofEraseCtx Γ)
      (proofErase Γ C) (proofErase Γ (.sort v))) (hle : k ≤ n) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C) (proofErase Γ a) (proofErase Γ b) ↔
      PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.sort v))
        (proofErase Γ a) (proofErase Γ b) :=
  ⟨fun H => H.compute_to_universe heq hs hΓ hC hv ha hb RC.base,
    fun H => PiInertCarrierHistory.carrier_prefix (RC.raise hle) H⟩

/-- A universe-valued Eq recursor supports reversible carrier conversion for
arbitrary completed histories. Its index child is an earlier carrier history,
so indices may be unit-like or function-extensional rather than computationally
joined. No ordinary-core reduction of the recursor is required. -/
theorem pi_inert_eq_rec_universe_histories_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M (.sort z) b p) (.sort u))
    (hx : env.HasType univs Γ x (eqRecApp v w α a M (.sort z) b p))
    (hy : env.HasType univs Γ y (eqRecApp v w α a M (.sort z) b p))
    (HI : PiInertCarrierHistory D k (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) (hle : k+1 ≤ n) :
    PiInertCarrierHistory D n (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M (.sort z) b p)) (proofErase Γ x) (proofErase Γ y) ↔
      PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.sort z))
        (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨_, _, _, _, _, hm, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  exact pi_inert_guarded_universe_histories_iff heq hs hΓ hr (hm.sort_inv henv.ordered) hx hy
    (HI.eq_rec heq hs hl hcon hreg hoff hD hΓ hr) hle

omit [Params] in
/-- Actual canonical-Eq environments discharge all primitive and registration
premises for reversible universe-valued Eq carrier conversion. -/
theorem EnvironmentCore.eq_rec_universe_histories_iff {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ v w α a M z b p u x y k n}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (eqRecApp v w α a M (.sort z) b p) (.sort u) →
      env.HasType U Γ x (eqRecApp v w α a M (.sort z) b p) →
      env.HasType U Γ y (eqRecApp v w α a M (.sort z) b p) →
      PiInertCarrierHistory definitions k (proofEraseCtx Γ) (proofErase Γ α)
        (proofErase Γ a) (proofErase Γ b) → k+1 ≤ n →
      (PiInertCarrierHistory definitions n (proofEraseCtx Γ)
        (proofErase Γ (eqRecApp v w α a M (.sort z) b p)) (proofErase Γ x) (proofErase Γ y) ↔
      PiInertCarrierHistory definitions n (proofEraseCtx Γ) (proofErase Γ (.sort z))
        (proofErase Γ x) (proofErase Γ y)) := by
  letI := henv.params U
  intro Γ v w α a M z b p u x y k n heq hΓ hr hx hy HI hle
  obtain ⟨data, hlookup, hrec, hn, _⟩ := heq.recursorRegistration henv
  exact pi_inert_eq_rec_universe_histories_iff heq sound (levelCompatible (fun H => H))
    (fun H => H) hlookup (hrec.eqRec_target heq hn).2.1 (no_eqRec heq) hΓ hr hx hy HI hle

end Lean4Lean.VEnv.Strengthening
