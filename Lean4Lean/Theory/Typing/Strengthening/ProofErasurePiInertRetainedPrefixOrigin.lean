import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaFrameOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertNextApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTrackedHeadHole

/-! # Locate a retained origin across a finite enclosing prefix

The exact endpoint substitution lifts beneath every retained binder after its
recorded annotation conversion. A tracked hole records the enclosing syntax;
the resulting equation holds for every competing endpoint, not just the
selected execution. Only ordinary context interpretations are composed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

private theorem tracked_spine {C : ScopedHole Δ Θ}
    (HC : TrackedHeadHole C) (args : List ProofShape) :
    ∃ C' : ScopedHole Δ Θ, TrackedHeadHole C' ∧
      ∀ e, C'.plug e = ProofShape.mkApps (C.plug e) args := by
  induction args using List.snoc_induction with
  | nil => exact ⟨C, HC, fun _ => rfl⟩
  | snoc args x ih =>
    obtain ⟨C', HC', EC⟩ := ih
    refine ⟨.appFn C' x, .appFn HC', ?_⟩
    intro e
    simp only [ScopedHole.plug, ProofShape.mkApps_snoc, EC]

private theorem tracked_compose {C : ScopedHole Δ Θ} {B : ScopedHole Θ Ξ}
    (HC : TrackedHeadHole C) (HB : TrackedHeadHole B) :
    ∃ C' : ScopedHole Δ Ξ, TrackedHeadHole C' ∧
      ∀ e, C'.plug e = C.plug (B.plug e) := by
  induction HC with
  | hole => exact ⟨B, HB, fun _ => rfl⟩
  | @appFn Δ Θ x C HC ih =>
    obtain ⟨C', HC', EC⟩ := ih HB
    exact ⟨.appFn C' x, .appFn HC', fun e => congrArg (fun f => ProofShape.app f x) (EC e)⟩
  | lamBody _ ih =>
    obtain ⟨C', HC', EC⟩ := ih HB
    exact ⟨.lamBody _ C', .lamBody HC', fun e => congrArg (ProofShape.lam _) (EC e)⟩
  | @identity Δ Θ A C HC ih =>
    obtain ⟨C', HC', EC⟩ := ih HB
    exact ⟨.appArg (.lam A (.bvar 0)) C', .identity HC', fun e => congrArg (ProofShape.app (.lam A (.bvar 0))) (EC e)⟩

variable [Params]

/-- An arbitrary retained prefix and its next endpoint substitution determine
one tracked hole and one interpreted substitution into its exact binder
context. The equation is uniform in the endpoint. Each annotation conversion
is composed with the lifted later substitution; no guarded computation or
native recovery certificate is transported. -/
theorem PiInertRetainedPrefix.substitution_hole
    (HP : PiInertRetainedPrefix D Δ Θ plug)
    (W : ContextSubstitution Θ Ξ τ) :
    ∃ Λ σ, ∃ C : ScopedHole Ξ Λ, TrackedHeadHole C ∧
      ContextSubstitution Δ Λ σ ∧ ∀ e, (plug e).subst τ = C.plug (e.subst σ) := by
  induction HP with
  | refl => exact ⟨Ξ, τ, .hole, .hole, W, fun _ => rfl⟩
  | @retained Δ A u n cd A' plug Θ args SD RD WI HP ih =>
    obtain ⟨Λ, σ, C, HC, WS, EC⟩ := ih W
    have WB : ContextSubstitution (A :: Δ) (A'.subst σ :: Λ) σ.lift := by
      intro Γ hΓ EΓ
      simpa only [ProofShape.Subst.id, ProofShape.subst] using
        (ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') WS) hΓ EΓ)
    obtain ⟨B, HB, EB⟩ := tracked_spine
      (TrackedHeadHole.lamBody (A := A'.subst σ) (.hole : TrackedHeadHole
        (.hole : ScopedHole (A'.subst σ :: Λ) (A'.subst σ :: Λ))))
      (args.map (·.subst σ))
    obtain ⟨C', HC', EC'⟩ := tracked_compose HC HB
    refine ⟨A'.subst σ :: Λ, σ.lift, C', HC', WB, ?_⟩
    intro e
    rw [EC, EC', EB]
    simp only [ProofShape.subst_mkApps, ProofShape.subst, ScopedHole.plug]

/-- Pending arguments extend the same tracked hole, while leaving its inner
context interpretation unchanged. This is the exact source of the next
application computation for every competing endpoint. -/
theorem PiInertRetainedPrefix.application_hole
    (HP : PiInertRetainedPrefix D Δ Θ plug)
    (W : ContextSubstitution Θ Ξ τ) (args : List ProofShape) :
    ∃ Λ σ, ∃ C : ScopedHole Ξ Λ, TrackedHeadHole C ∧
      ContextSubstitution Δ Λ σ ∧
      ∀ e, ProofShape.mkApps ((plug e).subst τ) args = C.plug (e.subst σ) := by
  obtain ⟨Λ, σ, C, HC, WS, EC⟩ := HP.substitution_hole W
  obtain ⟨C', HC', EC'⟩ := tracked_spine HC args
  exact ⟨Λ, σ, C', HC', WS, fun e => by rw [EC, EC']⟩

/-- The next actual application represented by its enclosing tracked hole
and exact substitution at the inner endpoint. The predicate equivalence keeps
the original continuation fixed on every competitor, so the recorded path
cannot be replaced by an unrelated existential minimum. -/
def PiInertNextApplicationAtHole (D : Definitions) (Ω : List ProofShape) (out : ProofShape)
    (Δ : List ProofShape) (K : ProofShape → Nat → Prop) (e : ProofShape) (ck : Nat) : Prop :=
    ∃ Ξ Λ σ, ∃ C : ScopedHole Ξ Λ, ∃ n cs endpoint ck' K',
      TrackedHeadHole C ∧ ContextSubstitution Δ Λ σ ∧
      TypedSource Ξ (C.plug (e.subst σ)) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ (C.plug (e.subst σ)) endpoint ∧
      PiInertTypedContinuationRun D Ω out Ξ K' endpoint ck' ∧ cs+ck' = ck ∧
      ∀ body k, K body k ↔ ∃ later j tail l, j+l = k ∧
        ScopedComputeCount (PiInertStage D later) j Ξ (C.plug (body.subst σ)) tail ∧
        K' tail l

/-- Locate the selected endpoint inside the next actual application after any
retained prefix. The original continuation is identified pointwise with paths
from the substituted endpoint in this hole, preserving all competitors and
exact continuation costs. -/
theorem PiInertNextApplication.substitution_hole
    (H : PiInertNextApplication D Ω out Δ K e ck) :
    PiInertNextApplicationAtHole D Ω out Δ K e ck := by
  obtain ⟨Θ, Ξ, τ, args, plug, n, cs, endpoint, ck', K', HP, W, _, HT, R, HK, hc, EK⟩ := H
  obtain ⟨Λ, σ, C, HC, WS, EC⟩ := HP.application_hole W args
  refine ⟨Ξ, Λ, σ, C, n, cs, endpoint, ck', K', HC, WS, EC e ▸ HT, EC e ▸ R, HK, hc, ?_⟩
  intro body k
  simpa only [PiInertApplicationContinuation, EC] using EK body k

/-- The hole presentation preserves the full joint minimum with a preceding
path in its original scope. The next computation has exactly the original
continuation budget, hence is strictly smaller when that preceding path has
positive cost. No preceding guarded computation is substituted. -/
theorem PiInertNextApplicationAtHole.joint_minimum
    (H : PiInertNextApplicationAtHole D Ω out Δ K e ck)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (hcost : cb+ck = cost)
    (hmin : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Δ source body →
      K body k → cost ≤ j+k) :
    ∃ Ξ Λ σ, ∃ C : ScopedHole Ξ Λ, ∃ suffixStage cs endpoint ck' K',
      TrackedHeadHole C ∧ ContextSubstitution Δ Λ σ ∧
      TypedSource Ξ (C.plug (e.subst σ)) ∧
      ScopedComputeCount (PiInertStage D suffixStage) cs Ξ (C.plug (e.subst σ)) endpoint ∧
      PiInertTypedContinuationRun D Ω out Ξ K' endpoint ck' ∧ cs+ck' = ck ∧
      PiInertTypedContinuationMinimum D Ω out Ξ (C.plug (e.subst σ)) ck ∧
      (0 < cb → ck < cost) ∧
      ∀ firstStage later j body k tail l,
        ScopedComputeCount (PiInertStage D firstStage) j Δ source body →
        ScopedComputeCount (PiInertStage D later) k Ξ (C.plug (body.subst σ)) tail →
        K' tail l → cost ≤ j+k+l := by
  obtain ⟨Ξ, Λ, σ, C, suffixStage, cs, endpoint, ck', K', HC, WS, HT, RT, HK, hc, EK⟩ :=
    H
  have HM : PiInertTypedContinuationMinimum D Ω out Ξ (C.plug (e.subst σ)) ck := by
    refine ⟨K', suffixStage, cs, ck', endpoint, HT, RT, HK, hc, ?_⟩
    intro later j tail l RJ HL
    have HH := hmin n cb e (j+l) R ((EK e (j+l)).2 ⟨later, j, tail, l, rfl, RJ, HL⟩)
    omega
  refine ⟨Ξ, Λ, σ, C, suffixStage, cs, endpoint, ck', K', HC, WS, HT, RT, HK, hc,
    HM, (by omega), ?_⟩
  intro firstStage later j body k tail l RJ RK HL
  have HH := hmin firstStage j body (k+l) RJ ((EK body (k+l)).2 ⟨later, k, tail, l, rfl, RK, HL⟩)
  omega

/-- Ordinary eta origin survives any finite retained prefix before the next
application. The actual next path starts in a tracked hole containing the
substituted eta lambda. Its exact original argument supply is built into that
hole, and the continuation equivalence holds for every replacement lambda.
Following computation inside or through this hole still requires a subsequent
origin/target-agreement argument. -/
theorem PiInertNextApplication.eta_origin
    (H : PiInertNextApplication D Ω out Δ K
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) ck)
    (HO : TypedEtaOrigin Δ A f u) :
    ∃ Ξ Λ σ, ∃ C : ScopedHole Ξ Λ, ∃ n cs endpoint ck' K',
      TrackedHeadHole C ∧ ContextSubstitution Δ Λ σ ∧
      TypedEtaOrigin Λ (A.subst σ) (f.subst σ) u ∧
      TypedSource Ξ (C.plug (.lam (A.subst σ) (.app ((f.subst σ).liftN 1) (etaArgument u)))) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ
        (C.plug (.lam (A.subst σ) (.app ((f.subst σ).liftN 1) (etaArgument u)))) endpoint ∧
      PiInertTypedContinuationRun D Ω out Ξ K' endpoint ck' ∧ cs+ck' = ck ∧
      ∀ q k, K (ProofShape.mkApps q args) k ↔ ∃ later j tail l, j+l = k ∧
        ScopedComputeCount (PiInertStage D later) j Ξ (C.plug (q.subst σ)) tail ∧
        K' tail l := by
  obtain ⟨Ξ, Λ, σ, C, n, cs, endpoint, ck', K', HC, WS, HT, RT, HK, hc, EK⟩ := H.substitution_hole
  obtain ⟨B, HB, EB⟩ := tracked_spine (.hole : TrackedHeadHole (.hole : ScopedHole Λ Λ))
    (args.map (·.subst σ))
  obtain ⟨C', HC', EC⟩ := tracked_compose HC HB
  have EE : ∀ q, C'.plug (q.subst σ) = C.plug ((ProofShape.mkApps q args).subst σ) := by
    intro q
    rw [EC, EB]
    simp only [ScopedHole.plug, ProofShape.subst_mkApps]
  have Eeta : (ProofShape.lam A (.app (f.liftN 1) (etaArgument u))).subst σ =
      .lam (A.subst σ) (.app ((f.subst σ).liftN 1) (etaArgument u)) := by
    simp only [ProofShape.subst, ProofShape.lift_subst_lift, ProofShape.etaArgument_subst]
  refine ⟨Ξ, Λ, σ, C', n, cs, endpoint, ck', K', HC', WS, HO.subst WS, ?_, ?_, HK, hc, ?_⟩
  · rw [← Eeta, EE]
    exact HT
  · rw [← Eeta, EE]
    exact RT
  · intro q k
    simpa only [← EE] using EK (ProofShape.mkApps q args) k

end Lean4Lean.VEnv.Strengthening
