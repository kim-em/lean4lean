import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTrackedHeadHole

/-! # Focus actual computation through application and binder holes

Retained prefixes produce only function-application and lambda-body holes.
Reify these as typed continuation frames. Every competitor in the focused
continuation composes back to the original path with exactly the same cost.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- The precise hole grammar produced by retained prefixes and pending
arguments. It excludes arbitrary argument positions and identity payloads. -/
inductive SpineBinderHole : {Δ Θ : List ProofShape} → ScopedHole Δ Θ → Prop where
  | hole : SpineBinderHole (.hole : ScopedHole Δ Δ)
  | appFn {C : ScopedHole Δ Θ} : SpineBinderHole C → SpineBinderHole (.appFn C x)
  | lamBody {C : ScopedHole (A :: Δ) Θ} : SpineBinderHole C → SpineBinderHole (.lamBody A C)

/-- Every application/binder hole follows the tracked head. -/
theorem SpineBinderHole.tracked (H : SpineBinderHole C) : TrackedHeadHole C := by
  induction H with
  | hole => exact .hole
  | appFn _ ih => exact .appFn ih
  | lamBody _ ih => exact .lamBody ih

variable [Params]

private theorem identity_interpretation : ContextSubstitution Δ Δ ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  have W : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ) ProofShape.Subst.id :=
    ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ))
  simpa only [EΓ] using W hΓ rfl

private theorem typed_lambda_domain (HT : TypedSource Δ (.lam A body)) :
    ∃ u, DomainSort Δ A u := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, hA⟩, _, _⟩ := ht.lam_inv henv hΓ
  exact ⟨u, Γ, A₀, hΓ, rfl, hA, EA⟩

/-- A continuation absorbs any additional computation in its own input
scope, with additive primitive count. This property does not substitute the
added path or constrain competitors by typing. -/
def PiInertPrefixClosed (D : Definitions) (Δ : List ProofShape)
    (K : ProofShape → Nat → Prop) : Prop :=
  ∀ n j a b k, ScopedComputeCount (PiInertStage D n) j Δ a b → K b k → K a (j+k)

/-- An application with identity endpoint substitution absorbs computation
of its function in the same scope. The pending arguments are held fixed. -/
theorem pi_inert_identity_application_prefix_closed :
    PiInertPrefixClosed D Δ (PiInertApplicationContinuation D Δ ProofShape.Subst.id args K) := by
  rintro n j a b k RJ ⟨m, ct, endpoint, ck, hc, RT, HK⟩
  refine ⟨max n m, j+ct, endpoint, ck, by omega, ?_, HK⟩
  have RP := (RJ.mono (pi_inert_stage_mono (Nat.le_max_left n m))).mkApps
    (ScopedArgumentsCount.refl (args := args))
  have RT' : ScopedComputeCount (PiInertStage D (max n m)) ct Δ
      (ProofShape.mkApps b args) endpoint := by
    simpa only [ProofShape.subst_id] using (RT.mono (pi_inert_stage_mono (Nat.le_max_right n m)))
  simpa only [ProofShape.subst_id, Nat.add_zero] using RP.trans RT'

/-- Focusing through the precise retained-hole grammar constructs an actual
typed continuation at the inner endpoint. Each focused competitor maps back
to the original predicate with the identical count; the focused predicate is
also closed under preceding computation in its own scope. -/
theorem SpineBinderHole.focus_continuation {C : ScopedHole Δ Θ}
    (HC : SpineBinderHole C)
    (HK : PiInertTypedContinuationRun D Ω out Δ K (C.plug e) ck)
    (Hclose : PiInertPrefixClosed D Δ K) :
    ∃ L, PiInertTypedContinuationRun D Ω out Θ L e ck ∧
      PiInertPrefixClosed D Θ L ∧ ∀ body k, L body k → K (C.plug body) k := by
  induction HC generalizing K ck with
  | hole => exact ⟨K, HK, Hclose, fun _ _ H => H⟩
  | @appFn Δ Θ x C HC ih =>
    have HT : TypedSource Δ (.app (C.plug e) x) := HK.typed
    have HTf : TypedSource Δ (C.plug e) := (ScopedHole.appFn .hole x).typed HT
    have HR : PiInertTypedContinuationRun D Ω out Δ
        (PiInertApplicationContinuation D Δ ProofShape.Subst.id [x] K) (C.plug e) ck := by
      have R : ScopedComputeCount (PiInertStage D 0) 0 Δ
          (ProofShape.mkApps ((C.plug e).subst ProofShape.Subst.id) [x]) (.app (C.plug e) x) := by
        simpa only [ProofShape.subst_id, ProofShape.mkApps] using
          (ScopedComputeCount.beta (Step := PiInertStage D 0) (Δ := Δ)
            (BetaRed.refl (e := .app (C.plug e) x)))
      simpa only [Nat.zero_add] using PiInertTypedContinuationRun.application HTf
        (.identity identity_interpretation) (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HT) R HK
    obtain ⟨L, HL, HLC, EL⟩ := ih HR pi_inert_identity_application_prefix_closed
    refine ⟨L, HL, HLC, ?_⟩
    intro body k H
    obtain ⟨n, j, endpoint, l, hc, R, HK'⟩ := EL body k H
    have HH := Hclose n j (.app (C.plug body) x) endpoint l
      (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using R) HK'
    simpa only [hc, ScopedHole.plug] using HH
  | @lamBody A Δ Θ C HC ih =>
    have HT : TypedSource Δ (.lam A (C.plug e)) := HK.typed
    have HTb : TypedSource (A :: Δ) (C.plug e) := (ScopedHole.lamBody A .hole).typed HT
    obtain ⟨u, SD⟩ := typed_lambda_domain HT
    have HR : PiInertTypedContinuationRun D Ω out (A :: Δ)
        (fun body k => K (.lam A body) k) (C.plug e) ck :=
      .retained (args := []) HTb SD
        (ScopedComputeCount.beta (Step := PiInertStage D 0) (BetaRed.refl (e := A)))
        identity_interpretation HK
    have HLC : PiInertPrefixClosed D (A :: Δ) (fun body k => K (.lam A body) k) := by
      intro n j a b k RJ HK'
      have R : ScopedComputeCount (PiInertStage D n) j Δ (.lam A a) (.lam A b) := by
        simpa only [Nat.zero_add] using
          (ScopedComputeCount.beta (Step := PiInertStage D n) (BetaRed.refl (e := A))).lam RJ
      exact Hclose n j _ _ k R HK'
    obtain ⟨L, HL, HC, EL⟩ := ih HR HLC
    exact ⟨L, HL, HC, EL⟩

/-- Focus a complete selected path and remaining typed run onto the hole's
input. Every focused competitor reassembles into a path from the same outer
source followed by the same original continuation, at exactly its count. -/
theorem SpineBinderHole.focus_path {C : ScopedHole Δ Θ}
    (HC : SpineBinderHole C) (HT : TypedSource Δ (C.plug e))
    (R : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug e) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck) :
    ∃ L, PiInertTypedContinuationRun D Ω out Θ L e (ct+ck) ∧
      PiInertPrefixClosed D Θ L ∧
      ∀ body k, L body k → ∃ later j tail l, j+l = k ∧
        ScopedComputeCount (PiInertStage D later) j Δ (C.plug body) tail ∧ K tail l := by
  have HR : PiInertTypedContinuationRun D Ω out Δ
      (PiInertApplicationContinuation D Δ ProofShape.Subst.id [] K) (C.plug e) (ct+ck) :=
    .application HT (.identity identity_interpretation)
      (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HT)
      (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using R) HK
  obtain ⟨L, HL, HLC, EL⟩ := HC.focus_continuation HR pi_inert_identity_application_prefix_closed
  refine ⟨L, HL, HLC, ?_⟩
  intro body k H
  simpa only [PiInertApplicationContinuation, ProofShape.subst_id, ProofShape.mkApps] using EL body k H

/-- A minimum at a whole application/binder hole focuses to a typed minimum
at its inner source with exactly the same budget. This is a non-increasing
scope move, not a strict-decrease claim. The original whole-path minimum
ranges over all stages, endpoints and original continuation competitors. -/
theorem SpineBinderHole.focus_minimum {C : ScopedHole Δ Θ}
    (HC : SpineBinderHole C) (HT : TypedSource Δ (C.plug e))
    (R : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug e) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hmin : ∀ later j tail l, ScopedComputeCount (PiInertStage D later) j Δ
      (C.plug e) tail → K tail l → ct+ck ≤ j+l) :
    PiInertTypedContinuationMinimum D Ω out Θ e (ct+ck) := by
  obtain ⟨L, HL, HLC, EL⟩ := HC.focus_path HT R HK
  refine ⟨L, 0, 0, ct+ck, e, HL.typed, .beta .refl, HL, by omega, ?_⟩
  intro later j body k RJ HK'
  obtain ⟨m, c, tail, l, hc, RT, HK''⟩ := EL e (j+k) (HLC later j e body k RJ HK')
  have HH := hmin m c tail l RT HK''
  omega

end Lean4Lean.VEnv.Strengthening
