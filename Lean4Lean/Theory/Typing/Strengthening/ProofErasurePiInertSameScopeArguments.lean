import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLeastFailureConsumedRoot

/-! # Flatten same-scope projection frames with their arguments

Only identity application frames remain in the observer's scope. Their argument
vectors concatenate, their computations concatenate under the later arguments,
and their predicate agrees with projection after that combined application at
every raw candidate and count. Actual typing is reconstructed backwards through
application spines; no typing is required of competing candidates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Move an actual application typing backwards along a typed function
computation. Non-proof reflection aligns the computed function with the
application's independent typed representative in the same erased context. -/
theorem TypedSource.compute_app_backward
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ f) (R : ScopedCompute Step Δ f g)
    (HX : TypedSource Δ (.app g x)) : TypedSource Δ (.app f x) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HX
  obtain ⟨g₀, x₀, rfl, hn, Eg, Ex⟩ := erase_app_inv Ee
  obtain ⟨A, B, hg, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨Γ', f₀, F, hΓ', EΓ', hf, Ef⟩ := HT
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  have hf' := hf.defeqDFC henv W
  have Ef' := (proofErase_defeqCtx hΓ' W hf).symm.trans Ef
  obtain ⟨f₁, HF, EF⟩ := proofErase_scoped_compute_realize hstep hΓ hf' EΓ Ef' R
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg HF.hasType.2 (Eg.trans EF.symm)).2
    (not_isProof_fn hΓ hg hx hn)
  have hf₁ := ((HE.defeq hΓ).of_l henv hΓ hg).hasType.2
  have hfPi := hf'.defeqU_r henv hΓ (HF.hasType.2.uniqU henv hΓ hf₁)
  have happ := hfPi.app hx
  have hn' : ¬ IsProof Γ (.app f₀ x₀) := by
    rintro ⟨P, hP, hProp⟩
    exact hn ⟨P, (hg.app hx).defeqU_r henv hΓ (happ.uniqU henv hΓ hP), hProp⟩
  exact ⟨Γ, .app f₀ x₀, _, hΓ, EΓ, happ, by simp only [proofErase, if_neg hn', Ef', Ex]⟩

/-- Backwards application typing extends to any finite pending vector. -/
theorem TypedSource.compute_mkApps_backward
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ f) (R : ScopedCompute Step Δ f g)
    (HX : TypedSource Δ (ProofShape.mkApps g args)) :
    TypedSource Δ (ProofShape.mkApps f args) := by
  induction args using List.snoc_induction with
  | nil => exact HT
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at HX ⊢
    have HTg := (ScopedHole.appFn .hole x).typed HX
    have HTf := ih HTg
    exact TypedSource.compute_app_backward hstep HTf (R.mkApps (List.Forall₂.rfl (fun _ _ => .refl))) HX

/-- In the observer's scope, all remaining arguments and computations flatten
into one actual major path and its final projection. The continuation predicate
is exactly projected computation at the combined application for every raw
candidate and budget; actual typing is needed only for the chosen execution. -/
theorem PiInertProjectionContinuationRun.same_scope_arguments
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hscope : Δ = Ω) :
    ∃ args stage cb major observerStage co, cb+co = ck ∧
      TypedSource Δ (ProofShape.mkApps e args) ∧
      ScopedComputeCount (PiInertStage D stage) cb Δ (ProofShape.mkApps e args) major ∧
      TypedSource Δ (.proj family index major) ∧
      ScopedComputeCount (PiInertStage D observerStage) co Δ (.proj family index major) out ∧
      ∀ candidate cost, K candidate cost ↔
        PiInertProjectionContinuation D Δ family index out (ProofShape.mkApps candidate args) cost := by
  induction H with
  | projection HT HP R => exact ⟨[], 0, 0, _, _, _, by omega, HT, .beta .refl, HP, R,
      fun _ _ => Iff.rfl⟩
  | @application Δ e Θ τ args n cs e' K ck HT W HNext RNext HK ih =>
    cases W with
    | identity =>
      obtain ⟨rest, stage, cb, major, observerStage, co, hc, HTall, RB, HP, RO, EP⟩ := ih hscope
      have RNext' : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps e args) e' := by
        simpa only [ProofShape.subst_id] using RNext
      have HNext' : TypedSource Δ (ProofShape.mkApps e args) := by
        simpa only [ProofShape.subst_id] using HNext
      have HTwhole := TypedSource.compute_mkApps_backward
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
        HNext' RNext'.forget HTall
      have RPrefix := RNext'.mkApps (ScopedArgumentsCount.refl (args := rest))
      have RAll := (RPrefix.mono (pi_inert_stage_mono (Nat.le_max_left n stage))).trans
        (RB.mono (pi_inert_stage_mono (Nat.le_max_right n stage)))
      refine ⟨args ++ rest, _, cs+cb, major, observerStage, co, by omega,
        by simpa only [ProofShape.mkApps_append] using HTwhole,
        by simpa only [ProofShape.mkApps_append, Nat.add_zero] using RAll, HP, RO, ?_⟩
      intro candidate cost
      constructor
      · rintro ⟨later, j, endpoint, k, hsum, RJ, RK⟩
        obtain ⟨tailStage, RL⟩ := (EP endpoint k).1 RK
        have RJ' := RJ.mkApps (ScopedArgumentsCount.refl (args := rest))
        have RR := (RJ'.mono (pi_inert_stage_mono (Nat.le_max_left later tailStage))).proj.trans
          (RL.mono (pi_inert_stage_mono (Nat.le_max_right later tailStage)))
        exact ⟨_, by simpa only [ProofShape.subst_id, ProofShape.mkApps_append, Nat.add_zero, hsum] using RR⟩
      · rintro ⟨later, RJ⟩
        refine ⟨later, 0, ProofShape.mkApps candidate args, cost, by omega, ?_, ?_⟩
        · simpa only [ProofShape.subst_id] using
            (ScopedComputeCount.beta (Step := PiInertStage D later) (Δ := Δ)
              (BetaRed.refl (e := ProofShape.mkApps candidate args)))
        · apply (EP _ _).2
          exact ⟨later, by simpa only [ProofShape.mkApps_append] using RJ⟩
    | inst =>
      have HL := HK.scope_length_le
      have HE := congrArg List.length hscope
      simp only [List.length_cons] at HE
      omega
  | retained _ _ _ _ HK ih =>
    have HL := HK.scope_length_le
    have HE := congrArg List.length hscope
    simp only [List.length_cons] at HE
    omega

end Lean4Lean.VEnv.Strengthening
