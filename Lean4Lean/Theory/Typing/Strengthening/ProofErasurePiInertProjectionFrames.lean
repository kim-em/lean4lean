import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionExposure

/-! # Projection factorization with surviving administrative frames

Every sorted projection path, including a path ending under lambda-headed
wrappers, has a terminal projection factorization after finitely many tracked
head deletions. These deletions are beta reductions, not a normalization
assumption. The major path retains its exact original stage and scope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual

/-- Deleting a tracked identity is a compatible beta reduction, including
when the tracked payload survives inside other administrative frames. -/
theorem IdentityHeadDeletion.reduce (H : IdentityHeadDeletion e lower) : BetaRed e lower := by
  induction H with
  | refl => exact .refl
  | drop =>
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons] using
      (ProofShape.BetaRed.beta (A := _) (b := .bvar 0) (a := _))
  | app _ ih => exact .app ih .refl
  | lam _ ih => exact .lam .refl ih
  | identity _ ih => exact .app .refl ih

/-- A finite trace of surviving administrative head deletions. This relation
records which beta contractions are used, without allowing arbitrary beta
normalization or any transport of guarded primitive certificates. -/
inductive AdministrativeHeadDeletion : ProofShape → ProofShape → Prop where
  | refl : AdministrativeHeadDeletion e e
  | constant : ConstantHeadDeletion e lower → AdministrativeHeadDeletion e lower
  | identity : IdentityHeadDeletion e lower → AdministrativeHeadDeletion e lower
  | trans : AdministrativeHeadDeletion e middle → AdministrativeHeadDeletion middle lower →
      AdministrativeHeadDeletion e lower

/-- The recorded administrative deletions give a finite compatible beta path. -/
theorem AdministrativeHeadDeletion.reduce (H : AdministrativeHeadDeletion e lower) :
    BetaRed e lower := by
  induction H with
  | refl => exact .refl
  | constant H => exact H.reduce
  | identity H => exact H.reduce
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- At a non-lambda-headed endpoint every tracked administrative deletion has
already been consumed. This recovers exact endpoints for exposed outputs. -/
theorem AdministrativeHeadDeletion.eq_of_nonlambda (H : AdministrativeHeadDeletion e lower)
    (hout : ∀ A b args, e ≠ ProofShape.mkApps (.lam A b) args) : e = lower := by
  induction H with
  | refl => rfl
  | constant H =>
    rcases H.eq_or_lambda with E | ⟨A, b, args, E⟩
    · exact E
    · exact (hout A b args E).elim
  | identity H =>
    rcases H.eq_or_lambda with E | ⟨A, b, args, E⟩
    · exact E
    · exact (hout A b args E).elim
  | trans _ _ ih₁ ih₂ =>
    have E := ih₁ hout
    exact E.trans (ih₂ (E ▸ hout))

variable [Params] {D : Definitions}

/-- Bypass either administrative root expansion without restricting the final
output. A surviving wrapper is recorded at the output, and the simulated
source path uses no more primitives than the original tail. -/
theorem pi_inert_expansion_count_bypass_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ target)
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ target out) :
    ∃ lower k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ source lower ∧
      AdministrativeHeadDeletion out lower := by
  rcases H with H | H
  · cases H with
    | intro _ =>
      obtain ⟨lower, k, hk, RK, HK⟩ :=
        ConstantHeadDeletion.compute heq hs .drop HT RT
      exact ⟨lower, k, hk, RK, .constant HK⟩
  · cases H with
    | intro _ =>
      obtain ⟨lower, k, hk, RK, HK⟩ := IdentityHeadDeletion.compute .drop RT
      exact ⟨lower, k, hk, RK, .identity HK⟩

/-- A sorted projection computation can be factored after a finite trace of
administrative endpoint deletions. The counted factorization either retains
the projection or exposes a genuine selection. Removing a root wrapper makes
the induction strictly decrease even when its endpoint wrapper survives. -/
theorem pi_inert_sorted_projection_frames_count
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj s i m) out) :
    ∃ lower, AdministrativeHeadDeletion out lower ∧
      ((∃ major k, k ≤ cost ∧ lower = .proj s i major ∧
          ScopedComputeCount (PiInertStage D n) k Δ m major) ∨
       ∃ major field before after, before + 1 + after ≤ cost ∧
          ScopedComputeCount (PiInertStage D n) before Δ m major ∧
          Primitive D (.proj s i major) field ∧
          ScopedComputeCount (PiInertStage D n) after Δ field lower) := by
  induction cost using Nat.strongRecOn generalizing m out with
  | ind cost ih =>
    rcases R.projection_first_root with ⟨major, EO, RM⟩ |
        ⟨major, target, before, after, HC, RM, RP, RT⟩
    · exact ⟨out, .refl, .inl ⟨major, cost, by omega, EO, RM⟩⟩
    have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
      fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
        hΓ hΓ' W ht R.1
    have HT' : ControlTyping Δ (.proj s i major) (.sort u) := HT.compute hd (.proj RM.forget)
    have HTtarget : TypedSource Δ target := by
      obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT'.compute hd (.base RP)
      exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
    rcases static_structure_sorted_projection_root heq hs HT' RP.1 with RI | RC | ⟨k, _, RN⟩
    · exact ⟨out, .refl, .inr ⟨major, target, before, after, by omega, RM, RI, RT⟩⟩
    all_goals
      have HB : ∃ lower j, j ≤ after ∧
          ScopedComputeCount (PiInertStage D n) j Δ (.proj s i major) lower ∧
          AdministrativeHeadDeletion out lower := by
        first
        | exact pi_inert_expansion_count_bypass_frames heq hs HTtarget
            (Recovery := PiInertStage D n) (.inl RC) RT
        | exact pi_inert_expansion_count_bypass_frames heq hs HTtarget (.inr RN) RT
      obtain ⟨middle, j, hj, RJ, HJ⟩ := HB
      obtain ⟨lower, HL, HF⟩ := ih j (by omega) HT' RJ
      refine ⟨lower, HJ.trans HL, ?_⟩
      rcases HF with ⟨last, cb, HB, EO, RL⟩ | ⟨last, field, cb, ca, HB, RL, RI, RF⟩
      · exact .inl ⟨last, before + cb, by omega, EO, RM.trans RL⟩
      · exact .inr ⟨last, field, before + cb, ca, by omega, RM.trans RL, RI, RF⟩

/-- Every full-stage sorted projection path has a terminal projection result
modulo tracked administrative head deletions. No condition on the output
shape, normalization, confluence, or forward comparison closure is needed. -/
theorem pi_inert_sorted_projection_terminal_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (R : ScopedCompute (PiInertStage D n) Δ (.proj s i m) out) :
    ∃ major lower, AdministrativeHeadDeletion out lower ∧
      ScopedCompute (PiInertStage D n) Δ m major ∧ ProjectionResult s i major lower := by
  obtain ⟨cost, RC⟩ := R.count
  obtain ⟨lower, HL, HF⟩ := pi_inert_sorted_projection_frames_count heq hs HT RC
  rcases HF with ⟨major, _, _, EO, RM⟩ | ⟨major, field, _, _, _, RM, RI, RF⟩
  · exact ⟨major, lower, HL, RM.forget, EO ▸ .keep⟩
  · cases RI with
    | projIota hi hl hg =>
      have hj := (List.getElem?_eq_some_iff.1 hg).1
      refine ⟨_, lower, HL, RM.forget.trans (RF.forget.selected_argument hg), ?_⟩
      exact .select hi (by simpa only [List.length_set] using hl) (by simp [hj])

/-- Move a beta tail of either terminal result back into its major. In the
selection case only the selected argument changes; the retained projection
case uses beta inversion. The ambient guarded stage is arbitrary. -/
theorem ProofShape.ProjectionResult.beta_tail
    (H : ProjectionResult s i m field) (R : ProofShape.BetaRed field out) :
    ∃ major, ScopedCompute Step Δ m major ∧ ProjectionResult s i major out := by
  cases H with
  | keep =>
    obtain ⟨major, rfl, RM⟩ := ProofShape.beta_proj_inv R
    exact ⟨major, .beta RM, .keep⟩
  | select hi hl hg =>
    have hj := (List.getElem?_eq_some_iff.1 hg).1
    refine ⟨_, (ScopedCompute.beta R).selected_argument hg, ?_⟩
    exact .select hi (by simpa only [List.length_set] using hl) (by simp [hj])

/-- Two sorted projections reaching any common output admit synchronized
terminal factorizations. Raw beta confluence aligns surviving administrative
frames; each resulting beta tail is moved into its own major. The two guarded
paths may use different finite stages, and the common output need not be
normal or exposed. -/
theorem pi_inert_sorted_projection_common_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HX : ControlTyping Δ (.proj s i x) (.sort u))
    (HY : ControlTyping Δ (.proj s i y) (.sort v))
    (RX : ScopedCompute (PiInertStage D n) Δ (.proj s i x) out)
    (RY : ScopedCompute (PiInertStage D k) Δ (.proj s i y) out) :
    ∃ left right lower, ProofShape.BetaRed out lower ∧
      ScopedCompute (PiInertStage D n) Δ x left ∧
      ScopedCompute (PiInertStage D k) Δ y right ∧
      ProjectionResult s i left lower ∧ ProjectionResult s i right lower := by
  obtain ⟨left, a, HA, RL, HL⟩ := pi_inert_sorted_projection_terminal_frames heq hs HX RX
  obtain ⟨right, b, HB, RR, HR⟩ := pi_inert_sorted_projection_terminal_frames heq hs HY RY
  obtain ⟨lower, RA, RB⟩ := HA.reduce.raw_confluent HB.reduce
  obtain ⟨left', RL', HL'⟩ := HL.beta_tail (Step := PiInertStage D n) (Δ := Δ) RA
  obtain ⟨right', RR', HR'⟩ := HR.beta_tail (Step := PiInertStage D k) (Δ := Δ) RB
  exact ⟨left', right', lower, HA.reduce.trans RA, RL.trans RL', RR.trans RR', HL', HR'⟩

/-- Exact characterization of a common full-stage projection computation by
same-stage major computations with a common terminal result. This handles
computation-to-reflexivity certificates with arbitrary surviving wrappers;
it does not assert closure for general structural comparison certificates. -/
theorem pi_inert_sorted_projection_common_terminal_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HX : ControlTyping Δ (.proj s i x) (.sort u))
    (HY : ControlTyping Δ (.proj s i y) (.sort v)) :
    (∃ out, ScopedCompute (PiInertStage D n) Δ (.proj s i x) out ∧
      ScopedCompute (PiInertStage D k) Δ (.proj s i y) out) ↔
    ∃ left right lower, ScopedCompute (PiInertStage D n) Δ x left ∧
      ScopedCompute (PiInertStage D k) Δ y right ∧
      ProjectionResult s i left lower ∧ ProjectionResult s i right lower := by
  constructor
  · rintro ⟨out, RX, RY⟩
    obtain ⟨left, right, lower, _, RL, RR, HL, HR⟩ :=
      pi_inert_sorted_projection_common_terminal heq hs HX HY RX RY
    exact ⟨left, right, lower, RL, RR, HL, HR⟩
  · rintro ⟨left, right, lower, RL, RR, HL, HR⟩
    have terminal {stage major} (H : ProjectionResult s i major lower) :
        ScopedCompute (PiInertStage D stage) Δ (.proj s i major) lower := by
      cases H with
      | keep => exact .refl
      | select hi hl hg => exact .base (pi_inert_stage_core (.inl (.inl (.inl (.projIota hi hl hg)))))
    exact ⟨lower, (ScopedCompute.proj RL).trans (terminal HL),
      (ScopedCompute.proj RR).trans (terminal HR)⟩

end Lean4Lean.VEnv.Strengthening
