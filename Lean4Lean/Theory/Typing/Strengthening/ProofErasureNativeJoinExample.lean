import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinFirstStage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeExample

/-! # One binder conversion requiring both ingredients

The source changes a universe's syntax and beta-expands an arbitrary result.
Family alignment handles the universe change; computation removes the result
expansion. With a generic result variable neither the old finite alignment nor
a common core reduct of the whole annotations is available on its own.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework.Example
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private forall_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
open JoinedNative.Example (expanded expanded_equal expanded_erasure expanded_compute)
variable [Params] {hq : QuotRegistered env}

/-- A deliberately noncanonical presentation of the zero universe. -/
def declared : VLevel := .max .zero .zero
/-- A function returning the arbitrary ambient type. -/
def targetType (T : VExpr) : VExpr := .forallE (.sort .zero) T.lift
/-- Both a universe annotation and the result syntax differ from the target. -/
def sourceType (T : VExpr) : VExpr := .forallE (.sort declared) (expanded T.lift)

private theorem domain_equal : env.IsDefEq univs Γ (.sort declared) (.sort .zero)
    (.sort (.succ declared)) :=
  .sortDF (by trivial) (by trivial) (by simp [declared, VLevel.equiv_def, VLevel.eval])

/-- The two complete annotations are actually equal and well typed. -/
theorem types_equal (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    env.IsDefEq univs Γ (sourceType T) (targetType T)
      (.sort (.imax (.succ declared) (.succ .zero))) :=
  .forallEDF domain_equal (expanded_equal (hT.weak henv))

/-- Whenever the result type has a value, the target function type is inhabited. -/
theorem target_inhabited (ht : env.HasType univs Γ t T) :
    env.HasType univs Γ (.lam (.sort .zero) t.lift) (targetType T) :=
  .lam (.sort (by trivial)) (ht.weak henv)

private theorem body_erasure (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) (hu : u.WF univs) :
    proofErase (.sort u :: Γ) T.lift = (proofErase Γ T).liftN 1 :=
  proofErase_liftN hΓ ⟨hΓ, _, HasType.sort hu⟩ Ctx.LiftN.one hT

/-- Both erased annotations expose the same arbitrary result, with an expansion
on the source side and different literal universe syntax at the input. -/
theorem erasures (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    proofErase Γ (sourceType T) = .forallE (.sort declared)
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) ((proofErase Γ T).liftN 1)) ∧
    proofErase Γ (targetType T) = .forallE (.sort .zero) ((proofErase Γ T).liftN 1) := by
  have HE := types_equal hT
  have hΔ : OnCtx (.sort declared :: Γ) (env.IsType univs) := ⟨hΓ, _, domain_equal.hasType.1⟩
  constructor
  · rw [show proofErase Γ (sourceType T) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.1)]
    rw [show proofErase Γ (.sort declared) = .sort declared from
      if_neg (not_isProof_of_sort hΓ domain_equal.hasType.1)]
    rw [expanded_erasure hΔ (hT.weak henv), body_erasure hΓ hT (by trivial)]
  · rw [show proofErase Γ (targetType T) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
    rw [show proofErase Γ (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓ domain_equal.hasType.2)]
    rw [body_erasure hΓ hT (by trivial)]

/-- Computation supplies the intermediate carrier, and finite input alignment
connects the actual target to it without classifying the arbitrary result. -/
theorem combined_certificate (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    ∃ mid, NativeFamilyFramework.Alignment (definitions hq) PolymorphicTypeFamily Γ (targetType T) mid ∧
      Compute (Step hq) (proofErase Γ (sourceType T)) mid := by
  refine ⟨.forallE (.sort declared) ((proofErase Γ T).liftN 1), ?_, ?_⟩
  · apply NativeFamilyFramework.Alignment.input (show PolymorphicTypeFamily Γ (.sort .zero) from .sort)
    rw [← body_erasure hΓ hT (by trivial : VLevel.zero.WF univs)]
    exact .exact
  · rw [(erasures hΓ hT).1]
    apply Compute.forallE .refl
    simpa [ProofShape.inst, instVar, ProofShape.liftN_zero] using
      (Compute.beta (Step := Step hq) (BetaRed.beta (A := .sort (.succ .zero))
        (b := .bvar 0) (a := (proofErase Γ T).liftN 1)))

/-- Every recursive carrier certificate crosses the combined annotation change. -/
theorem carrier_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort (.succ .zero)))
    (ha : env.HasType univs (sourceType T :: Γ) a C) (hb : env.HasType univs (sourceType T :: Γ) b C)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (sourceType T :: Γ))
      (proofErase (sourceType T :: Γ) C) (proofErase (sourceType T :: Γ) a) (proofErase (sourceType T :: Γ) b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (targetType T :: Γ))
      (proofErase (sourceType T :: Γ) C) (proofErase (sourceType T :: Γ) a) (proofErase (sourceType T :: Γ) b) := by
  letI := NativeFamilyFramework.polymorphic_inputLaws (D := definitions hq)
  obtain ⟨mid, HA, RC⟩ := combined_certificate (hq := hq) hΓ hT
  exact aligned_carrier_context hcon hΓ (types_equal hT) HA RC ha hb H

/-- Distinct literal input universes preclude a common ordinary-core reduct,
regardless of what the result type computes to. -/
theorem no_core_join (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    ¬ ∃ shared, Compute (Step hq) (proofErase Γ (sourceType T)) shared ∧
      Compute (Step hq) (proofErase Γ (targetType T)) shared := by
  rintro ⟨shared, RA, RB⟩
  rw [(erasures hΓ hT).1] at RA
  rw [(erasures hΓ hT).2] at RB
  obtain ⟨A, B, rfl, HA, _⟩ := forall_parts hq RA
  obtain ⟨A', B', EE, HB, _⟩ := forall_parts hq RB
  obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
  have EA := (HA.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).sort_fixed
    (fun H => erased_iota_primitive_head H)
  have EB := (HB.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).sort_fixed
    (fun H => erased_iota_primitive_head H)
  cases EA.symm.trans EB

private theorem aligned_variable_fixed (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ (.bvar i) (.sort v))
    (H : NativeFamilyFramework.Alignment D F Γ (.bvar i) out) : out = .bvar i := by
  rcases H.shape with RC | ⟨u, E⟩ | ⟨A, B, E⟩
  · rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_isProof_of_sort hΓ hT)] at RC
    exact (RC.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).bvar_fixed
      (fun H => erased_iota_primitive_head H)
  · cases E
  · cases E

/-- At a generic result variable, direct old alignment also fails for every
input predicate. Hence this example needs computation and family alignment
in combination, rather than merely selecting one of the previous methods. -/
theorem no_direct_alignment (F : List VExpr → VExpr → Prop)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ (.bvar i) (.sort (.succ .zero))) :
    ¬ NativeFamilyFramework.Alignment (definitions hq) F Γ (targetType (.bvar i))
      (proofErase Γ (sourceType (.bvar i))) := by
  intro H
  have ET : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ hT)
  rw [(erasures hΓ hT).1, ET] at H
  simp only [targetType, VExpr.lift, VExpr.liftN, ProofShape.liftN, liftVar, Nat.not_lt_zero, if_false,
    Nat.add_comm] at H
  have hΔ : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hv : env.HasType univs (.sort .zero :: Γ) (.bvar (i + 1)) (.sort (.succ .zero)) := by
    simpa [HasType, VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm] using hT.weak henv (B := .sort .zero)
  rcases H.expose with HT | RC | ⟨A, B, rawA, rawB, EE, HB, _, RC⟩
  · cases HT with
    | function _ HB => cases HB
  · have ETarget := (erasures hΓ hT).2
    rw [ET] at ETarget
    simp only [targetType, VExpr.lift, VExpr.liftN, ProofShape.liftN, liftVar, Nat.not_lt_zero,
      if_false, Nat.add_comm] at ETarget
    rw [ETarget] at RC
    obtain ⟨A, B, EE, HA, _⟩ := forall_parts hq RC
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have E := (HA.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    cases E
  · obtain ⟨rfl, rfl⟩ := VExpr.forallE.inj EE
    obtain ⟨A, B, EE, _, RB⟩ := forall_parts hq RC
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    have E := aligned_variable_fixed (definitions hq) hΔ hv (HB.convert RB)
    cases E

/-- The same conversion transports whole first-stage singleton and Eq-prefix
computation paths, not only their base comparison guards. -/
theorem first_stage_context
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort (.succ .zero)))
    (ht : env.HasType univs (sourceType T :: Γ) e C)
    (R : ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx (sourceType T :: Γ)) (proofErase (sourceType T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx (targetType T :: Γ)) (proofErase (sourceType T :: Γ) e) out := by
  letI := NativeFamilyFramework.polymorphic_inputLaws (D := definitions hq)
  obtain ⟨mid, HA, RC⟩ := combined_certificate (hq := hq) hΓ hT
  exact compute_context heq hcon hΓ (types_equal hT) HA RC ht R

/-- A concrete well-formed context contains both a generic type and its value.
The resulting function inhabits both annotations. Their combined certificate
exists, while direct finite alignment and an ordinary-core join both fail. -/
theorem inhabited_boundary :
    ∃ Γ T p, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ T (.sort (.succ .zero)) ∧
      env.HasType univs Γ p (targetType T) ∧ env.HasType univs Γ p (sourceType T) ∧
      (∃ mid, NativeFamilyFramework.Alignment (definitions hq) PolymorphicTypeFamily Γ (targetType T) mid ∧
        Compute (Step hq) (proofErase Γ (sourceType T)) mid) ∧
      (∀ F, ¬ NativeFamilyFramework.Alignment (definitions hq) F Γ (targetType T)
        (proofErase Γ (sourceType T))) ∧
      ¬ ∃ shared, Compute (Step hq) (proofErase Γ (sourceType T)) shared ∧
        Compute (Step hq) (proofErase Γ (targetType T)) shared := by
  let Γ : List VExpr := [.bvar 0, .sort (.succ .zero)]
  have hΓ₁ : OnCtx [VExpr.sort (.succ .zero)] (env.IsType univs) :=
    ⟨by trivial, _, HasType.sort (by trivial)⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₁, _, HasType.bvar .zero⟩
  have hT : env.HasType univs Γ (.bvar 1) (.sort (.succ .zero)) := .bvar (.succ .zero)
  have ht : env.HasType univs Γ (.bvar 0) (.bvar 1) := .bvar .zero
  have hp := target_inhabited ht
  exact ⟨Γ, .bvar 1, _, hΓ, hT, hp, (types_equal hT).symm.defeq hp,
    combined_certificate hΓ hT, fun F => no_direct_alignment F hΓ hT, no_core_join hΓ hT⟩

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework.Example
