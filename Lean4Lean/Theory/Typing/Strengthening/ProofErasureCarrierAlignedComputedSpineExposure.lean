import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSpineRoot

/-! # Parameterized family exposure for complete computed joint checking

All computed application constructors retain inferred checking of the function.
That check exposes a rigid family spine even in appComputed, without replaying
its chosen lambda or assuming confluence. Root universe changes retain their
equivalence evidence; parameters may compute and their arity is preserved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
open private ProofShape.const_spine_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure
variable [Params]
namespace ProofShape

private theorem const_exposure_pair
    (hn : SpineRootLevels Step c)
    (H : ComputedJointCheck Step Δ kind a b) (hm : kind = .compare false) :
    (∀ ls args, a = mkApps (.const c ls) args →
      ∃ ls' args', ScopedCompute Step Δ b (mkApps (.const c ls') args') ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ args'.length = args.length) ∧
    (∀ ls args, b = mkApps (.const c ls) args →
      ∃ ls' args', ScopedCompute Step Δ a (mkApps (.const c ls') args') ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ args'.length = args.length) := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl => exact ⟨fun ls args E => ⟨ls, args, E ▸ .refl, .rfl (fun _ _ => by rfl), rfl⟩,
        fun ls args E => ⟨ls, args, E ▸ .refl, .rfl (fun _ _ => by rfl), rfl⟩⟩
    | sort =>
      constructor <;> intro ls args E <;>
        have HE := congrArg constHead E <;>
        simp only [constHead_mkApps, constHead] at HE <;> cases HE
    | const HL =>
      constructor
      · intro ls args E
        obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_const E.symm
        exact ⟨_, [], .refl, HL, rfl⟩
      · intro ls args E
        obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_const E.symm
        exact ⟨_, [], .refl, HL.flip.imp (fun _ _ H => H.symm), rfl⟩
  | @app Δ f g x y mode HF HX ihf ihx =>
    have IH := ihf rfl
    constructor
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.1 ls args₀ Ef
      refine ⟨ls', args' ++ [y], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.2 ls args₀ Ef
      refine ⟨ls', args' ++ [x], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  | @appCarrier Δ f A B g x y mode R HF HX ihf ihx =>
    have IH := ihf rfl
    constructor
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.1 ls args₀ Ef
      refine ⟨ls', args' ++ [y], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.2 ls args₀ Ef
      refine ⟨ls', args' ++ [x], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  | @appComputed Δ f A body g x y mode R HF HX ihf ihx =>
    have IH := ihf rfl
    constructor
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.1 ls args₀ Ef
      refine ⟨ls', args' ++ [y], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    · intro ls args E
      obtain ⟨args₀, rfl, Ef⟩ := const_spine_app E.symm
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.2 ls args₀ Ef
      refine ⟨ls', args' ++ [x], ?_, HL, ?_⟩
      · rw [mkApps_snoc]; exact .app R .refl
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro ls args E <;>
      have HE := congrArg constHead E <;>
      simp only [constHead_mkApps, constHead] at HE <;> cases HE
  | compute Ra Rb HC ih =>
    have IH := ih hm
    constructor
    · intro ls args E
      obtain ⟨ls₁, args₁, E₁, HL₁, H₁⟩ := (E ▸ Ra).const_spine_levels hn
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.1 ls₁ args₁ E₁
      exact ⟨ls', args', Rb.trans R, HL₁.trans (fun _ _ _ H K => H.trans K) HL, hlen.trans H₁.length_eq.symm⟩
    · intro ls args E
      obtain ⟨ls₁, args₁, E₁, HL₁, H₁⟩ := (E ▸ Rb).const_spine_levels hn
      obtain ⟨ls', args', R, HL, hlen⟩ := IH.2 ls₁ args₁ E₁
      exact ⟨ls', args', Ra.trans R, HL₁.trans (fun _ _ _ H K => H.trans K) HL, hlen.trans H₁.length_eq.symm⟩
  | symm H ih => exact (ih hm).symm
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- The full computed inferred checker exposes a parameterized rigid family
at equivalent universes and the same arity, including its appComputed rule.
No typing, confluence, substitution or parameter comparison premise is needed. -/
theorem ComputedJointCompare.const_spine_levels_exposure
    (hn : SpineRootLevels Step family)
    (H : ComputedJointCompare Step Δ false (mkApps (.const family ls) args) b) :
    ∃ ls' args', ScopedCompute Step Δ b (mkApps (.const family ls') args') ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ args'.length = args.length :=
  (const_exposure_pair hn H rfl).1 ls args rfl

end ProofShape

/-- Typed computed comparison in either mode exposes a displayed parameterized
family. This is the complete computed checker, not arbitrary aligned promotion. -/
theorem proofErase_carrier_aligned_computed_family_exposure
    (hstep : ErasedScopedPrimitiveDescent Step) (hn : SpineRootLevels Step family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = mkApps (.const family ls) args) :
    ∃ ls' args', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (mkApps (.const family ls') args') ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ args'.length = args.length := by
  have HI := proofErase_computed_joint_types_inferred hstep hΓ ha hb H
  rw [Ea] at HI
  exact HI.const_spine_levels_exposure hn

/-- Parameterized family exposure is closed for computed comparisons in the
level-extended union. Native aligned promotions remain a separate case. -/
theorem proofErase_carrier_aligned_level_union_computed_family_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = mkApps (.const family ls) args) :
    ∃ ls' args', ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) (mkApps (.const family ls') args') ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ args'.length = args.length :=
  proofErase_carrier_aligned_computed_family_exposure (erased_level_recovered_union_descent heq hs)
    (erased_level_recovered_union_spine_levels heq hc hD) hΓ ha hb H Ea

end Lean4Lean.VEnv.Strengthening
