import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointProofInstantiation

/-! # Literal joins cannot align every recovered type

A non-proof substitution image may have a declared universe syntactically
different from its unique recoverable universe. All joint computations fix
literal sorts. Universe comparison, already present in joint checking, aligns
the two types; demanding a literal computational join cannot replace it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace ProofShape

/-- Recovery from a displayed sort only computes from its successor universe. -/
theorem ScopedTypeRecovery.sort_compute
    (R : ScopedTypeRecovery Step Δ (.sort u) out) :
    ScopedCompute Step Δ (.sort (.succ u)) out := by
  generalize E : ProofShape.sort u = source at R
  induction R with
  | sort _ => cases E; exact .refl
  | convert _ H ih => exact (ih E).trans H
  | bvar | const | lam | app | forallE | proj => cases E

/-- At a literal universe carrier, the full joint grammar reduces to its
ordinary comparison mode, even with nested recovered applications. -/
theorem JointCarrierGuard.sort_checked
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCarrierGuard Step Δ (.sort u) a b) : JointCompare Step Δ true a b := by
  change JointCheck Step Δ (.carrier (.sort u)) a b at H
  generalize E : JointCheckKind.carrier (.sort u) = kind at H
  induction H generalizing u with
  | carrierChecked H => exact H
  | carrierSubsingleton H => cases E; exact (H.not_sort rfl).elim
  | carrierFunction => cases E
  | carrierSymm _ ih => exact .symm (ih E)
  | carrierCompute R _ ih =>
    cases E
    exact ih (congrArg JointCheckKind.carrier (R.sort_fixed hhead).symm)
  | carrierReduce Ra Rb _ ih => exact .compute Ra Rb (ih E)
  | carrierIntro | carrierNested =>
    have HE := JointCheckKind.carrier.inj E
    have HH := congrArg ProofShape.constHead HE
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
    cases HH
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Universe-indexed raw guards carry no additional syntax beyond checking the
endpoints. Actual use still supplies endpoint typings at the target carrier. -/
theorem JointCarrierGuard.sort_reindex
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCarrierGuard Step Δ (.sort u) a b) : JointCarrierGuard Step Δ (.sort v) a b :=
  .carrierChecked (H.sort_checked hhead)

end ProofShape
namespace RecoveryJoinBoundary

private def declared : VLevel := .max (.succ .zero) .zero

omit [Params] in
private theorem declared_equiv : declared ≈ .succ .zero := by
  simp [declared, VLevel.equiv_def, VLevel.eval]

private theorem erase_sort (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem image_typed : env.HasType univs Γ (.sort .zero) (.sort declared) :=
  (IsDefEq.sortDF (by trivial) (by trivial) declared_equiv.symm).defeq (HasType.sort (by trivial))

private theorem no_join
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.sort .zero) out)
    (HA : ScopedCompute Step Δ (.sort declared) shared)
    (HB : ScopedCompute Step Δ out shared) : False := by
  have E := R.sort_compute.sort_fixed hhead
  have EA := HA.sort_fixed hhead
  rw [E] at HB
  have EB := HB.sort_fixed hhead
  cases EA.symm.trans EB

/-- In every well-formed context a typed non-proof image has a recovered type,
and its declared and recovered types compare, but no recovered output has a
literal computational join with the declared type. This holds in the entire
joint-stage union, for any core, hence also for the quotient-enriched core. -/
theorem typed_join_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ e T out, env.HasType univs Γ e T ∧ ¬ IsProof Γ e ∧
      ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out ∧
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false (proofErase Γ T) out ∧
      ∀ out' shared,
        ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out' →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) shared →
        ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) out' shared := by
  refine ⟨.sort .zero, .sort declared, .sort (.succ .zero), image_typed, ?_, ?_, ?_, ?_⟩
  · exact not_isProof_of_sort hΓ (HasType.sort (by trivial))
  · rw [erase_sort hΓ (by trivial)]
    exact .sort (by trivial)
  · rw [erase_sort hΓ (by trivial)]
    exact .leaf (.sort declared_equiv)
  · intro out' shared R HA HB
    rw [erase_sort hΓ (by trivial)] at R HA
    exact no_join erased_joint_union_head R HA HB

/-- The obstruction comes from an actual typed substitution, not an arbitrary
chosen raw type: a variable recovers its declared type before being replaced
by Prop. After substitution, no selected recovered output joins that type.
The existing joint universe comparison aligns a recovered output at stage zero. -/
theorem substitution_join_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ e T, env.HasType univs Γ e T ∧
      OnCtx (T :: Γ) (env.IsType univs) ∧
      Ctx.SubstEq env univs Γ (VExpr.Subst.one e) (VExpr.Subst.one e) (T :: Γ) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) (.bvar 0)) (proofErase (T :: Γ) T.lift) ∧
      (∃ out, ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) out ∧
        JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false (proofErase Γ T) out) ∧
      ∀ out shared,
        ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) shared →
        ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) out shared := by
  have ht : env.HasType univs Γ (.sort .zero) (.sort declared) := image_typed
  have hT : env.HasType univs Γ (.sort declared) (.sort (.succ declared)) := .sort (by trivial)
  have hΓT : OnCtx (.sort declared :: Γ) (env.IsType univs) := ⟨hΓ, _, hT⟩
  have hv : env.HasType univs (.sort declared :: Γ) (.bvar 0) (.sort declared) := .bvar .zero
  refine ⟨.sort .zero, .sort declared, ht, hΓT, ?_, ?_, ?_, ?_⟩
  · exact (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := VExpr.sort .zero) (A₀ := .sort declared)).substEq hΓT ht
  · rw [show proofErase (.sort declared :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hΓT hv)]
    rw [← erasedTypeOracle_valid hΓT (Lookup.zero (ty := VExpr.sort declared)), ← proofEraseCtx_oracle]
    exact .bvar
  · refine ⟨.sort (.succ .zero), ?_, ?_⟩
    · rw [erase_sort hΓ (by trivial)]
      exact .sort (by trivial)
    · rw [erase_sort hΓ (by trivial)]
      exact .leaf (.sort declared_equiv)
  · intro out shared R HA HB
    rw [erase_sort hΓ (by trivial)] at R HA
    exact no_join erased_joint_union_head R HA HB

end RecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
