import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedProjectionSupport

/-! # Projection of arbitrary typed joint comparisons

The comparison induction allows carrier checking inside applications. Exposed
constructors select their smaller field comparison; computation replays at the
original major type. No carrier conversion or comparison transitivity is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem project_inferred (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.JointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_joint_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  by_cases hp : IsProof Γ (.proj s i a)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hp)]
    exact .leaf .refl
  · have hp' := mt (isProof_congr hΓ HP).2 hp
    rw [show proofErase Γ (.proj s i a) = .proj s i (proofErase Γ a) from if_neg hp,
      show proofErase Γ (.proj s i b) = .proj s i (proofErase Γ b) from if_neg hp']
    exact .proj H

private theorem structure_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj family i a) T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ea : proofErase Γ a = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (H : ∀ j (h : j < fields.length), fields[j] ≠ .proof →
      ProofShape.JointCompare Step (proofEraseCtx Γ) true fields[j]
        (.proj family j (proofErase Γ b)))
    (hidx : i < fields.length) :
    ProofShape.JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b)) := by
  have HM : ProofShape.JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
    rw [Ea]
    exact .structFields hi hx hp hf hadm H
  have HAB := proofErase_joint_carrier_reflect hstep hΓ ha hb (.carrierChecked HM)
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.toU.of_l henv hΓ ht) T ht
  by_cases hproof : IsProof Γ (.proj family i a)
  · rw [proofErase_eq_proof.2 hproof, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hproof)]
    exact .leaf .refl
  have hproof' := mt (isProof_congr hΓ HP).2 hproof
  have Eleft : proofErase Γ (.proj family i a) =
      .proj family i (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)) := by
    rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hproof, Ea]
  have R : ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.proj family i a)) fields[i] := by
    rw [Eleft]
    apply hprim
    apply ProofShape.Primitive.projIota hi (by simp [hp, hf])
    rw [← hp, List.getElem?_append_right (by omega)]
    simp [hidx]
  have hn : fields[i] ≠ .proof := by
    intro E
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨out, HE, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ht rfl
      (by simpa only [ProofShape.liftN_zero] using R)
    simp only [ProofShape.liftN_zero] at EE
    exact hproof ((isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (EE.trans E)))
  rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hproof']
  exact .compute R .refl (H i hidx hn)

/-- Every typed joint comparison projects at common original major and field
types, including recursive carrier comparisons inside applications. -/
theorem proofErase_joint_project_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hta : env.HasType univs Γ (.proj s i a) T) (htb : env.HasType univs Γ (.proj s i b) T)
    (H : ProofShape.JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  generalize EΔ : proofEraseCtx Γ = Δ at H
  generalize Ea : proofErase Γ a = sa at H
  generalize Eb : proofErase Γ b = sb at H
  change ProofShape.JointCheck Step Δ (.compare mode) sa sb at H
  generalize EK : ProofShape.JointCheckKind.compare mode = kind at H
  induction H generalizing a b A T mode with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf .refl)
    | sort H =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.sort H))
    | const H =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.const H))
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ hta (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ htb (Eb.trans E)).elim
  | app Hf Hx =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .app Hf Hx)
  | appCarrier R Hf Hx =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .appCarrier R Hf Hx)
  | proj H =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .proj H)
  | forallE HD HB =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallE HD HB)
  | forallSorted SA SA' HD SB SB' HB =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallSorted SA SA' HD SB SB' HB)
  | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
    exact (proofErase_projection_not_lam hΓ hta Ea).elim
  | etaBodyR => exact (proofErase_projection_not_lam hΓ htb Eb).elim
  | structFields hi hx hp hf hadm HF =>
    obtain ⟨ES, hidx⟩ := proofErase_projection_constructor_family hΓ hta hi hx hp hf Ea
    subst s
    rw [← EΔ]
    exact structure_project hstep hprim hΓ ha hb hta hi hx hp hf hadm Ea
      (by simpa only [EΔ, Eb] using HF) hidx
  | compute Ra Rb _ ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ha EΔ
      (by simpa only [ProofShape.liftN_zero, Ea] using Ra)
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hb EΔ
      (by simpa only [ProofShape.liftN_zero, Eb] using Rb)
    simp only [ProofShape.liftN_zero] at EA EB
    have hta' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).of_l henv hΓ ht) T hta).hasType.2
    have htb' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ b b' from ⟨_, HB⟩).of_l henv hΓ ht) T htb).hasType.2
    exact .compute
      (proofErase_scoped_compute_project hΓ HA hta (by rwa [Ea, EA]))
      (proofErase_scoped_compute_project hΓ HB htb (by rwa [Eb, EB]))
      (ih HA.hasType.2 HB.hasType.2 hta' htb' EΔ EA EB EK)
  | symm _ ih => exact .symm (ih hb ha htb hta EΔ Eb Ea EK)
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- A single original projection typing suffices. Joint reflection constructs
the second projection's common field type before applying projection closure. -/
theorem proofErase_joint_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.JointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_joint_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  exact proofErase_joint_project_typed hstep hprim hΓ ha hb ht HP.hasType.2 H

end Lean4Lean.VEnv.Strengthening
