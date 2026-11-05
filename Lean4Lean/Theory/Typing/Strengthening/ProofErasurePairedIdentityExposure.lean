import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecordExposure

/-! # Identity exposure with separate annotations and computation contexts

Each endpoint retains its own written type and computes in its own context.
The outputs compare in the left context. This permits function recursion to
keep the right binder instead of transporting its computation to the left
binder. Existence from arbitrary carrier certificates remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Two independently annotated endpoints compute to outputs comparing in
common mode in the left context. The right computation uses its own context;
no equality or computation between the annotations or contexts is assumed.
This is an exposure interface, not an existence or context-transport axiom. -/
def PairedIdentityExposure (D : Definitions) (Δ Δ' : List ProofShape)
    (A B a b : ProofShape) : Prop :=
  ∃ x y,
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) a) x ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ' (.app (.lam B (.bvar 0)) b) y ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true x y

/-- A common base comparison permits both independent annotations to contract.
The right context has no role in the beta contractions. -/
theorem PairedIdentityExposure.of_compare
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true a b) :
    PairedIdentityExposure D Δ Δ' A B a b :=
  ⟨a, b, .beta (raw_identity_beta _ _), .beta (raw_identity_beta _ _), H⟩

/-- A base carrier guard and an inferred comparison of the two annotations
compare the retained wrappers directly. Only the left wrapper's exact native
Pi is used; no native certificate is transferred to the right annotation. -/
theorem PairedIdentityExposure.of_guard
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false A B)
    (H : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) Δ A a b) :
    PairedIdentityExposure D Δ Δ' A B a b :=
  ⟨_, _, .refl, .refl, .appCarrier (.lam .bvar) (.lam HT (.leaf .refl)) H⟩

/-- Retained annotations allow the endpoint paths to run in separate contexts. -/
theorem PairedIdentityExposure.reduce
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ' b b')
    (H : PairedIdentityExposure D Δ Δ' A B a' b') :
    PairedIdentityExposure D Δ Δ' A B a b := by
  obtain ⟨x, y, RX, RY, HC⟩ := H
  exact ⟨x, y, (ScopedCompute.app .refl Ra).trans RX, (ScopedCompute.app .refl Rb).trans RY, HC⟩

/-- Each written annotation can compute independently before recursive
exposure. There is no requirement that their outputs agree. -/
theorem PairedIdentityExposure.annotations
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ A A')
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ' B B')
    (H : PairedIdentityExposure D Δ Δ' A' B' a b) :
    PairedIdentityExposure D Δ Δ' A B a b := by
  obtain ⟨x, y, RX, RY, HC⟩ := H
  exact ⟨x, y, (ScopedCompute.app (.lam RA .refl) .refl).trans RX,
    (ScopedCompute.app (.lam RB .refl) .refl).trans RY, HC⟩

/-- The previous same-carrier invariant supplies paired common exposure.
The extra identity layer turns its carrier guard into an inferred comparison. -/
theorem IdentityCarrierExposure.paired
    (H : IdentityCarrierExposure D Δ A a b) : PairedIdentityExposure D Δ Δ A A a b := by
  obtain ⟨_, x, y, _, RX, RY, _, _, HC⟩ := H.native_compared_outputs (mode := true)
  exact ⟨x, y, RX, RY, HC⟩

/-- At identical annotations and contexts, paired common exposure recovers
the original carrier invariant with the original carrier unchanged. -/
theorem PairedIdentityExposure.carrier
    (H : PairedIdentityExposure D Δ Δ A A a b) : IdentityCarrierExposure D Δ A a b := by
  obtain ⟨x, y, RX, RY, HC⟩ := H
  exact ⟨A, x, y, .refl, RX, RY, .carrierChecked HC⟩

/-- The new interface is equivalent to the old one on its diagonal; it does
not replace the goal with a weaker same-carrier exposure requirement. -/
theorem paired_identity_exposure_diagonal_iff :
    PairedIdentityExposure D Δ Δ A A a b ↔ IdentityCarrierExposure D Δ A a b :=
  ⟨PairedIdentityExposure.carrier, IdentityCarrierExposure.paired⟩

/-- Function exposure keeps both written domains and both body contexts.
Common-mode lambda comparison needs only the recursively exposed bodies in
the left context. No native recovery or computation is moved across binders.
The body exposure premise remains the recursive obligation. -/
theorem PairedIdentityExposure.function
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ' C (.sort w)) (hE : env.HasType univs (C :: Γ') E (.sort z))
    (H : PairedIdentityExposure D (proofEraseCtx (A :: Γ)) (proofEraseCtx (C :: Γ'))
      (proofErase (A :: Γ) B) (proofErase (C :: Γ') E)
      (.app (f.liftN 1) (etaArgument u)) (.app (g.liftN 1) (etaArgument w))) :
    PairedIdentityExposure D (proofEraseCtx Γ) (proofEraseCtx Γ')
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))
      (.forallE (proofErase Γ' C) (proofErase (C :: Γ') E)) f g := by
  obtain ⟨x, y, RX, RY, HC⟩ := H
  exact ⟨.lam (proofErase Γ A) x, .lam (proofErase Γ' C) y,
    (first_stage_identity_function_body hΓ hA hB).trans (.lam .refl RX),
    (first_stage_identity_function_body hΓ' hC hE).trans (.lam .refl RY), .lamCommon HC⟩

/-- Compared annotations upgrade paired common exposure to inferred outputs
while preserving separate exact native types. An extra identity layer carries
each original annotation to the output. The annotation comparison is an
explicit premise, not a consequence of ordinary type equality. -/
theorem PairedIdentityExposure.native_inferred_outputs
    (H : PairedIdentityExposure D Δ Δ' A B a b)
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false A B) :
    ∃ x y,
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.app (.lam A (.bvar 0)) a) x ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ' (.app (.lam B (.bvar 0)) b) y ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ x A ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ' y B ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false x y := by
  obtain ⟨x, y, RX, RY, HC⟩ := H
  have RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.app (.lam A (.bvar 0)) a) (.app (.lam A (.bvar 0)) (.app (.lam A (.bvar 0)) a)) :=
    .base (.inr (.inr (.inr (.inl (.intro (raw_identity_native _ _))))))
  have RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ'
      (.app (.lam B (.bvar 0)) b) (.app (.lam B (.bvar 0)) (.app (.lam B (.bvar 0)) b)) :=
    .base (.inr (.inr (.inr (.inl (.intro (raw_identity_native _ _))))))
  exact ⟨_, _, RA.trans (.app .refl RX), RB.trans (.app .refl RY),
    raw_identity_native _ _, raw_identity_native _ _, .app (.lam HT (.leaf .refl)) HC⟩

/-- Paired exposure of each retained field assembles paired record exposure.
Parameters may differ if they already compare at stage zero. Each field uses
its own major's recipe and its own computation context. This discharges the
vector assembly obligation, while field exposure itself remains a premise. -/
theorem PairedIdentityExposure.record
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hq : qs.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result)
    (HP : List.Forall₂ (ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true) ps qs)
    (HF : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      PairedIdentityExposure D Δ Δ'
        (projectionType family info doms i (by have := HT.numFields; omega) ps a)
        (projectionType family info doms i (by have := HT.numFields; omega) qs b)
        (.proj family i a) (.proj family i b)) :
    PairedIdentityExposure D Δ Δ' (ProofShape.mkApps (.const family ls) ps)
      (ProofShape.mkApps (.const family ls) qs) a b := by
  classical
  have Hfields : ∀ i, ∃ x y,
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
        (identityStructureField family info ls doms ps a i) x ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ'
        (identityStructureField family info ls doms qs b i) y ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true x y := by
    intro i
    unfold identityStructureField
    by_cases hj : i < info.numFields
    · have hj' : info.nparams + i < doms.length := by have := HT.numFields; omega
      simp only [dif_pos hj']
      by_cases hm : StructureReplay.ProofField env univs info ls i
      · simp only [if_pos hm]; exact ⟨.proof, .proof, .refl, .refl, .leaf .refl⟩
      · simp only [if_neg hm]; exact HF i hj hm
    · have hj' : ¬ info.nparams + i < doms.length := by have := HT.numFields; omega
      simp only [dif_neg hj']; exact ⟨.proof, .proof, .refl, .refl, .leaf .refl⟩
  let xs := fun i => (Hfields i).choose
  let ys := fun i => (Hfields i).choose_spec.choose
  have HH i := (Hfields i).choose_spec.choose_spec
  have RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ)
      ((List.range info.numFields).map (identityStructureField family info ls doms ps a))
      ((List.range info.numFields).map xs) := by
    apply List.forall₂_map_left_iff.2
    apply List.forall₂_map_right_iff.2
    exact Lean4Lean.List.Forall₂.rfl (fun i _ => (HH i).1)
  have RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ')
      ((List.range info.numFields).map (identityStructureField family info ls doms qs b))
      ((List.range info.numFields).map ys) := by
    apply List.forall₂_map_left_iff.2
    apply List.forall₂_map_right_iff.2
    exact Lean4Lean.List.Forall₂.rfl (fun i _ => (HH i).2.1)
  have HC : List.Forall₂ (ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true)
      ((List.range info.numFields).map xs) ((List.range info.numFields).map ys) := by
    apply List.forall₂_map_left_iff.2
    apply List.forall₂_map_right_iff.2
    exact Lean4Lean.List.Forall₂.rfl (fun i _ => (HH i).2.2)
  exact ⟨_, _,
    (first_stage_identity_record_fields hi hx hp hadm HT).trans
      (.mkApps .refl (List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) RX)),
    (first_stage_identity_record_fields hi hx hq hadm HT).trans
      (.mkApps .refl (List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) RY)),
    (ComputedJointCompare.mkApps (.leaf .refl) (List.Forall₂.append' HP HC)).common⟩

/-- The original record-carrier case reduces to paired exposure at its
separate dependent field annotations. Unlike a same-carrier field induction,
this statement matches exactly the annotations produced by record expansion. -/
theorem IdentityCarrierExposure.record_of_paired_fields
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result)
    (HF : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      PairedIdentityExposure D Δ Δ
        (projectionType family info doms i (by have := HT.numFields; omega) ps a)
        (projectionType family info doms i (by have := HT.numFields; omega) ps b)
        (.proj family i a) (.proj family i b)) :
    IdentityCarrierExposure D Δ (ProofShape.mkApps (.const family ls) ps) a b :=
  (PairedIdentityExposure.record hi hx hp hp hadm HT
    (Lean4Lean.List.Forall₂.rfl (fun _ _ => .leaf .refl)) HF).carrier

end Lean4Lean.VEnv.Strengthening
