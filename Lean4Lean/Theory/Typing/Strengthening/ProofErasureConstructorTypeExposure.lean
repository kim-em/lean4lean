import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedComputedSpineExposure

/-! # One-sided constructor exposure retaining its type argument

The opposite endpoint need not already be a constructor. Inferred checking
exposes its stable head while retaining comparison of the selected type
argument. Native and computed application domains are interpreted at actual
argument types before their carrier guards are read.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private control_realize typed_compute typed_app_fn unary_compute binary_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
variable [Params]

private theorem source_realize (H : TypedSource Δ e)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ) :
    ∃ f T, env.HasType univs Γ f T ∧ proofErase Γ f = e := by
  obtain ⟨Γ', f, T, hΓ', EΓ', hf, Ef⟩ := H
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  exact ⟨f, T, hf.defeqDFC henv W, (proofErase_defeqCtx hΓ' W hf).symm.trans Ef⟩

/-- Inferred equality of two actually applied functions transfers the sort
assignment of one argument to the other. This is ordinary typing transport;
no raw carrier certificate or comparison is transported by this lemma. -/
theorem inferred_application_argument_sort
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HTX : TypedSource Δ (.app f x)) (HTY : TypedSource Δ (.app g y))
    (HX : ControlTyping Δ x (.sort u))
    (HF : ComputedJointCompare Step Δ false f g) : ControlTyping Δ y (.sort u) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTX
  obtain ⟨f₀, x₀, rfl, hn, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨e', T', ht', Ee'⟩ := source_realize HTY hΓ EΓ
  obtain ⟨g₀, y₀, rfl, hn', Eg, Ey⟩ := erase_app_inv Ee'
  obtain ⟨A, B, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨C, D, hg, hy⟩ := ht'.app_inv henv hΓ
  have HFG := (proofErase_computed_joint_compare_reflect hstep hΓ hf hg
    (by simpa only [EΓ, Ef, Eg] using HF)).2 rfl
      (not_isProof_fn hΓ hf hx hn) (not_isProof_fn hΓ hg hy hn')
  have hyA := argument_at_displayed_domain hΓ hg (HFG.of_l henv hΓ hf).hasType.2 hy
  obtain ⟨x₁, hx₁, Ex₁⟩ := control_realize HX hΓ EΓ
  have hnx : ¬ IsProof Γ x₀ := fun hp => HX.ne_proof (Ex.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hx hx₁ (Ex.trans Ex₁.symm)).2 hnx
  have hxSort := ((HE.defeq hΓ).of_r henv hΓ hx₁).hasType.1
  have hySort := hyA.defeqU_r henv hΓ (hx.uniqU henv hΓ hxSort)
  exact ⟨Γ, y₀, hΓ, EΓ, hySort, Ey⟩

/-- Computation to a lambda supplies its actual displayed argument domain.
At two sort-typed arguments, the resulting carrier guard is ordinary common
comparison. The original function need not have a displayed lambda head. -/
theorem computed_application_type_arguments_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (.app f x))
    (HX : ControlTyping Δ x (.sort u)) (HY : ControlTyping Δ y (.sort v))
    (RF : ScopedCompute Step Δ f (.lam A body))
    (H : ComputedJointCarrierGuard Step Δ A x y) :
    ComputedJointCompare Step Δ true x y := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨D, C, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨f', HF, EF⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv EF
  obtain ⟨⟨w, hA⟩, B₀, hb⟩ := HF.hasType.2.lam_inv henv hΓ
  have hxA := argument_at_displayed_domain hΓ HF.hasType.2 (HasType.lam hA hb) hx
  obtain ⟨x₁, hx₁, Ex₁⟩ := control_realize HX hΓ EΓ
  obtain ⟨y₁, hy₁, Ey₁⟩ := control_realize HY hΓ EΓ
  have hn : ¬ IsProof Γ x₀ := fun hp => HX.ne_proof (Ex.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hxA hx₁ (Ex.trans Ex₁.symm)).2 hn
  have hx₁A := ((HE.defeq hΓ).of_l henv hΓ hxA).hasType.2
  have HC := proofErase_computed_carrier_types_checked hstep hΓ hx₁ hy₁ (.inl hx₁A)
    (by simpa only [EΓ, EA, Ex₁, Ey₁] using H)
  simpa only [EΓ, Ex₁, Ey₁] using HC

private theorem constant_exposure (hroot : SpineRootLevels Step c)
    (H : ComputedJointCompare Step Δ false (.const c []) f) :
    ScopedCompute Step Δ f (.const c []) := by
  obtain ⟨ls, args, R, HL, HA⟩ :=
    (show ComputedJointCompare Step Δ false (ProofShape.mkApps (.const c []) []) f from H).const_spine_levels_exposure hroot
  cases HL
  have EA : args = [] := by simpa using HA
  subst args
  exact R

private theorem unary_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (H : ComputedJointCompare Step Δ false a b)
    (HTA : TypedSource Δ a) (HTB : TypedSource Δ b) :
    (∀ x u, a = .app (.const c []) x → ControlTyping Δ x (.sort u) →
      ∃ y, ScopedCompute Step Δ b (.app (.const c []) y) ∧ ComputedJointCompare Step Δ true x y) ∧
    (∀ y u, b = .app (.const c []) y → ControlTyping Δ y (.sort u) →
      ∃ x, ScopedCompute Step Δ a (.app (.const c []) x) ∧ ComputedJointCompare Step Δ true y x) := by
  change ComputedJointCheck Step Δ (.compare false) a b at H
  generalize EK : JointCheckKind.compare false = kind at H
  induction H with
  | leaf H =>
    cases EK
    cases H with
    | refl => constructor <;> intro x u E HX <;> exact ⟨x, E ▸ .refl, .leaf .refl⟩
    | sort | const => constructor <;> intro x u E HX <;> cases E
  | app HF HA =>
    constructor
    · intro x u E HX
      cases E
      exact ⟨_, .app (constant_exposure hroot HF) .refl, HA⟩
    · intro y u E HY
      cases E
      exact ⟨_, .app (constant_exposure hroot (.symm HF)) .refl, .symm HA⟩
  | appCarrier RN HF HA =>
    constructor
    · intro x u E HX
      cases E
      have HY := inferred_application_argument_sort hstep HTA HTB HX HF
      exact ⟨_, .app (constant_exposure hroot HF) .refl,
        recovered_application_type_arguments_checked hstep HTA HX HY RN HA⟩
    · intro y u E HY
      cases E
      have HX := inferred_application_argument_sort hstep HTB HTA HY (.symm HF)
      exact ⟨_, .app (constant_exposure hroot (.symm HF)) .refl,
        .symm (recovered_application_type_arguments_checked hstep HTA HX HY RN HA)⟩
  | appComputed RF HF HA =>
    constructor
    · intro x u E HX
      cases E
      have HY := inferred_application_argument_sort hstep HTA HTB HX HF
      exact ⟨_, .app (constant_exposure hroot HF) .refl,
        computed_application_type_arguments_checked hstep HTA HX HY RF HA⟩
    · intro y u E HY
      cases E
      have HX := inferred_application_argument_sort hstep HTB HTA HY (.symm HF)
      exact ⟨_, .app (constant_exposure hroot (.symm HF)) .refl,
        .symm (computed_application_type_arguments_checked hstep HTA HX HY RF HA)⟩
  | compute RA RB HC ih =>
    have IH := ih (typed_compute hstep HTA RA) (typed_compute hstep HTB RB) EK
    constructor
    · intro x u E HX
      obtain ⟨x', EX, RX⟩ := unary_compute hroot (E ▸ RA)
      obtain ⟨y, RY, HY⟩ := IH.1 x' u EX (HX.compute hstep RX)
      exact ⟨y, RB.trans RY, .compute RX .refl HY⟩
    · intro y u E HY
      obtain ⟨y', EY, RY⟩ := unary_compute hroot (E ▸ RB)
      obtain ⟨x, RX, HX⟩ := IH.2 y' u EY (HY.compute hstep RY)
      exact ⟨x, RA.trans RX, .compute RY .refl HX⟩
  | symm H ih => exact (ih HTB HTA EK).symm
  | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro x u E HX <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- One displayed unary constant spine suffices to expose the other endpoint
and retain common comparison of its type argument. The source's actual type
argument is preserved, even if it computes during the supplied comparison. -/
theorem computed_stable_unary_type_exposure
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (HTA : TypedSource Δ (.app (.const c []) x)) (HTB : TypedSource Δ b)
    (HX : ControlTyping Δ x (.sort u))
    (H : ComputedJointCompare Step Δ false (.app (.const c []) x) b) :
    ∃ y, ScopedCompute Step Δ b (.app (.const c []) y) ∧ ComputedJointCompare Step Δ true x y :=
  (unary_exposure_pair hstep hroot H HTA HTB).1 x u rfl HX

private theorem binary_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (H : ComputedJointCompare Step Δ false a b)
    (HTA : TypedSource Δ a) (HTB : TypedSource Δ b) :
    (∀ x value u, a = .app (.app (.const c []) x) value → ControlTyping Δ x (.sort u) →
      ∃ y other, ScopedCompute Step Δ b (.app (.app (.const c []) y) other) ∧
        ComputedJointCompare Step Δ true x y) ∧
    (∀ y value u, b = .app (.app (.const c []) y) value → ControlTyping Δ y (.sort u) →
      ∃ x other, ScopedCompute Step Δ a (.app (.app (.const c []) x) other) ∧
        ComputedJointCompare Step Δ true y x) := by
  change ComputedJointCheck Step Δ (.compare false) a b at H
  generalize EK : JointCheckKind.compare false = kind at H
  induction H with
  | leaf H =>
    cases EK
    cases H with
    | refl => constructor <;> intro x value u E HX <;> exact ⟨x, value, E ▸ .refl, .leaf .refl⟩
    | sort | const => constructor <;> intro x value u E HX <;> cases E
  | app HF HA | appCarrier RN HF HA | appComputed RN HF HA =>
    constructor
    · intro x value u E HX
      cases E
      obtain ⟨y, RY, HY⟩ := computed_stable_unary_type_exposure hstep hroot
        (typed_app_fn HTA) (typed_app_fn HTB) HX HF
      exact ⟨y, _, .app RY .refl, HY⟩
    · intro y value u E HY
      cases E
      obtain ⟨x, RX, HX⟩ := computed_stable_unary_type_exposure hstep hroot
        (typed_app_fn HTB) (typed_app_fn HTA) HY (.symm HF)
      exact ⟨x, _, .app RX .refl, HX⟩
  | compute RA RB HC ih =>
    have IH := ih (typed_compute hstep HTA RA) (typed_compute hstep HTB RB) EK
    constructor
    · intro x value u E HX
      obtain ⟨x', value', EX, RX, _⟩ := binary_compute hroot (E ▸ RA)
      obtain ⟨y, other, RY, HY⟩ := IH.1 x' value' u EX (HX.compute hstep RX)
      exact ⟨y, other, RB.trans RY, .compute RX .refl HY⟩
    · intro y value u E HY
      obtain ⟨y', value', EY, RY, _⟩ := binary_compute hroot (E ▸ RB)
      obtain ⟨x, other, RX, HX⟩ := IH.2 y' value' u EY (HY.compute hstep RY)
      exact ⟨x, other, RA.trans RX, .compute RY .refl HX⟩
  | symm H ih => exact (ih HTB HTA EK).symm
  | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro x value u E HX <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- A displayed binary constructor spine exposes the opposite constructor and
retains comparison of their first type arguments. The opposite source may be
neutral; no constructor shape or field typing is assumed for it beforehand. -/
theorem computed_stable_binary_type_exposure
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (HTA : TypedSource Δ (.app (.app (.const c []) x) value)) (HTB : TypedSource Δ b)
    (HX : ControlTyping Δ x (.sort u))
    (H : ComputedJointCompare Step Δ false (.app (.app (.const c []) x) value) b) :
    ∃ y other, ScopedCompute Step Δ b (.app (.app (.const c []) y) other) ∧
      ComputedJointCompare Step Δ true x y :=
  (binary_exposure_pair hstep hroot H HTA HTB).1 x value u rfl HX

/-- For a displayed dependent-pair constructor, inferred core comparison
retains comparison of its selected type field with the other major's type
projection. The other major is exposed computationally inside the proof;
no shape or independent field-comparison premise is imposed on it. -/
theorem proofErase_core_pair_selected_type_projection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EX : proofErase Γ x = .app (.app (.const info.ctorName []) A) a)
    (H : ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) true
      A (.proj family 0 (proofErase Γ y)) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
    intro Δ levels args out HR
    exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0 (Δ := Δ) HR
  have hproj := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ x)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 x, hΓ, rfl, hproj, if_neg (not_isProof_of_sort hΓ hproj)⟩
  have HA : ControlTyping (proofEraseCtx Γ) A (.sort (.succ .zero)) := by
    apply HT.compute (Step := fun _ => ErasedLevelCore D) @hstep
    rw [EX]
    exact .base (.inl (.inl (.inl (.projIota hi (args := [A, a])
      (by simp [hp, hf]) (by simp [hp])))))
  have TX : TypedSource (proofEraseCtx Γ) (proofErase Γ x) := ⟨Γ, x, _, hΓ, rfl, hx, rfl⟩
  have TY : TypedSource (proofEraseCtx Γ) (proofErase Γ y) := ⟨Γ, y, _, hΓ, rfl, hy, rfl⟩
  rw [EX] at TX
  obtain ⟨B, b, RY, HC⟩ := computed_stable_binary_type_exposure @hstep @hroot TX TY HA
    (by simpa only [EX] using H)
  have RB : ScopedCompute (fun _ => ErasedLevelCore D) (proofEraseCtx Γ)
      (.proj family 0 (.app (.app (.const info.ctorName []) B) b)) B :=
    .base (.inl (.inl (.inl (.projIota hi (args := [B, b])
      (by simp [hp, hf]) (by simp [hp])))))
  exact .compute .refl ((ScopedCompute.proj RY).trans RB) HC

end Lean4Lean.VEnv.Strengthening
