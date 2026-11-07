import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionOpacity

/-! # Reading type arguments from inferred constructor-prefix comparisons

A stable constant head allows computation prefixes to be read componentwise.
At independently sort-typed arguments, native carrier checks give ordinary
comparison. This retains type-argument evidence that head-and-arity exposure
alone discards. Administrative expansions are not assumed head-stable.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem control_realize (H : ControlTyping Δ e t)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ) :
    ∃ f, env.HasType univs Γ f t.expr ∧ proofErase Γ f = e := by
  obtain ⟨Γ', f, hΓ', EΓ', hf, Ef⟩ := H
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  exact ⟨f, hf.defeqDFC henv W, (proofErase_defeqCtx hΓ' W hf).symm.trans Ef⟩

private theorem typed_compute (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ a) (R : ScopedCompute Step Δ a b) : TypedSource Δ b := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R
  exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, Ee'⟩

private theorem typed_app_fn (HT : TypedSource Δ (.app f a)) : TypedSource Δ f :=
  (ScopedHole.appFn .hole a).typed HT

/-- A recovered application domain checks two independently sort-typed
arguments by ordinary comparison. Only the left application needs an actual
typed realization; its recovered domain types the left argument. -/
theorem recovered_application_type_arguments_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (.app f x))
    (HX : ControlTyping Δ x (.sort u)) (HY : ControlTyping Δ y (.sort v))
    (RN : ScopedTypeRecovery Step Δ f (.forallE A B))
    (H : ComputedJointCarrierGuard Step Δ A x y) :
    ComputedJointCompare Step Δ true x y := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨D, C, hf, hx⟩ := ht.app_inv henv hΓ
  have RN' : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f₀) (.forallE A B) := by
    rw [EΓ, Ef]; exact RN
  obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN'
  obtain ⟨A₀, B₀, rfl, _, EA, _⟩ := erase_forallE_inv EP
  have hxA := argument_at_displayed_domain hΓ hf hfP hx
  obtain ⟨x₁, hx₁, Ex₁⟩ := control_realize HX hΓ EΓ
  obtain ⟨y₁, hy₁, Ey₁⟩ := control_realize HY hΓ EΓ
  have hn : ¬ IsProof Γ x₀ := fun hp => HX.ne_proof (Ex.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hxA hx₁ (Ex.trans Ex₁.symm)).2 hn
  have hx₁A := ((HE.defeq hΓ).of_l henv hΓ hxA).hasType.2
  have HC := proofErase_computed_carrier_types_checked hstep hΓ hx₁ hy₁ (.inl hx₁A)
    (by simpa only [EΓ, EA, Ex₁, Ey₁] using H)
  simpa only [EΓ, Ex₁, Ey₁] using HC

omit [Params] in
private theorem unary_compute
    (hroot : SpineRootLevels Step c)
    (R : ScopedCompute Step Δ (.app (.const c []) x) out) :
    ∃ y, out = .app (.const c []) y ∧ ScopedCompute Step Δ x y := by
  obtain ⟨ls', args', EO, HL, HA⟩ :=
    (show ScopedCompute Step Δ (ProofShape.mkApps (.const c []) [x]) out from R).const_spine_levels hroot
  cases HL
  cases HA with
  | cons RX HS => cases HS; exact ⟨_, EO, RX⟩

/-- Inferred comparison of stable unary constant spines retains an ordinary
comparison of their type arguments. Full computed-checker recursion is allowed,
including native-domain applications and arbitrary computation prefixes.
Both type arguments may compute; their original endpoints are restored by
those same component paths. -/
theorem computed_stable_unary_type_argument
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (HTX : TypedSource Δ (.app (.const c []) x))
    (HTY : TypedSource Δ (.app (.const c []) y))
    (HX : ControlTyping Δ x (.sort u)) (HY : ControlTyping Δ y (.sort v))
    (H : ComputedJointCompare Step Δ false (.app (.const c []) x) (.app (.const c []) y)) :
    ComputedJointCompare Step Δ true x y := by
  generalize EL : ProofShape.app (.const c []) x = a at H
  generalize ER : ProofShape.app (.const c []) y = b at H
  change ComputedJointCheck Step Δ (.compare false) a b at H
  generalize EK : JointCheckKind.compare false = kind at H
  induction H generalizing x y u v with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (EL.trans ER.symm)).2
      rw [E]; exact .leaf .refl
    | sort | const => cases EL
  | app HF HA => cases EL; cases ER; exact HA
  | appCarrier RN HF HA =>
    cases EL; cases ER
    exact recovered_application_type_arguments_checked hstep HTX HX HY RN HA
  | appComputed RN HF HA =>
    cases EL
    obtain ⟨ls', args', EO, _, _⟩ :=
      (show ScopedCompute Step _ (ProofShape.mkApps (.const c []) []) _ from RN).const_spine_levels hroot
    have E := congrArg ProofShape.constHead EO
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | compute RA RB HC ih =>
    obtain ⟨x', EX, RX⟩ := unary_compute hroot (EL ▸ RA)
    obtain ⟨y', EY, RY⟩ := unary_compute hroot (ER ▸ RB)
    have RAX : ScopedCompute Step _ (.app (.const c []) x) _ := EL ▸ RA
    have RBY : ScopedCompute Step _ (.app (.const c []) y) _ := ER ▸ RB
    rw [EX] at RAX
    rw [EY] at RBY
    exact .compute RX RY (ih
      (typed_compute hstep HTX RAX)
      (typed_compute hstep HTY RBY)
      (HX.compute hstep RX) (HY.compute hstep RY) EX.symm EY.symm EK)
  | symm H ih => exact .symm (ih HTY HTX HY HX ER EL EK)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases EL
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

omit [Params] in
private theorem binary_compute
    (hroot : SpineRootLevels Step c)
    (R : ScopedCompute Step Δ (.app (.app (.const c []) x) a) out) :
    ∃ y b, out = .app (.app (.const c []) y) b ∧
      ScopedCompute Step Δ x y ∧ ScopedCompute Step Δ a b := by
  obtain ⟨ls', args', EO, HL, HA⟩ :=
    (show ScopedCompute Step Δ (ProofShape.mkApps (.const c []) [x, a]) out from R).const_spine_levels hroot
  cases HL
  cases HA with
  | cons RX HS =>
    cases HS with
    | cons RA HS => cases HS; exact ⟨_, _, EO, RX, RA⟩

/-- A second applied argument does not hide the first type argument in inferred
comparison. This covers fully applied two-field constructor spines, including
recursive carrier-aware application rules and every compatible computation
prefix allowed by the stable-head primitive relation. -/
theorem computed_stable_binary_type_argument
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step c)
    (HTX : TypedSource Δ (.app (.app (.const c []) x) a))
    (HTY : TypedSource Δ (.app (.app (.const c []) y) b))
    (HX : ControlTyping Δ x (.sort u)) (HY : ControlTyping Δ y (.sort v))
    (H : ComputedJointCompare Step Δ false
      (.app (.app (.const c []) x) a) (.app (.app (.const c []) y) b)) :
    ComputedJointCompare Step Δ true x y := by
  generalize EL : ProofShape.app (.app (.const c []) x) a = left at H
  generalize ER : ProofShape.app (.app (.const c []) y) b = right at H
  change ComputedJointCheck Step Δ (.compare false) left right at H
  generalize EK : JointCheckKind.compare false = kind at H
  induction H generalizing x y a b u v with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (ProofShape.app.inj (EL.trans ER.symm)).1).2
      rw [E]; exact .leaf .refl
    | sort | const => cases EL
  | app HF HA | appCarrier RN HF HA | appComputed RN HF HA =>
    cases EL; cases ER
    exact computed_stable_unary_type_argument hstep hroot
      (typed_app_fn HTX) (typed_app_fn HTY) HX HY HF
  | compute RA RB HC ih =>
    obtain ⟨x', a', EX, RX, RXa⟩ := binary_compute hroot (EL ▸ RA)
    obtain ⟨y', b', EY, RY, RYb⟩ := binary_compute hroot (ER ▸ RB)
    have RAX : ScopedCompute Step _ (.app (.app (.const c []) x) a) _ := EL ▸ RA
    have RBY : ScopedCompute Step _ (.app (.app (.const c []) y) b) _ := ER ▸ RB
    rw [EX] at RAX
    rw [EY] at RBY
    exact .compute RX RY (ih (typed_compute hstep HTX RAX) (typed_compute hstep HTY RBY)
      (HX.compute hstep RX) (HY.compute hstep RY) EX.symm EY.symm EK)
  | symm H ih => exact .symm (ih HTY HTX HY HX ER EL EK)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases EL
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- Actual dependent-pair constructors compared by the full inferred core
checker expose comparison of their selected type fields, with both projection
redexes already contracted. Actual projection typing supplies the field sorts;
no type-argument comparison is assumed and no forward beta/iota checker law
is used. Common-mode structure eta and expanded primitive stages are outside
this theorem. -/
theorem proofErase_core_pair_constructor_type_fields
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
    (EY : proofErase Γ y = .app (.app (.const info.ctorName []) B) b)
    (H : ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) true A B := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
    intro Δ levels args out HR
    exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0 (Δ := Δ) HR
  have field {z C value} (hzt : env.HasType univs Γ z (.const family []))
      (EZ : proofErase Γ z = .app (.app (.const info.ctorName []) C) value) :
      ControlTyping (proofEraseCtx Γ) C (.sort (.succ .zero)) := by
    have hproj := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hzt).1
    have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ z)) (.sort (.succ .zero)) :=
      ⟨Γ, .proj family 0 z, hΓ, rfl, hproj, if_neg (not_isProof_of_sort hΓ hproj)⟩
    apply HT.compute (Step := fun _ => ErasedLevelCore D) @hstep
    rw [EZ]
    exact .base (.inl (.inl (.inl (.projIota hi (args := [C, value])
      (by simp [hp, hf]) (by simp [hp])))))
  have HA := field hx EX
  have HB := field hy EY
  have TX : TypedSource (proofEraseCtx Γ) (proofErase Γ x) := ⟨Γ, x, _, hΓ, rfl, hx, rfl⟩
  have TY : TypedSource (proofEraseCtx Γ) (proofErase Γ y) := ⟨Γ, y, _, hΓ, rfl, hy, rfl⟩
  rw [EX] at TX
  rw [EY] at TY
  exact computed_stable_binary_type_argument @hstep @hroot TX TY HA HB (by simpa only [EX, EY] using H)

end Lean4Lean.VEnv.Strengthening
