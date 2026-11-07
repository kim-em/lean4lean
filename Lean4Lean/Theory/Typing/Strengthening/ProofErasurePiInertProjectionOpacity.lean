import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionFrames

/-! # Opaque major spines obstruct variable field selection

Stage-zero constant wrappers cannot hide a change of a core-stable constant
head at an exposed output. Consequently, a sorted projection of a different
opaque head cannot compute to a variable. A constructor-to-opaque-major path
therefore obstructs the proposed field-selection law and typed core confluence.
The obstruction is conditional on that actual path; no environment or
counterexample to canonical-Eq strengthening is asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- Absence of selected delta equations and registered pattern heads is enough
for core spine stability. The constant may still have an ordinary definition
in the environment; no semantic rigidity of that alias is assumed. -/
theorem erased_level_core_spine_stable_of_no_rules
    (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hpat : ∀ {p r}, Pat p r → p.constHead ≠ some c) :
    SpineRootLevels (fun _ => ErasedLevelCore D) c := by
  have hn {a b} (H : ErasedIotaPrimitive D a b) (hh : a.constHead = some c) : False := by
    rcases H with (H | H) | H
    · cases H with
      | delta HD => cases Option.some.inj hh; exact hD _ _ HD
      | projIota => cases hh
    · cases H with
      | select hp _ hm => exact hpat hp (hm.constHead.symm.trans hh)
      | apply hp _ hm => exact hpat hp (hm.constHead.symm.trans hh)
    · cases H with
      | intro hp _ _ hm => exact hpat hp (hm.constHead.symm.trans hh)
  intro Δ ls args out H
  rcases H with H | H
  · exact (hn H (ProofShape.constHead_mkApps _ _)).elim
  · exact level_primitive_spine_roots univs c (Δ := Δ) H

/-- Bypass an administrative expansion at a proper spine prefix before any
non-lambda-headed result. Pending arguments, native stage and scope remain
exact; the primitive count cannot increase. -/
theorem pi_inert_expansion_prefix_count_bypass_nonlambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps target pending) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ (ProofShape.mkApps source pending) out := by
  rcases H with H | H
  · obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
    cases H with
    | intro _ =>
      have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
        .sort (by trivial)
      have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
        if_neg (not_isProof_of_sort hΓ hA)
      exact pi_inert_constant_spine_count_eliminate heq hs hΓ hA ht hout
        (by simpa only [EA, ProofShape.constantExpansion] using RT)
  · cases H with
    | intro _ => exact RT.pi_inert_identity_spine_eliminate hout

/-- Core-stable constant heads survive every stage-zero computation with a
non-lambda-headed output. Minimal primitive count eliminates arbitrarily many
constant expansions, including expansions at proper spine prefixes. This
needs soundness and typing but not typed core confluence or normalization. -/
theorem pi_inert_zero_stable_spine_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (R : ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c ls) args) out) :
    ∃ ls' args', out = ProofShape.mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) args args' := by
  obtain ⟨cost, RC, Hmin⟩ := R.minimal_count
  rcases RC.const_spine_or_cut @hroot with H |
      ⟨ls', pre, pending, target, cp, ct, HC, _, _, RP, HR, HN, RT⟩
  · exact H
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs 0
      hΓ hΓ' W ht R.1
  rcases HR.1 with HR | HR
  · exact (HN HR).elim
  · have HP := RP.forget.spine_cut_source_typed hd HT
    obtain ⟨k, hk, RK⟩ := pi_inert_expansion_prefix_count_bypass_nonlambda heq hs HP
      (Recovery := PiInertStage D 0) (.inl HR) RT hout
    rw [← ProofShape.mkApps_append] at RK
    have HB := Hmin (cp + k) (RP.trans RK)
    omega

omit [Params] in
private theorem const_spine_nonlambda :
    ∀ A b rest, ProofShape.mkApps (.const c ls) args ≠ ProofShape.mkApps (.lam A b) rest := by
  intro A b rest E
  have H := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at H
  cases H

/-- A sorted projection of a core-stable constant spine can compute to a
variable at stage zero only if that head is the registered constructor itself.
Administrative wrapper insertion cannot manufacture constructor exposure. -/
theorem pi_inert_zero_projection_variable_head
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : ControlTyping Δ (.proj family i (ProofShape.mkApps (.const c ls) args)) (.sort u))
    (HM : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (R : ScopedCompute (PiInertStage D 0) Δ
      (.proj family i (ProofShape.mkApps (.const c ls) args)) (.bvar j)) :
    c = info.ctorName := by
  have hout : ∀ A b rest, ProofShape.bvar j ≠ ProofShape.mkApps (.lam A b) rest := by
    intro A b rest E
    cases rest using List.snoc_induction with
    | nil => cases E
    | snoc rest a => rw [ProofShape.mkApps_snoc] at E; cases E
  obtain ⟨major, RM, RI⟩ := pi_inert_sorted_projection_terminal_selection heq hs HT hout
    (fun _ E => ProofShape.noConfusion E) R
  cases RI with
  | projIota hi' hl hg =>
    cases henv.ordered.projections_unique hi hi'
    obtain ⟨_, _, E, _, _⟩ := pi_inert_zero_stable_spine_readout heq hs @hroot HM
      const_spine_nonlambda RM
    have HC := congrArg ProofShape.constHead E
    simpa only [ProofShape.constHead_mkApps, ProofShape.constHead, Option.some.injEq] using HC.symm

/-- If constructor unfolding is absent, selection commutes with an arbitrary
stage-zero major path ending at a non-lambda-headed output. The residual is
another saturated constructor, and the original selected field computes to
its new selected field at the same stage. No core confluence is required. -/
theorem pi_inert_zero_constructor_selection_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ m)
    (RI : Primitive D (.proj family i m) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (R : ScopedCompute (PiInertStage D 0) Δ m out) :
    ∃ selected, Primitive D (.proj family i out) selected ∧
      ScopedCompute (PiInertStage D 0) Δ field selected := by
  cases RI with
  | projIota hi' hl hg =>
    cases henv.ordered.projections_unique hi hi'
    have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
      intro Ω levels params target HR
      exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0
        (Δ := Ω) HR
    obtain ⟨ls', args', rfl, _, HA⟩ := pi_inert_zero_stable_spine_readout heq hs @hroot HT hout R
    obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hg
    have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
    have RF := HA.getElem_of (info.nparams + i) hj hj'
    rw [HE] at RF
    exact ⟨_, .projIota hi (HA.length_eq.symm.trans hl)
      (List.getElem?_eq_some_iff.2 ⟨hj', rfl⟩), RF⟩

/-- The open selection law cannot coexist with a stage-zero path from a
variable-selecting record to a differently headed opaque major. All actual
typings and the path are explicit; this is an obstruction schema, not a
constructed counterexample environment. -/
theorem pi_inert_pair_selection_opaque_obstruction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c) (hne : c ≠ info.ctorName)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EY : proofErase Γ y = ProofShape.mkApps (.const c ls) args)
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) (.bvar j))
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    ¬ PiInertPairTypeFieldSelection D 0 family := by
  intro K
  have HG : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y) :=
    .carrierReduce R .refl (.carrierChecked (.leaf .refl))
  have RP := K.variable_readout heq hs hi hp hf hz hadm hshape hΓ hx hy HG RI
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 y, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have HM : TypedSource (proofEraseCtx Γ) (proofErase Γ y) := ⟨Γ, y, _, hΓ, rfl, hy, rfl⟩
  rw [EY] at RP HT HM
  exact hne (pi_inert_zero_projection_variable_head heq hs hi @hroot HT HM RP)

/-- The same opaque-major configuration is incompatible with typed core
confluence. Thus the obstruction cannot occur in the actual EnvironmentCore;
soundness of a selected definition table alone does not provide this escape. -/
theorem pi_inert_opaque_major_no_core_confluence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c) (hne : c ≠ info.ctorName)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EY : proofErase Γ y = ProofShape.mkApps (.const c ls) args)
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) (.bvar j))
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    ¬ TypedCoreConfluence (ErasedLevelCore D) := by
  intro hc
  have hpx := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have EX : proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ hpx)
  obtain ⟨major, RX, RY⟩ := proofErase_pi_inert_zero_common_core_join heq hs hc hΓ hx hy R .refl
  have RXI : Compute (ErasedLevelCore D) (.proj family 0 (proofErase Γ x)) (.bvar j) :=
    .base (.inl (.inl (.inl RI)))
  obtain ⟨field, RV, RF⟩ := hc hΓ hpx (EX ▸ RXI) (EX ▸ Compute.proj RX)
  have EF : field = .bvar j := (RV.in_pi_inert_stage (n := 0) (Δ := proofEraseCtx Γ)).pi_inert_bvar_fixed
  have RP : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ y)) (.bvar j) :=
    EF ▸ ((Compute.proj RY).trans RF).in_pi_inert_stage
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 y, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have HM : TypedSource (proofEraseCtx Γ) (proofErase Γ y) := ⟨Γ, y, _, hΓ, rfl, hy, rfl⟩
  rw [EY] at RP HT HM
  exact hne (pi_inert_zero_projection_variable_head heq hs hi @hroot HT HM RP)

/-- A single stored constructor-to-alias equation supplies the obstructing
major path. The actual records and alias erasure remain explicit premises;
there is no assumed computation or missing selection theorem in this witness. -/
theorem pi_inert_pair_selection_alias_equation_obstruction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c) (hne : c ≠ info.ctorName)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EX : proofErase Γ x = ProofShape.mkApps (.const info.ctorName ls) args)
    (EY : proofErase Γ y = ProofShape.mkApps (.const c levels) args)
    (hl : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams]? = some (.bvar j))
    (HE : proofErase [] (.const c levels) = .const c levels)
    (HD : D.unfolds info.ctorName ls (.const c levels)) :
    ¬ PiInertPairTypeFieldSelection D 0 family ∧ ¬ TypedCoreConfluence (ErasedLevelCore D) := by
  have RI : Primitive D (.proj family 0 (proofErase Γ x)) (.bvar j) := by
    rw [EX]
    exact .projIota hi hl (by simpa only [Nat.add_zero] using hg)
  have RD : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (.const info.ctorName ls) (.const c levels) := by
    rw [← HE]
    exact .base (pi_inert_stage_core (.inl (.inl (.inl (.delta HD)))))
  have R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) := by
    rw [EX, EY]
    exact RD.mkApps (.rfl (fun _ _ => .refl))
  exact ⟨pi_inert_pair_selection_opaque_obstruction heq hs hi hp hf hz hadm hshape @hroot hne
    hΓ hx hy EY RI R,
    pi_inert_opaque_major_no_core_confluence heq hs hi hp hf hz hadm hshape @hroot hne
      hΓ hx hy EY RI R⟩

end Lean4Lean.VEnv.Strengthening
