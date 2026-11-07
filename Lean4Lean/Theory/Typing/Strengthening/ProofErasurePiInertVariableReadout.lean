import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionRoot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertZeroEvidence

/-! # Exact variable readout from comparison of types

A type variable has no Pi-inert computation. A comparison with it cannot use
function or structure eta because both endpoints are types. Consequently the
other endpoint must compute to that exact variable at the same stage. This
gives an operational test of the proposed dependent-pair selection condition;
ordinary equality of its selected type fields is insufficient for this test.
For majors with a common stage-zero computation, typed core confluence supplies
the full type-field history, including arbitrary future typed substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params] {D : Definitions}

private theorem variable_readout_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCompare (PiInertStage D n) Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ i, sa = .bvar i → ScopedCompute (PiInertStage D n) Δ sb (.bvar i)) ∧
    (∀ i, sb = .bvar i → ScopedCompute (PiInertStage D n) Δ sa (.bvar i)) := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht R.1
  change ComputedJointCheck (PiInertStage D n) Δ (.compare mode) sa sb at H
  generalize EK : JointCheckKind.compare mode = kind at H
  induction H generalizing Γ a b u v mode with
  | leaf H =>
    cases EK
    cases H with
    | refl => exact ⟨fun _ E => E ▸ .refl, fun _ E => E ▸ .refl⟩
    | sort | const => constructor <;> intro _ E <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ ha (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hb (Eb.trans E)).elim
  | app | appCarrier | appComputed | proj | forallE | forallSorted =>
    constructor <;> intro _ E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
    exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hd hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hd hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB EK
    constructor
    · intro i E
      exact RB.trans (IH.1 i (E ▸ RA).pi_inert_bvar_fixed)
    · intro i E
      exact RA.trans (IH.2 i (E ▸ RB).pi_inert_bvar_fixed)
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea EK).symm
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- For independently sort-typed endpoints, comparison with a variable forces
an exact computation to that same variable. The guard stage and comparison
mode are arbitrary; no confluence or normalization hypothesis is used. -/
theorem proofErase_pi_inert_types_variable_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (Ea : proofErase Γ a = .bvar i)
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ b) (.bvar i) :=
  (variable_readout_pair heq hs H hΓ ha hb rfl rfl rfl).1 i Ea

/-- At a variable type endpoint, either comparison mode is exactly finite
operational readout of the other endpoint, not merely ordinary type equality. -/
theorem proofErase_pi_inert_types_variable_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (Ea : proofErase Γ a = .bvar i) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b) ↔
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ b) (.bvar i) := by
  constructor
  · exact proofErase_pi_inert_types_variable_readout heq hs hΓ ha hb Ea
  · intro R
    rw [Ea]
    exact .compute .refl R (.leaf .refl)

/-- The dependent-pair selection condition entails actual same-stage readout
of any variable selected on the left from the uncontracted right projection.
This remains necessary even when the input record guard arose solely by
computing the left constructor to the right major. -/
theorem PiInertPairTypeFieldSelection.variable_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (K : PiInertPairTypeFieldSelection D n family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) (.bvar i)) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ y)) (.bvar i) := by
  have hpx := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have EX : proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ hpx)
  have EY : proofErase Γ (.proj family 0 y) = .proj family 0 (proofErase Γ y) :=
    if_neg (not_isProof_of_sort hΓ hpy)
  have RX : ScopedCompute (fun _ => ErasedLevelCore D) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ x)) (.bvar i) := .base (.inl (.inl (.inl RI)))
  obtain ⟨a, HA, EA⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hpx rfl EX RX
  have HC := K hΓ hx hy H RI .keep
  have HC' : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ (.proj family 0 y)) := by rwa [EA, EY]
  simpa only [EY] using proofErase_pi_inert_types_variable_readout heq hs hΓ HA.hasType.2 hpy EA HC'

/-- Core-joined actual majors have core-joined terminal type-field results.
The two selections and the major paths are independent. Confluence is used
only at the original typed projections, never at an invented raw intermediate. -/
theorem proofErase_projection_results_core_join
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ (.proj s i x) (.sort u))
    (hy : env.HasType univs Γ (.proj s i y) (.sort v))
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ x) (proofErase Γ y))
    (HL : ProjectionResult s i (proofErase Γ x) left)
    (HR : ProjectionResult s i (proofErase Γ y) right) :
    ComputeJoin (ErasedLevelCore D) left right := by
  have EX : proofErase Γ (.proj s i x) = .proj s i (proofErase Γ x) :=
    if_neg (not_isProof_of_sort hΓ hx)
  have EY : proofErase Γ (.proj s i y) = .proj s i (proofErase Γ y) :=
    if_neg (not_isProof_of_sort hΓ hy)
  obtain ⟨m, RX, RY⟩ := HJ
  obtain ⟨a, RL, RA⟩ := hc hΓ hx (EX ▸ HL.compute) (EX ▸ Compute.proj RX)
  obtain ⟨b, RR, RB⟩ := hc hΓ hy (EY ▸ HR.compute)
    (EY ▸ (Compute.proj RY).trans RA)
  exact ⟨b, RL.trans RB, RR⟩

/-- A finite stage-zero common computation of two actual majors gives an
ordinary core join, including arbitrary interleaving of beta, level roots,
stored equations and constant expansion. The middle term is realized from
one original source before typed confluence is used. -/
theorem proofErase_pi_inert_zero_common_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y B)
    (RX : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) middle)
    (RY : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ y) middle) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ x) (proofErase Γ y) := by
  have JX := RX.pi_inert_zero_core_join heq hs hc ⟨Γ, x, A, hΓ, rfl, hx, rfl⟩
  have JY := RY.pi_inert_zero_core_join heq hs hc ⟨Γ, y, B, hΓ, rfl, hy, rfl⟩
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs 0
      hΓ hΓ' W ht R.1
  obtain ⟨z, HZ, EZ⟩ := proofErase_scoped_compute_realize hd hΓ hx rfl rfl RX
  rw [← EZ] at JX JY
  exact JX.trans_typed hc hΓ HZ.hasType.2 JY.symm

/-- The type-field selection conclusion holds for arbitrary terminal results
when the input record comparison comes from two stage-zero computations to a
common major. This proves that entire computation-to-reflexivity case, with no
normality restriction on either selected field. General structural comparison
certificates and computations using higher-stage guards remain open. -/
theorem pi_inert_pair_type_selection_of_zero_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (RX : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) middle)
    (RY : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ y) middle)
    (HL : ProjectionResult family 0 (proofErase Γ x) left)
    (HR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode left right := by
  have J := proofErase_pi_inert_zero_common_core_join heq hs hc hΓ hx hy RX RY
  obtain ⟨out, RL, RR⟩ := proofErase_projection_results_core_join hc hΓ
    (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
    (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1 J HL HR
  exact .compute RL.in_pi_inert_stage RR.in_pi_inert_stage (.leaf .refl)

/-- Common stage-zero major computations supply the complete type-field
carrier history. All independent field residuals and arbitrary future typed
substitutions are included, so this also supplies the weaker world history.
The output stage is unrestricted and may be zero. -/
theorem pi_inert_pair_type_history_of_zero_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (RX : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ x) middle)
    (RY : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ y) middle) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (.sort (.succ .zero))
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  have hpx := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have TX : TypedSource (proofEraseCtx Γ) (.proj family 0 (proofErase Γ x)) :=
    ⟨Γ, .proj family 0 x, _, hΓ, rfl, hpx, if_neg (not_isProof_of_sort hΓ hpx)⟩
  have TY : TypedSource (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) :=
    ⟨Γ, .proj family 0 y, _, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have J := proofErase_pi_inert_zero_common_core_join heq hs hc hΓ hx hy RX RY
  have H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) :=
    (PiInertEvidence.of_core_join hc TX TY J.proj).join hc
      (PiInertEvidence.of_core_join hc TY TY .refl)
  exact H.carrier_history

omit [Params] in
/-- The actual environment core discharges soundness and confluence in the
common-computation case. The result is a full type-field history, not an
assumed instance of the still-open general selection condition. -/
theorem EnvironmentCore.pair_type_history_of_zero_common
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info Γ x y middle n}, env.HasCanonicalEq → env.projections family info →
      info.nparams = 0 → info.numFields = 2 → info.nindices = 0 →
      (info.resultLevel.inst []).IsNeverZero →
      info.ctorType.instL [] = .forallE (.sort (.succ .zero))
        (.forallE (.bvar 0) (.const family [])) →
      OnCtx Γ (env.IsType U) → env.HasType U Γ x (.const family []) →
      env.HasType U Γ y (.const family []) →
      ScopedCompute (PiInertStage definitions 0) (proofEraseCtx Γ) (proofErase Γ x) middle →
      ScopedCompute (PiInertStage definitions 0) (proofEraseCtx Γ) (proofErase Γ y) middle →
      PiInertCarrierHistory definitions n (proofEraseCtx Γ) (.sort (.succ .zero))
        (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  letI := henv.params U
  intro family info Γ x y middle n heq hi hp hf hz hadm hshape hΓ hx hy RX RY
  exact pi_inert_pair_type_history_of_zero_common heq sound
    (typed_level_core_confluence (fun H => H)) hi hp hf hz hadm hshape hΓ hx hy RX RY

end Lean4Lean.VEnv.Strengthening
