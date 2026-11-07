import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeExposure

/-! # Contract displayed type-field projections in core comparisons

A projection of a displayed two-field constructor can be contracted inside a
comparison of sort-typed endpoints. Computation either retains the projection
with a computed selected field, or has already selected that field. The proj
checker rule uses one-sided inferred constructor exposure. This is a specific
iota law, not forward closure under arbitrary beta or core computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private binary_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params] {D : Definitions}

private theorem pair_select (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2) :
    Primitive D (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) A :=
  .projIota hi (args := [A, value]) (by simp [hp, hf]) (by simp [hp])

private theorem pair_select_path (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2) :
    ScopedCompute (fun _ => ErasedLevelCore D) Δ
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) A :=
  .base (.inl (.inl (.inl (pair_select hi hp hf))))

private theorem control_source (H : ControlTyping Δ a t) : TypedSource Δ a := by
  obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := H
  exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩

private theorem typed_proj_major (H : TypedSource Δ (.proj s i m)) : TypedSource Δ m :=
  (ScopedHole.proj s i .hole).typed H

private theorem sort_control_not_lam (H : ControlTyping Δ (.lam A b) (.sort u)) : False := by
  obtain ⟨Γ, e, hΓ, _, ht, Ee⟩ := H
  exact sort_not_lam hΓ ht Ee

/-- Core computation from a displayed pair's first projection either retains
that projection with a computed field, or is already reachable from the selected
field. Constructor stability preserves the saturated spine and exact index. -/
theorem core_pair_projection_path_cases
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName)
    (R : ScopedCompute (fun _ => ErasedLevelCore D) Δ
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) out) :
    (∃ A' value', out = .proj family 0 (.app (.app (.const info.ctorName []) A') value') ∧
      ScopedCompute (fun _ => ErasedLevelCore D) Δ A A') ∨
    ScopedCompute (fun _ => ErasedLevelCore D) Δ A out := by
  obtain ⟨cost, RC⟩ := R.count
  rcases RC.projection_first_root with ⟨major, EO, RM⟩ |
      ⟨major, field, _, _, _, RM, HR, RT⟩
  · obtain ⟨A', value', EM, RA, _⟩ := binary_compute @hroot RM.forget
    exact .inl ⟨A', value', by rw [EO, EM], RA⟩
  · obtain ⟨A', value', EM, RA, _⟩ := binary_compute @hroot RM.forget
    obtain ⟨info', levels, args, hi', EM', hl, hg⟩ := erased_level_core_projection_root HR
    have RI : Primitive D (.proj family 0 major) field := by
      rw [EM']; exact .projIota hi' hl hg
    have RI' : Primitive D (.proj family 0 major) A' := by
      rw [EM]; exact pair_select hi hp hf
    have EF := RI.projection_deterministic RI'
    exact .inr (RA.trans (EF ▸ RT.forget))

private theorem contraction_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (H : ComputedJointCompare (fun _ => ErasedLevelCore D) Δ true a b)
    (HA : ControlTyping Δ a (.sort u)) (HB : ControlTyping Δ b (.sort v)) :
    (∀ A value, a = .proj family 0 (.app (.app (.const info.ctorName []) A) value) →
      ComputedJointCompare (fun _ => ErasedLevelCore D) Δ true A b) ∧
    (∀ B value, b = .proj family 0 (.app (.app (.const info.ctorName []) B) value) →
      ComputedJointCompare (fun _ => ErasedLevelCore D) Δ true B a) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
    intro Ω levels args out HR
    exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0 (Δ := Ω) HR
  change ComputedJointCheck _ Δ (.compare true) a b at H
  generalize EK : JointCheckKind.compare true = kind at H
  induction H generalizing u v with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      constructor <;> intro A value E
      all_goals
        rw [E]
        exact .compute .refl (pair_select_path hi hp hf) (.leaf .refl)
    | sort | const => constructor <;> intro A value E <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_control_not_lam (E ▸ HA)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_control_not_lam (E ▸ HB)).elim
  | proj HM =>
    constructor
    · intro A value E
      cases E
      have HA' := HA.compute (Step := fun _ => ErasedLevelCore D) @hstep (pair_select_path hi hp hf)
      obtain ⟨B, other, RM, HC⟩ := computed_stable_binary_type_exposure @hstep @hroot
        (typed_proj_major (control_source HA)) (typed_proj_major (control_source HB)) HA' HM
      exact .compute .refl ((ScopedCompute.proj RM).trans (pair_select_path hi hp hf)) HC
    · intro B value E
      cases E
      have HB' := HB.compute (Step := fun _ => ErasedLevelCore D) @hstep (pair_select_path hi hp hf)
      obtain ⟨A, other, RM, HC⟩ := computed_stable_binary_type_exposure @hstep @hroot
        (typed_proj_major (control_source HB)) (typed_proj_major (control_source HA)) HB' (.symm HM)
      exact .compute .refl ((ScopedCompute.proj RM).trans (pair_select_path hi hp hf)) HC
  | compute RA RB HC ih =>
    cases EK
    have IH := ih (HA.compute (Step := fun _ => ErasedLevelCore D) @hstep RA)
      (HB.compute (Step := fun _ => ErasedLevelCore D) @hstep RB) rfl
    constructor
    · intro A value E
      rcases core_pair_projection_path_cases hi hp hf @hroot (E ▸ RA) with ⟨A', value', EO, RF⟩ | RF
      · exact .compute RF RB (IH.1 A' value' EO)
      · exact .compute RF RB HC
    · intro B value E
      rcases core_pair_projection_path_cases hi hp hf @hroot (E ▸ RB) with ⟨B', value', EO, RF⟩ | RF
      · exact .compute RF RA (IH.2 B' value' EO)
      · exact .compute RF RA (.symm HC)
  | symm H ih => exact (ih HB HA EK).symm
  | app | appCarrier | appComputed | forallE | forallSorted =>
    constructor <;> intro A value E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_control_not_lam HA).elim
  | etaBodyR => exact (sort_control_not_lam HB).elim
  | structFields hi' hz' hp' hf' =>
    obtain ⟨Γ, e, hΓ, _, ht, Ee⟩ := HA
    exact (sort_not_constructor hΓ ht hi' hz' hp' hf' Ee).elim
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- Contract a displayed first projection of a two-field constructor in a
comparison of independently sort-typed endpoints. The other endpoint is
arbitrary. This handles every common-mode checker constructor in the ordinary
level core, without confluence or generalized forward beta closure. -/
theorem core_pair_type_projection_contract
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HA : ControlTyping Δ (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) (.sort u))
    (HB : ControlTyping Δ b (.sort v))
    (H : ComputedJointCompare (fun _ => ErasedLevelCore D) Δ true
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) b) :
    ComputedJointCompare (fun _ => ErasedLevelCore D) Δ true A b :=
  (contraction_pair heq hs hi hp hf hD H HA HB).1 A value rfl

omit [Params] in
private theorem two_arguments {args : List α} (H : args.length = 2) :
    ∃ a b, args = [a, b] := by
  cases args with
  | nil => simp at H
  | cons a args =>
    cases args with
    | nil => simp at H
    | cons b rest =>
      have E : rest = [] := by simpa using H
      exact ⟨a, b, by rw [E]⟩

/-- A selected first field of an actually typed closed dependent pair has the
exact two-argument, empty-universe constructor shape required by contraction.
The original projection's primitive supplies the selected field; actual typing
rules out extra universe arguments. -/
theorem proofErase_closed_pair_selection_shape
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) field) :
    ∃ value, proofErase Γ x = .app (.app (.const info.ctorName []) field) value := by
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
    (show ([] : List VExpr).length = info.nparams from hp.symm) hz hx).2 (.inl hadm)
  obtain ⟨ci, Hci, _, hls⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hexp⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at Hci
  cases Option.some.inj Hci
  have hu : info.uvars = 0 := hls.symm
  generalize EM : proofErase Γ x = m at RI
  cases RI with
  | projIota hi' hl hg =>
    cases henv.ordered.projections_unique hi hi'
    obtain ⟨original, EX, _⟩ := proofErase_const_spine_inv EM
    have hw : VExpr.WF env univs Γ x := ⟨_, hx⟩
    rw [EX] at hw
    obtain ⟨ci', Hci', _, hls'⟩ := (VExpr.WF.of_mkApps henv hΓ hw).const_inv henv hΓ
    rw [henv.ordered.projectionConstructor hi] at Hci'
    cases Option.some.inj Hci'
    simp only [hu] at hls'
    have EL := hls'
    simp at EL
    cases EL
    obtain ⟨A, value, Eargs⟩ := two_arguments (by simpa only [hp, hf, Nat.zero_add] using hl)
    rw [Eargs] at EM hg
    simp only [hp, Nat.add_zero, List.getElem?_cons_zero] at hg
    cases Option.some.inj hg
    exact ⟨value, by simp only [Eargs, ProofShape.mkApps]⟩

/-- The full ordinary-core carrier checker supports one-sided type-field
selection of an actual dependent pair. The opposite result may retain its
projection or select its field too. Structure eta, carrierChecked and nested
carrier certificates are all included through typed field readout followed by
the proved sort-typed projection contraction. No extra selection obligation,
confluence or forward beta-closure premise is supplied. -/
theorem proofErase_core_pair_type_field_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) left)
    (RR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) true left right := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute (fun _ => ErasedLevelCore D) Δ a b :=
    fun R => .base (.inl (.inl (.inl R)))
  have HC := (proofErase_computed_dependent_pair_fields @hstep @hprim hi hp hf hz hadm hshape hΓ hx hy H).1
  have hpx := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have TX : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ x)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 x, hΓ, rfl, hpx, if_neg (not_isProof_of_sort hΓ hpx)⟩
  have TY : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 y, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have TL : ControlTyping (proofEraseCtx Γ) left (.sort (.succ .zero)) :=
    TX.compute (Step := fun _ => ErasedLevelCore D) @hstep (hprim RI)
  obtain ⟨value, EX⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hx RI
  rw [EX] at TX HC
  have HL := core_pair_type_projection_contract heq hs hi hp hf hD TX TY HC
  rcases RR.keep_or_primitive (D := D) with rfl | RR
  · exact HL
  · obtain ⟨other, EY⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hy RR
    rw [EY] at TY HL
    exact .symm (core_pair_type_projection_contract heq hs hi hp hf hD TY TL (.symm HL))

/-- Every pair of terminal type-field results compares for an actual core
record guard: either projection can independently be retained or selected.
This discharges the complete ordinary-core terminal-selection condition. -/
theorem proofErase_core_pair_terminal_type_fields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (RL : ProjectionResult family 0 (proofErase Γ x) left)
    (RR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) true left right := by
  rcases RL.keep_or_primitive (D := D) with rfl | RL
  · rcases RR.keep_or_primitive (D := D) with rfl | RR
    · exact (proofErase_computed_dependent_pair_fields (erased_level_core_descent hs)
        (fun R => .base (.inl (.inl (.inl R)))) hi hp hf hz hadm hshape hΓ hx hy H).1
    · exact .symm (proofErase_core_pair_type_field_selection heq hs hi hp hf hz hadm hshape hD
        hΓ hy hx (.carrierSymm H) RR .keep)
  · exact proofErase_core_pair_type_field_selection heq hs hi hp hf hz hadm hshape hD hΓ hx hy H RL RR

/-- The actual environment core supplies soundness and the no-constructor-
unfolding premise automatically. Its complete carrier checker therefore
supports every terminal combination of the two dependent-pair type fields.
The Pi-inert expansion stages are not identified with this ordinary core. -/
theorem EnvironmentCore.pair_terminal_type_fields
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard (fun _ => ErasedLevelCore EnvironmentCore.definitions)
      (proofEraseCtx Γ) (.const family []) (proofErase Γ x) (proofErase Γ y))
    (RL : ProjectionResult family 0 (proofErase Γ x) left)
    (RR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (fun _ => ErasedLevelCore EnvironmentCore.definitions)
      (proofEraseCtx Γ) true left right :=
  proofErase_core_pair_terminal_type_fields heq EnvironmentCore.sound hi hp hf hz hadm hshape
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi)) hΓ hx hy H RL RR

end Lean4Lean.VEnv.Strengthening
