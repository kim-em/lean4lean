import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionResiduals

/-! # Delay projection iota until the end of an ordinary-core path

A selected-field tail can be computed inside the constructor argument before
selection. Thus arbitrary projection residuals need only major residuals and
zero or one final projection contraction. This preserves the exact endpoint;
no normalization or confluence hypothesis is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
namespace ProofShape

/-- Compatible computation of a head and all its arguments computes the spine. -/
theorem Compute.mkApps_pair (HF : Compute Step f g)
    (HA : List.Forall₂ (Compute Step) args args') :
    Compute Step (mkApps f args) (mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

private theorem compute_selected_argument
    (HG : args[j]? = some field) (R : Compute Step field out) :
    List.Forall₂ (Compute Step) args (args.set j out) := by
  induction args generalizing j with
  | nil => simp at HG
  | cons a args ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero] at HG
      cases Option.some.inj HG
      exact .cons R (.rfl (fun _ _ => .refl))
    | succ j =>
      exact .cons .refl (ih (by simpa only [List.getElem?_cons_succ] using HG))

/-- Computation of a selected argument can occur before constructor projection.
Every other argument stays unchanged; dependent typing is not needed for this
raw compatible-computation statement. -/
theorem Compute.selected_argument
    (HG : args[j]? = some field) (R : Compute Step field out) :
    Compute Step (mkApps f args) (mkApps f (args.set j out)) :=
  Compute.mkApps_pair .refl (compute_selected_argument HG R)

end ProofShape
variable [Params] {D : Definitions}
namespace ProofShape

/-- The last action of a projection path: retain the projection or select one
field of its saturated registered constructor. The major has already computed. -/
inductive ProjectionResult (s : Name) (i : Nat) : ProofShape → ProofShape → Prop where
  | keep : ProjectionResult s i m (.proj s i m)
  | select (hi : env.projections s info)
      (hl : args.length = info.nparams + info.numFields)
      (hg : args[info.nparams + i]? = some field) :
      ProjectionResult s i (mkApps (.const info.ctorName ls) args) field

/-- Separate a retained projection from a single primitive selection without
eliminating an indexed equality of actual erasures. -/
theorem ProjectionResult.keep_or_primitive (H : ProjectionResult s i m out) :
    out = .proj s i m ∨ Primitive D (.proj s i m) out := by
  cases H with
  | keep => exact .inl rfl
  | select hi hl hg => exact .inr (.projIota hi hl hg)

/-- A terminal projection result is zero or one ordinary-core projection step. -/
theorem ProjectionResult.compute (H : ProjectionResult s i m out) :
    Compute (ErasedLevelCore D) (.proj s i m) out := by
  cases H with
  | keep => exact .refl
  | select hi hl hg => exact .base (.inl (.inl (.inl (.projIota hi hl hg))))

/-- Terminal projection results commute with arbitrary raw substitutions,
including substitutions that create new redexes elsewhere in the major. -/
theorem ProjectionResult.subst (H : ProjectionResult s i m out) :
    ProjectionResult s i (m.subst σ) (out.subst σ) := by
  cases H with
  | keep => exact .keep
  | select hi hl hg =>
    simp only [subst_mkApps, ProofShape.subst]
    exact .select hi (by simpa only [List.length_map] using hl)
      (by simp only [List.getElem?_map, hg, Option.map_some])

/-- Move every post-selection computation into the selected constructor
argument. Every arbitrary full-core projection path therefore ends with at
most one projection iota; its output is retained exactly. -/
theorem Compute.projection_terminal
    (R : Compute (ErasedLevelCore D) (.proj s i m) out) :
    ∃ m', Compute (ErasedLevelCore D) m m' ∧ ProjectionResult s i m' out := by
  rcases R.projection_core_cases with ⟨m', rfl, RM⟩ |
      ⟨info, ls, args, field, hi, hl, hg, RM, RT⟩
  · exact ⟨m', RM, .keep⟩
  · have hj := (List.getElem?_eq_some_iff.1 hg).1
    refine ⟨mkApps (.const info.ctorName ls) (args.set (info.nparams+i) out),
      RM.trans (RT.selected_argument hg), .select hi ?_ ?_⟩
    · simpa only [List.length_set] using hl
    · simp [hj]

/-- Exact characterization of projected full-core residuals by computed majors
and terminal field selection, in both directions. -/
theorem Compute.projection_terminal_iff :
    Compute (ErasedLevelCore D) (.proj s i m) out ↔
      ∃ m', Compute (ErasedLevelCore D) m m' ∧ ProjectionResult s i m' out :=
  ⟨Compute.projection_terminal, fun ⟨_, RM, H⟩ => (ProofShape.Compute.proj RM).trans H.compute⟩

end ProofShape

/-- The terminal major has an actual realization at the original major type.
The exact final raw result is either its projection or its selected field.
This supplies typings without manufacturing new strong-derivation ranks. -/
theorem proofErase_projection_terminal_major
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m A)
    (ht : env.HasType univs Γ (.proj s i m) T) (hn : ¬ IsProof Γ (.proj s i m))
    (R : Compute (ErasedLevelCore D) (proofErase Γ (.proj s i m)) out) :
    ∃ m', env.IsDefEq univs Γ m m' A ∧
      env.IsDefEq univs Γ (.proj s i m) (.proj s i m') T ∧
      Compute (ErasedLevelCore D) (proofErase Γ m) (proofErase Γ m') ∧
      ProjectionResult s i (proofErase Γ m') out := by
  have EP : proofErase Γ (.proj s i m) = .proj s i (proofErase Γ m) := if_neg hn
  obtain ⟨major, RM, H⟩ := (EP ▸ R).projection_terminal
  obtain ⟨m', HM, EM⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hm rfl rfl (RM.scoped (fun R => .base R))
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HM.toU.of_l henv hΓ ht) T ht
  exact ⟨m', HM, HP, EM ▸ RM, EM ▸ H⟩

/-- Testing every pair of terminal selections at major residuals is exactly
the full projection-comparison interpretation. This removes arbitrary field
tails from the readout obligation, without asserting that it is discharged. -/
theorem pi_inert_projection_interpret_iff_terminal :
    PiInertInterpret D n (.compare mode) Δ (.proj s i a) (.proj s i b) ↔
      ∀ {a' b' left right}, Compute (ErasedLevelCore D) a a' →
        Compute (ErasedLevelCore D) b b' → ProjectionResult s i a' left →
        ProjectionResult s i b' right →
        ComputedJointCompare (PiInertStage D n) Δ mode left right := by
  constructor
  · intro H a' b' left right RA RB HL HR
    exact H ((ProofShape.Compute.proj RA).trans HL.compute) ((ProofShape.Compute.proj RB).trans HR.compute)
  · intro H left right RL RR
    obtain ⟨a', RA, HL⟩ := RL.projection_terminal
    obtain ⟨b', RB, HR⟩ := RR.projection_terminal
    exact H RA RB HL HR

/-- Missing one-step readout for the registered pair's type field. The left
projection contracts exactly once; the right either remains a projection or
contracts once. Majors retain actual family typings and the full computed
guard. The general-stage obligation remains open; stage zero is proved for
constructor-stable definition tables in ProofErasurePiInertPairSelection. This
is a local sufficient requirement for projection histories, not a claimed
smaller sufficient frontier for strengthening. -/
def PiInertPairTypeFieldSelection (D : Definitions) (n : Nat) (family : Name) : Prop :=
  ∀ {Γ x y left right}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ x (.const family []) → env.HasType univs Γ y (.const family []) →
    ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y) →
    Primitive D (.proj family 0 (proofErase Γ x)) left →
    ProjectionResult family 0 (proofErase Γ y) right →
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true left right

/-- Existing field readout handles two retained projections. Symmetry makes
one-sided selection sufficient for every remaining terminal combination,
including contraction of both projections. -/
theorem PiInertPairTypeFieldSelection.terminal
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
    (HL : ProjectionResult family 0 (proofErase Γ x) left)
    (HR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true left right := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed R)
  have hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute (PiInertStage D n) Δ a b :=
    fun R => .base (pi_inert_stage_core (.inl (.inl (.inl R))))
  rcases HL.keep_or_primitive (D := D) with rfl | HL
  · rcases HR.keep_or_primitive (D := D) with rfl | HR
    · exact (proofErase_computed_dependent_pair_fields hd hprim hi hp hf hz hadm hshape hΓ hx hy H).1
    · exact .symm (K hΓ hy hx (.carrierSymm H) HR .keep)
  · exact K hΓ hx hy H HL HR

/-- The one-step selection requirement supplies all independent field
residuals. Post-iota computation is absorbed into the major before reading
its retained guard, so the handler never sees an arbitrary field tail. -/
theorem PiInertCarrierResidual.dependent_type_field_of_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (K : PiInertPairTypeFieldSelection D n family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertInterpret D n (.compare true) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  apply pi_inert_projection_interpret_iff_terminal.2
  intro a b left right RA RB HL HR
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hx rfl rfl (RA.scoped (fun R => .base R))
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hy rfl rfl (RB.scoped (fun R => .base R))
  exact PiInertPairTypeFieldSelection.terminal heq hs hi hp hf hz hadm hshape K
    hΓ HX.hasType.2 HY.hasType.2 (by simpa only [EX, EY] using H .refl RA RB)
    (EX ▸ HL) (EY ▸ HR)

/-- Every actual pair history yields its complete type-field history once
the one-step selection requirement is supplied. Constructor-exposing majors,
all independent field/carrier paths and all allowed worlds are included;
there is no no-contraction premise or normalization requirement. -/
theorem PiInertWorldHistory.dependent_type_field_of_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (K : PiInertPairTypeFieldSelection D n family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : PiInertWorldHistory D n (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertWorldHistory D n (proofEraseCtx Γ) (.sort (.succ .zero))
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  refine ⟨fun _ RA RB => .carrierChecked
    (PiInertCarrierResidual.dependent_type_field_of_selection heq hs hi hp hf hz hadm hshape K
      hΓ hx hy H.base RA RB), ?_⟩
  intro Λ σ W C a b _ RA RB
  obtain ⟨Γ', τ, hΓ', EΓ', WT, ES⟩ := W.typed hΓ rfl
  have hx' : env.HasType univs Γ' (x.subst τ) (.const family []) :=
    hx.subst henv.orderedStrong WT hΓ'
  have hy' : env.HasType univs Γ' (y.subst τ) (.const family []) :=
    hy.subst henv.orderedStrong WT hΓ'
  have EX := proofErase_subst_with hΓ' WT hx ES
  have EY := proofErase_subst_with hΓ' WT hy ES
  have HC : PiInertCarrierResidual D n (proofEraseCtx Γ') (.const family [])
      (proofErase Γ' (x.subst τ)) (proofErase Γ' (y.subst τ)) := by
    rw [EΓ', EX, EY]
    exact H.future W
  have HT : PiInertInterpret D n (.compare true) (proofEraseCtx Γ')
      (.proj family 0 (proofErase Γ' (x.subst τ)))
      (.proj family 0 (proofErase Γ' (y.subst τ))) :=
    PiInertCarrierResidual.dependent_type_field_of_selection heq hs hi hp hf hz hadm hshape K
      hΓ' hx' hy' HC
  simp only [EΓ', EX, EY] at HT
  exact .carrierChecked (HT RA RB)

end Lean4Lean.VEnv.Strengthening
