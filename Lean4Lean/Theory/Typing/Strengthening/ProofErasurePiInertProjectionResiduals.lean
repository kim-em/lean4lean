import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNeutralSpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedProjectionReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicCoreReflection

/-! # Projection residuals and the first constructor contraction

Ordinary core computation either retains the projection and computes its major,
or first contracts projection iota and continues from the selected field.
Variable-only world maps preserve absence of that contraction. In the latter-free
case, dependent-pair type-field readout supplies a full world history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
namespace ProofShape

/-- Every projected computation has either only major computation or a first
primitive at the projection root, with its entire remaining computation kept. -/
theorem Compute.projection_first_root (R : Compute Step (.proj s i m) out) :
    (∃ m', out = .proj s i m' ∧ Compute Step m m') ∨
    ∃ m' field, Compute Step m m' ∧ Step (.proj s i m') field ∧
      Compute Step field out := by
  generalize E : ProofShape.proj s i m = source at R
  induction R generalizing m with
  | base H => exact .inr ⟨m, _, .refl, E ▸ H, .refl⟩
  | beta H =>
    obtain ⟨m', EO, HM⟩ := ProofShape.beta_proj_inv (E ▸ H)
    exact .inl ⟨m', EO, .beta HM⟩
  | trans R S ihR ihS =>
    rcases ihR E with ⟨m', rfl, RM⟩ | ⟨m', field, RM, HR, RT⟩
    · rcases ihS rfl with ⟨m'', EO, RN⟩ | ⟨m'', field, RN, HR, RT⟩
      · exact .inl ⟨m'', EO, RM.trans RN⟩
      · exact .inr ⟨m'', field, RM.trans RN, HR, RT⟩
    · exact .inr ⟨m', field, RM, HR, RT.trans S⟩
  | proj R => cases E; exact .inl ⟨_, rfl, R⟩
  | app | lam | forallE => cases E

end ProofShape
variable [Params] {D : Definitions}

/-- The only ordinary level-core primitive at a projection root is saturated
projection iota. Registered capture/template rules require a constant spine;
universe conversion cannot have a projection source. -/
theorem erased_level_core_projection_root
    (H : ErasedLevelCore D (.proj s i m) field) :
    ∃ info ls args, env.projections s info ∧
      m = ProofShape.mkApps (.const info.ctorName ls) args ∧
      args.length = info.nparams + info.numFields ∧ args[info.nparams + i]? = some field := by
  rcases H with ((H | H) | H) | H
  · cases H with
    | projIota hi hl hg => exact ⟨_, _, _, hi, rfl, hl, hg⟩
  · cases H with
    | select _ _ hm => cases hm
    | apply _ _ hm => cases hm
  · cases H with
    | intro _ _ _ hm => cases hm
  · cases H

/-- Full core projection paths retain the complete major prefix, registered
constructor, selected field and post-iota tail. No typing, normalization or
confluence premise is used; both alternatives remain available. -/
theorem ProofShape.Compute.projection_core_cases
    (R : Compute (ErasedLevelCore D) (.proj s i m) out) :
    (∃ m', out = .proj s i m' ∧ Compute (ErasedLevelCore D) m m') ∨
    ∃ info ls args field, env.projections s info ∧
      args.length = info.nparams + info.numFields ∧ args[info.nparams + i]? = some field ∧
      Compute (ErasedLevelCore D) m (ProofShape.mkApps (.const info.ctorName ls) args) ∧
      Compute (ErasedLevelCore D) field out := by
  rcases R.projection_first_root with H | ⟨m', field, RM, HR, RT⟩
  · exact .inl H
  · obtain ⟨info, ls, args, hi, rfl, hl, hg⟩ := erased_level_core_projection_root HR
    exact .inr ⟨info, ls, args, field, hi, hl, hg, RM, RT⟩

namespace ProofShape

/-- Every substitution image is a variable. Unlike atomic substitutions,
these cannot create a universe-conversion step at an old variable. -/
def VariableImages (σ : Subst) : Prop := ∀ i, ∃ j, σ i = .bvar j

omit [Params] in
/-- Variable images are atomic even when distinct variables are identified. -/
theorem VariableImages.atomic (H : VariableImages σ) : AtomicSubstitution σ := by
  intro i
  obtain ⟨j, E⟩ := H i
  rw [E]
  exact .bvar

omit [Params] in
/-- Variable-only images remain variable-only beneath a binder. -/
theorem VariableImages.lift (H : VariableImages σ) : VariableImages σ.lift := by
  intro i
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i =>
    obtain ⟨j, E⟩ := H i
    exact ⟨j+1, by simp [Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm]⟩

omit [Params] in
/-- A sort cannot be introduced by a variable-only substitution. -/
theorem VariableImages.sort_inv {e : ProofShape} (H : VariableImages σ) (E : e.subst σ = .sort u) :
    e = .sort u := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    obtain ⟨j, HJ⟩ := H i
    rw [HJ] at E
    cases E
  all_goals cases E <;> rfl

/-- Universe conversion reflects through variable-only images. Allowing sorts
as images would create level steps at old variables, so atomicity is insufficient. -/
theorem LevelPrimitive.variable_subst_inv
    (H : VariableImages σ) (R : LevelPrimitive univs (e.subst σ) out) :
    ∃ e', LevelPrimitive univs e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  cases R with
  | sort HE hw =>
    obtain rfl := H.sort_inv E
    exact ⟨_, .sort HE hw, rfl⟩
  | const HE hw =>
    obtain rfl := H.atomic.const_inv E
    exact ⟨_, .const HE hw, rfl⟩

end ProofShape

/-- The entire ordinary level core reflects exactly through variable images. -/
theorem erased_level_core_variable_subst_inv
    (H : VariableImages σ) (R : ErasedLevelCore D (e.subst σ) out) :
    ∃ e', ErasedLevelCore D e e' ∧ e'.subst σ = out := by
  rcases R with R | R
  · obtain ⟨e', R', E⟩ := erased_iota_primitive_atomic_subst_inv H.atomic R
    exact ⟨e', .inl R', E⟩
  · obtain ⟨e', R', E⟩ := R.variable_subst_inv H
    exact ⟨e', .inr R', E⟩

namespace ProofShape

omit [Params] in
/-- Variable-image primitive reflection extends to all compatible paths. -/
theorem Compute.variable_subst_inv
    (hroot : ∀ {σ a b}, VariableImages σ → Step (a.subst σ) b →
      ∃ a', Step a a' ∧ a'.subst σ = b)
    (H : VariableImages σ) (R : Compute Step (e.subst σ) out) :
    ∃ e', Compute Step e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  induction R generalizing e σ with
  | base R =>
    obtain ⟨e', RE, EE⟩ := hroot H (E.symm ▸ R)
    exact ⟨e', .base RE, EE⟩
  | beta R =>
    obtain ⟨e', RE, EE⟩ := (E.symm ▸ R).atomic_subst_inv H.atomic
    exact ⟨e', .beta RE, EE⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, RM, EM⟩ := ih₁ H E
    obtain ⟨out, RO, EO⟩ := ih₂ H EM
    exact ⟨out, RM.trans RO, EO⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, EF, EA⟩ := H.atomic.app_inv E
    obtain ⟨f', RF, rfl⟩ := ihf H EF
    obtain ⟨a', RA, rfl⟩ := iha H EA
    exact ⟨_, .app RF RA, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, EM⟩ := H.atomic.proj_inv E
    obtain ⟨m', RM, rfl⟩ := ih H EM
    exact ⟨_, .proj RM, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, EA, EB⟩ := H.atomic.lam_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨b', RB, rfl⟩ := ihb H.lift EB
    exact ⟨_, .lam RA RB, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, EA, EB⟩ := H.atomic.pi_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨B', RB, rfl⟩ := ihB H.lift EB
    exact ⟨_, .forallE RA RB, rfl⟩

/-- Ordinary level-core paths reflect through variable images, with the exact
unsubstituted output and no source typing or injectivity assumption. -/
theorem Compute.level_core_variable_subst_inv
    (H : VariableImages σ) (R : Compute (ErasedLevelCore D) (e.subst σ) out) :
    ∃ e', Compute (ErasedLevelCore D) e e' ∧ e'.subst σ = out :=
  R.variable_subst_inv (fun H R => erased_level_core_variable_subst_inv H R) H

end ProofShape

/-- This major cannot enable a primitive contraction of the selected projection
along any ordinary-core path. Projection_core_cases identifies the excluded
case precisely as a saturated constructor followed by field selection. -/
def ProofShape.ProjectionCoreStuck (D : Definitions) (s : Name) (i : Nat)
    (m : ProofShape) : Prop :=
  ∀ {m' field}, Compute (ErasedLevelCore D) m m' →
    ¬ ErasedLevelCore D (.proj s i m') field

/-- With no enabled projection contraction, every field residual is exactly a
projection of a major residual. This implication does not assume normalization. -/
theorem ProofShape.ProjectionCoreStuck.project
    (H : ProjectionCoreStuck D s i m)
    (R : Compute (ErasedLevelCore D) (.proj s i m) out) :
    ∃ m', out = .proj s i m' ∧ Compute (ErasedLevelCore D) m m' := by
  rcases R.projection_first_root with K | ⟨m', field, RM, HR, _⟩
  · exact K
  · exact (H RM HR).elim

/-- Variable-only substitutions cannot introduce a constructor contraction that was
unavailable before substitution, even when variable images are identified. -/
theorem ProofShape.ProjectionCoreStuck.subst
    (H : ProjectionCoreStuck D s i m) (W : VariableImages σ) :
    ProjectionCoreStuck D s i (m.subst σ) := by
  intro m' field RM HR
  obtain ⟨m₀, RM₀, rfl⟩ := RM.level_core_variable_subst_inv W
  obtain ⟨field₀, HR₀, _⟩ := erased_level_core_variable_subst_inv (e := .proj s i m₀) W HR
  exact H RM₀ HR₀

/-- Core worlds have exactly the variable-image property needed by reflection. -/
theorem PiInertCoreWorld.variable_images (W : PiInertCoreWorld D Δ Λ σ) : VariableImages σ := by
  intro i
  obtain ⟨j, E, _⟩ := W.lookup i
  exact ⟨j, E⟩

/-- Variable-headed majors cannot enable projection iota, even when their
arguments contain arbitrary ordinary-core computation. Thus the residual
readout applies to opaque variable applications as well as bare variables. -/
theorem ProofShape.ProjectionCoreStuck.variable_spine :
    ProjectionCoreStuck D s i (ProofShape.mkApps (.bvar j) args) := by
  intro m' field RM HR
  obtain ⟨args', rfl, _⟩ := RM.level_core_bvar_spine
  obtain ⟨info, ls, fields, _, E, _, _⟩ := erased_level_core_projection_root HR
  have HH := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
  cases HH

/-- Without constructor contraction on either major, the type-field readout
retains all independent ordinary-core projection residuals. This supplies
comparison, rather than just a guard at the unreduced projections. -/
theorem PiInertCarrierResidual.dependent_type_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (NX : ProjectionCoreStuck D family 0 (proofErase Γ x))
    (NY : ProjectionCoreStuck D family 0 (proofErase Γ y))
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertInterpret D n (.compare true) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  intro a b RA RB
  obtain ⟨a', rfl, RM⟩ := NX.project RA
  obtain ⟨b', rfl, RN⟩ := NY.project RB
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hx rfl rfl (RM.scoped (fun R => .base R))
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hy rfl rfl (RN.scoped (fun R => .base R))
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed R)
  have hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute (PiInertStage D n) Δ a b :=
    fun R => .base (pi_inert_stage_core (.inl (.inl (.inl R))))
  have HF := proofErase_computed_dependent_pair_fields hd hprim hi hp hf hz hadm hshape
    hΓ HX.hasType.2 HY.hasType.2 (by simpa only [EX, EY] using H .refl RM RN)
  simpa only [EX, EY] using HF.1

/-- The first field now has a full world history, including independent field
and carrier residuals. The non-contraction premise is required only in the
original context: variable-only world reflection proves it in every future.
Removing it requires the constructor/selected-field branch of
Compute.projection_core_cases, not a beta-only projection inversion. -/
theorem PiInertWorldHistory.dependent_type_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (NX : ProjectionCoreStuck D family 0 (proofErase Γ x))
    (NY : ProjectionCoreStuck D family 0 (proofErase Γ y))
    (H : PiInertWorldHistory D n (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertWorldHistory D n (proofEraseCtx Γ) (.sort (.succ .zero))
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  refine ⟨fun _ RA RB => .carrierChecked
    (PiInertCarrierResidual.dependent_type_field heq hs hi hp hf hz hadm hshape hΓ hx hy NX NY H.base RA RB), ?_⟩
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
  have HX : ProjectionCoreStuck D family 0 (proofErase Γ' (x.subst τ)) :=
    EX ▸ NX.subst W.variable_images
  have HY : ProjectionCoreStuck D family 0 (proofErase Γ' (y.subst τ)) :=
    EY ▸ NY.subst W.variable_images
  have HT : PiInertInterpret D n (.compare true) (proofEraseCtx Γ')
      (.proj family 0 (proofErase Γ' (x.subst τ)))
      (.proj family 0 (proofErase Γ' (y.subst τ))) :=
    PiInertCarrierResidual.dependent_type_field heq hs hi hp hf hz hadm hshape hΓ' hx' hy' HX HY HC
  simp only [EΓ', EX, EY] at HT
  exact .carrierChecked (HT RA RB)

end Lean4Lean.VEnv.Strengthening
