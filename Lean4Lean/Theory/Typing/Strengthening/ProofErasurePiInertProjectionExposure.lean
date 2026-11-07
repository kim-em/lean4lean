import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertVariableReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedWrappers

/-! # Constructor selection behind full-stage projection computation

A sorted projection reaching an output with neither a projection root nor a
lambda head must eventually select a constructor field. Constant and native
identity wrappers can be removed with a strict decrease in the outer primitive
count. Native guards and compatible major computation retain their full stage;
no confluence, normalization, or forward comparison closure is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual

namespace ProofShape

private theorem scoped_spine_pair (HF : ScopedCompute Step Δ f g)
    (HA : List.Forall₂ (ScopedCompute Step Δ) args args') :
    ScopedCompute Step Δ (mkApps f args) (mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

private theorem scoped_selected_argument
    (HG : args[j]? = some field) (R : ScopedCompute Step Δ field out) :
    List.Forall₂ (ScopedCompute Step Δ) args (args.set j out) := by
  induction args generalizing j with
  | nil => simp at HG
  | cons a args ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero] at HG
      cases Option.some.inj HG
      exact .cons R (.rfl (fun _ _ => .refl))
    | succ j => exact .cons .refl (ih (by simpa only [List.getElem?_cons_succ] using HG))

/-- A selected field's entire scoped computation can occur in its constructor
argument instead. Other arguments remain exact, and the stage and scope of
every native guard are unchanged. -/
theorem ScopedCompute.selected_argument
    (HG : args[j]? = some field) (R : ScopedCompute Step Δ field out) :
    ScopedCompute Step Δ (ProofShape.mkApps f args) (ProofShape.mkApps f (args.set j out)) :=
  scoped_spine_pair .refl (scoped_selected_argument HG R)

/-- Counted projection paths either retain the projection throughout or have
a first root primitive. The latter decomposition accounts exactly for the
major prefix, that primitive, and the complete tail. -/
theorem ScopedComputeCount.projection_first_root
    (R : ScopedComputeCount Step cost Δ (.proj s i m) out) :
    (∃ m', out = .proj s i m' ∧ ScopedComputeCount Step cost Δ m m') ∨
    ∃ m' field before after, before + 1 + after = cost ∧
      ScopedComputeCount Step before Δ m m' ∧ Step Δ (.proj s i m') field ∧
      ScopedComputeCount Step after Δ field out := by
  generalize E : ProofShape.proj s i m = source at R
  induction R generalizing m with
  | base H => exact .inr ⟨m, _, 0, 0, by omega, .beta .refl, E ▸ H, .beta .refl⟩
  | beta H =>
    obtain ⟨m', EO, HM⟩ := ProofShape.beta_proj_inv (E ▸ H)
    exact .inl ⟨m', EO, .beta HM⟩
  | trans R S ihR ihS =>
    rcases ihR E with ⟨m', rfl, RM⟩ | ⟨m', field, before, after, HC, RM, HR, RT⟩
    · rcases ihS rfl with ⟨m'', EO, RN⟩ | ⟨m'', field, before, after, HC, RN, HR, RT⟩
      · exact .inl ⟨m'', EO, RM.trans RN⟩
      · exact .inr ⟨m'', field, _, after, by omega, RM.trans RN, HR, RT⟩
    · exact .inr ⟨m', field, before, _, by omega, RM, HR, RT.trans S⟩
  | proj R => cases E; exact .inl ⟨_, rfl, R⟩
  | app | lam | forallE => cases E

end ProofShape
variable [Params] {D : Definitions}

/-- Removing an administrative root wrapper before a non-lambda-headed output
does not increase the tail's primitive count. Unlike the earlier carrier
exposure formulation, this also covers variables, sorts, and neutral spines. -/
theorem pi_inert_expansion_count_bypass_nonlambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ target out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ source out := by
  rcases H with H | H
  · obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
    cases H with
    | intro _ =>
      have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
        .sort (by trivial)
      have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
        if_neg (not_isProof_of_sort hΓ hA)
      exact pi_inert_constant_spine_count_eliminate (args := []) heq hs hΓ hA ht hout
        (by simpa only [EA, ProofShape.constantExpansion, ProofShape.mkApps] using RT)
  · cases H with
    | intro _ => exact RT.pi_inert_identity_spine_eliminate (args := []) hout

/-- Every full-stage sorted projection computation exposing a non-projection,
non-lambda-headed result has a genuine constructor selection in its history.
After administrative wrappers are bypassed, the major prefix plus field tail
cost strictly less than the original path, accounting for the selected iota.
This measure ignores guard sizes and permits recursive definitions. -/
theorem pi_inert_sorted_projection_selection_count
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj s i major)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj s i m) out) :
    ∃ major field before after, before + 1 + after ≤ cost ∧
      ScopedComputeCount (PiInertStage D n) before Δ m major ∧
      Primitive D (.proj s i major) field ∧
      ScopedComputeCount (PiInertStage D n) after Δ field out := by
  induction cost using Nat.strongRecOn generalizing m with
  | ind cost ih =>
    rcases R.projection_first_root with ⟨major, EO, _⟩ |
        ⟨major, target, before, after, HC, RM, RP, RT⟩
    · exact (hproj major EO).elim
    have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
      fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
        hΓ hΓ' W ht R.1
    have HT' : ControlTyping Δ (.proj s i major) (.sort u) := HT.compute hd (.proj RM.forget)
    rcases static_structure_sorted_projection_root heq hs HT' RP.1 with RI | RC | ⟨k, _, RN⟩
    · exact ⟨major, target, before, after, by omega, RM, RI, RT⟩
    all_goals
      have HTsource : TypedSource Δ (.proj s i major) := by
        obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT'
        exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
    · obtain ⟨j, hj, RJ⟩ := pi_inert_expansion_count_bypass_nonlambda heq hs HTsource
        (Recovery := PiInertStage D n) (.inl RC) RT hout
      obtain ⟨last, field, cb, ca, HB, RL, RI, RF⟩ := ih j (by omega) HT' RJ
      exact ⟨last, field, before + cb, ca, by omega, RM.trans RL, RI, RF⟩
    · obtain ⟨j, hj, RJ⟩ := pi_inert_expansion_count_bypass_nonlambda heq hs HTsource (.inr RN) RT hout
      obtain ⟨last, field, cb, ca, HB, RL, RI, RF⟩ := ih j (by omega) HT' RJ
      exact ⟨last, field, before + cb, ca, by omega, RM.trans RL, RI, RF⟩

/-- Forgetting the cost gives a same-stage constructor-selection factorization
for arbitrary finite computations, including higher-stage native guards. -/
theorem pi_inert_sorted_projection_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj s i major)
    (R : ScopedCompute (PiInertStage D n) Δ (.proj s i m) out) :
    ∃ major field, ScopedCompute (PiInertStage D n) Δ m major ∧
      Primitive D (.proj s i major) field ∧ ScopedCompute (PiInertStage D n) Δ field out := by
  obtain ⟨cost, RC⟩ := R.count
  obtain ⟨major, field, _, _, _, RM, RI, RF⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HT hout hproj RC
  exact ⟨major, field, RM.forget, RI, RF.forget⟩

/-- Move the whole selected-field tail back into the constructor argument.
For these exposed outputs, a full-stage projection computation can therefore
be chosen with one final iota and the exact original output. -/
theorem pi_inert_sorted_projection_terminal_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj s i major)
    (R : ScopedCompute (PiInertStage D n) Δ (.proj s i m) out) :
    ∃ major, ScopedCompute (PiInertStage D n) Δ m major ∧ Primitive D (.proj s i major) out := by
  obtain ⟨major, field, RM, RI, RF⟩ := pi_inert_sorted_projection_selection heq hs HT hout hproj R
  cases RI with
  | projIota hi hl hg =>
    have hj := (List.getElem?_eq_some_iff.1 hg).1
    refine ⟨_, RM.trans (RF.selected_argument hg), .projIota hi ?_ ?_⟩
    · simpa only [List.length_set] using hl
    · simp [hj]

/-- Exact same-stage characterization of exposed sorted projection outputs by
major computation and one terminal constructor selection. The implication
from left to right bypasses arbitrarily many administrative wrappers. -/
theorem pi_inert_sorted_projection_terminal_selection_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj s i major) :
    ScopedCompute (PiInertStage D n) Δ (.proj s i m) out ↔
      ∃ major, ScopedCompute (PiInertStage D n) Δ m major ∧ Primitive D (.proj s i major) out := by
  constructor
  · exact pi_inert_sorted_projection_terminal_selection heq hs HT hout hproj
  · rintro ⟨major, RM, RI⟩
    exact (ScopedCompute.proj RM).trans (.base (pi_inert_stage_core (.inl (.inl (.inl RI)))))

/-- The open field-selection condition forces an actual right-major residual
whose constructor selects the same variable type field. This is stronger than
ordinary equality or an abstract field comparison: the complete constructor
exposure is retained at the original stage and actual record assignment. -/
theorem PiInertPairTypeFieldSelection.variable_constructor
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
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) (.bvar j)) :
    ∃ y', env.IsDefEq univs Γ y y' (.const family []) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ y) (proofErase Γ y') ∧
      Primitive D (.proj family 0 (proofErase Γ y')) (.bvar j) := by
  have R := K.variable_readout heq hs hi hp hf hz hadm hshape hΓ hx hy H RI
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 y, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have hout : ∀ A b args, ProofShape.bvar j ≠ ProofShape.mkApps (.lam A b) args := by
    intro A b args E
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [ProofShape.mkApps_snoc] at E; cases E
  obtain ⟨major, RM, RP⟩ := pi_inert_sorted_projection_terminal_selection heq hs HT hout
    (fun _ E => ProofShape.noConfusion E) R
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht R.1
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize hd hΓ hy rfl rfl RM
  exact ⟨y', HY, by simpa only [EY] using RM, by simpa only [EY] using RP⟩

end Lean4Lean.VEnv.Strengthening
