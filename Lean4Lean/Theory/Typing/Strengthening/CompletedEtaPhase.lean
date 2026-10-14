import Lean4Lean.Theory.Typing.Strengthening.PrefixHeadPreservation
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaCompatibility
import Lean4Lean.Theory.Typing.Strengthening.EtaDuplicationPhaseBoundary

/-! # Eta phase representation up to computational completion

The right endpoint may compute further before the three phases meet it. This
repairs the selective-projection example while retaining Pi and rigid-family
head exposure. `EtaParameterCompletionBoundary` obstructs general coverage
when structure eta changes a constructor's parameter through conversion.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- A computational completion of the target admits the earlier three phases.
This is not a representation of every typed FullReduction: reparameterized
structure eta has the obstruction in `EtaParameterCompletionBoundary`. -/
def CompletedEtaPhase (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ out, PrefixCompute D Γ b out ∧ PrefixEtaNormal D Γ a out

/-- Every exact phase representation already has an empty completion. -/
theorem PrefixEtaNormal.completed (H : PrefixEtaNormal D Γ a b) :
    CompletedEtaPhase D Γ a b := ⟨b, .refl, H⟩

/-- A computation into the right endpoint can be included in its completion. -/
theorem CompletedEtaPhase.right_compute (R : PrefixCompute D Γ b c)
    (H : CompletedEtaPhase D Γ a c) : CompletedEtaPhase D Γ a b := by
  obtain ⟨out, RC, HP⟩ := H
  exact ⟨out, R.trans RC, HP⟩

/-- A computation before the left endpoint precedes the existing phases. -/
theorem CompletedEtaPhase.left_compute (R : PrefixCompute D Γ a b)
    (H : CompletedEtaPhase D Γ b c) : CompletedEtaPhase D Γ a c := by
  obtain ⟨out, RC, HP⟩ := H
  exact ⟨out, RC, HP.prepend_compute R⟩

/-- Soundness uses original typings of both endpoints. A raw computational
completion alone does not assert typing of its source. -/
theorem CompletedEtaPhase.defeq (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CompletedEtaPhase D Γ a b)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    env.IsDefEq univs Γ a b A := by
  obtain ⟨out, RC, HP⟩ := H
  have HE := HP.defeq hs hΓ ha
  exact HE.trans (((RC.simAt hs hΓ _ hb).toU.symm).of_l henv hΓ HE.hasType.2)

/-- Completing a Pi endpoint retains its Pi head, so eta still disappears
from the left-hand exposure. -/
theorem CompletedEtaPhase.pi_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (H : CompletedEtaPhase D Γ e (.forallE A B)) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨out, RC, HP⟩ := H
  obtain ⟨_, _, rfl⟩ := RC.pi_shape
  exact HP.pi_exposure hΓ

/-- Completing a rigid family endpoint retains the exact head, levels, and
arity needed by the earlier phase-exposure theorem. -/
theorem CompletedEtaPhase.family_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (H : CompletedEtaPhase D Γ e (mkApps (.const family levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨out, RC, HP⟩ := H
  obtain ⟨args0, rfl, hlen⟩ := RC.rigid_spine (henv.projectionRigid hi) hn
  obtain ⟨ls, args', R, hls, hl⟩ := HP.family_exposure hs hΓ hi ht
  exact ⟨ls, args', R, hls, hl.trans hlen⟩

/-- Function-type repair survives completion; the witnessed front is still
used only to reflect the reconstructed computational path. -/
theorem CompletedEtaPhase.function_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (H : CompletedEtaPhase D Γ' (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      env.IsDefEqU univs Γ T (.forallE A' B') := by
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  obtain ⟨_, _, RC⟩ := H.pi_exposure hΓ'
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨A', B', hf.defeqU_r henv hΓ ⟨_, HE⟩, _, HE⟩

/-- Family-type repair survives completion, with the same universe and arity
constraints as exact phase repair. The family head must not unfold in D. -/
theorem CompletedEtaPhase.family_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (hm : env.HasType univs Γ m T)
    (H : CompletedEtaPhase D Γ' (T.lift' ρ) (mkApps (.const family levels) args)) :
    ∃ levels' args', env.HasType univs Γ m (mkApps (.const family levels') args') ∧
      env.IsDefEqU univs Γ T (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  obtain ⟨levels', args0, RC, hlevels, hlen⟩ := H.family_exposure hs hΓ' hi hn (hT.weak' henv W)
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨args', rfl, rfl⟩ := lift'_eq_const_spine he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨levels', args', hm.defeqU_r henv hΓ ⟨_, HE⟩, ⟨_, HE⟩, hlevels, by
    simpa only [List.length_map] using hlen⟩

/-- The exact-factorization obstruction has a completion back to its source,
using only its remaining projection contraction. -/
theorem selective_projection_completed (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]) T) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    CompletedEtaPhase D Γ source
      (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) :=
  ⟨_, selective_projection_computes_back hi hp hf,
    PrefixEtaNormal.of_terminal (EtaNormal.normal (.refl ht))⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
