import Lean4Lean.Theory.Typing.Strengthening.ReconstructionHeads
import Lean4Lean.Theory.Typing.Strengthening.StructureEtaParameterCompletion

/-! # Computational joins with the extended reconstruction terminal

Every structure-eta root followed by finite computation now has this phase,
including arbitrary data parameters. Pi and family head repair remain valid.
General compatible mixed composition and terminal confluence are still open.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Both endpoints compute before the extended terminal comparison. Completeness
for arbitrary full paths is not part of this definition. -/
def PrefixReconstructionJoin (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a0 b0, PrefixCompute D Γ a a0 ∧ PrefixCompute D Γ b b0 ∧ ReconstructionJoin Γ a0 b0

/-- The old symmetric phase is retained exactly as a special case. -/
theorem PrefixEtaJoin.reconstruction (H : PrefixEtaJoin D Γ a b) :
    PrefixReconstructionJoin D Γ a b := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  exact ⟨a0, b0, RA, RB, HJ.reconstruction⟩

/-- Independent source typings suffice for soundness of the extended phase. -/
theorem PrefixReconstructionJoin.defeq (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : PrefixReconstructionJoin D Γ a b)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    env.IsDefEq univs Γ a b A := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  have HA := RA.simAt hs hΓ _ ha
  have HB := RB.simAt hs hΓ _ hb
  have HE := HA.trans (HJ.defeq hΓ HA.hasType.2 HB.hasType.2)
  exact HE.trans (HB.toU.symm.of_l henv hΓ HE.hasType.2)

/-- A Pi on the right still exposes an actual computational Pi on the left. -/
theorem PrefixReconstructionJoin.pi_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : PrefixReconstructionJoin D Γ e (.forallE A B))
    (ht : env.HasType univs Γ (.forallE A B) T) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  obtain ⟨_, _, rfl⟩ := RB.pi_shape
  obtain ⟨A', B', rfl⟩ := HJ.pi_source hΓ (RB.simAt hs hΓ _ ht).hasType.2
  exact ⟨A', B', RA⟩

/-- A registered family on the right still exposes that family computationally
on the left, with equivalent universes and the original argument count. -/
theorem PrefixReconstructionJoin.family_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (H : PrefixReconstructionJoin D Γ e (mkApps (.const family levels) args))
    (ht : env.HasType univs Γ e (.sort u))
    (hr : env.HasType univs Γ (mkApps (.const family levels) args) (.sort v)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  obtain ⟨args0, rfl, hlen⟩ := RB.rigid_spine (henv.projectionRigid hi) hn
  obtain ⟨levels', args', RC, hlevels, hlen'⟩ := HJ.family_exposure hΓ hi
    (RA.simAt hs hΓ _ ht).hasType.2 (RB.simAt hs hΓ _ hr).hasType.2
  exact ⟨levels', args', RA.trans RC, hlevels, hlen'.trans hlen⟩

/-- Lower function-type repair only reflects the recovered computational path.
The explicit upper Pi typing is supplied by any typed full path to that Pi. -/
theorem PrefixReconstructionJoin.function_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (H : PrefixReconstructionJoin D Γ' (T.lift' ρ) (.forallE A B))
    (hpi : env.HasType univs Γ' (.forallE A B) S) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      env.IsDefEqU univs Γ T (.forallE A' B') := by
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  obtain ⟨_, _, RC⟩ := H.pi_exposure hs hΓ' hpi
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨A', B', hf.defeqU_r henv hΓ ⟨_, HE⟩, _, HE⟩

/-- Lower family-type repair retains the head and arity without demanding that
either reconstruction phase's intermediate parameters or annotations be scoped below. -/
theorem PrefixReconstructionJoin.family_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (hm : env.HasType univs Γ m T)
    (H : PrefixReconstructionJoin D Γ' (T.lift' ρ) (mkApps (.const family levels) args))
    (hr : env.HasType univs Γ' (mkApps (.const family levels) args) (.sort v)) :
    ∃ levels' args', env.HasType univs Γ m (mkApps (.const family levels') args') ∧
      env.IsDefEqU univs Γ T (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  obtain ⟨levels', args0, RC, hlevels, hlen⟩ := H.family_exposure hs hΓ' hi hn (hT.weak' henv W) hr
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨args', rfl, rfl⟩ := lift'_eq_const_spine he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨levels', args', hm.defeqU_r henv hΓ ⟨_, HE⟩, ⟨_, HE⟩, hlevels, by
    simpa only [List.length_map] using hlen⟩

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- Every structure eta root followed by arbitrary finite computation has the
extended phase. Majors may expose constructors at converted data parameters
and different universe syntax; no parameter or family phase is assumed. -/
theorem structure_eta_compute_reconstruction
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    PrefixReconstructionJoin actualD Γ major out := by
  rcases structure_eta_compute_join_or_parameter_change hcon hΓ hi hp hx hm hc R with
    H | ⟨left, right, RL, RR, HP⟩
  · exact H.reconstruction
  · have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
    have hr := ((R.trans RR).simAt hs hΓ _ hc).hasType.2
    exact ⟨left, right, RL, RR, right, right, .parameters HP, .refl, .refl hr⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
