import Lean4Lean.Theory.Typing.Strengthening.SymmetricEtaHeads
import Lean4Lean.Theory.Typing.Strengthening.CompletedEtaPhase
import Lean4Lean.Theory.Typing.Strengthening.EtaParameterCompletionBoundary
import Lean4Lean.Theory.Typing.Strengthening.ConstructorEtaCompletion

/-! # Symmetric computational and eta phases

Both endpoints compute and then expand by eta before normal comparison. This
contains the previous completed phase and repairs the converted-parameter test.
Pi/family head repair survives. General coverage and transitivity remain open.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- A computational path from each endpoint followed by a symmetric eta join.
The relation does not assume a general factorization theorem for FullReduction. -/
def PrefixEtaJoin (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a0 b0, PrefixCompute D Γ a a0 ∧ PrefixCompute D Γ b b0 ∧ EtaJoin Γ a0 b0

theorem PrefixEtaJoin.of_eta (H : EtaJoin Γ a b) : PrefixEtaJoin D Γ a b :=
  ⟨a, b, .refl, .refl, H⟩

/-- Every completed one-sided phase is already a symmetric phase. -/
theorem CompletedEtaPhase.join (H : CompletedEtaPhase D Γ a b) : PrefixEtaJoin D Γ a b := by
  obtain ⟨out, RB, HP⟩ := H
  obtain ⟨a0, RA, HE⟩ := PrefixEtaNormal.terminal_iff.1 HP
  exact ⟨a0, out, RA, RB, HE.join⟩

theorem PrefixEtaJoin.symm (hΓ : OnCtx Γ (env.IsType univs)) (H : PrefixEtaJoin D Γ a b) :
    PrefixEtaJoin D Γ b a := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  exact ⟨b0, a0, RB, RA, HJ.symm hΓ⟩

/-- Computation into either endpoint may precede its existing phase. -/
theorem PrefixEtaJoin.prepend_left (R : PrefixCompute D Γ a b) (H : PrefixEtaJoin D Γ b c) :
    PrefixEtaJoin D Γ a c := by
  obtain ⟨b0, c0, RB, RC, HJ⟩ := H
  exact ⟨b0, c0, R.trans RB, RC, HJ⟩

theorem PrefixEtaJoin.prepend_right (R : PrefixCompute D Γ b c) (H : PrefixEtaJoin D Γ a c) :
    PrefixEtaJoin D Γ a b := by
  obtain ⟨a0, c0, RA, RC, HJ⟩ := H
  exact ⟨a0, c0, RA, R.trans RC, HJ⟩

/-- Separate original endpoint typings suffice for soundness of a symmetric
phase; no typing is inferred backwards through raw computational paths. -/
theorem PrefixEtaJoin.defeq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixEtaJoin D Γ a b) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    env.IsDefEq univs Γ a b A := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  have HA := RA.simAt hs hΓ _ ha
  have HB := RB.simAt hs hΓ _ hb
  have HE := HA.trans (HJ.defeq hΓ HA.hasType.2 HB.hasType.2)
  exact HE.trans (HB.toU.symm.of_l henv hΓ HE.hasType.2)

/-- A Pi on the right survives both right phases. The left eta phase must
therefore also have started at a Pi. -/
theorem PrefixEtaJoin.pi_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : PrefixEtaJoin D Γ e (.forallE A B))
    (ht : env.HasType univs Γ (.forallE A B) T) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  obtain ⟨_, _, rfl⟩ := RB.pi_shape
  obtain ⟨A', B', rfl⟩ := HJ.pi_source hΓ (RB.simAt hs hΓ _ ht).hasType.2
  exact ⟨A', B', RA⟩

/-- Symmetric eta still exposes a registered family, with equivalent universes
and unchanged arity. The right computational phase preserves its rigid head. -/
theorem PrefixEtaJoin.family_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (H : PrefixEtaJoin D Γ e (mkApps (.const family levels) args))
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
theorem PrefixEtaJoin.function_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (H : PrefixEtaJoin D Γ' (T.lift' ρ) (.forallE A B))
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
either eta phase's intermediate parameters or annotations be scoped below. -/
theorem PrefixEtaJoin.family_type_below (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (hm : env.HasType univs Γ m T)
    (H : PrefixEtaJoin D Γ' (T.lift' ρ) (mkApps (.const family levels) args))
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

/-- The selective-projection obstruction to exact phases is covered. -/
theorem selective_projection_symmetric_phase
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]) T) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    PrefixEtaJoin D Γ source (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) :=
  (selective_projection_completed hi hp hf ht).join

/-- Right eta repairs the converted-parameter obstruction. No computation of
the atomic target is required or asserted. -/
theorem parameter_eta_symmetric_phase
    (hi : env.projections innerFamily innerInfo)
    (hp : innerInfo.nparams = 0) (hx : innerInfo.nindices = 0)
    (hv : env.HasType univs Γ (.bvar i) (.const innerFamily innerLevels))
    (hc : env.HasType univs Γ (structExpand innerFamily innerInfo innerLevels [] (.bvar i))
      (.const innerFamily innerLevels))
    (ht : env.HasType univs Γ (mkApps (.const outer levels)
      [structExpand innerFamily innerInfo innerLevels [] (.bvar i), field]) T) :
    PrefixEtaJoin D Γ (mkApps (.const outer levels)
      [structExpand innerFamily innerInfo innerLevels [] (.bvar i), field])
      (mkApps (.const outer levels) [.bvar i, field]) :=
  .of_eta ⟨_, _, .refl, constructor_parameter_reverse_eta hi hp hx hv hc, .refl ht⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
