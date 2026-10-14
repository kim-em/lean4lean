import Lean4Lean.Theory.Typing.Strengthening.NormalSortHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.SymmetricPrefixEtaPhase

/-! # Argument certificates from symmetric family phases

Head beta transport retains the original eta paths from constant spines.
Consequently a phase between sort-typed registered family applications yields
phases between corresponding arguments, not merely ordinary conversions.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- A head-beta-normalized eta expansion of a sort-typed constant spine retains
pointwise eta expansions and exactly its original head and universe syntax. -/
theorem TypedEtaExpansion.headBeta_const_arguments (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ (mkApps (.const name levels) args) mid)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) (.sort u))
    (RB : HeadBetaRed mid (mkApps (.const name' levels') args')) :
    name = name' ∧ levels = levels' ∧ List.Forall₂ (TypedEtaExpansion Γ) args args' := by
  have RE := eta_constant_headBeta hΓ R ht RB
  obtain ⟨args0, he, HE⟩ := RE.const_spine_source hΓ (.inl ⟨_, ht⟩)
  obtain ⟨hc, hl, ha⟩ := mkApps_const_inj he
  subst args0
  exact ⟨hc, hl, HE⟩

/-- A symmetric eta join of sort-typed family applications compares every
argument by a symmetric eta join. Universe syntax may differ at the endpoints. -/
theorem EtaJoin.family_arguments (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (H : EtaJoin Γ (mkApps (.const family levels) args) (mkApps (.const family levels') args'))
    (ht : env.HasType univs Γ (mkApps (.const family levels) args) (.sort u))
    (ht' : env.HasType univs Γ (mkApps (.const family levels') args') (.sort v)) :
    List.Forall₂ (· ≈ ·) levels levels' ∧ List.Forall₂ (EtaJoin Γ) args args' := by
  obtain ⟨left, right, RL, RR, HN⟩ := H
  have hl := (RL.simAt hΓ _ ht).hasType.2
  obtain ⟨rightArgs, RB, _⟩ := RR.family_headBeta hΓ hi ht'
  obtain ⟨left0, RB0, HN0⟩ := normal_sort_head_beta_simulation hΓ HN hl RB
  have hl0 := (RB0.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hl).hasType.2
  obtain ⟨n, HN0⟩ := HN0
  rcases normal_spine_expose_headBeta hΓ .const n HN0 (bs := []) .nil hl0 with
    hp | ⟨head, leftArgs, hh, RB1, HA⟩ | ⟨A, body, m, xs, B, hm, RB1, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB1, hz, HB, ha, hf⟩
  · exact (HasType.sort_not_proof hΓ hl0 hp).elim
  · cases hh with
    | const hlevels =>
      simp only [mkApps_nil] at RB1
      simp only [List.append_nil] at HA
      obtain ⟨_, rfl, HE⟩ := RL.headBeta_const_arguments hΓ ht (RB0.trans RB1)
      obtain ⟨_, _, HE'⟩ := RR.headBeta_const_arguments hΓ ht' RB
      refine ⟨hlevels, ?_⟩
      have Hmid : List.Forall₂ (fun a b => ∃ x, TypedEtaExpansion Γ a x ∧ NormalEq Γ x b)
          args rightArgs := HE.trans
        (fun a x b (E : TypedEtaExpansion Γ a x) (N : NormalEq Γ x b) => ⟨x, E, N⟩) HA
      exact Hmid.trans (fun a b c (H : ∃ x, TypedEtaExpansion Γ a x ∧ NormalEq Γ x b)
          (E' : TypedEtaExpansion Γ c b) => by
        obtain ⟨x, E, N⟩ := H
        exact ⟨x, b, E, E', N⟩) HE'.flip
  · have hb := (RB1.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hl0).hasType.2
    exact (HasType.sort_not_lam hΓ hb).elim
  · have hz' := (RB1.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hl0).hasType.2
    exact ((hz'.uniqU henv hΓ hz).sort_forallE_inv henv hΓ).elim

/-- Computation followed by symmetric eta/normal comparison between rigid
family applications supplies a phase for each parameter or index. -/
theorem PrefixEtaJoin.family_arguments (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ ls rhs, ¬ D.unfolds family ls rhs)
    (H : PrefixEtaJoin D Γ (mkApps (.const family levels) args) (mkApps (.const family levels') args'))
    (ht : env.HasType univs Γ (mkApps (.const family levels) args) (.sort u))
    (ht' : env.HasType univs Γ (mkApps (.const family levels') args') (.sort v)) :
    List.Forall₂ (· ≈ ·) levels levels' ∧ List.Forall₂ (PrefixEtaJoin D Γ) args args' := by
  obtain ⟨left, right, RL, RR, HJ⟩ := H
  obtain ⟨leftArgs, rfl, HL⟩ := RL.rigid_spine_paths (henv.projectionRigid hi) hn
  obtain ⟨rightArgs, rfl, HR⟩ := RR.rigid_spine_paths (henv.projectionRigid hi) hn
  obtain ⟨hlevels, HA⟩ := HJ.family_arguments hΓ hi (RL.simAt hs hΓ _ ht).hasType.2
    (RR.simAt hs hΓ _ ht').hasType.2
  refine ⟨hlevels, ?_⟩
  have HLJ : List.Forall₂ (PrefixEtaJoin D Γ) args rightArgs :=
    HL.trans (fun a b c (R : PrefixCompute D Γ a b) (H : EtaJoin Γ b c) =>
      (PrefixEtaJoin.of_eta H).prepend_left R) HA
  exact HLJ.trans (fun a b c (H : PrefixEtaJoin D Γ a b) (R : PrefixCompute D Γ c b) =>
    H.prepend_right R) HR.flip

end Lean4Lean.VEnv.Strengthening.PureObservation
