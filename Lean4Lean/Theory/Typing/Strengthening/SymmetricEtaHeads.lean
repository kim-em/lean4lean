import Lean4Lean.Theory.Typing.Strengthening.EtaSpineHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaCompatibility
import Lean4Lean.Theory.Typing.Strengthening.NormalBetaSimulation

/-! # Head exposure with eta expansion on both sides

A terminal join may expand either endpoint before ordinary normal comparison.
Pi heads survive immediately; family heads are recovered by head-beta
normalization of the right eta spine and beta simulation of normal comparison.
These head results require no composition assumption. `SymmetricEtaAlgebra`
proves composition through a typed middle using exact eta confluence.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Finite typed eta on both sides, followed by ordinary normal comparison.
Composition through a typed middle is proved in `SymmetricEtaAlgebra`. -/
def EtaJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b', TypedEtaExpansion Γ a a' ∧ TypedEtaExpansion Γ b b' ∧ NormalEq Γ a' b'

/-- An existing one-sided terminal phase is a symmetric terminal join. -/
theorem EtaNormal.join (H : EtaNormal Γ a b) : EtaJoin Γ a b := by
  obtain ⟨a', RE, HN⟩ := H
  exact ⟨a', b, RE, .refl, HN⟩

theorem EtaJoin.symm (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaJoin Γ a b) :
    EtaJoin Γ b a := by
  obtain ⟨a', b', RA, RB, HN⟩ := H
  exact ⟨b', a', RB, RA, HN.symm hΓ⟩

/-- Independent source typings suffice for soundness; the output equality is
at the left endpoint's type. -/
theorem EtaJoin.defeq (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaJoin Γ a b)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    env.IsDefEq univs Γ a b A := by
  obtain ⟨a', b', RA, RB, HN⟩ := H
  have HA := RA.simAt hΓ _ ha
  have HB := RB.simAt hΓ _ hb
  have HE := HA.trans ((HN.defeq hΓ).of_l henv hΓ HA.hasType.2)
  exact HE.trans (HB.toU.symm.of_l henv hΓ HE.hasType.2)

/-- Actual eta expansion of a typed Pi retains a Pi on the right. -/
theorem TypedEtaExpansion.pi_shape (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ (.forallE A B) out)
    (ht : env.HasType univs Γ (.forallE A B) T) :
    ∃ A' B', out = .forallE A' B' := by
  obtain ⟨A', B', he, _, _⟩ := R.full.forallE_inv hΓ ht
  exact ⟨A', B', he⟩

/-- An eta-expanded registered family spine reaches the same head by head
beta alone. All original arguments retain full paths, hence their arity. -/
theorem TypedEtaExpansion.family_headBeta (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (R : TypedEtaExpansion Γ (mkApps (.const family levels) args) out)
    (ht : env.HasType univs Γ (mkApps (.const family levels) args) (.sort u)) :
    ∃ args', HeadBetaRed out (mkApps (.const family levels) args') ∧
      args'.length = args.length := by
  obtain ⟨doms, w, _, hhead⟩ := StructureReplay.family_head_telescope henv hΓ hi ⟨_, ht⟩
  have hS : SortHeaded family levels := fun hΔ => ⟨doms, w, hhead hΔ⟩
  have hargs : TypedArgs Γ args := fun a ha => mkApps_arg_type hΓ ht ha
  obtain ⟨n, HE⟩ := EtaSpine.fullReduction (henv.projectionRigid hi) hS hΓ R.full
    (EtaSpine.spine (FullReduction.forall₂_rfl args)) hargs ht
  obtain ⟨args', RB, HA⟩ := etaSpine_sort_headBeta hΓ HE hargs (R.simAt hΓ _ ht).hasType.2
  exact ⟨args', RB, HA.length_eq.symm⟩

/-- Eta followed by beta and normal comparison to a family exposes that family
by actual computation. The extra beta path may compute under arbitrary syntax;
its source need not already be a literal constant spine. -/
theorem eta_beta_normal_family_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (RE : TypedEtaExpansion Γ e etaOut)
    (RB : BetaRed etaOut betaOut)
    (HN : NormalEq Γ betaOut (mkApps (.const family levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  have htEta := (RE.simAt hΓ _ ht).hasType.2
  have htBeta := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htEta).hasType.2
  obtain ⟨n, HN⟩ := HN
  rcases normal_spine_expose_beta hΓ .const n HN (bs := []) .nil htBeta with
    hp | ⟨head, args0, hh, RB0, HA⟩ | ⟨A, body, m, xs, B, hm, RB0, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB0, hz, HB, ha, hf⟩
  · exact (HasType.sort_not_proof hΓ htBeta hp).elim
  · cases hh with
    | const hlevels =>
      simp only [mkApps_nil] at RB0
      have RX := (RE.observation (D := Definitions.empty) hΓ ht).trans
        (.compute (.base (.of_beta (RB.trans RB0))))
      obtain ⟨args1, RC, hlen⟩ := RX.family_exposure (fun _ _ _ _ _ h => False.elim h) hi
      have RC' : PatternCompute D e (mkApps (.const family _) args1) :=
        RC.mono (fun h => False.elim h)
      exact ⟨_, args1, .base RC', hlevels, hlen.trans (by simpa using HA.length_eq)⟩
  · have hbody := (RB0.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htBeta).hasType.2
    exact (HasType.sort_not_lam hΓ hbody).elim
  · have hz' := (RB0.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htBeta).hasType.2
    exact ((hz'.uniqU henv hΓ hz).sort_forallE_inv henv hΓ).elim

/-- Eta on both sides cannot hide the left Pi head of a Pi comparison. -/
theorem EtaJoin.pi_source (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaJoin Γ e (.forallE A B)) (ht : env.HasType univs Γ (.forallE A B) T) :
    ∃ A' B', e = .forallE A' B' := by
  obtain ⟨left, right, RL, RR, HN⟩ := H
  obtain ⟨_, _, rfl⟩ := RR.pi_shape hΓ ht
  obtain ⟨_, _, rfl⟩ := normal_pi_right hΓ HN
  exact RL.forallE_source

/-- A symmetric eta join retains registered family head exposure, equivalent
levels and the original arity. Both endpoint sort typings are explicit. -/
theorem EtaJoin.family_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (H : EtaJoin Γ e (mkApps (.const family levels) args))
    (ht : env.HasType univs Γ e (.sort u))
    (hr : env.HasType univs Γ (mkApps (.const family levels) args) (.sort v)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨left, right, RL, RR, HN⟩ := H
  obtain ⟨args0, RB, hlen⟩ := RR.family_headBeta hΓ hi hr
  obtain ⟨left', RB', HN'⟩ := normal_beta_simulation hΓ HN RB.toBeta
  obtain ⟨levels', args', RC, Hlevels, Hlen⟩ :=
    eta_beta_normal_family_exposure hΓ hi RL RB' HN' ht
  exact ⟨levels', args', RC, Hlevels, Hlen.trans hlen⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
