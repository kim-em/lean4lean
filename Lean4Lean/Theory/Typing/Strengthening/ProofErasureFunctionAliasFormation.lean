import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolyAliasFamily

/-! # Function-valued family aliases from actual declarations

A registered lambda can compute a family parameter from an arbitrary dependent
argument. Its domain may be Prop. Registry typing supplies all body observations;
only ordinary typing of the supplied argument is needed for an application.
-/
namespace Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
open _root_.Lean4Lean Params ProofShape DemandProfile
open ConstructorDemand (TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier)
variable [Params]
/-- The earlier monomorphic observer excludes applied stored aliases at any
function profile, even when the alias has no universe parameters. -/
theorem stored_function_application_not_monomorphic
    (hc : env.Rigid family)
    (HD : (PureObservation.Definitions.ofEnv env univs henv).unfolds name levels rhs) :
    ¬ AliasDemandProfile.Obs family arity Δ S (.app (.const name levels) x) profile o := by
  intro H
  have HH := H.primitive_head (by trivial) (by intro n E; cases E)
  have hn : name = family := Option.some.inj HH
  exact PureObservation.Definitions.ofEnv_no_rigid henv hc (hn ▸ HD)

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv
include hF

/-- A family-producing lambda observes its result without demanding the
argument. The parameter may depend on the bound variable, including a proof. -/
theorem family_lambda_observation
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs (A :: Γ) p (Q.control U).expr) :
    Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.lam A (.app (.const t []) p))) (.arrow .ignored .sort) (.app [] .pi) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hB := (hF.weak0 (Γ := A :: Γ) henv.ordered).app hp
  have hf := HasType.lam hA hB
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EF : proofErase Γ (.lam A (.app (.const t []) p)) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) (.app (.const t []) p)) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have HB := Obs.of_rigid (DependentRecordDemand.rigid_family_observation hi hS Q hF hΓA hp)
  rw [EF]
  apply Obs.lam ⟨Γ, _, _, hΓ, rfl, hf, Fits.of_sortTelescope hΓ hPi (.forallE .sort), EF⟩ (by simp)
  simpa only [ProofShape.subst_id, proofEraseCtx, spineProfile] using
    HB.rename ContextRenaming.identity.interpretation
      (T := Sets.cons .ignored [] (fun _ _ _ => False)) (by intro i t k h; cases h)

/-- Every actual instance of a registered family-producing lambda has an
ordinarily typed domain and parameter. Both come from the stored body's typing. -/
theorem registered_function_instance
    (hreg : env.definitionRegistry name = some value)
    (hbody : value.value = .lam A (.app (.const t []) p))
    (HD : (D₀).unfolds name levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ u, env.HasType univs Γ (A.instL levels) (.sort u) ∧
      env.HasType univs (A.instL levels :: Γ) (p.instL levels) (Q.control U).expr := by
  obtain ⟨v, hv, _, Er⟩ := PureObservation.Definitions.ofEnv_origin henv HD
  cases Option.some.inj (hreg.symm.trans hv)
  have EB : rhs = .lam (A.instL levels) (.app (.const t []) (p.instL levels)) := by
    simp only [Er, hbody, VExpr.instL, List.map_nil]
  have hs : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  obtain ⟨T, HT⟩ := hs Γ name levels rhs HD
  have H : env.HasType univs Γ (.lam (A.instL levels) (.app (.const t []) (p.instL levels))) T := EB ▸ HT.hasType.2
  obtain ⟨⟨u, hA⟩, B, hb⟩ := H.lam_inv henv hΓ
  have hΓA : OnCtx (A.instL levels :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hb' : env.HasType univs (A.instL levels :: Γ) (.app (.const t []) (p.instL levels)) B := hb
  obtain ⟨A', B', hf, hp⟩ := hb'.app_inv henv hΓA
  exact ⟨u, hA, argument_at_displayed_domain hΓA hf (hF.weak0 henv.ordered) hp⟩

/-- A registered function alias carries a function demand. All equivalent
universe instances are initialized from their own actual typed lambda bodies. -/
theorem registered_function_observation
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hbody : value.value = .lam A (.app (.const t []) p))
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = value.uvars)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.const name levels)) (.arrow .ignored .sort) (.app [] .pi) := by
  have HD := registered_unfold hreg hname hw hl
  obtain ⟨u, hA, hp⟩ := registered_function_instance hi hS Q hF hreg hbody HD hΓ
  have hB := (hF.weak0 (Γ := A.instL levels :: Γ) henv.ordered).app hp
  have hf := HasType.lam hA hB
  have EB : value.value.instL levels = .lam (A.instL levels) (.app (.const t []) (p.instL levels)) := by
    simp only [hbody, VExpr.instL, List.map_nil]
  have hs : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  have ht := ((hs Γ name levels _ HD).of_r henv hΓ (EB ▸ hf)).hasType.1
  obtain ⟨_, hPi⟩ := ht.isType henv hΓ
  have EE : proofErase Γ (.const name levels) = .const name levels := if_neg (not_isProof_function_to_sort hΓ ht)
  rw [EE]
  apply Obs.delta ⟨Γ, _, _, hΓ, rfl, ht, Fits.of_sortTelescope hΓ hPi (.forallE .sort), EE⟩ HD
  intro levels' rhs' _ HD'
  obtain ⟨u', hA', hp'⟩ := registered_function_instance hi hS Q hF hreg hbody HD' hΓ
  obtain ⟨v, hv, _, Er⟩ := PureObservation.Definitions.ofEnv_origin henv HD'
  cases Option.some.inj (hreg.symm.trans hv)
  obtain ⟨T, HT⟩ := hs [] name levels' rhs' HD'
  have EC := proofErase_closed_context ((D₀).closed HD') HT.hasType.2 hΓ
  rw [← EC, Er]
  simp only [hbody, VExpr.instL, List.map_nil]
  exact family_lambda_observation hi hS Q hF hΓ hA' hp'

/-- Applying a registered family-producing function alias gives both the
ordinary record carrier and independent operational family evidence. The argument
has ordinary typing only; the domain may be a proposition or depend on universes. -/
theorem registered_function_application_evidence
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hbody : value.value = .lam A (.app (.const t []) p))
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = value.uvars)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (A.instL levels)) :
    TypeEquality (proofEraseCtx Γ) (proofErase Γ (.app (.const name levels) x)) (.atom RT) ∧
      Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
        (proofErase Γ (.app (.const name levels) x)) .sort .pi := by
  have HD := registered_unfold hreg hname hw hl
  obtain ⟨u, hA, hp⟩ := registered_function_instance hi hS Q hF hreg hbody HD hΓ
  have hΓA : OnCtx (A.instL levels :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf := hF.weak0 (Γ := A.instL levels :: Γ) henv.ordered
  have hB := hf.app hp
  have HL := HasType.lam hA hB
  have EB : value.value.instL levels = .lam (A.instL levels) (.app (.const t []) (p.instL levels)) := by
    simp only [hbody, VExpr.instL, List.map_nil]
  have hs : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  have HA := (hs Γ name levels _ HD).of_r henv hΓ (EB ▸ HL)
  have HB : env.IsDefEq univs (A.instL levels :: Γ) (.app (.const t []) (p.instL levels))
      (HeterogeneousControl.ControlType.atom RT).expr (.sort (.succ .zero)) :=
    IsDefEq.appDF hf (Q.value_equal hi hS hp)
  have HI : env.IsDefEq univs Γ ((VExpr.app (.const t []) (p.instL levels)).inst x)
      (HeterogeneousControl.ControlType.atom RT).expr (.sort (.succ .zero)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, HeterogeneousControl.ControlType.expr_subst,
      VExpr.subst] using HB.instN henv.ordered hx Ctx.InstN.zero
  have HE := (IsDefEq.appDF (EB ▸ HA) hx).trans ((IsDefEq.beta hB hx).trans HI)
  refine ⟨⟨Γ, _, hΓ, rfl, HE, rfl⟩, ?_⟩
  obtain ⟨_, hPi⟩ := HA.hasType.1.isType henv hΓ
  exact (registered_function_observation hi hS Q hF hreg hname hbody hw hl hΓ).telescope
    (args := [x]) hΓ HA.hasType.1 (Fits.of_sortTelescope hΓ hPi (.forallE .sort)) (.cons hx .nil)

end Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
