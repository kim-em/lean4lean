import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolyAliasReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordInput

/-! # Polymorphic aliases from actual registered family templates

The actual registered body supplies ordinary typing at every universe instance.
No separate typing, observation, computation or native certificate for its
parameter is assumed. The family itself retains its registered monomorphic signature.
-/
namespace Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- Ordinary carrier equality fixes the monomorphic family instance in the
computational readout. Alias unfolding remains an explicit operational step. -/
theorem family_head
    (HE : TypeEquality Δ e (.atom RT))
    (HR : Obs t 1 Δ (fun _ _ _ => False) e .sort .pi) :
    ∃ a, Compute (ErasedIotaPrimitive D₀) (e.subst σ) (.app (.const t []) a) := by
  have HS : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  obtain ⟨ls, args, hn, RB⟩ := HR.head_readout (σ := Subst.id)
  simp only [ProofShape.subst_id] at RB
  obtain ⟨Γ, A, hΓ, _, HE, EA⟩ := HE
  obtain ⟨actual, RA, EE⟩ := proofErase_compute_replay HS (erased_iota_replay HS)
    hΓ HE.hasType.1 (EA ▸ RB)
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EE
  have HE' := HE.symm.trans (RA.simAt HS hΓ _ HE.hasType.1)
  have HF : env.IsDefEqU univs Γ (VExpr.mkApps (.const t []) [Q.value hi hS])
      (VExpr.mkApps (.const t ls) args') := HE'.toU
  have HL := (HF.structApp_inv henv hΓ hTag HE.hasType.2).1
  cases HL
  cases args with
  | nil => simp at hn
  | cons a args =>
    have E : args = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hn; omega)
    subst args
    exact ⟨a.subst σ, by simpa only [ProofShape.mkApps, List.foldl_cons, List.foldl_nil,
      ProofShape.subst] using RB.subst (fun H => erased_iota_primitive_subst H) (σ := σ)⟩

/-- An installed definition unfolds at every well-formed universe instance
of its declared arity. This uses the actual registry equation. -/
theorem registered_unfold
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = value.uvars) :
    (D₀).unfolds name levels (value.value.instL levels) := by
  have hdef := (definitionRegistry_registered hreg).1.2
  exact ⟨value.toDefEq, levels, hdef, hw, hl, by
    simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl, hname], rfl⟩

/-- Registry typing gives independent observations for every equivalent
universe instance of a family alias. Application inversion recovers each actual
parameter's typing; no parameter or observation premise is needed. -/
theorem registered_family_evidence
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hbody : value.value = .app (.const t []) p)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = value.uvars)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    TypeEquality (proofEraseCtx Γ) (proofErase Γ (.const name levels)) (.atom RT) ∧
      Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
        (proofErase Γ (.const name levels)) .sort .pi := by
  have hs : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  have HP : ∀ {ls rhs}, (D₀).unfolds name ls rhs →
      rhs = .app (.const t []) (p.instL ls) →
      env.HasType univs Γ (p.instL ls) (Q.control U).expr := by
    intro ls rhs HD EB
    obtain ⟨T, HT⟩ := hs Γ name ls rhs HD
    have H : env.HasType univs Γ (.app (.const t []) (p.instL ls)) T := EB ▸ HT.hasType.2
    obtain ⟨A, B, hf, hp⟩ := H.app_inv henv hΓ
    exact argument_at_displayed_domain hΓ hf (hF.weak0 henv.ordered) hp
  have HD := registered_unfold hreg hname hw hl
  have EB : value.value.instL levels = .app (.const t []) (p.instL levels) := by
    simp only [hbody, VExpr.instL, List.map_nil]
  have hfamily := (hF.weak0 (Γ := Γ) henv.ordered).app (HP HD EB)
  have HA := (hs Γ name levels _ HD).of_r henv hΓ (EB ▸ hfamily)
  have HE := IsDefEq.appDF (hF.weak0 (Γ := Γ) henv.ordered) (Q.value_equal hi hS (HP HD EB))
  have ht := HA.hasType.1
  have EE : proofErase Γ (.const name levels) = .const name levels := if_neg (not_isProof_of_sort hΓ ht)
  refine ⟨⟨Γ, _, hΓ, rfl, HA.trans (EB ▸ HE), rfl⟩, ?_⟩
  rw [EE]
  obtain ⟨_, hU⟩ := ht.isType henv hΓ
  apply Obs.delta ⟨Γ, _, _, hΓ, rfl, ht, DemandProfile.Fits.of_sortTelescope hΓ hU .sort, EE⟩ HD
  intro levels' rhs' _ HD'
  obtain ⟨v, hv, _, Er⟩ := PureObservation.Definitions.ofEnv_origin henv HD'
  cases Option.some.inj (hreg.symm.trans hv)
  have EB' : rhs' = .app (.const t []) (p.instL levels') := by
    simp only [Er, hbody, VExpr.instL, List.map_nil]
  obtain ⟨T, HT⟩ := hs [] name levels' rhs' HD'
  have HR := Obs.of_rigid (DependentRecordDemand.rigid_family_observation hi hS Q hF hΓ (HP HD' EB'))
  have EC := proofErase_closed_context ((D₀).closed HD') HT.hasType.2 hΓ
  rw [← EC, EB']
  exact HR

end Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
