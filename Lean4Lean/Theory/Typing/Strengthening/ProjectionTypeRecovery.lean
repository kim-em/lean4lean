import Lean4Lean.Theory.Typing.Strengthening.CastComputation

/-! # Reconstruct projection types from a recovered major family

The actual projection typing supplies its field selection and elimination guard.
Rigid-family injectivity transports that selection to any recovered major type.
Field-type syntax also commutes with arbitrary binder insertion and reflects it.
No target field typing or projection guard is assumed in the smaller context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- A recovered family application determines the type of an already
well-formed projection. Its parameters may differ from the original typing's
parameters; rigid-head injectivity and field congruence align them below. -/
theorem projection_at_recovered_family (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hi : env.projections s info)
    (ht : VExpr.WF env U Γ (.proj s i m))
    (hm : env.HasType U Γ m (mkApps (.const s ls) args))
    (hfield : info.fieldType s ls (args.take info.nparams) i m = some F) :
    env.HasType U Γ (.proj s i m) F := by
  obtain ⟨_, ht⟩ := ht
  obtain ⟨info₀, ls₀, ps₀, is₀, sm₀, F₀, u₀, hi₀, hw₀, hl₀, hp₀, hiLen₀,
    hfield₀, hF₀, hm₀, hclosed, hguard⟩ := HasType.proj_inv henv hΓ ht
  obtain rfl := henv.ordered.projections_unique hi₀ hi
  obtain ⟨v, hfamily₀⟩ := hm₀.hasType.2.isType henv hΓ
  have htypes := hm₀.hasType.2.uniqU henv hΓ hm
  obtain ⟨hls, hargs⟩ := htypes.rigidApp_inv henv hΓ (henv.projectionRigid hi₀) hfamily₀
  have hps := List.forall₂_take hargs info₀.nparams
  rw [← hp₀, List.take_left] at hps
  rw [hp₀] at hps
  obtain ⟨_, hfamily⟩ := hm.isType henv hΓ
  obtain ⟨_, hhead⟩ := (show VExpr.WF env U Γ (mkApps (.const s ls) args) from ⟨_, hfamily⟩).of_mkApps henv hΓ
  obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ hhead
  have hcongr := fieldType_congr henv.ordered hi₀ hls hw hps ⟨_, hm₀⟩ hfield₀ hfield
  have hF := (hF₀.strong henv hΓ).hasType'.1.congrUB_defeq henv
    henv.chainHeadInjectivity hΓ (.zero []) hcongr
  have hp : env.HasType U Γ (.proj s i m) F₀ :=
    .projDF hi₀ hw₀ hl₀ hp₀ hiLen₀ hfield₀ hF₀ hm₀ hm₀ hclosed hguard
  exact hF.defeq hp

/-- Field selection commutes with an arbitrary injective binder renaming. -/
theorem fieldType_lift'_some {info : VProjectionInfo} (hclosed : info.ctorType.Closed)
    (H : info.fieldType s ls ps i m = some F) :
    info.fieldType s ls (ps.map (·.lift' ρ)) i (m.lift' ρ) = some (F.lift' ρ) := by
  have h := info.fieldType_subst_some hclosed H (substitution := Subst.lift_r Subst.id ρ)
  simpa only [← lift_as_subst] using h

/-- Selecting a field on lifted parameters and major produces a lifted field
type. The retraction is used only for raw syntax, with no typing assumption. -/
theorem fieldType_lift'_inv {info : VProjectionInfo} (hclosed : info.ctorType.Closed)
    (H : info.fieldType s ls (ps.map (·.lift' ρ)) i (m.lift' ρ) = some F) :
    ∃ F₀, F = F₀.lift' ρ ∧ info.fieldType s ls ps i m = some F₀ := by
  have h := info.fieldType_subst_some hclosed H (substitution := ρ.inv)
  simp only [List.map_map, Function.comp_def, subst_lift', lift_l_inv, subst_id, List.map_id'] at h
  have hh := fieldType_lift'_some hclosed h (ρ := ρ)
  rw [H] at hh
  exact ⟨_, Option.some.inj hh, h⟩

end Lean4Lean.VEnv.Strengthening
