import Lean4Lean.Theory.Typing.Strengthening.CastHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.FamilyHeadRepair
import Lean4Lean.Theory.Typing.Strengthening.StructureFamilyArity

/-! # Recover family heads through an outer type cast

Full saturation of a registered family recovers sort typing from arbitrary
typing. Thus a family-exposing payload trace can justify contraction of its
outer type cast, without a syntactic endpoint match or a supplied lower endpoint
equality. This is a root cast rule; compatible arbitrary cast erasure is not used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
open ConstructorObservation (EtaCompute ConstructorRigid)
variable [Params] {D : Definitions}

/-- A saturated family exposure of a cast payload supplies its sort typing
below. Uniqueness then aligns the cast endpoints and replays the computation. -/
theorem cast_family_exposure_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.HasType univs Γ (typeCast u X Y p x) (.sort v))
    (hlen : args.length = info.nparams + info.nindices)
    (R : CastCompute D (x.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args₀, args₀.length = args.length ∧
      env.IsDefEq univs Γ (typeCast u X Y p x) (mkApps (.const s ls) args₀) (.sort v) := by
  obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, hc⟩
  obtain ⟨out, R₀, he⟩ := R.lift_inv
  obtain ⟨args₀, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine he.symm
  have hxf := R₀.simAt heq hs hΓ X hx
  have hf := StructureReplay.family_isType_of_arity henv hΓ hi ⟨_, hxf.hasType.2⟩
    (by simpa using hlen)
  have hxt := IsType.defeqU_l henv hΓ ⟨_, hxf.symm⟩ hf
  exact ⟨args₀, by simp, (cast_type_eq henv heq hΓ hc hxt).trans_l henv hΓ hxf⟩

/-- Both eta forms may occur in the payload trace. Empty tuple observations
repair it while preserving the arity needed for lower sort reconstruction. -/
theorem cast_mixed_family_exposure_below (heq : env.HasCanonicalEq)
    (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hi : env.projections s info) (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.HasType univs Γ (typeCast u X Y p x) (.sort v))
    (hlen : args.length = info.nparams + info.nindices)
    (R : EtaCompute D (x.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args₀, args₀.length = args.length ∧
      env.IsDefEq univs Γ (typeCast u X Y p x) (mkApps (.const s ls) args₀) (.sort v) := by
  obtain ⟨args', RC, ha⟩ := R.family_exposure hD hi
  obtain ⟨args₀, ha₀, H⟩ := cast_family_exposure_below heq hs hi hΓ hc (ha.trans hlen) (.base RC)
  exact ⟨args₀, ha₀.trans ha, H⟩

/-- An inferred projection-major type may be an outer cast. A saturated family
exposure of its payload above still supplies a usable field typing below. -/
theorem cast_projection_type_below (heq : env.HasCanonicalEq)
    (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hi : env.projections s info) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ (.proj s i m))
    (hm : env.HasType univs Γ m (typeCast u X Y p x))
    (hlen : args.length = info.nparams + info.nindices)
    (R : EtaCompute D (x.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args₀ F,
      env.IsDefEqU univs Γ (typeCast u X Y p x) (mkApps (.const s ls) args₀) ∧
      info.fieldType s ls (args₀.take info.nparams) i m = some F ∧
      env.HasType univs Γ (.proj s i m) F := by
  obtain ⟨_, hc⟩ := hm.isType henv hΓ
  obtain ⟨args₀, _, H⟩ := cast_mixed_family_exposure_below heq hD hs hi hΓ hc hlen R
  obtain ⟨F, hF, hp⟩ := projection_at_recovered_family_exists henv hΓ hi ht (H.defeq hm)
  exact ⟨args₀, F, ⟨_, H⟩, hF, hp⟩

end Lean4Lean.VEnv.Strengthening
