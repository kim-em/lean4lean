import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary

/-! # Full family-head exposure from declarative equality

Confluence supplies a join. A rigid sort-headed family spine can normalize its
eta expansions back to a literal spine; transporting that normalization through
the join exposes the same head on the other side. Sort typing excludes the
proof and lambda alternatives of normal-comparison spine exposure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Equality to a sort-typed rigid family gives an actual full reduction to that
family head. Levels and arguments may differ from the supplied family typing. -/
theorem defeq_rigid_full_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hrig : env.Rigid c) (hS : @SortHeaded (henv.params U) c ls)
    (hT : env.HasType U Γ T (.sort u))
    (H : env.IsDefEqU U Γ T (mkApps (.const c ls) args)) :
    ∃ ls' args', @FullReduction (henv.params U) Γ T (mkApps (.const c ls') args') := by
  letI := henv.params U
  have HE := H.of_l henv hΓ hT
  have hfamily := HE.hasType.2
  obtain ⟨left, right, hl, hr, hn⟩ := henv.church_rosser heq hΓ HE
  have htargs : TypedArgs Γ args := fun a ha => mkApps_arg_type hΓ hfamily ha
  obtain ⟨n, HR⟩ := EtaSpine.fullReduction hrig hS hΓ hr
    (EtaSpine.spine (FullReduction.forall₂_rfl args)) htargs hfamily
  have hright := hr.hasType hΓ hfamily
  rcases EtaSpine.normalize hΓ n HR htargs hright with
    ⟨args', hnorm, _⟩ | ⟨A, body, _, _, hnorm, _⟩
  · obtain ⟨left', hleft', hn'⟩ := hn.fullReduction hΓ hnorm
    have hleft := FullReduction.hasType hΓ (hl.trans hleft') hT
    obtain ⟨k, hk⟩ := hn'
    rcases NormalEqN.spine_expose hΓ .const k hk (bs := []) (bs' := []) .nil hleft with
      hp | ⟨h', args'', he, hred, _⟩ | ⟨A, g, _, _, _, _, hred, _⟩
    · exact (HasType.sort_not_proof hΓ hleft hp).elim
    · cases he with
      | const hls => exact ⟨_, _, (hl.trans hleft').trans hred⟩
    · exact (HasType.sort_not_lam hΓ (hred.hasType hΓ hleft)).elim
  · exact (HasType.sort_not_lam hΓ (hnorm.hasType hΓ hright)).elim

/-- Registered projection families satisfy the sort-headed hypothesis from
their normalized declaration telescope. No syntactic header assumption remains. -/
theorem defeq_projection_family_full_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hi : env.projections s info)
    (hT : env.HasType U Γ T (.sort u))
    (H : env.IsDefEqU U Γ T (mkApps (.const s ls) args)) :
    ∃ ls' args', @FullReduction (henv.params U) Γ T (mkApps (.const s ls') args') := by
  have hfamily := (H.of_l henv hΓ hT).hasType.2
  obtain ⟨doms, w, _, hhead⟩ := StructureReplay.family_head_telescope henv hΓ hi ⟨_, hfamily⟩
  apply defeq_rigid_full_exposure henv heq hΓ (henv.projectionRigid hi) _ hT H
  exact fun hΔ => ⟨doms, w, hhead hΔ⟩

/-- Every inferred major type at a well-formed projection has full reduction
to the required family head. Field selection is handled separately by totality. -/
theorem projection_type_full_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ (.proj s i m))
    (hm : env.HasType U Γ m T) :
    ∃ ls args, @FullReduction (henv.params U) Γ T (mkApps (.const s ls) args) := by
  obtain ⟨_, ht⟩ := ht
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm₀, _, _⟩ :=
    HasType.proj_inv henv hΓ ht
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  exact defeq_projection_family_full_exposure henv heq hΓ hi hT
    (hm.uniqU henv hΓ hm₀.hasType.2)

end Lean4Lean.VEnv.Strengthening
