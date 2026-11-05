import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeStructureTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureTelescopeSyntax

/-! # Structure eta and unit-like equality in computation chains

Generic exact recovery supplies the structure guard. Computation-chain
instantiation transports the equation to arbitrary actual majors, without
transporting that native certificate or assuming computational confluence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Structure expansion after any finite dependent telescope has a typed
computation chain. The actual function/major needs ordinary typing only; every
native guard is supplied by the generic declaration before instantiation. -/
theorem TypedComputationEq.structure_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps))) :
    TypedComputationEq D Γ f
      (VExpr.wrapLams ds (structExpand family info ls ps (etaOpen ds.length f)))
      (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) := by
  let T := VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
  obtain ⟨hge, RG⟩ := static_structure_generic_structure_eta_telescope heq hs hΓ hi hp hx hadm hT
  have HG := TypedComputationEq.of_compute heq hs hΓT hg hge RG
  have HI := HG.inst heq hs hΓ hT hf
  simpa only [EtaTelescope.generic_structure_inst, VExpr.inst, VExpr.instVar_zero,
    VExpr.inst_lift] using HI

/-- Every admissible ordinary structure eta equation has a computation chain,
including retained fields, proof fields, dependent parameters and proof majors. -/
theorem TypedComputationEq.structEta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs Γ (structExpand family info ls ps m) (VExpr.mkApps (.const family ls) ps)) :
    TypedComputationEq D Γ (structExpand family info ls ps m) m (VExpr.mkApps (.const family ls) ps) := by
  have H := TypedComputationEq.structure_eta_telescope (ds := []) heq hs hΓ hi hp hx
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc) hm
  exact H.symm

/-- Ordinary equality between two inhabitants of an empty unindexed structure
is a chain through its registered constructor. No native evidence for either
inhabitant and no joining premise is required. -/
theorem TypedComputationEq.unitLike
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hn : env.HasType univs Γ n (VExpr.mkApps (.const family ls) ps)) :
    TypedComputationEq D Γ m n (VExpr.mkApps (.const family ls) ps) := by
  have hcm : env.HasType univs Γ (structExpand family info ls ps m) (VExpr.mkApps (.const family ls) ps) := by
    simpa only [structExpand, hz, List.range_zero, List.map_nil, List.append_nil] using
      hm.unitLike_constructor henv hΓ hi hp hx hz
  have hcn : env.HasType univs Γ (structExpand family info ls ps n) (VExpr.mkApps (.const family ls) ps) := by
    simpa only [structExpand, hz, List.range_zero, List.map_nil, List.append_nil] using
      hn.unitLike_constructor henv hΓ hi hp hx hz
  have HM := TypedComputationEq.structEta heq hs hΓ hi hp hx hm hcm
  have HN := TypedComputationEq.structEta heq hs hΓ hi hp hx hn hcn
  simp only [structExpand, hz, List.range_zero, List.map_nil, List.append_nil] at HM HN
  exact HM.symm.trans HN

end Lean4Lean.VEnv.Strengthening
