import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeStructureTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureTelescopeSyntax
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextLambdaAnnotation

/-! # Structure eta beneath arbitrary dependent lambda prefixes

The generic telescope supplies all native guards before instantiation. Actual
lambda bodies, parameters and whole abstractions need no native certificates.
Joining still assumes the open type-only fork premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every actual admissible structure eta equation beneath a finite dependent
lambda telescope is joined in all typed type contexts, assuming TypeForkJoin.
There is no bound on telescope length, no restriction on proof domains or fields,
and no native recovery assumption on the original major or its abstraction.
General lambda congruence and the type-fork premise itself remain open. -/
theorem TypeForkJoin.contextual_structure_eta_under_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hi : env.projections family info) (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs (ds.reverse ++ Γ) m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs (ds.reverse ++ Γ) (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps)) :
    TypeContextJoin D Γ (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps))
      (VExpr.wrapLams ds m) (VExpr.wrapLams ds (structExpand family info ls ps m)) := by
  intro K z hK
  have hLam := (IsDefEq.etaOpen_wrapLams hΓ hctx hm).hasType.1
  obtain ⟨u, hT⟩ := hLam.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ)
      (env.IsType univs) := ⟨hΓ, u, hT⟩
  have HE : env.IsDefEq univs Γ (VExpr.wrapLams ds m)
      (VExpr.wrapLams ds (structExpand family info ls ps m))
      (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) :=
    (IsDefEq.structEta hi hp hx hm hc).symm.etaOpen_wrapLams hΓ hctx
  classical
  by_cases hn : IsProof Γ (VExpr.wrapLams ds m)
  · exact TypeContextJoin.of_erasure_eq hΓT hLam HE.hasType.2
      ((proofErase_eq_proof.2 hn).trans (proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hn)).symm) hK
  have hu : ¬ u ≈ .zero := by
    intro hu
    exact hn ⟨_, hLam, (IsDefEq.sortDF (hT.sort_r henv hΓ) (by trivial) hu).defeq hT⟩
  have hng : ¬ IsProof (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ) (.bvar 0) :=
    fun h => hu ((isProof_fresh_iff hΓ hT).1 h)
  obtain ⟨hg, RG⟩ := static_structure_generic_structure_eta_telescope heq hs hΓ hi hp hx
    ((StructureReplay.expansion_typed_iff henv hctx hi hp hx hm).1 hc) hT
  rw [show proofErase (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ) (.bvar 0) =
    .bvar 0 from if_neg hng] at RG
  exact type_forks_generic_context_beta heq hs HF hΓ hT hLam hg RG
    (EtaTelescope.generic_structure_inst_wrapLams_beta ds m) hK

end Lean4Lean.VEnv.Strengthening
