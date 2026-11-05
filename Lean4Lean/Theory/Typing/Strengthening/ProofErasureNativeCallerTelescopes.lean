import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeReification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualTelescopeAnnotations
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeStructureTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureTelescopeSyntax

/-! # Transforming dependent function arguments through native callers

A caller can run a computation of its fresh generic argument before supplying
the actual argument. Applying this to an entire eta telescope replaces every
written lambda domain simultaneously. The actual function argument needs no
native certificate, and its annotations need no individual computation paths.
The same construction performs structure eta below the entire lambda prefix.
The caller's exact native Pi remains essential and explicit.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every computation of the caller's generic argument can run through the
whole retained call before the actual argument is supplied. No recovery of that
argument is needed. The computed generic image may still depend on the generic
variable and may be raw; this is not a forward path for the argument itself. -/
theorem static_structure_native_caller_generic_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B)))
    (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ (.app f x))
    (RG : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.bvar 0)) generic) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (.app (proofErase Γ f) (generic.inst (proofErase Γ x))) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hfg : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
      HasType.app (hf.weakN henv Ctx.LiftN.one) (show env.HasType univs (A :: Γ) (.bvar 0) A.lift from .bvar .zero)
  have hng : ¬ IsProof (A :: Γ) (.app f.lift (.bvar 0)) := by
    intro hp
    have HP := (isProof_instN hΓA hx Ctx.InstN.zero hfg).2 hp
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] at HP
    exact hn HP
  have RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
      (.app (proofErase (A :: Γ) f.lift) generic) := by
    rw [show proofErase (A :: Γ) (.app f.lift (.bvar 0)) = .app _ _ from if_neg hng]
    exact .app .refl RG
  have RC := static_structure_native_application_instantiation heq hs hΓ hf RF hx RB ScopedCompute.refl
  rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one hf] at RC
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using RC

/-- An exactly recovered caller replaces all written domains of a supplied
lambda telescope by its assigned dependent domains. The whole body is retained.
Proof-valued functions, proof domains, dependent result types and arbitrary
telescope lengths are included. No type-fork or instantiation-joining premise,
native argument certificate, or join between written domains is used. -/
theorem static_structure_native_caller_telescope_annotations
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (VExpr.wrapForalls ds T) C))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE (VExpr.wrapForalls ds T) C)))
    (hx : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f (VExpr.wrapLams written b)))
      (proofErase Γ (.app f (VExpr.wrapLams ds b))) := by
  have HE := telescope_annotations_defeq hΓ hx hlen
  have Hcall := IsDefEq.appDF hf HE
  classical
  by_cases hp : IsProof Γ (.app f (VExpr.wrapLams written b))
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ Hcall).1 hp)]
    exact .refl
  have hp' := mt (isProof_congr hΓ Hcall).2 hp
  obtain ⟨u, hT⟩ := hx.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg := generic_eta_telescope_typing hΓ hT
  have RG := static_structure_generic_eta_telescope heq hs hΓ hT
  have RC := static_structure_native_caller_generic_argument heq hs hΓ hf RF hx hp RG
  have RB := proofErase_beta_forward hΓ (hg.instN henv.ordered Ctx.InstN.zero hx)
    (EtaTelescope.generic_inst_reannotate_beta hlen b)
  rw [proofErase_instN hΓT hx Ctx.InstN.zero hg] at RB
  rw [show proofErase Γ (.app f (VExpr.wrapLams ds b)) = .app _ _ from if_neg hp']
  exact RC.trans (.beta (.app .refl RB))

/-- Two supplied lambda telescopes with the same body meet through their
native caller at the assigned annotations. Their written domains may all differ
and need not have a common reduct in isolation. This covers a callable context,
not arbitrary type contexts or arbitrary pairs of argument bodies. -/
theorem static_structure_native_caller_same_body_telescopes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (VExpr.wrapForalls ds T) C))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE (VExpr.wrapForalls ds T) C)))
    (hl : env.HasType univs Γ (VExpr.wrapLams left b) (VExpr.wrapForalls ds T))
    (hr : env.HasType univs Γ (VExpr.wrapLams right b) (VExpr.wrapForalls ds T))
    (hlenL : left.length = ds.length) (hlenR : right.length = ds.length) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams left b)))
        (proofErase Γ (.app f (VExpr.wrapLams ds b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (VExpr.wrapLams right b)))
        (proofErase Γ (.app f (VExpr.wrapLams ds b))) :=
  ⟨static_structure_native_caller_telescope_annotations heq hs hΓ hf RF hl hlenL,
    static_structure_native_caller_telescope_annotations heq hs hΓ hf RF hr hlenR⟩

/-- A native caller performs structure eta beneath an arbitrary dependent
lambda prefix of its supplied argument. Actual typing of the expansion derives
admissibility. Neither the original major nor its lambda closure needs native
recovery, and no parameter joins or type-fork premise occur. The caller still
must recover its displayed Pi exactly; ordinary caller typing does not supply
that certificate in general. -/
theorem static_structure_native_caller_structure_eta_under_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hi : env.projections family info) (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs (ds.reverse ++ Γ) m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs (ds.reverse ++ Γ) (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps))
    (hf : env.HasType univs Γ f
      (.forallE (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) C))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (.forallE (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) C))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f (VExpr.wrapLams ds m)))
      (proofErase Γ (.app f (VExpr.wrapLams ds (structExpand family info ls ps m)))) := by
  have hLam := (IsDefEq.etaOpen_wrapLams hΓ hctx hm).hasType.1
  have HE : env.IsDefEq univs Γ (VExpr.wrapLams ds m)
      (VExpr.wrapLams ds (structExpand family info ls ps m))
      (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) :=
    (IsDefEq.structEta hi hp hx hm hc).symm.etaOpen_wrapLams hΓ hctx
  have Hcall := IsDefEq.appDF hf HE
  classical
  by_cases hn : IsProof Γ (.app f (VExpr.wrapLams ds m))
  · rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 ((isProof_congr hΓ Hcall).1 hn)]
    exact .refl
  have hn' := mt (isProof_congr hΓ Hcall).2 hn
  obtain ⟨u, hT⟩ := hLam.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ)
      (env.IsType univs) := ⟨hΓ, u, hT⟩
  obtain ⟨hg, RG⟩ := static_structure_generic_structure_eta_telescope heq hs hΓ hi hp hx
    ((StructureReplay.expansion_typed_iff henv hctx hi hp hx hm).1 hc) hT
  have RC := static_structure_native_caller_generic_argument heq hs hΓ hf RF hLam hn RG
  have RB := proofErase_beta_forward hΓ (hg.instN henv.ordered Ctx.InstN.zero hLam)
    (EtaTelescope.generic_structure_inst_wrapLams_beta ds m)
  rw [proofErase_instN hΓT hLam Ctx.InstN.zero hg] at RB
  rw [show proofErase Γ (.app f (VExpr.wrapLams ds (structExpand family info ls ps m))) =
    .app _ _ from if_neg hn']
  exact RC.trans (.beta (.app .refl RB))

end Lean4Lean.VEnv.Strengthening
