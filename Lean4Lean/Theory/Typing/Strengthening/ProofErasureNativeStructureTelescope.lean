import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaReplay

/-! # Structure eta at the end of a native function telescope

Opening the declared telescope supplies exact recovery for the final major.
The parameters can depend on every opened binder. No argument requires native
recovery, and proof-valued functions and structures are included.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Exact assigned native recovery suffices for an actual structure expansion
in the full union, including erased majors and mixed retained/proof fields. -/
theorem static_structure_exact_native_structure_eta
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs Γ (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps))
    (RN : ¬ IsProof Γ m → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ m) (proofErase Γ (VExpr.mkApps (.const family ls) ps))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (proofErase Γ (structExpand family info ls ps m)) := by
  classical
  have HE := IsDefEq.structEta hi hp hx hm hc
  by_cases hn : IsProof Γ m
  · have hnp : IsProof Γ (structExpand family info ls ps m) := (isProof_congr hΓ HE).2 hn
    rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 hnp]
    exact .refl
  have hnc : ¬ IsProof Γ (structExpand family info ls ps m) :=
    fun h => hn ((isProof_congr hΓ HE).1 h)
  obtain ⟨_, hF⟩ := hm.isType henv hΓ
  have RF := RN hn
  rw [proofErase_const_spine hΓ hF (not_isProof_of_sort hΓ hF)] at RF
  rw [proofErase_nativeStructureOutput hΓ hi hp hc hnc]
  exact .base (erased_static_structure_eta_expansion_union_structure
    (.intro hi hx ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
      (by simpa only [List.length_map] using hp) RF))

/-- Ordinary telescope eta followed by admissible structure eta preserves the
original assigned function type, including dependent structure parameters. -/
theorem structure_eta_telescope_defeq
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps))) :
    env.IsDefEq univs Γ f
      (VExpr.wrapLams ds (structExpand family info ls ps (etaOpen ds.length f)))
      (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) := by
  obtain ⟨hctx, hopen⟩ := hf.etaOpen_wf henv.ordered hΓ
  have hc := (StructureReplay.expansion_typed_iff henv hctx hi hp hx hopen).2 hadm
  exact (hf.etaOpen_defeq henv hΓ).trans
    ((IsDefEq.structEta hi hp hx hopen hc).symm.etaOpen_wrapLams hΓ hctx)

/-- Exact assigned native recovery opens any finite dependent telescope and
expands its final structure major. The only admissibility premise is precisely
the one equivalent to ordinary typing of structure eta; no coverage is assumed. -/
theorem static_structure_native_structure_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f)
      (proofErase Γ (VExpr.wrapLams ds (structExpand family info ls ps (etaOpen ds.length f)))) := by
  induction ds generalizing Γ f with
  | nil =>
    exact static_structure_exact_native_structure_eta hΓ hi hp hx hf
      ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hf).2 hadm) RF
  | cons A ds ih =>
    obtain ⟨⟨u, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hf' := hf.weak henv (B := A)
    have hx' : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0))
        (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using HasType.app hf' hx'
    have RB := static_structure_exact_native_app hΓA hf' hx'
      (static_structure_exact_native_weak heq hs hΓ hA hf RF)
    have RB' : ¬ IsProof (A :: Γ) (.app f.lift (.bvar 0)) →
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
          (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
          (proofErase (A :: Γ) (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps))) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using RB
    exact (static_structure_exact_native_eta hΓ hf RF).trans
      (proofErase_scoped_compute_lam_eq hΓ hA
        (structure_eta_telescope_defeq hΓA hi hp hx hadm hb) (ih hΓA hb RB'))

/-- A fresh generic function supplies every guard for structure eta below its
entire declared telescope. The output is typed before any actual function is
substituted, so this construction does not demand native coverage of that value. -/
theorem static_structure_generic_structure_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hT : env.HasType univs Γ (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)) (.sort u)) :
    let T := VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)
    let g := VExpr.wrapLams (EtaTelescope.liftDomains ds 0)
      (structExpand family info ls (ps.map (·.liftN 1 ds.length)) (etaOpen ds.length (.bvar 0)))
    env.HasType univs (T :: Γ) g T.lift ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) (.bvar 0)) (proofErase (T :: Γ) g) := by
  dsimp only
  have hΓT : OnCtx (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ)
      (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg : env.HasType univs (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps) :: Γ)
      (.bvar 0) (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)).lift := .bvar .zero
  have ET : (VExpr.wrapForalls ds (VExpr.mkApps (.const family ls) ps)).lift =
      VExpr.wrapForalls (EtaTelescope.liftDomains ds 0)
        (VExpr.mkApps (.const family ls) (ps.map (·.liftN 1 ds.length))) := by
    simp only [VExpr.lift, EtaTelescope.wrapForalls_lift, Nat.zero_add,
      VExpr.liftN_mkApps, VExpr.liftN]
  have hg' := hg
  rw [ET] at hg'
  have hp' : (ps.map (·.liftN 1 ds.length)).length = info.nparams := by
    simpa only [List.length_map] using hp
  have HE := structure_eta_telescope_defeq hΓT hi hp' hx hadm hg'
  have R := static_structure_native_structure_eta_telescope heq hs hΓT hi hp' hx hadm hg'
    (fun hn => by
      have R := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
        hΓT .zero hn ScopedCompute.refl
      rw [ET] at R
      exact R)
  rw [← ET] at HE
  simpa only [EtaTelescope.liftDomains_length] using And.intro HE.hasType.2 R

end Lean4Lean.VEnv.Strengthening
