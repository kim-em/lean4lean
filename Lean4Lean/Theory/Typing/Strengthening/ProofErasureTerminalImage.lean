import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSubstitution
import Lean4Lean.Theory.Typing.ProjectionIndexBound
import Lean4Lean.Theory.Typing.Strengthening.StructureProofField

/-! # Typed terminal images for recovery transport

Types and rigid data without projections cannot be functions or valid projection
majors. Fieldless structures have no valid projection index; structures with
only proof fields have no retained projection. Recovery transport can stop at
these images without recovering their assigned type syntactically.
No termination, canonical-form, or native-recovery premise is imposed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A closed all-proof-fields certificate supplies its individual field certificate.
The registered constructor fixes the finite telescope and its length. -/
theorem StructureReplay.ProofFields.field
    (H : StructureReplay.ProofFields env univs info ls)
    (hi : env.projections family info) (hj : i < info.numFields) :
    StructureReplay.ProofField env univs info ls i := by
  obtain ⟨decl, family', ctor, _, _, _, _, _, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := hraw.forallArity
  have hlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hs : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  exact ⟨doms, result, by omega, hs, hlen, H doms result hs hlen _ (by omega) (by omega)⟩

/-- Every projection of an all-proof-field unindexed structure is a proof.
Reconstruction supplies the typed expansion; no expansion typing is assumed. -/
theorem StructureReplay.ProofFields.projection
    (H : StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (hj : i < info.numFields) : IsProof Γ (.proj family i m) :=
  (H.field hi hj).projection hΓ hi hp
    (StructureReplay.structure_constructor_proofFields henv hΓ hi hp hx H hm)

/-- Typed images which cannot occur at a retained elimination position inspected
by native recovery. Fieldless structures have no valid index; proof-only
structures have no non-proof projection. -/
inductive TerminalImage (Γ : List VExpr) (e : VExpr) : Prop
  | type : env.HasType univs Γ e (.sort u) → TerminalImage Γ e
  | data : env.HasType univs Γ e (VExpr.mkApps (.const c ls) args) →
      env.Rigid c → (∀ info, ¬ env.projections c info) → TerminalImage Γ e
  | fieldless : env.HasType univs Γ e (VExpr.mkApps (.const c ls) args) →
      env.projections c info → info.numFields = 0 → TerminalImage Γ e
  | proofStructure : env.HasType univs Γ e (VExpr.mkApps (.const c ls) ps) →
      env.projections c info → ps.length = info.nparams → info.nindices = 0 →
      StructureReplay.ProofFields env univs info ls → TerminalImage Γ e

/-- Actual typed substitution preserves a terminal image. -/
theorem TerminalImage.subst (H : TerminalImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    TerminalImage Γ₀ (e.subst σ) := by
  cases H with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | data h hr hn =>
    have hh := h.subst henv.orderedStrong W hΓ₀
    simp only [VExpr.subst_mkApps, VExpr.subst_const] at hh
    exact .data hh hr hn
  | fieldless h hi hz =>
    have hh := h.subst henv.orderedStrong W hΓ₀
    simp only [VExpr.subst_mkApps, VExpr.subst_const] at hh
    exact .fieldless hh hi hz
  | proofStructure h hi hp hx HF =>
    have hh := h.subst henv.orderedStrong W hΓ₀
    simp only [VExpr.subst_mkApps, VExpr.subst_const] at hh
    exact .proofStructure hh hi (by simpa only [List.length_map] using hp) hx HF

/-- Replaying a source computation backwards retains terminal-image typing. -/
theorem TerminalImage.back (H : TerminalImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    TerminalImage Γ e := by
  cases H with
  | type h => exact .type (HE.toU.of_r henv hΓ h).hasType.1
  | data h hr hn => exact .data (HE.toU.of_r henv hΓ h).hasType.1 hr hn
  | fieldless h hi hz => exact .fieldless (HE.toU.of_r henv hΓ h).hasType.1 hi hz
  | proofStructure h hi hp hx HF => exact .proofStructure (HE.toU.of_r henv hΓ h).hasType.1 hi hp hx HF

/-- A terminal image cannot have a Pi type, even by conversion. -/
theorem TerminalImage.not_function (H : TerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  cases H with
  | type h => exact (h.uniqU henv hΓ hf).sort_forallE_inv henv hΓ
  | data h hr _ =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ hr
      ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)
  | fieldless h hi _ | proofStructure h hi _ _ _ =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)

/-- Any typed projection of a terminal image is a proof. Owner injectivity and
metadata uniqueness align a competing projection typing with the terminal
certificate; proof-field reconstruction uses the original universe instance. -/
theorem TerminalImage.projection_isProof (H : TerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T) : IsProof Γ (.proj s i e) := by
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  have hb := ht.proj_index_lt henv hΓ hi
  cases H with
  | type h =>
    exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ
        (HasType.sort (h.isType henv hΓ |>.choose_spec.sort_inv henv)))).elim
  | data h hr hn =>
    obtain ⟨_, hC⟩ := h.isType henv hΓ
    obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ hr (henv.projectionRigid hi)
      ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
    subst E
    exact (hn _ hi).elim
  | fieldless h hi₀ hz =>
    obtain ⟨_, hC⟩ := h.isType henv hΓ
    obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
      (henv.projectionRigid hi₀) (henv.projectionRigid hi)
      ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
    subst E
    cases henv.ordered.projections_unique hi₀ hi
    omega
  | proofStructure h hi₀ hp hx HF =>
    obtain ⟨_, hC⟩ := h.isType henv hΓ
    obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
      (henv.projectionRigid hi₀) (henv.projectionRigid hi)
      ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
    subst E
    cases henv.ordered.projections_unique hi₀ hi
    exact HF.projection hΓ hi₀ hp hx h hb

/-- A terminal image cannot be the major of a retained typed projection. -/
theorem TerminalImage.not_projection (H : TerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : False :=
  hn (H.projection_isProof hΓ ht)

end Lean4Lean.VEnv.Strengthening
