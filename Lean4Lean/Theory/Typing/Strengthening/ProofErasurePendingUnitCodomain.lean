import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidUnitReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Supplying pending unit arguments after dependent type computation

A constructor function's codomain can mention its fresh parameter. Keep its
computation in that parameter context, then realize application by a beta cut.
The existing rigid-family cut observer covers the codomain path, the independent
argument path, beta substitution, and every subsequent type continuation.
No lower-history demand is imposed before the argument has been supplied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open AtomicControl (ControlType ControlTyping)
variable [Params] {D : PureObservation.Definitions}

/-- Computing a dependent family body before supplying a computed unit argument
preserves canonical return through every later continuation. Both input paths
are actual full-union computations; the argument needs no native certificate. -/
theorem pending_unit_codomain_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (.const family [] :: Γ))
      (proofErase (.const family [] :: Γ) (.app (.const r []) (.bvar 0))) Y)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) a)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (Y.inst a) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have hA : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓA : OnCtx (.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have h0 : env.HasType univs (.const family [] :: Γ) (.bvar 0) (.const family []) := .bvar .zero
  have hb : env.HasType univs (.const family [] :: Γ)
      (.app (.const r []) (.bvar 0)) (.sort v) := .app (hF.weak henv.ordered) h0
  have hf := HasType.lam hA hb
  have ht : env.HasType univs Γ
      (.app (.lam (.const family []) (.app (.const r []) (.bvar 0))) (.bvar i)) (.sort v) :=
    hf.app (HasType.bvar hl)
  have EL : proofErase Γ (.lam (.const family []) (.app (.const r []) (.bvar 0))) =
      .lam (proofErase Γ (.const family []))
        (proofErase (.const family [] :: Γ) (.app (.const r []) (.bvar 0))) :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hf)
  have ET : proofErase Γ
      (.app (.lam (.const family []) (.app (.const r []) (.bvar 0))) (.bvar i)) =
      .app (.lam (proofErase Γ (.const family []))
        (proofErase (.const family [] :: Γ) (.app (.const r []) (.bvar 0))))
        (proofErase Γ (.bvar i)) := by
    rw [show proofErase Γ (.app (.lam (.const family []) (.app (.const r []) (.bvar 0))) (.bvar i)) =
      .app _ _ from if_neg (not_isProof_of_sort hΓ ht), EL]
  apply static_structure_rigid_unit_family_cut_return heq hs hi hp hx hz hD hS hr hDr
    hΓ hF hl hA
  change ScopedCompute _ _
    (proofErase Γ (.app (.lam (.const family []) (.app (.const r []) (.bvar 0))) (.bvar i))) out
  rw [ET]
  exact (ScopedCompute.app (.lam .refl RB) RX).trans ((ScopedCompute.beta .beta).trans RC)

/-- Arbitrary computation of the whole dependent Pi may change its domain,
codomain, and control wrappers. Once a literal Pi is exposed, a pending argument
computed from a unit lookup can be supplied, with unrestricted later computation.
The codomain need not be a lift from below its parameter binder. -/
theorem pending_unit_pi_result_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0)))) (.forallE X Y))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) a)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (Y.inst a) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have hA : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓA : OnCtx (.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hb : env.HasType univs (.const family [] :: Γ)
      (.app (.const r []) (.bvar 0)) (.sort v) :=
    .app (hF.weak henv.ordered) (HasType.bvar .zero)
  have EP : proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0))) =
      .forallE (proofErase Γ (.const family []))
        (proofErase (.const family [] :: Γ) (.app (.const r []) (.bvar 0))) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hb))
  rw [EP] at RP
  obtain ⟨_, _, _, _, _, _, _, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hb RP
  exact pending_unit_codomain_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hl RB RX RC

end Lean4Lean.VEnv.Strengthening
