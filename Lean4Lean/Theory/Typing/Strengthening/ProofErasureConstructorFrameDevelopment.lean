import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorFrames

/-! # Developments alternating constructor expansion and administrative frames

Frames may be created, evolved and contracted, and a structure expansion may
consume the entire framed major. Stored annotation histories survive argument
computation. The remaining coverage gap is arbitrary evolution of the control
functions themselves, rather than the literal frame changes represented here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Marked administrative frames around a constructor payload. -/
inductive ConstructorFrame where
  | payload (e : ProofShape)
  | constant (inner : ConstructorFrame)
  | identity (annotation : ProofShape) (inner : ConstructorFrame)

/-- The ordinary raw expression represented by a marked frame. -/
def ConstructorFrame.source : ConstructorFrame → ProofShape
  | .payload e => e
  | .constant s => constantExpansion s.source
  | .identity A s => .app (.lam A (.bvar 0)) s.source

variable [Params] {D : PureObservation.Definitions}

/-- Validity stores constructor ancestry at the payload and ordinary argument
typing plus independent annotation ancestry at every identity frame. -/
def ConstructorFrame.Valid (D : PureObservation.Definitions) (Γ : List VExpr)
    (r : Name) (info : VProjectionInfo) (origin : ProofShape) : ConstructorFrame → Prop
  | .payload e => ConstructorFamilyState D Γ r info origin e
  | .constant s => s.Valid D Γ r info origin
  | .identity A s => s.Valid D Γ r info origin ∧ WrapperTypeWitness Γ s.source A ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) origin A

/-- A valid marked frame supplies the unmarked constructor history. -/
theorem ConstructorFrame.Valid.history {s : ConstructorFrame} (H : s.Valid D Γ r info origin) :
    ConstructorFrameHistory D Γ r info origin s.source := by
  induction s with
  | payload => exact .payload H
  | constant _ ih => exact .constant (ih H)
  | identity _ _ ih => exact .identity (ih H.1) H.2.1 H.2.2

/-- Actual constructor rounds and root structure expansions interleave with
creation, annotation computation, recursive argument evolution and contraction
of constant/identity frames. Arbitrary control-function computations are not
claimed to have this representation. -/
inductive ConstructorFrameStep (D : PureObservation.Definitions) (Δ : List ProofShape)
    (info : VProjectionInfo) : ConstructorFrame → ConstructorFrame → Prop where
  | rounds : ConstructorRounds D Δ info a b → ConstructorFrameStep D Δ info (.payload a) (.payload b)
  | expand : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ s.source out →
      ConstructorFrameStep D Δ info s (.payload out)
  | constant_expand : ConstructorFrameStep D Δ info s (.constant s)
  | identity_expand : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ s.source A →
      ConstructorFrameStep D Δ info s (.identity A s)
  | constant_contract : ConstructorFrameStep D Δ info (.constant s) s
  | identity_contract : ConstructorFrameStep D Δ info (.identity A s) s
  | constant_inner : ConstructorFrameStep D Δ info s t →
      ConstructorFrameStep D Δ info (.constant s) (.constant t)
  | identity_inner : ConstructorFrameStep D Δ info s t →
      ConstructorFrameStep D Δ info (.identity A s) (.identity A t)
  | identity_annotation : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ A A' →
      ConstructorFrameStep D Δ info (.identity A s) (.identity A' s)

/-- Every represented step is a genuine full-union computation and preserves
the historical invariant. Native guards are consumed at frame creation or
structure expansion; old guards are not required again after the payload moves. -/
theorem ConstructorFrameStep.simulate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (R : ConstructorFrameStep D (proofEraseCtx Γ) info s t)
    (H : s.Valid D Γ r info origin) :
    t.Valid D Γ r info origin ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source t.source := by
  induction R with
  | rounds R => exact ⟨H.rounds heq hs hΓ hi hp hx HH R, R.compute⟩
  | expand R =>
    exact ⟨H.history.expand heq hs hΓ hi hp hx HH R,
      .base (erased_static_structure_eta_expansion_union_structure R)⟩
  | constant_expand => exact ⟨H, .base ⟨0, .inr (.intro H.history.ne_proof)⟩⟩
  | identity_expand RN =>
    obtain ⟨_, HT⟩ := H.history.witness hΓ
    exact ⟨⟨H, HT.of_native heq hs hΓ RN, H.history.native_origin heq hs hΓ hi hp hx HH RN⟩,
      .base (erased_static_structure_eta_expansion_union_identity (.intro RN))⟩
  | constant_contract => exact ⟨H, .beta (constantExpansion_beta _)⟩
  | @identity_contract A s =>
    refine ⟨H.1, .beta ?_⟩
    simpa only [ConstructorFrame.source, ProofShape.inst, instVar, Nat.lt_irrefl,
      ↓reduceIte, Nat.sub_self, ProofShape.liftN_zero] using
      (BetaRed.beta (A := A) (b := .bvar 0) (a := s.source))
  | constant_inner _ ih =>
    obtain ⟨H', R⟩ := ih H
    exact ⟨H', static_structure_constant_compute heq hs hΓ R⟩
  | identity_inner _ ih =>
    obtain ⟨H', R⟩ := ih H.1
    exact ⟨⟨H', H.2.1.compute_term heq hs hΓ R, H.2.2⟩, .app .refl R⟩
  | identity_annotation R =>
    exact ⟨⟨H.1, H.2.1.compute_type heq hs hΓ R, H.2.2.trans R⟩, .app (.lam R .refl) .refl⟩

/-- Arbitrarily many nested frame changes and constructor expansions retain
one family origin and compose to an actual computation of the whole source. -/
theorem constructor_frame_development
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (R : ReflTransGen (ConstructorFrameStep D (proofEraseCtx Γ) info) s t)
    (H : s.Valid D Γ r info origin) :
    t.Valid D Γ r info origin ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source t.source := by
  induction R with
  | rfl => exact ⟨H, .refl⟩
  | tail _ R ih =>
    obtain ⟨H', RC⟩ := ih
    obtain ⟨H'', RC'⟩ := R.simulate heq hs hΓ hi hp hx HH H'
    exact ⟨H'', RC.trans RC'⟩

/-- Every native type selected from a historical unit-parameter constructor
frame returns to the canonical family, independently of stored annotations. -/
theorem constructor_frame_unit_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : ConstructorFrameHistory D Γ r rinfo
      (proofErase Γ (.app (.const r []) (.bvar i))) source)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) :=
  static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hR) hDr hΓ hF hl (H.native_origin heq hs hΓ hR hrp hrx HH RN)

/-- Independently developed majors, native selections and arbitrary subsequent
type computations join at the canonical unit-family type. Major developments
can repeatedly wrap, evolve, contract and structure-expand entire framed
constructors. Full arbitrary major-continuation coverage remains open. -/
theorem constructor_frame_developments_native_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo) (hrp : rinfo.nparams = 1) (hrx : rinfo.nindices = 0)
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HH : ComputedStructureFamilyHeader D r rinfo [])
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (H : s.Valid D Γ r rinfo (proofErase Γ (.app (.const r []) (.bvar i))))
    (R₁ : ReflTransGen (ConstructorFrameStep D (proofEraseCtx Γ) rinfo) s t₁)
    (R₂ : ReflTransGen (ConstructorFrameStep D (proofEraseCtx Γ) rinfo) s t₂)
    (RN₁ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) t₁.source out₁)
    (RN₂ : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) t₂.source out₂)
    (RC₁ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₁ left)
    (RC₂ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out₂ right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.const info.ctorName [])) := by
  have H₁ := (constructor_frame_development heq hs hΓ hR hrp hrx HH R₁ H).1.history
  have H₂ := (constructor_frame_development heq hs hΓ hR hrp hrx HH R₂ H).1.history
  exact ⟨constructor_frame_unit_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hΓ hF hl H₁ (RN₁.convert RC₁),
    constructor_frame_unit_native_return heq hs hi hp hx hz hD hS hR hrp hrx hDr HH
      hΓ hF hl H₂ (RN₂.convert RC₂)⟩

end Lean4Lean.VEnv.Strengthening
