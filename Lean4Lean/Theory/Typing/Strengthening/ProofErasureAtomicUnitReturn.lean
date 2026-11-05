import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitReadout

/-! # Structural return paths for demanded unit data

Every computation of a unit-indexed neutral type reaches the family applied
to the unit constructor. Source lookup alone supplies the structural guard;
intermediate values need no native completeness or joining assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open AtomicControl (ControlType ControlTyping)
variable [Params]

/-- Lookup at an empty registered positive family supplies the final unit
step used after operational readout. No native hypothesis is assumed. -/
theorem static_structure_unit_lookup_compute
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const family [])) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (.const info.ctorName []) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have ht : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have hn := ControlType.not_isProof (t := .atom) hΓ ht
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hl hn .refl
  have ES : proofErase Γ (.const family []) = .const family [] :=
    if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn, ES] at RN
  have RU : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (.const info.ctorName []) := .intro (ps := []) hi hx hz hp.symm RN
  exact .base (erased_static_structure_eta_expansion_union_structure RU.maskedStructure)

/-- Arbitrary complete computations from a looked-up unit inhabitant reach
its fixed constructor. This allows full structure eta, not only function eta. -/
theorem static_structure_unit_variable_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const family []))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.const info.ctorName []) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have ht : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have EI : proofErase Γ (.bvar i) = .bvar i := if_neg (ControlType.not_isProof (t := .atom) hΓ ht)
  rw [EI] at R
  rcases AtomicUnitObservation.unit_variable_readout heq hs hi hz rfl hD
      ⟨Γ, _, hΓ, rfl, ht, EI⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl)
  · exact .beta HB

/-- Every computation of a type family applied to a looked-up unit value
reaches the family applied to its constructor. All computation interleavings
are allowed, including continuations after the first structure expansion. -/
theorem static_structure_unit_family_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar i))) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.bvar f) (.const info.ctorName [])) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have ht : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have hFi : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort v) := .app hF ht
  have EF : proofErase Γ (.bvar f) = .bvar f :=
    if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i := if_neg (ControlType.not_isProof (t := .atom) hΓ ht)
  have EFi : proofErase Γ (.app (.bvar f) (.bvar i)) = .app (.bvar f) (.bvar i) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hFi), EF, EI]
  rw [EFi] at R
  rcases AtomicUnitObservation.unit_family_application_readout heq hs hi hz rfl hD
      ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, ht, EI⟩ ⟨Γ, _, hΓ, rfl, hFi, EFi⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans
      (.app .refl (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl))
  · exact .beta HB

/-- A type-valued beta cut demanding a unit argument reaches the same
canonical family application after every continuation. The written annotation
need only be definitionally equal to the family; no directed annotation path
or native certificate for the lambda is required. -/
theorem static_structure_unit_family_cut_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (HL : env.IsDefEq univs Γ L (.const family []) (.sort z))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) (.bvar i))) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.bvar f) (.const info.ctorName [])) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have hL := HL.hasType.1
  have hΓL : OnCtx (L :: Γ) (env.IsType univs) := ⟨hΓ, z, hL⟩
  have h0 : env.HasType univs (L :: Γ) (.bvar 0) (.const family []) :=
    (HL.weak henv.ordered).defeq (HasType.bvar .zero)
  have hb : env.HasType univs (L :: Γ) (.app (VExpr.bvar f).lift (.bvar 0)) (.sort v) :=
    .app (hF.weak henv.ordered) h0
  have hf := HasType.lam hL hb
  have hX : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have ht : env.HasType univs Γ (.app (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) (.bvar i)) (.sort v) :=
    hf.app (HL.symm.defeq hX)
  have hv : v.WF univs := (ControlTyping.of_typed (t := .arrow .atom (.sort v)) hΓ hF).wf.2
  have hfS : env.HasType univs Γ (.lam L (.app (VExpr.bvar f).lift (.bvar 0)))
      (.forallE (.const family []) (.sort v)) :=
    (IsDefEq.forallEDF HL (HasType.sort hv)).defeq hf
  have EF : proofErase Γ (.bvar f) = .bvar f :=
    if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (ControlType.not_isProof (t := .atom) hΓ hX)
  have E0 : proofErase (L :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (ControlType.not_isProof (t := .atom) hΓL h0)
  have EFL := proofErase_liftN hΓ hΓL Ctx.LiftN.one hF
  rw [EF] at EFL
  have EB : proofErase (L :: Γ) (.app (VExpr.bvar f).lift (.bvar 0)) =
      .app ((.bvar f : ProofShape).liftN 1) (.bvar 0) := by
    rw [show proofErase (L :: Γ) (.app (VExpr.bvar f).lift (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓL hb), EFL, E0]
  have ELF : proofErase Γ (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) =
      .lam (proofErase Γ L) (.app ((.bvar f : ProofShape).liftN 1) (.bvar 0)) := by
    rw [show proofErase Γ (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) = .lam _ _ from
      if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hfS), EB]
  have ET : proofErase Γ (.app (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) (.bvar i)) =
      .app (.lam (proofErase Γ L) (.app ((.bvar f : ProofShape).liftN 1) (.bvar 0))) (.bvar i) := by
    rw [show proofErase Γ (.app (.lam L (.app (VExpr.bvar f).lift (.bvar 0))) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), ELF, EI]
  rw [ET] at R
  rcases AtomicUnitObservation.unit_family_cut_readout heq hs hi hz rfl hD
      ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, hX, EI⟩ ⟨Γ, _, hΓ, rfl, hL, rfl⟩
      ⟨Γ, _, hΓ, rfl, hfS, ELF⟩ ⟨Γ, _, hΓ, rfl, ht, ET⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans
      (.app .refl (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl))
  · exact .beta HB

/-- Computations of equal unit-indexed types, even with distinct original
unit variables, join at the same explicit type. Both histories are arbitrary. -/
theorem static_structure_unit_family_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort v)))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RI : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar i))) left)
    (RJ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar j))) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.bvar f) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.bvar f) (.const info.ctorName [])) :=
  ⟨static_structure_unit_family_return heq hs hi hp hx hz hD hS hΓ hF hli RI,
    static_structure_unit_family_return heq hs hi hp hx hz hD hS hΓ hF hlj RJ⟩

/-- The actual environment computation system supplies constructor rigidity
automatically; no declaration exclusion remains as a user premise. -/
theorem environment_static_structure_unit_family_join
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort v)))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RI : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar i))) left)
    (RJ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar j))) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        left (.app (.bvar f) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        right (.app (.bvar f) (.const info.ctorName [])) :=
  static_structure_unit_family_join heq EnvironmentCore.sound hi hp hx hz
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi)) hS hΓ hF hli hlj RI RJ

end Lean4Lean.VEnv.Strengthening
