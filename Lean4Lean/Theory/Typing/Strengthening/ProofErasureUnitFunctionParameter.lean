import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitComputes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerEtaRepair

/-! # Returning a retained function parameter through its caller

Arbitrary computation of a looked-up unit endofunction preserves its demand on
a fresh unit argument. The caller supplies the canonical lambda annotation;
computational readout supplies the body. No native certificate for the computed
function, and no return path for its own annotations, is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An actual native unit guard gives a structural computation to its empty
constructor, without any argument-typing or observation premise. -/
theorem unit_native_compute
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e (.const family [])) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e (.const info.ctorName []) := by
  have RU : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e (.const info.ctorName []) :=
    .intro (ps := []) hi hx hz hp.symm RN
  exact .base (erased_static_structure_eta_expansion_union_structure RU.maskedStructure)

/-- After arbitrary full-union computation of a unit endofunction lookup,
its application to the caller's fresh unit argument returns the unit constructor.
The computed function need not retain native recovery of its original Pi. -/
theorem unit_function_future_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const family []) (.const family [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) p) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (.const family [] :: proofEraseCtx Γ)
      (.app (p.liftN 1) (.bvar 0)) (.const info.ctorName []) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  let V : AtomicControl.Sets := fun j t o => j = i ∧ t = .arrow .atom .atom ∧ o = .app [.pi] .pi
  have hf : env.HasType univs Γ (.bvar i) (.forallE (.const family []) (.const family [])) := .bvar hl
  have EF : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓ hf)
  have HF : AtomicControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.arrow .atom .atom) := ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have HV : V.Typed (proofEraseCtx Γ) := by rintro j t o ⟨rfl, rfl, rfl⟩; exact HF
  have HK : AtomicControl.Demand (.arrow .atom .atom) (.app [.pi] .pi) :=
    .fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .atom) .atom
  have HO : AtomicUnitObservation.Obs info.ctorName (proofEraseCtx Γ) V (.bvar i)
      (.arrow .atom .atom) (.app [.pi] .pi) := .var HF HK ⟨rfl, rfl, rfl⟩
  have H := HO.static_structure_union heq hs hi hz rfl (henv.projectionCtorRigid hi) hD R HV
  have hSΓ : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have ES : proofErase Γ (.const family []) = .const family [] := if_neg (not_isProof_of_sort hΓ hSΓ)
  have SD : DomainSort (proofEraseCtx Γ) (.const family []) (.succ u) := ⟨Γ, _, hΓ, rfl, hSΓ, ES⟩
  have hΓS : OnCtx (VExpr.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have EΓS : proofEraseCtx (VExpr.const family [] :: Γ) = .const family [] :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, ES]
  have HL := H.lift (A := .atom) (keys := [.pi]) SD
  have HC : ∀ j t key, AtomicControl.Sets.cons .atom [.pi] V j t key →
      AtomicUnitObservation.Computes (ErasedStaticStructureEtaExpansionUnion D)
        (.const family [] :: proofEraseCtx Γ) info.ctorName (Subst.id j) t key := by
    intro j t key hj
    cases j with
    | zero =>
      obtain ⟨rfl, hk⟩ := hj
      obtain rfl := List.mem_singleton.1 hk
      simp only [AtomicUnitObservation.Computes]
      exact unit_native_compute hi hp hx hz ScopedTypeRecovery.bvar
    | succ j =>
      obtain ⟨rfl, rfl, rfl⟩ := hj
      simp only [AtomicUnitObservation.Computes]
      intro a _
      have hl' : Lookup (VExpr.const family [] :: Γ) (j+1) (.forallE (.const family []) (.const family [])) := .succ hl
      have hn := AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓS (HasType.bvar hl')
      have RN := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D) hΓS hl' hn .refl
      have hSA : env.HasType univs (VExpr.const family [] :: Γ) (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
      have hSAA : env.HasType univs (VExpr.const family [] :: VExpr.const family [] :: Γ)
          (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
      have EP : proofErase (VExpr.const family [] :: Γ) (.forallE (.const family []) (.const family [])) =
          .forallE (.const family []) (.const family []) := by
        rw [show proofErase _ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓS (.forallE hSA hSAA))]
        rw [show proofErase _ (.const family []) = .const family [] from if_neg (not_isProof_of_sort hΓS hSA)]
        rw [show proofErase (VExpr.const family [] :: VExpr.const family [] :: Γ) (.const family []) = .const family [] from
          if_neg (not_isProof_of_sort (Γ := VExpr.const family [] :: VExpr.const family [] :: Γ) ⟨hΓS, _, hSA⟩ hSAA)]
      rw [show proofErase _ (.bvar (j+1)) = .bvar (j+1) from if_neg hn, EP, EΓS] at RN
      exact unit_native_compute hi hp hx hz (ScopedTypeRecovery.app RN)
  have HR := HL.computes HC
  simp only [ProofShape.subst_id, AtomicUnitObservation.Computes] at HR
  exact HR (.bvar 0) (by
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    simp only [AtomicUnitObservation.Computes]
    exact unit_native_compute hi hp hx hz ScopedTypeRecovery.bvar)

/-- The caller retains and canonicalizes a computed FUNCTION parameter.
Only the caller recovers the selected Pi. Its native result may be dependent;
the argument's possibly changed lambda annotations need no computational join. -/
theorem unit_function_parameter_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const family []) (.const family [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) p)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) caller
      (.forallE (.forallE (.const family []) (.const family [])) C)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app caller p)
      (.app caller (.lam (.const family []) (.const info.ctorName []))) := by
  have hSΓ : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have hSS : env.HasType univs (VExpr.const family [] :: Γ) (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hQ := HasType.forallE hSΓ hSS
  have EQ : proofErase Γ (.forallE (.const family []) (.const family [])) = .forallE (.const family []) (.const family []) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ)]
    rw [show proofErase Γ (.const family []) = .const family [] from if_neg (not_isProof_of_sort hΓ hSΓ),
      show proofErase (VExpr.const family [] :: Γ) (.const family []) = .const family [] from if_neg (not_isProof_of_sort hΓS hSS)]
  have SQ : DomainSort (proofEraseCtx Γ) (.forallE (.const family []) (.const family [])) (.imax (.succ u) (.succ u)) :=
    ⟨Γ, _, hΓ, rfl, hQ, EQ⟩
  have hΓQ : OnCtx (VExpr.forallE (.const family []) (.const family []) :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hSQ : env.HasType univs (VExpr.forallE (.const family []) (.const family []) :: Γ) (.const family []) (.sort (.succ u)) :=
    hS.weak0 henv.ordered
  have SA : DomainSort (.forallE (.const family []) (.const family []) :: proofEraseCtx Γ)
      ((ProofShape.const family []).liftN 1) (.succ u) :=
    ⟨_, _, hΓQ, by simp only [proofEraseCtx, EQ], hSQ, if_neg (not_isProof_of_sort hΓQ hSQ)⟩
  have hpos : ¬ VLevel.imax (.succ u) (.succ u) ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval, Lean.Nat.imax] at E
  have hpos' : ¬ VLevel.succ u ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval] at E
  exact (static_structure_caller_argument_eta RN SQ hpos SA hpos').trans
    (.app .refl (.lam .refl (unit_function_future_body heq hs hi hp hx hz hD hS hΓ hl R)))

/-- Two independently computed unit endofunctions join inside one caller.
The two original lookups may differ; their computational common output is a
literal function, not merely a pointwise equality of application results. -/
theorem unit_function_parameter_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.forallE (.const family []) (.const family [])))
    (hlj : Lookup Γ j (.forallE (.const family []) (.const family [])))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) p)
    (RQ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar j) q)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) caller
      (.forallE (.forallE (.const family []) (.const family [])) C)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app caller p)
        (.app caller (.lam (.const family []) (.const info.ctorName []))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app caller q)
        (.app caller (.lam (.const family []) (.const info.ctorName []))) :=
  ⟨unit_function_parameter_return heq hs hi hp hx hz hD hS hΓ hli RP RN,
    unit_function_parameter_return heq hs hi hp hx hz hD hS hΓ hlj RQ RN⟩

/-- A type-family lookup supplies the caller certificate directly. Its
retained argument is an arbitrarily computed unit endofunction. No observed
header, selected-domain certificate or native recovery of that argument is a
premise. The family head is fixed; arbitrary whole-family continuations remain
outside this theorem. -/
theorem unit_function_family_lookup_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hv : v.WF univs)
    (hl : Lookup Γ i (.forallE (.const family []) (.const family [])))
    (hlF : Lookup Γ f (.forallE (.forallE (.const family []) (.const family [])) (.sort v)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) p) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app (.bvar f) p)
      (.app (.bvar f) (.lam (.const family []) (.const info.ctorName []))) := by
  have hSΓ : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have hSS : env.HasType univs (VExpr.const family [] :: Γ) (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hQ := HasType.forallE hSΓ hSS
  have hΓQ : OnCtx (VExpr.forallE (.const family []) (.const family []) :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hV : env.HasType univs (VExpr.forallE (.const family []) (.const family []) :: Γ) (.sort v) (.sort (.succ v)) := .sort hv
  have hFT := HasType.forallE hQ hV
  have EQ : proofErase Γ (.forallE (.const family []) (.const family [])) = .forallE (.const family []) (.const family []) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ)]
    rw [show proofErase Γ (.const family []) = .const family [] from if_neg (not_isProof_of_sort hΓ hSΓ),
      show proofErase (VExpr.const family [] :: Γ) (.const family []) = .const family [] from if_neg (not_isProof_of_sort hΓS hSS)]
  have EFT : proofErase Γ (.forallE (.forallE (.const family []) (.const family [])) (.sort v)) =
      .forallE (.forallE (.const family []) (.const family [])) (.sort v) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hFT), EQ]
    exact congrArg (ProofShape.forallE _) (if_neg (not_isProof_of_sort hΓQ hV))
  have hf : env.HasType univs Γ (.bvar f) (.forallE (.forallE (.const family []) (.const family [])) (.sort v)) := .bvar hlF
  have hn := not_isProof_function_to_sort hΓ hf
  have RN := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hlF hn .refl
  rw [show proofErase Γ (.bvar f) = .bvar f from if_neg hn, EFT] at RN
  exact unit_function_parameter_return heq hs hi hp hx hz hD hS hΓ hl R RN

end Lean4Lean.VEnv.Strengthening
