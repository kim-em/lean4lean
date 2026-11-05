import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidUnitTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Complete continuations of rigid families with retained unit parameters

A monomorphic rigid family retains its demanded unit argument through the
entire computation union. Beta readout leaves either the original variable or
the unit constructor; one unit step therefore supplies a fixed common output.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidUnitObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom ControlType ControlTyping Demand Sets)
variable [Params] [Atom]

/-- Only the selected unit variable is demanded from the ambient context. -/
def UnitSets (i : Nat) : Sets := fun j t o => j = i ∧ t = .atom ∧ o = .pi

/-- Atomic and type-valued leaves have separate operational readings. -/
def FamilyLeaves (r c : Name) (i : Nat) : ControlType → ProofShape → Prop
  | .atom, a => a = .bvar i ∨ a = .const c []
  | .sort _, a => a = .app (.const r []) (.bvar i) ∨ a = .app (.const r []) (.const c [])
  | .arrow _ _, _ => False

/-- Every full continuation of an observed rigid-family program beta-cleans
to the family at its original unit variable or at the unit constructor. No
native certificate is needed at any intermediate argument or function. -/
theorem program_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HX : ControlTyping Δ (.bvar i) .atom)
    (H : Obs info.ctorName r v Δ (UnitSets i) source (.sort v) .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out) :
    BetaRed out (.app (.const r []) (.bvar i)) ∨
      BetaRed out (.app (.const r []) (.const info.ctorName [])) := by
  have HS : (UnitSets i).Typed Δ := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HX
  have HO := H.static_structure_union heq hs hi hz EA (henv.projectionCtorRigid hi) hD hr hDr R HS
  have HF : Realizes (FamilyLeaves r info.ctorName i) (.const r [])
      (.arrow .atom (.sort v)) (.app [.pi] .pi) := by
    simp only [Realizes]
    intro a ha
    have HA := ha .pi (by simp)
    simp only [Realizes] at HA
    obtain ⟨a', ha', HB⟩ := HA
    rcases ha' with rfl | rfl
    · exact ⟨_, Or.inl rfl, .app .refl HB⟩
    · exact ⟨_, Or.inr rfl, .app .refl HB⟩
  have HM := HO.realizes (P := FamilyLeaves r info.ctorName i) (σ := Subst.id)
    (Or.inr rfl) HF (by
      rintro j t key ⟨rfl, rfl, rfl⟩
      simp only [Realizes]
      exact ⟨_, Or.inl rfl, .refl⟩)
  simp only [Realizes, subst_id] at HM
  obtain ⟨a, ha, HB⟩ := HM
  rcases ha with rfl | rfl
  · exact .inl HB
  · exact .inr HB

/-- A rigid family application starts the required observation using ordinary
typings alone. The constant demands its retained unit argument. -/
theorem application_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HF : ControlTyping Δ (.const r []) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (HT : ControlTyping Δ (.app (.const r []) (.bvar i)) (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.app (.const r []) (.bvar i)) out) :
    BetaRed out (.app (.const r []) (.bvar i)) ∨
      BetaRed out (.app (.const r []) (.const info.ctorName [])) := by
  apply program_readout heq hs hi hz EA hD hr hDr HX (R := R)
  exact .app HT (.rigid HF) (by
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var HX .atom ⟨rfl, rfl, rfl⟩)

/-- A type-valued beta cut that applies the rigid family to its demanded unit
input has the same complete readout. Its written binder annotation may differ
from the unit family; ordinary control typing supplies the conversion. -/
theorem cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (HF : ControlTyping Δ (.const r []) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (SD : DomainSort Δ L z)
    (HL : ControlTyping Δ (.lam L (.app ((.const r [] : ProofShape).liftN 1) (.bvar 0)))
      (.arrow .atom (.sort v)))
    (HT : ControlTyping Δ (.app (.lam L (.app ((.const r [] : ProofShape).liftN 1) (.bvar 0))) (.bvar i))
      (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.app (.lam L (.app ((.const r [] : ProofShape).liftN 1) (.bvar 0))) (.bvar i)) out) :
    BetaRed out (.app (.const r []) (.bvar i)) ∨
      BetaRed out (.app (.const r []) (.const info.ctorName [])) := by
  have HK : ∀ key ∈ ([.pi] : List PureObservation.Ob), Demand .atom key := by
    intro key hk; cases List.mem_singleton.1 hk; exact .atom
  have OF : Obs info.ctorName r v Δ (UnitSets i) (.const r [])
      (.arrow .atom (.sort v)) (.app [.pi] .pi) :=
    .rigid HF
  apply program_readout heq hs hi hz EA hD hr hDr HX (R := R)
  apply Obs.app HT (keys := [.pi])
  · apply Obs.lam HL HK
    apply Obs.app HL.lam_parts.1 (OF.lift SD)
    intro key hk
    exact .var HL.lam_parts.2 (HK key hk) ⟨rfl, hk⟩
  · intro key hk
    cases List.mem_singleton.1 hk
    exact .var HX .atom ⟨rfl, rfl, rfl⟩

end Lean4Lean.VEnv.Strengthening.RigidUnitObservation

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open AtomicControl (ControlType ControlTyping)
variable [Params]

/-- Every complete computation of a rigid family at a looked-up unit value
returns to that family at the unit constructor. The retained parameter may
have arbitrary interleaved computation; no parameter-chain joining is assumed. -/
theorem static_structure_rigid_unit_family_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have ht : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have hFi := HasType.app hF ht
  have EF : proofErase Γ (.const r []) = .const r [] :=
    if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i := if_neg (ControlType.not_isProof (t := .atom) hΓ ht)
  have EFi : proofErase Γ (.app (.const r []) (.bvar i)) = .app (.const r []) (.bvar i) := by
    rw [show proofErase Γ (.app (.const r []) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hFi), EF, EI]
  rw [EFi] at R
  rcases RigidUnitObservation.application_readout heq hs hi hz rfl hD hr hDr
      ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, ht, EI⟩ ⟨Γ, _, hΓ, rfl, hFi, EFi⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans
      (.app .refl (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl))
  · exact .beta HB

/-- Complete continuations of a rigid-family beta cut return to the same
canonical parameter. The written lambda annotation need only be ordinarily
equal to the unit carrier; neither a directed annotation path nor native
recovery of the lambda is assumed. -/
theorem static_structure_rigid_unit_family_cut_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (HL : env.IsDefEq univs Γ L (.const family []) (.sort z))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam L (.app (VExpr.const r []).lift (.bvar 0))) (.bvar i))) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  have hL := HL.hasType.1
  have hΓL : OnCtx (L :: Γ) (env.IsType univs) := ⟨hΓ, z, hL⟩
  have h0 : env.HasType univs (L :: Γ) (.bvar 0) (.const family []) :=
    (HL.weak henv.ordered).defeq (HasType.bvar .zero)
  have hb : env.HasType univs (L :: Γ) (.app (VExpr.const r []).lift (.bvar 0)) (.sort v) :=
    .app (hF.weak henv.ordered) h0
  have hf := HasType.lam hL hb
  have hX : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hl
  have ht : env.HasType univs Γ (.app (.lam L (.app (VExpr.const r []).lift (.bvar 0))) (.bvar i)) (.sort v) :=
    hf.app (HL.symm.defeq hX)
  have hv : v.WF univs := (ControlTyping.of_typed (t := .arrow .atom (.sort v)) hΓ hF).wf.2
  have hfS : env.HasType univs Γ (.lam L (.app (VExpr.const r []).lift (.bvar 0)))
      (.forallE (.const family []) (.sort v)) :=
    (IsDefEq.forallEDF HL (HasType.sort hv)).defeq hf
  have EF : proofErase Γ (.const r []) = .const r [] :=
    if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hF)
  have EI : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (ControlType.not_isProof (t := .atom) hΓ hX)
  have E0 : proofErase (L :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (ControlType.not_isProof (t := .atom) hΓL h0)
  have EFL := proofErase_liftN hΓ hΓL Ctx.LiftN.one hF
  rw [EF] at EFL
  have EB : proofErase (L :: Γ) (.app (VExpr.const r []).lift (.bvar 0)) =
      .app ((.const r [] : ProofShape).liftN 1) (.bvar 0) := by
    rw [show proofErase (L :: Γ) (.app (VExpr.const r []).lift (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓL hb), EFL, E0]
  have ELF : proofErase Γ (.lam L (.app (VExpr.const r []).lift (.bvar 0))) =
      .lam (proofErase Γ L) (.app ((.const r [] : ProofShape).liftN 1) (.bvar 0)) := by
    rw [show proofErase Γ (.lam L (.app (VExpr.const r []).lift (.bvar 0))) = .lam _ _ from
      if_neg (ControlType.not_isProof (t := .arrow .atom (.sort v)) hΓ hfS), EB]
  have ET : proofErase Γ (.app (.lam L (.app (VExpr.const r []).lift (.bvar 0))) (.bvar i)) =
      .app (.lam (proofErase Γ L) (.app ((.const r [] : ProofShape).liftN 1) (.bvar 0))) (.bvar i) := by
    rw [show proofErase Γ (.app (.lam L (.app (VExpr.const r []).lift (.bvar 0))) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), ELF, EI]
  rw [ET] at R
  rcases RigidUnitObservation.cut_readout heq hs hi hz rfl hD hr hDr
      ⟨Γ, _, hΓ, rfl, hF, EF⟩ ⟨Γ, _, hΓ, rfl, hX, EI⟩ ⟨Γ, _, hΓ, rfl, hL, rfl⟩
      ⟨Γ, _, hΓ, rfl, hfS, ELF⟩ ⟨Γ, _, hΓ, rfl, ht, ET⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans
      (.app .refl (static_structure_unit_lookup_compute hi hp hx hz hS hΓ hl))
  · exact .beta HB

/-- Independent complete continuations of the same rigid family at two unit
variables join at its fixed constructor parameter. Different parameter origins
and all subsequent computation are included. -/
theorem static_structure_rigid_unit_family_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar j))) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.const info.ctorName [])) :=
  ⟨static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hli RL,
    static_structure_rigid_unit_family_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hlj RR⟩

/-- Actual registered families supply rigidity, and the full environment core
excludes unfolding both rigid heads. The unit-parameter continuation join
therefore has no separate declaration-exclusion assumptions in this setting. -/
theorem environment_static_structure_registered_unit_family_join
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hR : env.projections r rinfo)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar i))) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const r []) (.bvar j))) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        left (.app (.const r []) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
        right (.app (.const r []) (.const info.ctorName [])) :=
  static_structure_rigid_unit_family_join heq EnvironmentCore.sound hi hp hx hz
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi)) hS (henv.projectionRigid hR)
    (EnvironmentCore.no_rigid (henv.projectionRigid hR)) hΓ hF hli hlj RL RR

end Lean4Lean.VEnv.Strengthening
