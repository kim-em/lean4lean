import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaUnitNativeBoundary

/-! # Complete continuations of unit values and unit-indexed types

A unit variable may either survive or expand to its constructor. A neutral
family applied to it has the corresponding two beta readouts. Lookup supplies
the final structural step, so all continuations reach the same type without a
native recovery premise on any intermediate value or a type-fork assumption.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom ControlType ControlTyping Demand Sets)
open PureObservation (Ob)
variable [Params] [Atom]

/-- Every complete computation of an atomic unit variable beta-reads either
that variable or the empty constructor, including all structure-eta stages. -/
theorem unit_variable_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.bvar i) .atom)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.bvar i) out) :
    BetaRed out (.bvar i) ∨ BetaRed out (.const info.ctorName []) := by
  let S : Sets := fun j t o => j = i ∧ t = .atom ∧ o = .pi
  let P : ControlType → ProofShape → Prop := fun _ a => a = .bvar i ∨ a = .const info.ctorName []
  have HS : S.Typed Δ := by rintro j t o ⟨rfl, rfl, rfl⟩; exact HT
  have H : Obs info.ctorName Δ S (.bvar i) .atom .pi := .var HT .atom ⟨rfl, rfl, rfl⟩
  have HO := H.static_structure_union heq hs hi hz EA (henv.projectionCtorRigid hi) hD R HS
  have HM := HO.realizes (P := P) (σ := Subst.id) (Or.inr rfl) (by
    rintro j t key ⟨rfl, rfl, rfl⟩
    simp only [Realizes]
    exact ⟨.bvar _, Or.inl rfl, .refl⟩)
  simp only [Realizes, subst_id] at HM
  obtain ⟨a, ha, HB⟩ := HM
  rcases ha with rfl | rfl
  · exact .inl HB
  · exact .inr HB

/-- Free demands for a neutral type family and its unit argument. -/
def FamilySets (f i : Nat) (v : VLevel) : Sets := fun j t o =>
  (j = i ∧ t = .atom ∧ o = .pi) ∨
  (j = f ∧ t = .arrow .atom (.sort v) ∧ o = .app [.pi] .pi)

/-- Atomic readouts and type-family readouts retain different final shapes. -/
def FamilyLeaves (f i : Nat) (c : Name) : ControlType → ProofShape → Prop
  | .atom, a => a = .bvar i ∨ a = .const c []
  | .sort _, a => a = .app (.bvar f) (.bvar i) ∨ a = .app (.bvar f) (.const c [])
  | .arrow _ _, _ => False

/-- The family/argument valuation is ordinarily typed even when their
assigned types are obtained by conversion. -/
theorem family_sets_typed
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom) : (FamilySets f i v).Typed Δ := by
  rintro j t o (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  · exact HX
  · exact HF

/-- An observed type-valued program demanding the family and the unit value
has two possible beta readouts after an arbitrary full-union continuation. -/
theorem unit_family_program_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (H : Obs info.ctorName Δ (FamilySets f i v) source (.sort v) .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out) :
    BetaRed out (.app (.bvar f) (.bvar i)) ∨
      BetaRed out (.app (.bvar f) (.const info.ctorName [])) := by
  have HO := H.static_structure_union heq hs hi hz EA (henv.projectionCtorRigid hi) hD R
    (family_sets_typed HF HX)
  have HM := HO.realizes (P := FamilyLeaves f i info.ctorName) (σ := Subst.id)
    (Or.inr rfl) (by
      rintro j t key (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · simp only [Realizes]
        exact ⟨.bvar _, Or.inl rfl, .refl⟩
      · simp only [Realizes]
        intro a ha
        have HA := ha .pi (by simp)
        simp only [Realizes] at HA
        obtain ⟨a', ha', HB⟩ := HA
        rcases ha' with rfl | rfl
        · exact ⟨_, Or.inl rfl, .app .refl HB⟩
        · exact ⟨_, Or.inr rfl, .app .refl HB⟩)
  simp only [Realizes, subst_id] at HM
  obtain ⟨a, ha, HB⟩ := HM
  rcases ha with rfl | rfl
  · exact .inl HB
  · exact .inr HB

/-- A demanded unit argument stays observable through arbitrary computation
of the entire family application, including function eta and beta wrappers. -/
theorem unit_family_application_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (HT : ControlTyping Δ (.app (.bvar f) (.bvar i)) (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.app (.bvar f) (.bvar i)) out) :
    BetaRed out (.app (.bvar f) (.bvar i)) ∨
      BetaRed out (.app (.bvar f) (.const info.ctorName [])) := by
  apply unit_family_program_readout heq hs hi hz EA hD HF HX (R := R)
  apply Obs.app HT (keys := [.pi])
  · exact .var HF (.fn (by intro key hk; cases List.mem_singleton.1 hk; exact .atom) .sort)
      (.inr ⟨rfl, rfl, rfl⟩)
  · intro key hk
    cases List.mem_singleton.1 hk
    exact .var HX .atom (.inl ⟨rfl, rfl, rfl⟩)

/-- A type-valued beta cut that applies the free family to its demanded unit
input has the same complete readout. Its written binder annotation may differ
from the unit family; ordinary control typing supplies the conversion. -/
theorem unit_family_cut_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort v)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (SD : DomainSort Δ L z)
    (HL : ControlTyping Δ (.lam L (.app ((.bvar f : ProofShape).liftN 1) (.bvar 0)))
      (.arrow .atom (.sort v)))
    (HT : ControlTyping Δ (.app (.lam L (.app ((.bvar f : ProofShape).liftN 1) (.bvar 0))) (.bvar i))
      (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.app (.lam L (.app ((.bvar f : ProofShape).liftN 1) (.bvar 0))) (.bvar i)) out) :
    BetaRed out (.app (.bvar f) (.bvar i)) ∨
      BetaRed out (.app (.bvar f) (.const info.ctorName [])) := by
  have HK : ∀ key ∈ ([.pi] : List Ob), Demand .atom key := by
    intro key hk; cases List.mem_singleton.1 hk; exact .atom
  have OF : Obs info.ctorName Δ (FamilySets f i v) (.bvar f)
      (.arrow .atom (.sort v)) (.app [.pi] .pi) :=
    .var HF (.fn HK .sort) (.inr ⟨rfl, rfl, rfl⟩)
  apply unit_family_program_readout heq hs hi hz EA hD HF HX (R := R)
  apply Obs.app HT (keys := [.pi])
  · apply Obs.lam HL HK
    apply Obs.app HL.lam_parts.1 (OF.lift SD)
    intro key hk
    exact .var HL.lam_parts.2 (HK key hk) ⟨rfl, hk⟩
  · intro key hk
    cases List.mem_singleton.1 hk
    exact .var HX .atom (.inl ⟨rfl, rfl, rfl⟩)

end Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
