import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitConstructorTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionHeadExpansion

/-! # Constructor parameter readout through compatible control developments

Constant, native identity and native eta roots may interleave with arbitrary
compatible beta reductions, including reductions inside generated functions.
Native guards use the full union. Structure expansion is not a root of this
restricted language; its missing parameter observation is not assumed here.
-/
namespace Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom}

/-- The ambient observation demands only the selected unit variable. -/
def UnitSets (unit : AtomicControl.Atom) (i : Nat) : Sets :=
  fun j t o => j = i ∧ t = .atom unit ∧ o = .pi

/-- Unit leaves and constructor-result leaves retain different carriers. -/
def ConstructorLeaves (unit record : AtomicControl.Atom) (c r : Name) (i : Nat) :
    HeterogeneousControl.ControlType → ProofShape → Prop
  | .atom carrier, a =>
      (carrier = unit ∧ (a = .bvar i ∨ a = .const c [])) ∨
      (carrier = record ∧ (a = .app (.const r []) (.bvar i) ∨
        a = .app (.const r []) (.const c [])))
  | _, _ => False

/-- Reading a record demand beta-cleans all control frames and retains an
observed unit argument. The two carriers must be distinct; no native type
coverage is used to establish this operational statement. -/
theorem Obs.record_readout (hne : unit ≠ record)
    (H : Obs unit record c r Δ (UnitSets unit i) source (.atom record) .pi) :
    BetaRed source (.app (.const r []) (.bvar i)) ∨
      BetaRed source (.app (.const r []) (.const c [])) := by
  have HF : Realizes (ConstructorLeaves unit record c r i) (.const r [])
      (.arrow (.atom unit) (.atom record)) (.app [.pi] .pi) := by
    simp only [Realizes]
    intro a ha
    have HA := ha .pi (by simp)
    simp only [Realizes, ConstructorLeaves] at HA ⊢
    obtain ⟨a', ha', HB⟩ := HA
    rcases ha' with ⟨_, rfl | rfl⟩ | ⟨he, _⟩
    · exact ⟨_, Or.inr ⟨trivial, Or.inl rfl⟩, .app .refl HB⟩
    · exact ⟨_, Or.inr ⟨trivial, Or.inr rfl⟩, .app .refl HB⟩
    · exact (hne he).elim
  have HM := H.realizes (P := ConstructorLeaves unit record c r i) (σ := Subst.id)
    (Or.inl ⟨rfl, Or.inr rfl⟩) HF (by
      rintro j t key ⟨rfl, rfl, rfl⟩
      simp only [Realizes, ConstructorLeaves]
      exact ⟨_, Or.inl ⟨trivial, Or.inl rfl⟩, .refl⟩)
  simp only [Realizes, subst_id] at HM
  obtain ⟨a, ha, HB⟩ := HM
  rcases ha with ⟨he, _⟩ | ⟨_, rfl | rfl⟩
  · exact (hne he.symm).elim
  · exact .inl HB
  · exact .inr HB

/-- A literal saturated constructor exposes its demanded unit parameter.
This also applies after beta contraction or evolution of its function prefix. -/
theorem Obs.constructor_parameter
    (H : Obs unit record c r Δ S (.app (.const r []) p) (.atom record) .pi) :
    Obs unit record c r Δ S p (.atom unit) .pi := by
  cases H with
  | app _ HF HX =>
    cases HF with
    | rigid => exact HX .pi (by simp)

/-- Actual control roots, whose guards may use all enriched computations. -/
inductive ControlStep (D : PureObservation.Definitions) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | constant : e ≠ .proof → ControlStep D Δ e (constantExpansion e)
  | identity : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e out →
      ControlStep D Δ e out
  | eta : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e out →
      ControlStep D Δ e out

/-- Each root belongs to the actual full computation union. -/
theorem ControlStep.full (R : ControlStep D Δ e out) :
    ErasedStaticStructureEtaExpansionUnion D Δ e out := by
  cases R with
  | constant hn => exact ⟨0, .inr (.intro hn)⟩
  | identity R =>
    cases R with
    | intro RN =>
      obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
        (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
      exact ⟨n+1, .inr (.inr (.inr (.inl (.intro RN))))⟩
  | eta R => exact erased_static_structure_eta_expansion_union_eta R

/-- Restricted roots inherit ordinary descent from their full-union inclusion. -/
theorem ControlStep.descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ControlStep D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  exact erased_static_structure_eta_expansion_union_descent heq hs hΓ hΓ' W ht R.full

/-- Full compatible closure, with beta allowed anywhere in generated controls,
preserves body and argument observations. This extends root-only developments. -/
theorem Obs.control_compute (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ControlStep D) Δ source out)
    (HS : S.Typed Δ) (H : Obs unit record c r Δ S source t o) :
    Obs unit record c r Δ S out t o := by
  apply H.compute (ControlStep.descent heq hs) ?_ R HS
  intro Δ a b S t o R H
  cases R with
  | constant => exact H.constant_expansion
  | identity R => exact H.native_identity (erased_static_structure_eta_expansion_union_descent heq hs) R
  | eta R => exact H.native_eta (erased_static_structure_eta_expansion_union_descent heq hs) R

/-- A constructor applied to its selected unit variable retains an explicit
constructor beta readout after arbitrary compatible control developments.
The result includes function-prefix and argument evolution and all beta
interleavings, but makes no claim about arbitrary structure expansion. -/
theorem application_control_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hne : unit ≠ record)
    (HF : HeterogeneousControl.ControlTyping Δ (.const r []) (.arrow (.atom unit) (.atom record)))
    (HX : HeterogeneousControl.ControlTyping Δ (.bvar i) (.atom unit))
    (HT : HeterogeneousControl.ControlTyping Δ (.app (.const r []) (.bvar i)) (.atom record))
    (R : ScopedCompute (ControlStep D) Δ (.app (.const r []) (.bvar i)) out) :
    BetaRed out (.app (.const r []) (.bvar i)) ∨
      BetaRed out (.app (.const r []) (.const c [])) := by
  have HS : (UnitSets unit i).Typed Δ := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HX
  have H : Obs unit record c r Δ (UnitSets unit i)
      (.app (.const r []) (.bvar i)) (.atom record) .pi :=
    .app HT (.rigid HF) (by
      intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact .var HX .atom ⟨rfl, rfl, rfl⟩)
  exact (H.control_compute heq hs R HS).record_readout hne

end Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
