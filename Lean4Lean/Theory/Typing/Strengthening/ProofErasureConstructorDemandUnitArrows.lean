import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandSemantics

/-! # Higher-order unit-valued inputs for joint constructor demands

A finite simple type over the registered unit supplies both its native type
observation and computational realizability. Function inputs may themselves be
functions of arbitrary finite order. Actual lookup, not arbitrary convertible
assignment, initializes the native certificate.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Finite simple types over one positive registered unit. -/
inductive UnitArrows where
  | unit
  | arrow (domain result : UnitArrows)

/-- The ordinary closed carrier of a simple unit type. -/
def UnitArrows.control (unit : AtomicControl.Atom) : UnitArrows → HeterogeneousControl.ControlType
  | .unit => .atom unit
  | .arrow A B => .arrow (A.control unit) (B.control unit)

/-- A function demands its argument at its complete simple key. -/
def UnitArrows.key (unit : AtomicControl.Atom) : UnitArrows → Key
  | .unit => .unit
  | .arrow A B => .fn (A.control unit) [A.key unit] (B.key unit)

/-- The literal native header uses no ambient variables. -/
def UnitArrows.raw (s : Name) : UnitArrows → ProofShape
  | .unit => .const s []
  | .arrow A B => .forallE (A.raw s) (B.raw s)

variable {unit record : AtomicControl.Atom}

/-- All simple keys have their intended ordinary carriers. -/
theorem UnitArrows.key_control (A : UnitArrows) : (A.key unit).control unit record = A.control unit := by
  induction A with
  | unit => rfl
  | arrow A B _ ih => simp only [key, Key.control, control, ih]

/-- Every argument key matches the function's stored carrier. -/
theorem UnitArrows.key_valid (A : UnitArrows) : (A.key unit).Valid unit record := by
  induction A with
  | unit => simp only [key, Key.Valid]
  | arrow A B ihA ihB =>
    simp only [key, Key.Valid]
    refine ⟨?_, ihB⟩
    intro k hk
    obtain rfl := List.mem_singleton.1 hk
    exact ⟨A.key_control, ihA⟩

/-- Simple unit carriers have no free universe parameters. -/
theorem UnitArrows.wf (A : UnitArrows) : (A.control unit).WF univs := by
  induction A with
  | unit => trivial
  | arrow A B ihA ihB => exact ⟨ihA, ihB⟩

omit [Params] in
/-- Raw simple headers are fixed by every substitution. -/
theorem UnitArrows.raw_subst (A : UnitArrows) : (A.raw s).subst σ = A.raw s := by
  induction A generalizing σ with
  | unit => rfl
  | arrow A B ihA ihB => simp only [raw, ProofShape.subst, ihA, ihB]

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
local notation "U" => unitCarrier hi hS

/-- Erasure preserves the full simple header in every ordinary context. -/
theorem UnitArrows.erase (A : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (A.control U).expr = A.raw s := by
  induction A generalizing Γ with
  | unit => exact if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  | arrow A B ihA ihB =>
    have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
      HeterogeneousControl.ControlType.typed A.wf
    have hB : env.HasType univs ((A.control U).expr :: Γ) (B.control U).expr (.sort (B.control U).level) :=
      HeterogeneousControl.ControlType.typed B.wf
    rw [show proofErase Γ ((UnitArrows.arrow A B).control U).expr =
        .forallE (proofErase Γ (A.control U).expr) (proofErase ((A.control U).expr :: Γ) (B.control U).expr) from
      if_neg (not_isProof_of_sort hΓ (.forallE hA hB))]
    rw [ihA hΓ, ihB (Γ := (A.control U).expr :: Γ) ⟨hΓ, _, hA⟩]
    rfl

/-- The literal simple header observes its own complete native-type key.
No native recovery or computation-preservation assumption is used. -/
theorem UnitArrows.type_observation (A : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs)) :
    Obs U record uc ctor family (proofEraseCtx Γ) S (A.raw s) (.type (A.key U)) := by
  have HE (A : UnitArrows) {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      TypeEquality (proofEraseCtx Γ) (A.raw s) (A.control U) :=
    ⟨Γ, _, hΓ, rfl, HeterogeneousControl.ControlType.typed A.wf, A.erase hi hS hΓ⟩
  induction A generalizing Γ S with
  | unit => exact .unit_type (HE .unit hΓ)
  | arrow A B ihA ihB =>
    have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
      HeterogeneousControl.ControlType.typed A.wf
    have hΓA : OnCtx ((A.control U).expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have HB := ihB (S := Sets.cons [A.key U] S) hΓA
    have EΓ : proofEraseCtx ((A.control U).expr :: Γ) = A.raw s :: proofEraseCtx Γ := by
      simp only [proofEraseCtx, A.erase hi hS hΓ]
    rw [EΓ] at HB
    apply Obs.pi
    · have HT := (HE (.arrow A B) hΓ).typing
      simpa only [key, Key.control, UnitArrows.key_control, control, raw] using HT
    · exact HE A hΓ
    · intro k hk; obtain rfl := List.mem_singleton.1 hk; exact A.key_control
    · intro k hk; obtain rfl := List.mem_singleton.1 hk; exact ihA hΓ
    · exact HB

/-- A native certificate at a simple unit header realizes every input key.
At arrows, native application works for any raw argument; the terminal unit
structure step therefore needs no native completeness hypothesis for arguments. -/
theorem UnitArrows.native_computes (A : UnitArrows)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e (A.raw s)) :
    Computes (ErasedStaticStructureEtaExpansionUnion D) Δ uc ctor family e (A.key U) := by
  induction A generalizing e with
  | unit =>
    have RU : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e (.const uc []) :=
      .intro (ps := []) hi rfl rfl rfl RN
    simp only [key, Computes]
    exact .base (erased_static_structure_eta_expansion_union_structure RU.maskedStructure)
  | arrow A B _ ihB =>
    simp only [key, Computes]
    intro a _
    have RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.app e a) ((B.raw s).inst a) :=
      .app RN
    simp only [ProofShape.inst_eq_subst, B.raw_subst] at RB
    exact ihB RB

/-- Actual lookup initializes the variable's ordinary typing, native type
observation and computational interpretation simultaneously. -/
theorem UnitArrows.lookup (A : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (A.control U).expr) :
    HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (A.control U) ∧
      Obs U record uc ctor family (proofEraseCtx Γ) S (contextOracle (proofEraseCtx Γ) i) (.type (A.key U)) ∧
      Computes (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) uc ctor family (.bvar i) (A.key U) := by
  have hx : env.HasType univs Γ (.bvar i) (A.control U).expr := .bvar hl
  have hn := HeterogeneousControl.ControlType.not_isProof hΓ hx
  have EX : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have E := erasedTypeOracle_valid hΓ hl
  rw [← proofEraseCtx_oracle, A.erase hi hS hΓ] at E
  refine ⟨⟨Γ, _, hΓ, rfl, hx, EX⟩, ?_, ?_⟩
  · exact E ▸ A.type_observation hi hS hΓ
  · exact A.native_computes hi hS (E ▸ ScopedTypeRecovery.bvar)

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
