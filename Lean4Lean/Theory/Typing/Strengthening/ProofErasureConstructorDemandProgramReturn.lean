import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandUnitArrows

/-! # Full native return with higher-order free unit functions

Actual simple-type lookups supply all three valuations needed by the joint
observer: ordinary typing, observed native headers, and computational demands.
This permits programs to call functions of arbitrary finite order, without
assuming those functions or their supplied arguments beta-normalize.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.const s []) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hTag hF

/-- Every actual simple unit lookup is an available free demand. The context
may also contain arbitrary other entries, which this valuation does not demand. -/
def UnitInputs (Γ : List VExpr) : Sets := fun i key =>
  ∃ A : UnitArrows, Lookup Γ i (A.control U).expr ∧ key = A.key U

/-- Actual lookups initialize typing, native annotations and computational
semantics, including higher-order free variables. None is an external premise. -/
theorem unit_inputs (hΓ : OnCtx Γ (env.IsType univs)) :
    (UnitInputs hi hS Γ).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT uc c t (proofEraseCtx Γ) (UnitInputs hi hS Γ) ∧
      (∀ i key, UnitInputs hi hS Γ i key →
        Computes (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) uc c t (.bvar i) key) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro i key ⟨A, hl, rfl⟩
    rw [A.key_control]
    exact (A.lookup hi hS (D := D) (record := RT) (ctor := c) (family := t)
      (S := UnitInputs hi hS Γ) hΓ hl).1
  · rintro i key ⟨A, hl, rfl⟩
    exact (A.lookup hi hS (D := D) (record := RT) (ctor := c) (family := t)
      (S := UnitInputs hi hS Γ) hΓ hl).2.1
  · rintro i key ⟨A, hl, rfl⟩
    exact (A.lookup hi hS (D := D) (record := RT) (ctor := c) (family := t)
      (S := UnitInputs hi hS Γ) hΓ hl).2.2

/-- Every continuation of an observed program realizes its result key, with
all free simple-unit functions initialized by actual lookup. This uses full
computation preservation before the semantic readout, not after it. -/
theorem program_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : Obs U RT uc c t (proofEraseCtx Γ) (UnitInputs hi hS Γ) source key)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source out) :
    Computes (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) uc c t out key := by
  obtain ⟨HS, HV, HC⟩ := unit_inputs hi hS hTag hF (D := D) hΓ
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV R
  have HR := HE.computes (σ := Subst.id) HC
  simpa only [ProofShape.subst_id] using HR

/-- Arbitrary whole-program computation, native recovery and later type
computation preserve the result-type demand. For a record result this is an
explicit path to Tag unitCtor, even with higher-order free inputs. -/
theorem program_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : Obs U RT uc c t (proofEraseCtx Γ) (UnitInputs hi hS Γ) source key)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) A out) :
    Computes (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) uc c t out (.type key) := by
  obtain ⟨HS, HV, HC⟩ := unit_inputs hi hS hTag hF (D := D) hΓ
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS hTag hF heq hs huc hc hf HS HV RN
  have HR := (HN.full_compute hi hS hTag hF heq hs huc hc hf HS HV RA).computes (σ := Subst.id) HC
  simpa only [ProofShape.subst_id] using HR

/-- A demanded unit program can be supplied to the registered constructor.
The ordinary constructor arrow is derived from the actual declarations. -/
theorem Obs.construct
    (H : Obs U RT uc c t Δ S e .unit) : Obs U RT uc c t Δ S (.app (.const c []) e) .record := by
  obtain ⟨Γ, x, hΓ, EΓ, hx, EX⟩ := H.typing
  have hctor := (registered_unit_constructor_simple_arrow hi hS hTag hF).weak0 (Γ := Γ) henv.ordered
  have he : env.HasType univs Γ (.app (.const c []) x) (HeterogeneousControl.ControlType.atom RT).expr :=
    .app hctor hx
  have EC : proofErase Γ (.const c []) = .const c [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof (t := .arrow (.atom U) (.atom RT)) hΓ hctor)
  have EE : proofErase Γ (.app (.const c []) x) = .app (.const c []) e := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EC, EX]
  refine .app ⟨Γ, _, hΓ, EΓ, he, EE⟩ (.record_ctor ⟨Γ, _, hΓ, EΓ, hctor, EC⟩) ?_
  intro key hk
  obtain rfl := List.mem_singleton.1 hk
  exact H

/-- Calling a free simple-unit function on a free input starts an observation
from lookups alone. The input may have arbitrarily high finite function order. -/
theorem unit_call_observation (A : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs))
    (hlf : Lookup Γ f ((UnitArrows.arrow A .unit).control U).expr)
    (hlx : Lookup Γ x (A.control U).expr) :
    Obs U RT uc c t (proofEraseCtx Γ) (UnitInputs hi hS Γ)
      (.app (.const c []) (.app (.bvar f) (.bvar x))) .record := by
  have hf : env.HasType univs Γ (.bvar f) ((UnitArrows.arrow A .unit).control U).expr := .bvar hlf
  have hx : env.HasType univs Γ (.bvar x) (A.control U).expr := .bvar hlx
  have he : env.HasType univs Γ (.app (.bvar f) (.bvar x)) (HeterogeneousControl.ControlType.atom U).expr := .app hf hx
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have EX : proofErase Γ (.bvar x) = .bvar x := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hx)
  have EE : proofErase Γ (.app (.bvar f) (.bvar x)) = .app (.bvar f) (.bvar x) := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EF, EX]
  apply Obs.construct hi hS hTag hF
  refine .app ⟨Γ, _, hΓ, rfl, he, EE⟩ (domain := A.control U) (keys := [A.key U]) ?_ ?_
  · apply Obs.var (key := (UnitArrows.arrow A .unit).key U)
    · rw [UnitArrows.key_control]; exact ⟨Γ, _, hΓ, rfl, hf, EF⟩
    · exact UnitArrows.key_valid _
    · exact ⟨_, hlf, rfl⟩
  · intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var (A.key_control ▸ ⟨Γ, _, hΓ, rfl, hx, EX⟩) A.key_valid ⟨A, hlx, rfl⟩

include hi hS hTag hF in
/-- A concrete constructor call at a higher-order free input has full native
return with no observation or valuation premise. The input's order is unbounded;
all three histories range over the complete enriched union. -/
theorem unit_call_native_return (A : UnitArrows)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hlf : Lookup Γ f ((UnitArrows.arrow A .unit).control U).expr)
    (hlx : Lookup Γ x (A.control U).expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.app (.bvar f) (.bvar x))) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image B)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) B out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const t []) (.const uc [])) := by
  simpa only [Computes] using program_native_return hi hS hTag hF heq hs huc hc hf hΓ
    (unit_call_observation hi hS hTag hF A hΓ hlf hlx) RE RN RB

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
