import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordRegisteredNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Full native preservation with ignored record parameters

Only the registered constructor and family heads carry operational evidence.
The supplied parameter needs no observation; its ordinary singleton carrier
fixes the control typing used by the joint native induction.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- A non-type demand with primitive head uses one of the three fixed constants.
In application nodes the function key is always non-type, even for a type-valued
result, so opaque type certificates cannot invent an operational function head. -/
theorem Obs.primitive_heads (H : Obs unit record parameter uc ctor family Δ S e key)
    (HH : PrimitiveHead e) (HK : ∀ k, key ≠ .type k) :
    e.constHead = some uc ∨ e.constHead = some ctor ∨ e.constHead = some family := by
  induction H with
  | var | lam | pi => cases HH
  | unit_ctor => exact .inl rfl
  | record_ctor => exact .inr (.inl rfl)
  | family => exact .inr (.inr rfl)
  | unit_type | univ | family_type => exact (HK _ rfl).elim
  | app _ _ _ ihf _ => exact ihf HH (by intro k E; cases E)

/-- Primitives excluded at the three rigid heads can only act inside an opaque
ordinary type certificate, which survives by source-typed replay. -/
theorem Obs.rigid_primitive (hstep : ErasedScopedPrimitiveDescent Step)
    (R : Step Δ a b) (HH : PrimitiveHead a)
    (Huc : a.constHead = some uc → False) (Hc : a.constHead = some ctor → False)
    (Hf : a.constHead = some family → False) (H : Obs unit record parameter uc ctor family Δ S a key) :
    Obs unit record parameter uc ctor family Δ S b key := by
  cases H with
  | var | lam | pi => cases HH
  | unit_ctor => exact (Huc rfl).elim
  | record_ctor => exact (Hc rfl).elim
  | family => exact (Hf rfl).elim
  | unit_type HE => exact .unit_type (HE.compute hstep (.base R))

  | univ HK HE => exact .univ HK (HE.compute hstep (.base R))
  | family_type HE => exact .family_type (HE.compute hstep (.base R))
  | app _ HF _ =>
    rcases HF.primitive_heads HH (by intro k E; cases E) with HC | HC | HC
    · exact (Huc HC).elim
    · exact (Hc HC).elim
    · exact (Hf HC).elim

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
