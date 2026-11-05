import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandRegisteredNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Primitive preservation of joint constructor demands

Opaque ordinary type certificates replay every sound primitive. Other observed
heads are the three fixed rigid constants; their primitive reductions are
excluded by actual environment rigidity and the definition collection.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- A non-type demand with primitive head uses one of the three fixed constants.
In application nodes the function key is always non-type, even for a type-valued
result, so opaque type certificates cannot invent an operational function head. -/
theorem Obs.primitive_heads (H : Obs unit record uc ctor family Δ S e key)
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
    (Hf : a.constHead = some family → False) (H : Obs unit record uc ctor family Δ S a key) :
    Obs unit record uc ctor family Δ S b key := by
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

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
