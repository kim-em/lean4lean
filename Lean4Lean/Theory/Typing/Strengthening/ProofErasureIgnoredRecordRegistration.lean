import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitArrowEquality

/-! # Actual record declarations with ignored higher-order parameters

Ordinary singleton equality presents the dependent constructor at a fixed
closed control carrier. Native observation still starts from the actual stored
dependent Pi and keeps the family head operational.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier UnitArrows)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
local notation "U" => unitCarrier hi hS
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))

/-- The family at the fixed closed parameter is a positive rigid carrier. -/
@[instance_reducible]
def recordCarrier : AtomicControl.Atom where
  type := .app (.const t []) (Q.value hi hS)
  sortLevel := .zero
  closed := ⟨trivial, Q.value_closed hi hS⟩
  typed := .app hF (Q.value_typed hi hS)
  noPi hΓ H := IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hTag)
    (args := [Q.value hi hS]) ((HasType.app hF (Q.value_typed hi hS)).weak0 henv.ordered) H

local notation "RT" => recordCarrier hi hS Q hTag hF

/-- The fresh parameter has its unchanged closed control type. -/
theorem parameter_fresh : env.HasType univs ((Q.control U).expr :: Γ) (.bvar 0) (Q.control U).expr := by
  apply HasType.bvar
  simpa only [VExpr.lift, (Q.control U).closedN.liftN_eq (Nat.zero_le _)] using
    (Lookup.zero (Γ := Γ) (ty := (Q.control U).expr))

/-- Instantiating the monomorphic constructor leaves its simple parameter
and dependent family result unchanged. -/
theorem constructor_instL :
    (PositiveHeaderRegistration.info 0 [(Q.control U).expr] t c).ctorType.instL [] =
      .forallE (Q.control U).expr (.app (.const t []) (.bvar 0)) := by
  change VExpr.forallE ((Q.control U).expr.instL []) (.app (.const t []) (.bvar 0)) = _
  rw [Q.control_instL hi hS]

include hTag hF in
/-- Ordinary parameter uniqueness converts the stored dependent constructor
to a simple control arrow. This does not change its native declaration. -/
theorem constructor_simple_arrow : env.HasType univs [] (.const c [])
    (.forallE (Q.control U).expr (.app (.const t []) (Q.value hi hS))) := by
  have HE := IsDefEq.appDF (hF.weak0 (Γ := [(Q.control U).expr]) henv.ordered)
    (Q.value_equal hi hS (parameter_fresh hi hS Q))
  have hQ : env.HasType univs [] (Q.control U).expr (.sort (Q.control U).level) := HeterogeneousControl.ControlType.typed Q.wf
  have HC : env.HasType univs [] (.const c [])
      (.forallE (Q.control U).expr (.app (.const t []) (.bvar 0))) := by
    have HC : env.HasType univs [] (.const c [])
        ((PositiveHeaderRegistration.info 0 [(Q.control U).expr] t c).ctorType.instL []) :=
      HasType.const (henv.ordered.projectionConstructor hTag) (by simp) rfl
    rwa [constructor_instL hi hS Q] at HC
  exact (IsDefEq.forallEDF hQ HE).defeq HC

include hF in
/-- Erasure of the actual dependent header retains the fresh argument even
though that argument has no computational demand in the observer. -/
theorem header_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.forallE (Q.control U).expr (.app (.const t []) (.bvar 0))) =
      .forallE (Q.raw s) (.app (.const t []) (.bvar 0)) := by
  have hQ : env.HasType univs Γ (Q.control U).expr (.sort (Q.control U).level) := HeterogeneousControl.ControlType.typed Q.wf
  have hΓQ : OnCtx ((Q.control U).expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf := hF.weak0 (Γ := (Q.control U).expr :: Γ) henv.ordered
  have hx := parameter_fresh hi hS Q (Γ := Γ)
  have hb := hf.app hx
  rw [show proofErase Γ (.forallE (Q.control U).expr (.app (.const t []) (.bvar 0))) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (.forallE hQ hb)), Q.erase hi hS hΓ,
    show proofErase ((Q.control U).expr :: Γ) (.app (.const t []) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓQ hb),
    show proofErase ((Q.control U).expr :: Γ) (.const t []) = .const t [] from
      if_neg (not_isProof_function_to_sort hΓQ hf),
    show proofErase ((Q.control U).expr :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (HeterogeneousControl.ControlType.not_isProof hΓQ hx)]

/-- The actual stored constructor header has a complete joint observation
with an empty argument-demand list. Only its dependent family head is demanded. -/
theorem registered_header_observation (hΓ : OnCtx Γ (env.IsType univs)) :
    Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S
      (.forallE (Q.raw s) (.app (.const t []) (.bvar 0))) (.type (.fn (Q.control U) [] .record)) := by
  have hQ : env.HasType univs Γ (Q.control U).expr (.sort (Q.control U).level) := HeterogeneousControl.ControlType.typed Q.wf
  have hΓQ : OnCtx ((Q.control U).expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have EΓ : proofEraseCtx ((Q.control U).expr :: Γ) = Q.raw s :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, Q.erase hi hS hΓ]
  have hf : env.HasType univs ((Q.control U).expr :: Γ) (.const t [])
      (HeterogeneousControl.ControlType.arrow (Q.control U) (.sort (HeterogeneousControl.ControlType.atom RT).level)).expr :=
    hF.weak0 henv.ordered
  have hx := parameter_fresh hi hS Q (Γ := Γ)
  have hb := hf.app hx
  have EF : proofErase ((Q.control U).expr :: Γ) (.const t []) = .const t [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓQ hf)
  have EX : proofErase ((Q.control U).expr :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓQ hx)
  have EB : proofErase ((Q.control U).expr :: Γ) (.app (.const t []) (.bvar 0)) = .app (.const t []) (.bvar 0) := by
    rw [show proofErase ((Q.control U).expr :: Γ) (.app (.const t []) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓQ hb), EF, EX]
  refine .pi ⟨Γ, _, hΓ, rfl, .forallE hQ hb, header_erasure hi hS Q hF hΓ⟩
    ⟨Γ, _, hΓ, rfl, hQ, Q.erase hi hS hΓ⟩ (by simp) (by simp) ?_
  exact .app ⟨(Q.control U).expr :: Γ, _, hΓQ, EΓ, hb, EB⟩
    (.family ⟨(Q.control U).expr :: Γ, _, hΓQ, EΓ, hf, EF⟩) (by simp)

include hi hS hTag hF in
/-- The stored native certificate is available in every raw context. -/
theorem constructor_native : ScopedTypeRecovery Step Δ (.const c [])
    (.forallE (Q.raw s) (.app (.const t []) (.bvar 0))) := by
  have R : ScopedTypeRecovery Step Δ (.const c [])
      (proofErase [] ((PositiveHeaderRegistration.info 0 [(Q.control U).expr] t c).ctorType.instL [])) :=
    ScopedTypeRecovery.const (ls := []) (henv.ordered.projectionConstructor hTag) (by simp) rfl
  rw [constructor_instL hi hS Q] at R
  rwa [header_erasure hi hS Q hF (by trivial)] at R

/-- Every conversion tail of the actual constant certificate starts at the
observed stored Pi. Type-computation preservation is discharged by stage
induction later, rather than assumed as semantic type coverage. -/
theorem registered_constructor_native_of_type_preservation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcomp : ∀ {a b key}, ScopedCompute Step (proofEraseCtx Γ) a b →
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S a (.type key) →
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S b (.type key))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const c []) out) :
    Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S out (.type (.fn (Q.control U) [] .record)) := by
  have R := RN.const_compute (henv.ordered.projectionConstructor hTag)
  rw [constructor_instL hi hS Q] at R
  rw [header_erasure hi hS Q hF (by trivial)] at R
  exact hcomp R (registered_header_observation hi hS Q hTag hF hΓ)

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
