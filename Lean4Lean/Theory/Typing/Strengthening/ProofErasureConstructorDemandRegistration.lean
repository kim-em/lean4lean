import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRegisteredConstructorControl

/-! # A registered constructor supplies its dependent type demand

The initial stored Pi header observes Tag at its retained fresh unit variable.
This is exactly the codomain that fixed lower-origin demands could not admit.
No native parameter premise or type-computation preservation is needed to
construct the initial observation; subsequent native conversions still need
that preservation, explicitly stated in the final theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- The registered positive unit is the argument carrier. -/
@[instance_reducible]
def unitCarrier
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero))) : AtomicControl.Atom :=
  AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS

/-- The closed canonical record instance is a separate positive carrier. -/
@[instance_reducible]
def recordCarrier
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) : AtomicControl.Atom where
  type := .app (.const t []) (.const uc [])
  sortLevel := .zero
  closed := ⟨trivial, trivial⟩
  typed := .app hF (.const (henv.ordered.projectionConstructor hi) (by simp) rfl)
  noPi hΓ H := IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hTag)
    (args := [.const uc []]) ((HasType.app hF
      (HasType.const (henv.ordered.projectionConstructor hi) (by simp) rfl)).weak0 henv.ordered) H

/-- The actual dependent constructor header carries a demand on its fresh
unit argument. The codomain records Tag #0 rather than pretending to be a
lift of a type fixed below that binder. -/
theorem registered_header_observation
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    let unit := unitCarrier hi hS
    let record := recordCarrier hi hTag hF
    Obs unit record uc c t (proofEraseCtx Γ) V
      (.forallE (.const s []) (.app (.const t []) (.bvar 0)))
      (.type (.fn (.atom unit) [.unit] .record)) := by
  let unit := unitCarrier hi hS
  let record := recordCarrier hi hTag hF
  change Obs unit record uc c t (proofEraseCtx Γ) V _ _
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have ES : proofErase Γ (.const s []) = .const s [] := if_neg (not_isProof_of_sort hΓ hSΓ)
  have EΓS : proofEraseCtx (VExpr.const s [] :: Γ) = .const s [] :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, ES]
  have HE : TypeEquality (proofEraseCtx Γ) (.const s []) (.atom unit) := ⟨Γ, _, hΓ, rfl, hSΓ, ES⟩
  have hx : env.HasType univs (VExpr.const s [] :: Γ) (.bvar 0) (.const s []) := .bvar .zero
  have hf : env.HasType univs (VExpr.const s [] :: Γ) (.const t [])
      (HeterogeneousControl.ControlType.arrow (.atom unit) (.sort (HeterogeneousControl.ControlType.atom record).level)).expr :=
    hF.weak0 henv.ordered
  have hb : env.HasType univs (VExpr.const s [] :: Γ) (.app (.const t []) (.bvar 0)) (.sort (.succ .zero)) := .app hf hx
  have hPi := HasType.forallE hSΓ hb
  have EF : proofErase (VExpr.const s [] :: Γ) (.const t []) = .const t [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓS hf)
  have EX : proofErase (VExpr.const s [] :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (HeterogeneousControl.ControlType.not_isProof (t := .atom unit) hΓS hx)
  have EB : proofErase (VExpr.const s [] :: Γ) (.app (.const t []) (.bvar 0)) =
      .app (.const t []) (.bvar 0) := by
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓS hb), EF, EX]
  have EP : proofErase Γ (.forallE (.const s []) (.app (.const t []) (.bvar 0))) =
      .forallE (.const s []) (.app (.const t []) (.bvar 0)) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi), ES, EB]
  refine .pi ⟨Γ, _, hΓ, rfl, hPi, EP⟩ HE ?_ ?_ ?_
  · intro key hk; obtain rfl := List.mem_singleton.1 hk; rfl
  · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .unit_type HE
  · exact .app ⟨VExpr.const s [] :: Γ, _, hΓS, EΓS, hb, EB⟩
      (.family ⟨VExpr.const s [] :: Γ, _, hΓS, EΓS, hf, EF⟩) (by
        intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact .var HE.fresh (by simp only [Key.Valid]) (by simp [Sets.cons]))

/-- The registered bare constructor's native case reduces to preservation of
its observed stored type through the actual conversion tail. This uses the
stored declaration directly, with no assumed initial header observation. -/
theorem registered_constructor_native_of_type_preservation
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcomp : ∀ {a b key}, ScopedCompute Step (proofEraseCtx Γ) a b →
      Obs (unitCarrier hi hS) (recordCarrier hi hTag hF) uc c t (proofEraseCtx Γ) V a (.type key) →
      Obs (unitCarrier hi hS) (recordCarrier hi hTag hF) uc c t (proofEraseCtx Γ) V b (.type key))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const c []) out) :
    Obs (unitCarrier hi hS) (recordCarrier hi hTag hF) uc c t (proofEraseCtx Γ) V out
      (.type (.fn (.atom (unitCarrier hi hS)) [.unit] .record)) := by
  have R := registered_unit_constructor_function_history hΓ hTag RN
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hS.weak0 henv.ordered⟩
  have hB : env.HasType univs (VExpr.const s [] :: Γ) (.app (.const t []) (.bvar 0)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) (HasType.bvar .zero)
  have hPi := HasType.forallE (hS.weak0 (Γ := Γ) henv.ordered) hB
  have EP : proofErase Γ (.forallE (.const s []) (.app (.const t []) (.bvar 0))) =
      .forallE (.const s []) (.app (.const t []) (.bvar 0)) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
    rw [show proofErase Γ (.const s []) = .const s [] from if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))]
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓS hB)]
    rw [show proofErase (VExpr.const s [] :: Γ) (.const t []) = .const t [] from
      if_neg (not_isProof_function_to_sort hΓS (hF.weak0 henv.ordered))]
    rw [show proofErase (VExpr.const s [] :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (HeterogeneousControl.ControlType.not_isProof (t := .atom (unitCarrier hi hS)) hΓS (HasType.bvar .zero))]
  rw [EP] at R
  exact hcomp R (registered_header_observation hi hS hTag hF hΓ)

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
