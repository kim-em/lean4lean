import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionParameterConstructor
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandRegistration

/-! # Actual headers for records retaining unit functions

Ordinary unit equality and function eta give a closed control carrier for the
record. The stored dependent header still retains its fresh function parameter;
that ordinary equality is never used as an operational parameter observation.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier)
variable [Params]

/-- The literal constant unit function has the closed parameter type. -/
theorem canonical_function_typed
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero))) :
    env.HasType univs Γ (.lam (.const s []) (.const uc []))
      (.forallE (.const s []) (.const s [])) :=
  .lam (hS.weak0 henv.ordered) (.const (henv.ordered.projectionConstructor hi) (by simp) rfl)

/-- Ordinary function eta and unit equality identify any assigned endofunction
with the canonical constant function. This asserts no directed raw computation. -/
theorem unit_function_equal
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hf : env.HasType univs Γ f (.forallE (.const s []) (.const s []))) :
    env.IsDefEq univs Γ f (.lam (.const s []) (.const uc []))
      (.forallE (.const s []) (.const s [])) := by
  have hbody : env.HasType univs (.const s [] :: Γ) (.app f.lift (.bvar 0)) (.const s []) :=
    .app (hf.weak henv.ordered) (HasType.bvar .zero)
  have hc : env.HasType univs (.const s [] :: Γ) (.const uc []) (.const s []) :=
    .const (henv.ordered.projectionConstructor hi) (by simp) rfl
  exact (IsDefEq.eta hf).symm.trans
    (.lamDF (hS.weak0 henv.ordered) (IsDefEq.unitLike hi (params := []) rfl rfl rfl hbody hc))

/-- The canonical record at the closed constant function is a positive atom. -/
@[instance_reducible]
def recordCarrier
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))) : AtomicControl.Atom where
  type := .app (.const t []) (.lam (.const s []) (.const uc []))
  sortLevel := .zero
  closed := ⟨trivial, trivial, trivial⟩
  typed := .app hF (canonical_function_typed hi hS)
  noPi hΓ H := IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hTag)
    (args := [.lam (.const s []) (.const uc [])])
    ((HasType.app hF (canonical_function_typed hi hS)).weak0 henv.ordered) H

/-- Ordinary conversion presents the dependent constructor as a closed arrow.
Its actual native header is still the dependent declaration read below. -/
theorem constructor_simple_arrow
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))) :
    env.HasType univs [] (.const c [])
      (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const t []) (.lam (.const s []) (.const uc [])))) := by
  let Q : VExpr := .forallE (.const s []) (.const s [])
  have hx : env.HasType univs [Q] (.bvar 0) Q := .bvar .zero
  have HE := IsDefEq.appDF (hF.weak0 (Γ := [Q]) henv.ordered) (unit_function_equal hi hS hx)
  have hQ : env.HasType univs [] Q (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE hS (hS.weak0 henv.ordered)
  exact (IsDefEq.forallEDF hQ HE).defeq (.const (henv.ordered.projectionConstructor hTag) (by simp) rfl)

/-- The actual dependent constructor Pi observes its fresh function argument
in the family application. The demanded function annotation is ordinary equality
at the empty-input-demand key, rather than a lower-context family origin. -/
theorem registered_header_observation
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    let unit := unitCarrier hi hS
    let record := recordCarrier hi hS hTag hF
    Obs unit record uc c t (proofEraseCtx Γ) V
      (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)))
      (.type (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] .record)) := by
  let unit := unitCarrier hi hS
  let record := recordCarrier hi hS hTag hF
  let Q : VExpr := .forallE (.const s []) (.const s [])
  change Obs unit record uc c t (proofEraseCtx Γ) V _ _
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have EQ := RigidFunctionObservation.unit_arrow_erasure hS hΓ
  have EΓQ : proofEraseCtx (Q :: Γ) = .forallE (.const s []) (.const s []) :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, Q, EQ]
  have HE : TypeEquality (proofEraseCtx Γ) (.forallE (.const s []) (.const s []))
      (.arrow (.atom unit) (.atom unit)) := ⟨Γ, _, hΓ, rfl, hQ, EQ⟩
  have hx : env.HasType univs (Q :: Γ) (.bvar 0) Q := .bvar .zero
  have hf : env.HasType univs (Q :: Γ) (.const t [])
      (HeterogeneousControl.ControlType.arrow (.arrow (.atom unit) (.atom unit))
        (.sort (HeterogeneousControl.ControlType.atom record).level)).expr := hF.weak0 henv.ordered
  have hb : env.HasType univs (Q :: Γ) (.app (.const t []) (.bvar 0)) (.sort (.succ .zero)) := .app hf hx
  have hPi := HasType.forallE hQ hb
  have EF : proofErase (Q :: Γ) (.const t []) = .const t [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓQ hf)
  have EX : proofErase (Q :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (HeterogeneousControl.ControlType.not_isProof (t := .arrow (.atom unit) (.atom unit)) hΓQ hx)
  have EB : proofErase (Q :: Γ) (.app (.const t []) (.bvar 0)) = .app (.const t []) (.bvar 0) := by
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓQ hb), EF, EX]
  have EP : proofErase Γ (.forallE Q (.app (.const t []) (.bvar 0))) =
      .forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi), EB]
    exact congrArg (fun A => ProofShape.forallE A _) EQ
  refine .pi ⟨Γ, _, hΓ, rfl, hPi, EP⟩ HE ?_ ?_ ?_
  · intro key hk; obtain rfl := List.mem_singleton.1 hk; rfl
  · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .function_type HE
  · exact .app ⟨Q :: Γ, _, hΓQ, EΓQ, hb, EB⟩
      (.family ⟨Q :: Γ, _, hΓQ, EΓQ, hf, EF⟩) (by
        intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact .var HE.fresh (by simp [Key.Valid]) (by simp [Sets.cons, unit]))

/-- The actual dependent constructor header has the displayed raw Pi shape. -/
theorem header_erasure
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0))) =
      .forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)) := by
  let Q : VExpr := .forallE (.const s []) (.const s [])
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf : env.HasType univs (Q :: Γ) (.const t []) (.forallE Q (.sort (.succ .zero))) := hF.weak0 henv.ordered
  have hb := hf.app (show env.HasType univs (Q :: Γ) (.bvar 0) Q from .bvar .zero)
  have EQ := RigidFunctionObservation.unit_arrow_erasure hS hΓ
  have EX : proofErase (Q :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (HeterogeneousControl.ControlType.not_isProof
      (t := .arrow (.atom (unitCarrier hi hS)) (.atom (unitCarrier hi hS))) hΓQ (HasType.bvar .zero))
  have EP : proofErase Γ (.forallE Q (.app (.const t []) (.bvar 0))) =
      .forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (.forallE hQ hb)),
      EQ, show proofErase (Q :: Γ) (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓQ hb),
      show proofErase (Q :: Γ) (.const t []) = .const t [] from if_neg (not_isProof_function_to_sort hΓQ hf), EX]
  exact EP

/-- The bare constructor's complete native conversion tail is observed from
its actual stored header once type-observation preservation is supplied. -/
theorem registered_constructor_native_of_type_preservation
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcomp : ∀ {a b key}, ScopedCompute Step (proofEraseCtx Γ) a b →
      Obs (unitCarrier hi hS) (recordCarrier hi hS hTag hF) uc c t (proofEraseCtx Γ) V a (.type key) →
      Obs (unitCarrier hi hS) (recordCarrier hi hS hTag hF) uc c t (proofEraseCtx Γ) V b (.type key))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const c []) out) :
    Obs (unitCarrier hi hS) (recordCarrier hi hS hTag hF) uc c t (proofEraseCtx Γ) V out
      (.type (.fn (.arrow (.atom (unitCarrier hi hS)) (.atom (unitCarrier hi hS)))
        [.fn (.atom (unitCarrier hi hS)) [] .unit] .record)) := by
  have hc := henv.ordered.projectionConstructor hTag
  have R := RN.const_compute hc
  change ScopedCompute Step (proofEraseCtx Γ)
    (proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)))) out at R
  have hC : env.HasType univs [] (.const c [])
      (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0))) := .const hc (by simp) rfl
  obtain ⟨_, hT⟩ := hC.isType henv (by trivial)
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL (ls := [])) hT hΓ
  change proofErase Γ (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0))) =
    proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0))) at EC
  rw [← EC] at R
  have H := registered_header_observation hi hS hTag hF hΓ (V := V)
  rw [header_erasure hi hS hF hΓ] at R
  exact hcomp R H

/-- The actual stored constructor header is natively available in every raw
context. The family declaration itself need not have a literal unit domain. -/
theorem constructor_native
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero)))) :
    ScopedTypeRecovery Step Δ (.const c [])
      (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0))) := by
  have R : ScopedTypeRecovery Step Δ (.const c [])
      (proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.app (.const t []) (.bvar 0)))) :=
    .const (henv.ordered.projectionConstructor hTag) (by simp) rfl
  rwa [header_erasure hi hS hF (by trivial)] at R

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
