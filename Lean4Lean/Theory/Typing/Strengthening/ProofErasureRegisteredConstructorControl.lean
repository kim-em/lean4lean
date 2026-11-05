import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlDevelopment

/-! # Registered constructor return with beta interleavings

Actual registered unit and phantom families instantiate both data carriers.
Every compatible control development from the saturated constructor returns to
its canonical unit instance. No control typing, observation, or native history
is assumed. The root language still excludes record structure expansion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Unit equality presents the dependent constructor as a simple arrow to
its closed canonical instance. This is an ordinary typing result, without a
claim that the canonical type computes to every selected native type. -/
theorem registered_unit_constructor_simple_arrow
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) :
    env.HasType univs [] (.const c [])
      (.forallE (.const s []) (.app (.const t []) (.const uc []))) := by
  have hu : env.HasType univs [VExpr.const s []] (.const uc []) (.const s []) :=
    .const (henv.ordered.projectionConstructor hi) (by simp) rfl
  have hx : env.HasType univs [VExpr.const s []] (.bvar 0) (.const s []) := .bvar .zero
  have HE := IsDefEq.appDF (hF.weak0 (Γ := [VExpr.const s []]) henv.ordered)
    (IsDefEq.unitLike hi (params := []) rfl rfl rfl hx hu)
  have Hpi := IsDefEq.forallEDF hS HE
  exact Hpi.defeq (.const (henv.ordered.projectionConstructor hTag) (by simp) rfl)

/-- From actual registered metadata, arbitrary compatible beta/control
interleavings return the constructor at the canonical unit. This covers nested
lambda-body and function-prefix computation, not just root wrapper creation.
Full annotation computation is permitted; term-level record structure expansion remains outside Development. -/
theorem registered_constructor_control_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const s []))
    (R : UnitConstructorObservation.Development D (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const c []) (.const uc [])) := by
  have hu : env.HasType univs [] (.const uc []) (.const s []) :=
    .const (henv.ordered.projectionConstructor hi) (by simp) rfl
  let unit : AtomicControl.Atom := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  let record : AtomicControl.Atom := {
    type := .app (.const t []) (.const uc [])
    sortLevel := .zero
    closed := ⟨trivial, trivial⟩
    typed := .app hF hu
    noPi := fun hΓ H => IsDefEqU.rigidApp_forallE_inv henv hΓ
      (henv.projectionRigid hTag) (args := [.const uc []])
      ((HasType.app hF hu).weak0 henv.ordered) H }
  have hne : unit ≠ record := by
    intro H
    have E := congrArg (fun a : AtomicControl.Atom => a.type) H
    cases E
  have hf : env.HasType univs Γ (.const c [])
      (HeterogeneousControl.ControlType.arrow (.atom unit) (.atom record)).expr :=
    (registered_unit_constructor_simple_arrow hi hS hTag hF).weak0 henv.ordered
  have hx : env.HasType univs Γ (.bvar i) (HeterogeneousControl.ControlType.atom unit).expr := .bvar hl
  have ht : env.HasType univs Γ (.app (.const c []) (.bvar i))
      (HeterogeneousControl.ControlType.atom record).expr := .app hf hx
  have EF : proofErase Γ (.const c []) = .const c [] :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have EX : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hx)
  have ET : proofErase Γ (.app (.const c []) (.bvar i)) = .app (.const c []) (.bvar i) := by
    rw [show proofErase Γ (.app (.const c []) (.bvar i)) = .app _ _ from
      if_neg (HeterogeneousControl.ControlType.not_isProof hΓ ht), EF, EX]
  rcases UnitConstructorObservation.application_development_readout (c := uc) heq hs hne
      ⟨Γ, _, hΓ, rfl, hf, EF⟩ ⟨Γ, _, hΓ, rfl, hx, EX⟩ ⟨Γ, _, hΓ, rfl, ht, ET⟩ R with HB | HB
  · exact (ScopedCompute.beta HB).trans (.app .refl
      (static_structure_unit_lookup_compute hi rfl rfl rfl hS hΓ hl))
  · exact .beta HB

end Lean4Lean.VEnv.Strengthening
