import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypeExposure

/-! # Comparison-directed exposure of selected recovered types

The three heads consumed by syntax-directed recovery are sorts, Pis and rigid
family applications. Joint comparison against such a head supplies computation
to the same kind of head; it need not supply a literal join of the full types.
These lemmas expose a new selected output from an existing recovery and type
comparison. They do not assert that either input certificate always exists.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

private def typeHead : ProofShape → Option Bool
  | .sort _ => some false
  | .forallE .. => some true
  | _ => none

variable [Params]

private theorem typeHead_compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ a b) (E : typeHead a = some tag) : typeHead b = some tag := by
  cases a with
  | sort u => rw [R.sort_fixed hhead]; exact E
  | forallE A B => obtain ⟨A', B', rfl⟩ := R.forallE_head hhead; exact E
  | proof | bvar | const | app | proj | lam => cases E

private theorem type_exposure_pair
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind a b) (hm : kind = .compare false) :
    (∀ tag, typeHead a = some tag → ∃ out, ScopedCompute Step Δ b out ∧ typeHead out = some tag) ∧
    (∀ tag, typeHead b = some tag → ∃ out, ScopedCompute Step Δ a out ∧ typeHead out = some tag) := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl | sort => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
    | const => constructor <;> intro _ E <;> cases E
  | forallE | forallSorted => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
  | app | appCarrier | proj | lam | lamSorted | etaLams =>
    constructor <;> intro _ E <;> cases E
  | compute Ra Rb HC ih =>
    have IH := ih hm
    constructor
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.1 tag (typeHead_compute hhead Ra E)
      exact ⟨out, Rb.trans R, HE⟩
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.2 tag (typeHead_compute hhead Rb E)
      exact ⟨out, Ra.trans R, HE⟩
  | symm H ih => exact (ih hm).symm
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Inferred joint comparison with a literal sort exposes a sort on the other
side using exactly the same primitive computation relation. -/
theorem JointCompare.sort_exposure
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false (.sort u) T) :
    ∃ v, ScopedCompute Step Δ T (.sort v) := by
  obtain ⟨out, R, HE⟩ := (type_exposure_pair hhead H rfl).1 false rfl
  cases out <;> try cases HE
  exact ⟨_, R⟩

/-- Inferred joint comparison with a literal Pi exposes some Pi on the other
side. Its domain and codomain need not match the source Pi syntactically. -/
theorem JointCompare.forallE_exposure
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false (.forallE A B) T) :
    ∃ A' B', ScopedCompute Step Δ T (.forallE A' B') := by
  obtain ⟨out, R, HE⟩ := (type_exposure_pair hhead H rfl).1 true rfl
  cases out <;> try cases HE
  exact ⟨_, _, R⟩

/-- An existing recovery whose selected type compares with a universe can be
extended to a universe recovery. The compared universe syntax may differ. -/
theorem ScopedTypeRecovery.sort_of_joint_compare
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ e T)
    (H : JointCompare Step Δ false T (.sort u)) :
    ∃ v, ScopedTypeRecovery Step Δ e (.sort v) := by
  obtain ⟨v, RT⟩ := JointCompare.sort_exposure hhead (.symm H)
  exact ⟨v, R.convert RT⟩

/-- An existing recovery whose selected type compares with a Pi can be extended
to a Pi recovery. This chooses a new domain rather than demanding exact
recovery of the originally assigned domain and codomain. -/
theorem ScopedTypeRecovery.pi_of_joint_compare
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ e T)
    (H : JointCompare Step Δ false T (.forallE A B)) :
    ∃ A' B', ScopedTypeRecovery Step Δ e (.forallE A' B') := by
  obtain ⟨A', B', RT⟩ := JointCompare.forallE_exposure hhead (.symm H)
  exact ⟨A', B', R.convert RT⟩

/-- An existing recovery comparing with a primitive-inert family application
can expose that family with the required argument count. Universes and argument
syntax may change; this does not assert aligned dependent projection carriers. -/
theorem ScopedTypeRecovery.family_of_joint_compare
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const c ls) args) out)
    (R : ScopedTypeRecovery Step Δ e T)
    (H : JointCompare Step Δ false T (mkApps (.const c ls) args)) :
    ∃ ls' args', ScopedTypeRecovery Step Δ e (mkApps (.const c ls') args') ∧
      args'.length = args.length := by
  obtain ⟨ls', args', RT, hlen⟩ := JointCompare.const_spine_exposure hn (.symm H)
  exact ⟨ls', args', R.convert RT, hlen⟩

end ProofShape
end Lean4Lean.VEnv.Strengthening
