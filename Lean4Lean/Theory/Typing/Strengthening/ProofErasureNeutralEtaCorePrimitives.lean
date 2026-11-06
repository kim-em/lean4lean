import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCorePrimitives

/-! # Core primitives preserve protected neutral eta marks

Visible pattern structure and universe lists remain exact. Captures may contain
eta marks; selection and stored templates retain the corresponding paired
captures. This proves primitive simulation without a typing premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

namespace ProofShape
variable {Guard : ProofShape → Nat → Prop}

private theorem app_parts (V : NeutralEtaVariant Guard n (.app f x) b) :
    ∃ g y, b = .app g y ∧ NeutralEtaVariant Guard n f g ∧ NeutralEtaVariant Guard n x y := by
  cases V with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app VF VX => exact ⟨_, _, rfl, VF, VX⟩

private theorem proj_parts (V : NeutralEtaVariant Guard n (.proj s i a) b) :
    ∃ m, b = .proj s i m ∧ NeutralEtaVariant Guard n a m := by
  cases V with
  | refl => exact ⟨_, rfl, .refl⟩
  | proj VM => exact ⟨_, rfl, VM⟩

/-- A constant-headed paired spine keeps the exact head and universe list. -/
theorem NeutralEtaVariant.constant_spine
    (V : NeutralEtaVariant Guard n (ProofShape.mkApps (.const c ls) args) b) :
    ∃ args', b = ProofShape.mkApps (.const c ls) args' ∧
      List.Forall₂ (NeutralEtaVariant Guard n) args args' := by
  induction args using List.snoc_induction generalizing b with
  | nil => cases V; exact ⟨[], rfl, .nil⟩
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at V
    obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V
    obtain ⟨args', rfl, HA⟩ := ih VF
    exact ⟨args' ++ [y], ProofShape.mkApps_snoc.symm, HA.append' (.cons VX .nil)⟩

/-- Paired heads and argument lists form a paired application spine. -/
theorem NeutralEtaVariant.mkApps_pair (V : NeutralEtaVariant Guard n f g)
    (H : List.Forall₂ (NeutralEtaVariant Guard n) args args') :
    NeutralEtaVariant Guard n (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  induction H generalizing f g with
  | nil => exact V
  | cons HX _ ih => exact ih (.app V HX)

/-- Every visible pattern match survives protected neutral eta changes, with the
same universe list and pointwise paired captures. -/
theorem Matches.neutral_eta_variant (H : Matches p a ls caps) (V : NeutralEtaVariant Guard n a b) :
    ∃ caps', Matches p b ls caps' ∧ ∀ i, NeutralEtaVariant Guard n (caps i) (caps' i) := by
  induction H generalizing b with
  | const => cases V; exact ⟨nofun, .const, nofun⟩
  | var H ih =>
    obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V
    obtain ⟨caps', HM, HC⟩ := ih VF
    refine ⟨_, .var HM, ?_⟩
    intro i; cases i with
    | none => exact VX
    | some i => exact HC i
  | app HF HX ihf ihx =>
    obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V
    obtain ⟨cf, HF, HCF⟩ := ihf VF
    obtain ⟨cx, HX, HCX⟩ := ihx VX
    refine ⟨_, .app HF HX, ?_⟩
    intro i; cases i with
    | inl i => exact HCF i
    | inr i => exact HCX i

variable [Params]

/-- Delta and projection simulate at every protected neutral eta variant. -/
theorem Primitive.neutral_eta_variant (R : Primitive D a out) (V : NeutralEtaVariant Guard n a b) :
    ∃ out', Primitive D b out' ∧ NeutralEtaVariant Guard n out out' := by
  cases R with
  | delta HD => cases V; exact ⟨_, .delta HD, .refl⟩
  | @projIota s info args i ls field hi hlen hget =>
    obtain ⟨m, rfl, VM⟩ := proj_parts V
    obtain ⟨args', rfl, HA⟩ := VM.constant_spine
    obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
    have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
    refine ⟨args'[info.nparams + i]'hj', .projIota hi (HA.length_eq.symm.trans hlen)
      (List.getElem?_eq_getElem hj'), ?_⟩
    rw [← HE]
    exact HA.getElem_of _ hj hj'

/-- Capturing and capture-application primitives keep their original rule check. -/
theorem CapturePrimitive.neutral_eta_variant (R : CapturePrimitive a out)
    (V : NeutralEtaVariant Guard n a b) :
    ∃ out', CapturePrimitive b out' ∧ NeutralEtaVariant Guard n out out' := by
  cases R with
  | select hp hc hm =>
    obtain ⟨caps', HM, HC⟩ := hm.neutral_eta_variant V
    exact ⟨_, .select hp hc HM, HC _⟩
  | apply hp hc hm =>
    obtain ⟨caps', HM, HC⟩ := hm.neutral_eta_variant V
    exact ⟨_, .apply hp hc HM, .app (HC _) (HC _)⟩

/-- Registered templates keep the exact closed RHS and vary only their captures. -/
theorem TemplatePrimitive.neutral_eta_variant (R : TemplatePrimitive a out)
    (V : NeutralEtaVariant Guard n a b) :
    ∃ out', TemplatePrimitive b out' ∧ NeutralEtaVariant Guard n out out' := by
  cases R with
  | intro hp hc ht hm =>
    obtain ⟨caps', HM, HC⟩ := hm.neutral_eta_variant V
    refine ⟨_, .intro hp hc ht HM, NeutralEtaVariant.refl.mkApps_pair ?_⟩
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map]
    exact HC _

end ProofShape
variable [Params] {Guard : ProofShape → Nat → Prop}

/-- All ordinary core primitives preserve protected neutral eta variants. Visible
patterns and universe checks are reused literally; no semantic endpoint equality
or global pattern-compatibility premise is assumed. -/
theorem erased_iota_neutral_eta_variant (R : ErasedIotaPrimitive D a out)
    (V : NeutralEtaVariant Guard n a b) :
    ∃ out', ErasedIotaPrimitive D b out' ∧ NeutralEtaVariant Guard n out out' := by
  rcases R with (R | R) | R
  · obtain ⟨out', R', V'⟩ := R.neutral_eta_variant V
    exact ⟨out', .inl (.inl R'), V'⟩
  · obtain ⟨out', R', V'⟩ := R.neutral_eta_variant V
    exact ⟨out', .inl (.inr R'), V'⟩
  · obtain ⟨out', R', V'⟩ := R.neutral_eta_variant V
    exact ⟨out', .inr R', V'⟩

/-- Explicit universe conversion is matched by the identical conversion on
its paired sort or constant. Eta marks affect only variables and lambdas. -/
theorem erased_level_core_neutral_eta_variant (R : ErasedLevelCore D a out)
    (V : NeutralEtaVariant Guard n a b) :
    ∃ out', ErasedLevelCore D b out' ∧ NeutralEtaVariant Guard n out out' := by
  rcases R with R | R
  · obtain ⟨out', R', V'⟩ := erased_iota_neutral_eta_variant R V
    exact ⟨out', .inl R', V'⟩
  · cases R with
    | sort HE hw => cases V; exact ⟨_, .inr (.sort HE hw), .refl⟩
    | const HE hw => cases V; exact ⟨_, .inr (.const HE hw), .refl⟩

end Lean4Lean.VEnv.Strengthening
