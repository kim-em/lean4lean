import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicCoreReflection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelCore

/-! # Core primitives preserve paired annotation origins

Visible patterns inspect constant/application structure and capture their other
arguments. Marked lambda annotations therefore do not change a match. Delta and
fixed RHS templates retain their exact universes, while projection and capture
rules select corresponding paired terms. No typing or guard transport oracle is
needed for this primitive simulation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private ProofShape.liftN_sort_inv ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

namespace ProofShape
variable {Guard : ProofShape → ProofShape → Prop}

private theorem app_parts (V : AnnotationVariant Guard n (.app f x) b) :
    ∃ g y, b = .app g y ∧ AnnotationVariant Guard n f g ∧ AnnotationVariant Guard n x y := by
  cases V with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app VF VX => exact ⟨_, _, rfl, VF, VX⟩

private theorem proj_parts (V : AnnotationVariant Guard n (.proj s i a) b) :
    ∃ m, b = .proj s i m ∧ AnnotationVariant Guard n a m := by
  cases V with
  | refl => exact ⟨_, rfl, .refl⟩
  | proj VM => exact ⟨_, rfl, VM⟩

/-- A constant-headed paired spine keeps the exact head and universe list. -/
theorem AnnotationVariant.constant_spine
    (V : AnnotationVariant Guard n (ProofShape.mkApps (.const c ls) args) b) :
    ∃ args', b = ProofShape.mkApps (.const c ls) args' ∧
      List.Forall₂ (AnnotationVariant Guard n) args args' := by
  induction args using List.snoc_induction generalizing b with
  | nil => cases V; exact ⟨[], rfl, .nil⟩
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at V
    obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V
    obtain ⟨args', rfl, HA⟩ := ih VF
    exact ⟨args' ++ [y], ProofShape.mkApps_snoc.symm, HA.append' (.cons VX .nil)⟩

/-- Paired heads and argument lists form a paired application spine. -/
theorem AnnotationVariant.mkApps_pair (V : AnnotationVariant Guard n f g)
    (H : List.Forall₂ (AnnotationVariant Guard n) args args') :
    AnnotationVariant Guard n (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  induction H generalizing f g with
  | nil => exact V
  | cons HX _ ih => exact ih (.app V HX)

/-- Every visible pattern match survives marked annotation changes, with the
same universe list and pointwise paired captures. -/
theorem Matches.annotation_variant (H : Matches p a ls caps) (V : AnnotationVariant Guard n a b) :
    ∃ caps', Matches p b ls caps' ∧ ∀ i, AnnotationVariant Guard n (caps i) (caps' i) := by
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

/-- Delta and projection simulate at every paired annotation variant. -/
theorem Primitive.annotation_variant (R : Primitive D a out) (V : AnnotationVariant Guard n a b) :
    ∃ out', Primitive D b out' ∧ AnnotationVariant Guard n out out' := by
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
theorem CapturePrimitive.annotation_variant (R : CapturePrimitive a out)
    (V : AnnotationVariant Guard n a b) :
    ∃ out', CapturePrimitive b out' ∧ AnnotationVariant Guard n out out' := by
  cases R with
  | select hp hc hm =>
    obtain ⟨caps', HM, HC⟩ := hm.annotation_variant V
    exact ⟨_, .select hp hc HM, HC _⟩
  | apply hp hc hm =>
    obtain ⟨caps', HM, HC⟩ := hm.annotation_variant V
    exact ⟨_, .apply hp hc HM, .app (HC _) (HC _)⟩

/-- Registered templates keep the exact closed RHS and vary only their captures. -/
theorem TemplatePrimitive.annotation_variant (R : TemplatePrimitive a out)
    (V : AnnotationVariant Guard n a b) :
    ∃ out', TemplatePrimitive b out' ∧ AnnotationVariant Guard n out out' := by
  cases R with
  | intro hp hc ht hm =>
    obtain ⟨caps', HM, HC⟩ := hm.annotation_variant V
    refine ⟨_, .intro hp hc ht HM, AnnotationVariant.refl.mkApps_pair ?_⟩
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map]
    exact HC _

end ProofShape
variable [Params] {Guard : ProofShape → ProofShape → Prop}

/-- All ordinary core primitives preserve paired annotation variants. Visible
patterns and universe checks are reused literally; no semantic endpoint equality
or global pattern-compatibility premise is assumed. -/
theorem erased_iota_annotation_variant (R : ErasedIotaPrimitive D a out)
    (V : AnnotationVariant Guard n a b) :
    ∃ out', ErasedIotaPrimitive D b out' ∧ AnnotationVariant Guard n out out' := by
  rcases R with (R | R) | R
  · obtain ⟨out', R', V'⟩ := R.annotation_variant V
    exact ⟨out', .inl (.inl R'), V'⟩
  · obtain ⟨out', R', V'⟩ := R.annotation_variant V
    exact ⟨out', .inl (.inr R'), V'⟩
  · obtain ⟨out', R', V'⟩ := R.annotation_variant V
    exact ⟨out', .inr R', V'⟩

/-- Explicit universe conversion is matched by the identical conversion on
its paired sort or constant. Marked domain changes occur only at lambdas. -/
theorem erased_level_core_annotation_variant (R : ErasedLevelCore D a out)
    (V : AnnotationVariant Guard n a b) :
    ∃ out', ErasedLevelCore D b out' ∧ AnnotationVariant Guard n out out' := by
  rcases R with R | R
  · obtain ⟨out', R', V'⟩ := erased_iota_annotation_variant R V
    exact ⟨out', .inl R', V'⟩
  · cases R with
    | sort HE hw => cases V; exact ⟨_, .inr (.sort HE hw), .refl⟩
    | const HE hw => cases V; exact ⟨_, .inr (.const HE hw), .refl⟩

private theorem level_root_lift_inv (R : ErasedLevelCore D (a.liftN n k) out) :
    ∃ a', ErasedLevelCore D a a' ∧ out = a'.liftN n k := by
  rcases R with R | R
  · rw [← subst_bvar_liftN] at R
    obtain ⟨a', R', E⟩ := erased_iota_primitive_atomic_subst_inv (fun _ => .bvar) R
    exact ⟨a', .inl R', by simpa only [subst_bvar_liftN] using E.symm⟩
  · generalize E : a.liftN n k = source at R
    cases R with
    | sort HE hw => obtain rfl := ProofShape.liftN_sort_inv E; exact ⟨_, .inr (.sort HE hw), rfl⟩
    | const HE hw => obtain rfl := ProofShape.liftN_const_inv E; exact ⟨_, .inr (.const HE hw), rfl⟩

/-- Entire level-core paths preserve omission of an inserted binder block.
This is a raw reflection theorem, including projection, delta and stored iota. -/
theorem ProofShape.Compute.level_core_lift_inv (R : Compute (ErasedLevelCore D) (a.liftN n k) out) :
    ∃ a', Compute (ErasedLevelCore D) a a' ∧ out = a'.liftN n k := by
  generalize E : a.liftN n k = source at R
  induction R generalizing a k with
  | base R => obtain ⟨a', RA, E'⟩ := level_root_lift_inv (E ▸ R); exact ⟨a', .base RA, E'⟩
  | beta R => obtain ⟨a', RA, E'⟩ := (E ▸ R).liftN_inv; exact ⟨a', .beta RA, E'⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨a₁, RA, E₁⟩ := ih₁ E
    obtain ⟨a₂, RB, E₂⟩ := ih₂ E₁.symm
    exact ⟨a₂, RA.trans RB, E₂⟩
  | app _ _ ihf ihx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := ProofShape.liftN_app_inv E
    obtain ⟨f', RF, rfl⟩ := ihf rfl
    obtain ⟨x', RX, rfl⟩ := ihx rfl
    exact ⟨_, .app RF RX, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, rfl⟩ := ProofShape.liftN_proj_inv E
    obtain ⟨m', RM, rfl⟩ := ih rfl
    exact ⟨_, .proj RM, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := ProofShape.liftN_lam_inv E
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', RB, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA RB, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := ProofShape.liftN_forallE_inv E
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩

end Lean4Lean.VEnv.Strengthening
