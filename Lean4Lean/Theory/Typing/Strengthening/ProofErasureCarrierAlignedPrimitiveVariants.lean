import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordVariants
import Lean4Lean.Theory.Typing.Strengthening.StructureLevelCompatibility
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIota

/-! # Universe variants of concrete erased primitives

Typed universe variants preserve declaration unfolding, projection selection and
visible registered pattern computation. Declaration bodies use their proved
level compatibility; concrete pattern checks are rebuilt from an original typed
match. No primitive unfolding or carrier conversion oracle is postulated.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

private theorem variant_app_inv (H : StructuralVariant (.app f x) b) :
    ∃ g y, b = .app g y ∧ StructuralVariant f g ∧ StructuralVariant x y := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app HF HX => exact ⟨_, _, rfl, HF, HX⟩

private theorem variant_proj_inv (H : StructuralVariant (.proj s i a) b) :
    ∃ m, b = .proj s i m ∧ StructuralVariant a m := by
  cases H with
  | refl => exact ⟨_, rfl, .refl⟩
  | proj H => exact ⟨_, rfl, H⟩

private theorem variant_lam_inv (H : StructuralVariant (.lam A a) b) :
    ∃ D c, b = .lam D c ∧ StructuralVariant A D ∧ StructuralVariant a c := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | lam HA H => exact ⟨_, _, rfl, HA, H⟩

private theorem variant_forallE_inv (H : StructuralVariant (.forallE A B) b) :
    ∃ D C, b = .forallE D C ∧ StructuralVariant A D ∧ StructuralVariant B C := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | forallE HA HB => exact ⟨_, _, rfl, HA, HB⟩

namespace ProofShape
/-- Structural variants of a head and all captures give a variant spine. -/
theorem StructuralVariant.mkApps_pair (H : StructuralVariant f g)
    (HA : List.Forall₂ StructuralVariant args args') :
    StructuralVariant (mkApps f args) (mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact H
  | cons HX _ ih => exact ih (.app H HX)

/-- A visible pattern match survives structural universe variation. The root
universes remain equivalent and every capture has a corresponding variant. -/
theorem Matches.variant (HM : Matches p a ls captures) (V : StructuralVariant a b) :
    ∃ ls' captures', Matches p b ls' captures' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧
      ∀ i, StructuralVariant (captures i) (captures' i) := by
  induction HM generalizing b with
  | const =>
    cases V with
    | refl => exact ⟨_, nofun, .const, .rfl (fun _ _ => by rfl), nofun⟩
    | const HL => exact ⟨_, nofun, .const, HL, nofun⟩
  | var HM ih =>
    obtain ⟨g, y, rfl, VF, VX⟩ := variant_app_inv V
    obtain ⟨ls', caps', HM', HL, HC⟩ := ih VF
    refine ⟨ls', _, .var HM', HL, ?_⟩
    intro i
    cases i with
    | none => exact VX
    | some i => exact HC i
  | app HF HX ihf ihx =>
    obtain ⟨g, y, rfl, VF, VX⟩ := variant_app_inv V
    obtain ⟨ls', caps', HF', HL, HCF⟩ := ihf VF
    obtain ⟨ls'', caps'', HX', _, HCX⟩ := ihx VX
    refine ⟨ls', _, .app HF' HX', HL, ?_⟩
    intro i
    cases i with
    | inl i => exact HCF i
    | inr i => exact HCX i
end ProofShape

variable [Params]

private theorem match_levels_wf {p : Pattern} {captures : p.Path → VExpr} (HM : p.Matches e ls captures)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∀ l ∈ ls, l.WF univs := by
  induction HM generalizing T with
  | const =>
    obtain ⟨_, _, hw, _⟩ := ht.const_inv henv hΓ
    exact hw
  | var _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact ih hf
  | app _ _ ihf _ =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact ihf hf

/-- Declaration and projection primitives simulate at a typed structural
variant. Sound, universe-compatible declarations may be recursive and their
right-hand sides need not normalize. -/
theorem proofErase_carrier_aligned_primitive_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (R : Primitive D a out) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (V : StructuralVariant a (proofErase Γ e)) :
    ∃ out', Primitive D (proofErase Γ e) out' ∧ StructuralVariant out out' := by
  cases R with
  | delta HD =>
    have VC : StructuralVariant (ProofShape.mkApps (.const _ _) []) (proofErase Γ e) := V
    obtain ⟨ls', args', EE, HL, HP⟩ := VC.constant_spine
    cases HP
    obtain rfl := erase_const_inv EE
    obtain ⟨_, _, hw, _⟩ := ht.const_inv henv hΓ
    obtain ⟨rhs', HD', HV⟩ := hlevels HD hw HL
    obtain ⟨_, HR⟩ := hs [] _ _ _ HD
    exact ⟨_, EE ▸ .delta HD', proofErase_carrier_aligned_level_variant HV (by trivial) HR.hasType.2⟩
  | @projIota s info args i ls field hi hlen hget =>
    obtain ⟨m, EE, VM⟩ := variant_proj_inv V
    obtain ⟨ls', args', EM, _, HA⟩ := VM.constant_spine
    obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
    have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
    refine ⟨args'[info.nparams + i]'hj', ?_, ?_⟩
    · rw [EE, EM]
      exact .projIota hi (HA.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj')
    · rw [← HE]
      exact HA.getElem_of _ hj hj'

/-- Concrete selecting and capture-application rules survive universe
variation. The original actual source supplies an enabled check; the concrete
rule reconstructs that check at the new equivalent universe instance. -/
theorem proofErase_carrier_aligned_capture_variant
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : CapturePrimitive a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a) (V : StructuralVariant a b) :
    ∃ out', CapturePrimitive b out' ∧ StructuralVariant out out' := by
  cases R with
  | select hp hc hm =>
    obtain ⟨ls', caps', HM', HL, HC⟩ := hm.variant V
    obtain ⟨original, HM, _⟩ := proofErase_pattern_match_inv (Γ := Γ) (e := e) (by simpa only [Ee] using hm)
    exact ⟨_, .select hp (concrete_check_levels (hcon hp) HL (hc hΓ HM ht)) HM', HC _⟩
  | apply hp hc hm =>
    obtain ⟨ls', caps', HM', HL, HC⟩ := hm.variant V
    obtain ⟨original, HM, _⟩ := proofErase_pattern_match_inv (Γ := Γ) (e := e) (by simpa only [Ee] using hm)
    exact ⟨_, .apply hp (concrete_check_levels (hcon hp) HL (hc hΓ HM ht)) HM', .app (HC _) (HC _)⟩

/-- Visible fixed-template iota rules preserve structural variants, including
the template's own universe annotations and every proof-erased capture. Both
actual matched endpoints provide the well-formed universe instances. -/
theorem proofErase_carrier_aligned_template_variant
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : TemplatePrimitive a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (Ee : proofErase Γ e = a) (V : StructuralVariant a (proofErase Γ' e')) :
    ∃ out', TemplatePrimitive (proofErase Γ' e') out' ∧ StructuralVariant out out' := by
  cases R with
  | intro hp hc hr hm =>
    rename_i ls U p check paths captures rhs hclosed
    obtain ⟨ls', caps', HM', HL, HC⟩ := hm.variant V
    obtain ⟨original, HM, _⟩ := proofErase_pattern_match_inv (Γ := Γ) (e := e) (by simpa only [Ee] using hm)
    obtain ⟨original', HMt, _⟩ := proofErase_pattern_match_inv HM'
    have hw := match_levels_wf HM hΓ ht
    have hw' := match_levels_wf HMt hΓ' ht'
    have HV := LEquiv.instL_expr rhs hw hw' HL
    have hr' := ((HV.defeq henv (by trivial) ⟨_, hr⟩).of_l henv (by trivial) hr).hasType.2
    refine ⟨_, .intro hp (concrete_check_levels (hcon hp) HL (hc hΓ HM ht)) hr' HM', ?_⟩
    apply (proofErase_carrier_aligned_level_variant HV (by trivial) hr).mkApps_pair
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map]
    exact HC _

/-- All context-independent concrete iota primitives simulate across typed
structural variants. This includes delta, projection, quotient capture rules
and arbitrary registered closed RHS templates. -/
theorem proofErase_carrier_aligned_iota_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ErasedIotaPrimitive D a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (Ee : proofErase Γ e = a) (V : StructuralVariant a (proofErase Γ' e')) :
    ∃ out', ErasedIotaPrimitive D (proofErase Γ' e') out' ∧ StructuralVariant out out' := by
  rcases R with (R | R) | R
  · obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_primitive_variant hs hlevels R hΓ' ht' V
    exact ⟨out', .inl (.inl R'), V'⟩
  · obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_capture_variant hcon R hΓ ht Ee V
    exact ⟨out', .inl (.inr R'), V'⟩
  · obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_template_variant hcon R hΓ hΓ' ht ht' Ee V
    exact ⟨out', .inr R', V'⟩

end Lean4Lean.VEnv.Strengthening
