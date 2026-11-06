import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicSubstitutionReflection

/-! # Atomic substitution creates no ordinary erased primitive

Visible matching reflects through atomic substitutions. Delta bodies and fixed
templates are closed, and projection/capture rules select the corresponding
original arguments. This covers the entire ordinary core without source typing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- A visible pattern after atomic substitution comes from a visible pattern
before substitution, with exactly corresponding captures. -/
theorem ProofShape.Matches.atomic_subst_inv
    (H : AtomicSubstitution σ) (HM : ProofShape.Matches p (e.subst σ) ls captures) :
    ∃ captures₀, ProofShape.Matches p e ls captures₀ ∧ ∀ i, (captures₀ i).subst σ = captures i := by
  generalize E : e.subst σ = source at HM
  induction HM generalizing e with
  | const =>
    obtain rfl := H.const_inv E
    exact ⟨nofun, .const, nofun⟩
  | var HM ih =>
    obtain ⟨f, a, rfl, EF, EA⟩ := H.app_inv E
    obtain ⟨caps, HC, EC⟩ := ih EF
    refine ⟨_, .var HC, ?_⟩
    intro i
    cases i with
    | none => exact EA
    | some i => exact EC i
  | app HF HA ihF ihA =>
    obtain ⟨f, a, rfl, EF, EA⟩ := H.app_inv E
    obtain ⟨cf, HF, EF⟩ := ihF EF
    obtain ⟨ca, HA, EA⟩ := ihA EA
    refine ⟨_, .app HF HA, ?_⟩
    intro i
    cases i with
    | inl i => exact EF i
    | inr i => exact EA i

variable [Params]

/-- Delta and saturated projection roots reflect through atomic images. -/
theorem ProofShape.Primitive.atomic_subst_inv
    (H : AtomicSubstitution σ) (R : ProofShape.Primitive D (e.subst σ) out) :
    ∃ e', ProofShape.Primitive D e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  cases R with
  | delta HD =>
    obtain rfl := H.const_inv E
    exact ⟨_, .delta HD, proofErase_closed_subst (D.closed HD)⟩
  | projIota hi hl hg =>
    obtain ⟨m, rfl, EM⟩ := H.proj_inv E
    obtain ⟨args, rfl, rfl⟩ := H.const_spine_inv EM
    rw [List.getElem?_map] at hg
    obtain ⟨field, hget, Efield⟩ := Option.map_eq_some_iff.mp hg
    exact ⟨field, .projIota hi (by simpa only [List.length_map] using hl) hget, Efield⟩

/-- Selecting and capture-application roots reflect with the same registered
rule and universe check; no new match can be introduced by an atomic image. -/
theorem ProofShape.CapturePrimitive.atomic_subst_inv
    (H : AtomicSubstitution σ) (R : CapturePrimitive (e.subst σ) out) :
    ∃ e', CapturePrimitive e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  cases R with
  | select hp hc hm =>
    obtain ⟨caps, HM, EC⟩ := (E.symm ▸ hm).atomic_subst_inv H
    exact ⟨_, .select hp hc HM, EC _⟩
  | apply hp hc hm =>
    obtain ⟨caps, HM, EC⟩ := (E.symm ▸ hm).atomic_subst_inv H
    exact ⟨_, .apply hp hc HM, by simp only [ProofShape.subst, EC]⟩

/-- Stored templates remain closed while reflected captures supply the exact
pre-substitution reduct, even when the template itself computes forever. -/
theorem ProofShape.TemplatePrimitive.atomic_subst_inv
    (H : AtomicSubstitution σ) (R : TemplatePrimitive (e.subst σ) out) :
    ∃ e', TemplatePrimitive e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  cases R with
  | intro hp hc ht hm =>
    obtain ⟨caps, HM, EC⟩ := (E.symm ▸ hm).atomic_subst_inv H
    refine ⟨_, .intro hp hc ht HM, ?_⟩
    simp only [ProofShape.subst_mkApps,
      proofErase_closed_subst (ht.closedN' henv.ordered.closed (by trivial)).1,
      List.map_map, Function.comp_def, EC]

/-- Every ordinary erased primitive after atomic substitution is the exact
image of an ordinary primitive before substitution. -/
theorem erased_iota_primitive_atomic_subst_inv
    (H : AtomicSubstitution σ) (R : ErasedIotaPrimitive D (e.subst σ) out) :
    ∃ e', ErasedIotaPrimitive D e e' ∧ e'.subst σ = out := by
  rcases R with (R | R) | R
  · obtain ⟨e', R', E⟩ := R.atomic_subst_inv H
    exact ⟨e', .inl (.inl R'), E⟩
  · obtain ⟨e', R', E⟩ := R.atomic_subst_inv H
    exact ⟨e', .inl (.inr R'), E⟩
  · obtain ⟨e', R', E⟩ := R.atomic_subst_inv H
    exact ⟨e', .inr R', E⟩

/-- Entire ordinary-core histories reflect through atomic substitution, with
the same exact endpoint after substitution. No typing or confluence is needed. -/
theorem ProofShape.Compute.iota_atomic_subst_inv
    (H : AtomicSubstitution σ) (R : ProofShape.Compute (ErasedIotaPrimitive D) (e.subst σ) out) :
    ∃ e', ProofShape.Compute (ErasedIotaPrimitive D) e e' ∧ e'.subst σ = out :=
  R.atomic_subst_inv (fun H R => erased_iota_primitive_atomic_subst_inv H R) H

end Lean4Lean.VEnv.Strengthening
