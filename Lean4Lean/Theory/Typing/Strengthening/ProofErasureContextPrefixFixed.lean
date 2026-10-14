import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextPrefixWitness
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSpineInversion

/-! # Fixedness of the partial-recursion composition candidates

A conservative syntactic test excludes beta and every full Eq.rec application.
Typed replay proves that erasures of terms passing this test are fixed by the
chosen beta/K fragment, including when some subterms collapse to proof markers.
-/
namespace Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- Every beta or full Eq.rec root is marked, regardless of its endpoint guard. -/
def rootRedex : VExpr → Bool
  | .app (.lam _ _) _ => true
  | .app (.app (.app (.app (.app (.app (.const ``Eq.rec _) _) _) _) _) _) _ => true
  | _ => false

/-- A decidable sufficient condition for fixedness in the selected fragment. -/
def normal (e : VExpr) : Bool := !rootRedex e && match e with
  | .app f a => normal f && normal a
  | .lam A b | .forallE A b => normal A && normal b
  | .proj _ _ m => normal m
  | _ => true

/-- The conservative test fixes every ordinary beta path. -/
theorem beta_fixed (R : VExpr.BetaRed e out) (hn : normal e = true) : out = e := by
  induction R with
  | refl => rfl
  | trans _ _ ih1 ih2 =>
    have E := ih1 hn
    exact (ih2 (E.symm ▸ hn)).trans E
  | beta => simp [normal, rootRedex] at hn
  | app _ _ ihf iha =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihf hn.2.1, iha hn.2.2]
  | lam _ _ ihA ihb | forallE _ _ ihA ihb =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihA hn.2.1, ihb hn.2.2]
  | proj _ ih =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ih hn.2]

variable [Params]

/-- A typed syntactically normal original has a fixed erasure. Original beta
replay handles markers; any primitive root would expose a forbidden full Eq.rec. -/
theorem erased_fixed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (hn : normal e = true) :
    ProofShape.ComputeFixed Step (proofErase Γ e) := by
  intro out R
  generalize HE : proofErase Γ e = source at R
  induction R generalizing Γ e T with
  | base R =>
    cases R with
    | intro H =>
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := proofErase_eqRec_inv HE
      simp [normal, rootRedex, eqRecApp] at hn
  | beta R =>
    obtain ⟨e', HB, EE⟩ := proofErase_beta_replay hΓ ht (HE ▸ R)
    obtain rfl := beta_fixed HB hn
    exact EE.symm.trans HE
  | trans R1 R2 ih1 ih2 =>
    have E := ih1 hΓ ht hn HE
    exact (ih2 hΓ ht hn (HE.trans E.symm)).trans E
  | app Rf Ra ihf iha =>
    obtain ⟨f, a, rfl, hp, Ef, Ea⟩ := erase_app_inv HE
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihf hΓ hf hn.2.1 Ef, iha hΓ ha hn.2.2 Ea]
  | proj Rm ih =>
    obtain ⟨m, rfl, hp, Em⟩ := erase_proj_inv HE
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    simp only [normal, Bool.and_eq_true] at hn
    rw [ih hΓ hm.hasType.2 hn.2 Em]
  | lam RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, hp, EA, Eb⟩ := erase_lam_inv HE
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihA hΓ hA hn.2.1 EA, ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb hn.2.2 Eb]
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, hp, EA, EB⟩ := erase_forallE_inv HE
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihA hΓ hA hn.2.1 EA, ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB hn.2.2 EB]

/-- Both candidate prefixes are fixed even though their eta-expanded applications
compute. This is the missing-prefix-step configuration tested by composition. -/
theorem prefixes_fixed (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    ProofShape.ComputeFixed Step (proofErase Γ (partialRec dependentMotive)) ∧
    ProofShape.ComputeFixed Step (proofErase Γ (partialRec constantMotive)) := by
  exact ⟨erased_fixed hΓ (dependent_typed heq) (by decide),
    erased_fixed hΓ (constant_typed heq hΓ) (by decide)⟩

end Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
