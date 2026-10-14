import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSimultaneous

/-! # Visible registered pattern matching after proof erasure

A visible erased match reconstructs the original match and all captured terms.
Selectors and applications of two captures then replay directly. The latter
includes the actual quotient-lift RHS. Proof-valued constructor majors erase to
markers and are intentionally not asserted to have a visible match.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute CheckFromTyping)
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- Match the retained constant/application structure of a registered pattern.
A captured argument may be a proof marker, but a matched constant may not. -/
inductive Matches : (p : Pattern) → ProofShape → List VLevel → (p.Path → ProofShape) → Prop
  | const : Matches (.const c) (.const c ls) ls nofun
  | var : Matches f f' levels captures → Matches (.var f) (.app f' a) levels (·.elim a captures)
  | app : Matches f f' levels captures → Matches a a' levels' captures' →
      Matches (.app f a) (.app f' a') levels (Sum.elim captures captures')

/-- A visible match never matches the proof marker as its whole source. -/
theorem Matches.ne_proof (H : Matches p e ls captures) : e ≠ .proof := by
  cases H <;> simp
end ProofShape

variable [Params]

/-- Every visible erased match lifts to a literal original pattern match.
Proof markers in capture positions retain their original proof terms. -/
theorem proofErase_pattern_match_inv
    (H : ProofShape.Matches p (proofErase Γ e) ls captures) :
    ∃ original, p.Matches e ls original ∧ ∀ i, proofErase Γ (original i) = captures i := by
  generalize hsrc : proofErase Γ e = source at H
  induction H generalizing e with
  | const =>
    obtain rfl := erase_const_inv hsrc
    exact ⟨nofun, .const, nofun⟩
  | var H ih =>
    obtain ⟨f, a, rfl, _, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨original, hm, he⟩ := ih Hf
    refine ⟨_, .var hm, ?_⟩
    intro i
    cases i with
    | none => exact Ha
    | some i => exact he i
  | app Hf Ha ihf iha =>
    obtain ⟨f, a, rfl, _, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨cf, hf, ef⟩ := ihf Hf
    obtain ⟨ca, ha, ea⟩ := iha Ha
    refine ⟨_, .app hf ha, ?_⟩
    intro i
    cases i with
    | inl i => exact ef i
    | inr i => exact ea i

namespace ProofShape
/-- Registered visible patterns with selecting or binary application RHSs.
Uniform checks come from source typing, not from erased terms' invented types. -/
inductive CapturePrimitive : ProofShape → ProofShape → Prop where
  | select {p : Pattern} {check : p.Check} {path : p.Path} {captures : p.Path → ProofShape} :
      Pat p (.var path, check) → CheckFromTyping env univs p (.var path, check) ls →
      Matches p source ls captures → CapturePrimitive source (captures path)
  | apply {p : Pattern} {check : p.Check} {f a : p.Path} {captures : p.Path → ProofShape} :
      Pat p (.app (.var f) (.var a), check) →
      CheckFromTyping env univs p (.app (.var f) (.var a), check) ls →
      Matches p source ls captures → CapturePrimitive source (.app (captures f) (captures a))
end ProofShape

/-- Selector and capture-application patterns replay from every typed source.
The source is non-proof because its matching shape remains visible. -/
theorem erased_capture_patterns_replay (hs : D.Sound env univs) :
    ErasedPrimitiveReplay D ProofShape.CapturePrimitive := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | select hp hc hm =>
    rw [← hsrc] at hm
    obtain ⟨original, HM, HE⟩ := proofErase_pattern_match_inv hm
    exact ⟨_, .pattern hp HM hc, HE _⟩
  | apply hp hc hm =>
    rw [← hsrc] at hm
    have hn : ¬ IsProof Γ e := fun h => hm.ne_proof (proofErase_eq_proof.2 h)
    obtain ⟨original, HM, HE⟩ := proofErase_pattern_match_inv hm
    have R' := PatternCompute.pattern (D := D) hp HM hc
    have HEq := R'.simAt hs hΓ T ht
    have hn' := mt (isProof_congr hΓ HEq).2 hn
    refine ⟨_, R', ?_⟩
    simp only [Pattern.RHS.apply] at hn' ⊢
    simp only [proofErase, if_neg hn', HE]

/-- The genuine quotient rule is an application of its minor to its data
capture. Its nonzero universe guard and registered typing check are retained. -/
theorem erased_quotient_step (hr : QuotRegistered env)
    (hp : Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hnz : ¬ ((VLevel.param 0).inst ls ≈ .zero))
    (hm : ProofShape.Matches quotPattern source ls captures) :
    ProofShape.CapturePrimitive source
      (.app (captures (.inl (some none))) (captures (.inr none))) :=
  .apply hp (fun hΓ HM ht => PureObservation.quot_check_of_typed henv hΓ hr HM ht hnz) hm

omit [Params] in
/-- A registered quotient supplies the rule-table membership itself when using
the actual confluence parameters of a well-formed environment. -/
theorem erased_quotient_step_concrete {E : VEnv} (hE : E.WF) (hr : QuotRegistered E)
    (hnz : ¬ ((VLevel.param 0).inst ls ≈ .zero))
    (hm : ProofShape.Matches quotPattern source ls captures) :
    @ProofShape.CapturePrimitive (hE.params U) source
      (.app (captures (.inl (some none))) (captures (.inr none))) := by
  letI := hE.params U
  exact erased_quotient_step hr (.inr (.inl (.intro hr))) hnz hm

/-- The concrete erasure fragment retains earlier primitives and adds visible
registered capture rules, including quotient computation. -/
def ErasedRegisteredPrimitive (D : Definitions) (a b : ProofShape) : Prop :=
  ProofShape.Primitive D a b ∨ ProofShape.CapturePrimitive a b

/-- Both primitive alternatives satisfy the same exact replay interface. -/
theorem erased_registered_replay (hs : D.Sound env univs) :
    ErasedPrimitiveReplay D (ErasedRegisteredPrimitive D) := by
  intro Γ e T out hΓ ht R
  exact R.elim (erased_primitives_replay hs hΓ ht) (erased_capture_patterns_replay hs hΓ ht)

/-- Common erased results using the concrete registered fragment descend
from independently typed original endpoints below arbitrary binder insertion. -/
theorem proofErase_registered_join_descend (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute (ErasedRegisteredPrimitive D) (proofErase Γ' (a.liftN n k)) out)
    (Rb : ProofShape.Compute (ErasedRegisteredPrimitive D) (proofErase Γ' (b.liftN n k)) out) :
    env.IsDefEq univs Γ a b T :=
  proofErase_compute_join_descend hs (erased_registered_replay hs) hΓ hΓ' W ha hb Ra Rb

end Lean4Lean.VEnv.Strengthening
