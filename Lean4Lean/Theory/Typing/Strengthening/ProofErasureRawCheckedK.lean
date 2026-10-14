import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction

/-! # Recursive K computation guarded by lambda checking

Common-type lambda checking feeds back into computation through an oracle-free,
substitution-stable fragment. Every finite stage descends and retains all earlier
compared-K stages. No declarative comparison completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
namespace ProofShape

/-- A raw checking certificate guards the two canonical Eq endpoints. -/
inductive RawCheckedKPrimitive (Step : ProofShape → ProofShape → Prop) : ProofShape → ProofShape → Prop where
  | intro : RawCheckedCompare Step true a b → RawCheckedKPrimitive Step (eqRec v w α a M m b p) m

/-- Checking guards weaken with predecessor computations. -/
theorem RawCheckedKPrimitive.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : RawCheckedKPrimitive Step e out) : RawCheckedKPrimitive Step (e.liftN n k) (out.liftN n k) := by
  cases H with
  | intro HC =>
    simpa only [eqRec, ProofShape.liftN] using
      (RawCheckedKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (HC.liftN hstep (n := n) (k := k)))

/-- Checking guards substitute without recovery assumptions on raw images. -/
theorem RawCheckedKPrimitive.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : RawCheckedKPrimitive Step e out) : RawCheckedKPrimitive Step (e.subst σ) (out.subst σ) := by
  cases H with
  | intro HC =>
    simpa only [eqRec, ProofShape.subst] using
      (RawCheckedKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (HC.subst hstep (σ := σ)))
end ProofShape

/-- Typed source inversion supplies the common endpoint type required by the
checking guard; its domain omissions therefore remain sound below insertion. -/
theorem erased_rawChecked_K_descent (heq : env.HasCanonicalEq) (hstep : ErasedPrimitiveDescent Step) :
    ErasedPrimitiveDescent (ProofShape.RawCheckedKPrimitive Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | intro HC =>
    rw [← proofErase_liftN hΓ hΓ' W ht] at hsrc
    obtain ⟨α', a', M', m', b', p', hs, _, Ha, _, Hm, Hb, _⟩ := proofErase_eqRec_inv hsrc
    rw [← lift'_consN_skipN] at hs
    obtain ⟨α₀, a₀, M₀, m₀, b₀, p₀, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      lift'_eq_eqRecApp hs
    obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W ha] at Ha
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W hb] at Hb
    rw [← Ha, ← Hb] at HC
    have hab := (proofErase_rawChecked_compare_descend hstep hΓ hΓ' W ha hb HC).1 ⟨_, hα⟩
    have HH := eqRecApp_simAt henv heq hΓ hab T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at Hm
    exact ⟨m₀, HH, Hm⟩

/-- Each finite stage adds checking guards from its predecessor. -/
def ErasedRawCheckedKStage (D : PureObservation.Definitions) : Nat → ProofShape → ProofShape → Prop
  | 0 => ErasedIotaPrimitive D
  | stage+1 => fun a b => ErasedRawCheckedKStage D stage a b ∨
      ProofShape.RawCheckedKPrimitive (ErasedRawCheckedKStage D stage) a b

/-- Every finite mutually computation/comparison stage has typed descent. -/
theorem erased_rawChecked_K_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedPrimitiveDescent (ErasedRawCheckedKStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    exact R.elim (ih hΓ hΓ' W ht) (erased_rawChecked_K_descent heq ih hΓ hΓ' W ht)

/-- Same-stage weakening of checking-guarded K computation. -/
theorem erased_rawChecked_K_stage_liftN : ∀ stage {a b n k}, ErasedRawCheckedKStage D stage a b →
    ErasedRawCheckedKStage D stage (a.liftN n k) (b.liftN n k) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_liftN H
  | succ stage ih =>
    intro a b n k H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.liftN ih))

/-- Guarded recursive comparison stages substitute without increasing the bound. -/
theorem erased_rawChecked_K_stage_subst : ∀ stage {a b} {σ : ProofShape.Subst},
    ErasedRawCheckedKStage D stage a b → ErasedRawCheckedKStage D stage (a.subst σ) (b.subst σ) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_subst H
  | succ stage ih =>
    intro a b σ H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.subst ih))

/-- Every earlier compared-K stage embeds at the same finite stage. -/
theorem erased_compared_K_stage_rawChecked : ∀ stage {a b}, ErasedComparedKStage D stage a b →
    ErasedRawCheckedKStage D stage a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro HC => exact .inr (.intro (.base (HC.mono ih)))

/-- Ambient reflection uses the zero-length insertion case of checked descent. -/
theorem proofErase_rawChecked_compare_reflect (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs Γ b B)
    (H : ProofShape.RawCheckedCompare Step mode (proofErase Γ a) (proofErase Γ b)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) :=
  proofErase_rawChecked_compare_descend hstep hΓ hΓ (Ctx.LiftN.zero []) ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using H)

/-- Raw substitution retraction gives arbitrary-thinning descent for every
finite checking stage, without recovery of the retraction images. -/
theorem proofErase_rawChecked_K_thinning (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.RawCheckedCompare (ErasedRawCheckedKStage D stage) mode
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ))) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  rw [proofErase_lift' hΓ hΓ' W ha, proofErase_lift' hΓ hΓ' W hb] at H
  exact proofErase_rawChecked_compare_reflect (erased_rawChecked_K_stage_descent heq hs stage)
    hΓ ha hb (ProofShape.relation_lift'_reflect
      (fun _ H => H.subst (fun H => erased_rawChecked_K_stage_subst stage H)) H)

/-- An actual typed Eq.rec source uses a raw checking guard at the next stage. -/
theorem proofErase_rawChecked_K_forward (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.RawCheckedCompare (ErasedRawCheckedKStage D stage) true
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compute (ErasedRawCheckedKStage D (stage+1))
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_rawChecked_compare_reflect (erased_rawChecked_K_stage_descent heq hs stage)
    hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    exact .base (.inr (.intro HC))

end Lean4Lean.VEnv.Strengthening
