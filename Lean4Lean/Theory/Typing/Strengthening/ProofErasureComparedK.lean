import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

/-! # Canonical Eq computation guarded by recursive erased comparison

Endpoint comparison can use eta at common-typed subterms. Finite stages alternate
compatible computation and the two-mode comparison; every stage descends from
source typing below arbitrary binder insertion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- Common-mode endpoint comparison guards canonical Eq computation. -/
inductive ComparedKPrimitive (Step : ProofShape → ProofShape → Prop) : ProofShape → ProofShape → Prop where
  | intro : Compare Step true a b → ComparedKPrimitive Step (eqRec v w α a M m b p) m

/-- Enlarging the primitive relation enlarges compatible computation. -/
theorem Compute.mono (hstep : ∀ {a b}, Step a b → Step' a b)
    (H : Compute Step a b) : Compute Step' a b := by
  induction H with
  | base h => exact .base (hstep h)
  | beta h => exact .beta h
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

/-- Enlarging computation enlarges both recursive comparison modes. -/
theorem Compare.mono (hstep : ∀ {a b}, Step a b → Step' a b)
    (H : Compare Step mode a b) : Compare Step' mode a b := by
  induction H with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | etaL h => exact .etaL h
  | etaR h => exact .etaR h
  | etaLams _ h ih => exact .etaLams ih h
  | compute Ra Rb _ ih => exact .compute (Ra.mono hstep) (Rb.mono hstep) ih

/-- Earlier common-target guards are recursive comparisons ending in reflexivity. -/
theorem KPrimitive.compared (H : KPrimitive Step a b) : ComparedKPrimitive Step a b := by
  cases H with
  | intro Ha Hb => exact .intro (.compute Ha Hb .refl)

/-- Recursive endpoint guards weaken along with their predecessor computations. -/
theorem ComparedKPrimitive.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : ComparedKPrimitive Step e out) : ComparedKPrimitive Step (e.liftN n k) (out.liftN n k) := by
  cases H with
  | intro HC =>
    simpa only [eqRec, ProofShape.liftN] using
      (ComparedKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (HC.liftN hstep (n := n) (k := k)))

/-- Recursive endpoint guards survive arbitrary simultaneous substitution. -/
theorem ComparedKPrimitive.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : ComparedKPrimitive Step e out) : ComparedKPrimitive Step (e.subst σ) (out.subst σ) := by
  cases H with
  | intro HC =>
    simpa only [eqRec, ProofShape.subst] using
      (ComparedKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (HC.subst hstep (σ := σ)))
end ProofShape

variable [Params]

/-- Source inversion gives common endpoint types below. Recursive comparison
then validates K, even if its major has no visible constructor shape. -/
theorem erased_compared_K_descent (heq : env.HasCanonicalEq) (hstep : ErasedPrimitiveDescent Step) :
    ErasedPrimitiveDescent (ProofShape.ComparedKPrimitive Step) := by
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
    have hab := (proofErase_compare_descend hstep hΓ hΓ' W ha hb HC).1 ⟨_, hα⟩
    have HH := eqRecApp_simAt henv heq hΓ hab T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at Hm
    exact ⟨m₀, HH, Hm⟩

/-- Each stage adds K whose recursive guards use only the preceding stage. -/
def ErasedComparedKStage (D : PureObservation.Definitions) : Nat → ProofShape → ProofShape → Prop
  | 0 => ErasedIotaPrimitive D
  | stage+1 => fun a b => ErasedComparedKStage D stage a b ∨
      ProofShape.ComparedKPrimitive (ErasedComparedKStage D stage) a b

/-- Every finite mutually computation/comparison stage has typed descent. -/
theorem erased_compared_K_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedPrimitiveDescent (ErasedComparedKStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    exact R.elim (ih hΓ hΓ' W ht) (erased_compared_K_descent heq ih hΓ hΓ' W ht)

/-- The earlier common-target K stages embed at the same stage number. -/
theorem erased_K_stage_compared : ∀ stage {a b}, ErasedKStage D stage a b →
    ErasedComparedKStage D stage a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro Ha Hb => exact .inr (.intro (.compute (Ha.mono ih) (Hb.mono ih) .refl))

/-- Guarded recursive comparison stages weaken without increasing the bound. -/
theorem erased_compared_K_stage_liftN : ∀ stage {a b n k}, ErasedComparedKStage D stage a b →
    ErasedComparedKStage D stage (a.liftN n k) (b.liftN n k) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_liftN H
  | succ stage ih =>
    intro a b n k H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.liftN ih))

/-- Guarded recursive comparison stages substitute without increasing the bound. -/
theorem erased_compared_K_stage_subst : ∀ stage {a b} {σ : ProofShape.Subst},
    ErasedComparedKStage D stage a b → ErasedComparedKStage D stage (a.subst σ) (b.subst σ) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_subst H
  | succ stage ih =>
    intro a b σ H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.subst ih))

/-- The mutually enlarged recursive comparison still gives equality below
insertion at a supplied common endpoint type. -/
theorem proofErase_compared_K_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ProofShape.Compare (ErasedComparedKStage D stage) true
      (proofErase Γ' (a.liftN n k)) (proofErase Γ' (b.liftN n k))) :
    env.IsDefEq univs Γ a b T := by
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb] at H
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  exact ((proofErase_compare_descend (erased_compared_K_stage_descent heq hs stage)
    hΓ hΓ' W ha hb H).1 ⟨_, hT⟩).of_l henv hΓ ha

/-- An actual typed Eq.rec source computes forwards whenever its erased
endpoints have a recursive certificate. Whole-proof results give identity;
non-proof results use the next-stage primitive with all actual captures. -/
theorem proofErase_compared_K_forward (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.Compare (ErasedComparedKStage D stage) true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compute (ErasedComparedKStage D (stage+1))
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_compare_reflect (erased_compared_K_stage_descent heq hs stage)
    hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    exact .base (.inr (.intro HC))

/-- A typed endpoint and its eta expansion provide a certificate at every
stage. This uses the forward eta theorem and does not assume endpoint equality. -/
theorem proofErase_compared_K_eta (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    ProofShape.Compare (ErasedComparedKStage D stage) true
      (proofErase Γ f) (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) := by
  rcases proofErase_eta_forward hΓ hf with H | H
  · rw [H]; exact .refl
  · exact .etaR H

end Lean4Lean.VEnv.Strengthening
