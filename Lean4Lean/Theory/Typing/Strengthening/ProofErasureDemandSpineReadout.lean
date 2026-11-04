import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentObservationTransport

/-! # Operational readout of neutral heads with ignored arguments -/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)

/-- Atomic observations may denote any beta-predecessor-closed predicate.
Function observations keep their usual finite argument demands. -/
def Realizes (P : ProofShape → Prop) (e : ProofShape) : Ob → Prop
  | .pi => P e
  | .sort => False
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes P a key) → Realizes P (.app e a) result
termination_by o => sizeOf o

variable {P : ProofShape → Prop}

/-- Operational predicates closed under beta predecessors extend to all
finite function demands. -/
theorem Realizes.beta_back
    (hP : ∀ {e e'}, ProofShape.BetaRed e e' → P e' → P e)
    (R : ProofShape.BetaRed e e') (H : Realizes P e' o) : Realizes P e o := by
  cases o with
  | pi =>
    simp only [Realizes] at H ⊢
    exact hP R H
  | sort => simp only [Realizes] at H
  | app keys result =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back hP (.app R .refl) (H a ha)
termination_by sizeOf o

variable [Params]

/-- Dependent typing decorations do not constrain operational substitution:
supplying the free demands suffices for every raw realizing substitution. -/
theorem Obs.realizes (H : Obs Δ S e t o)
    (hP : ∀ {e e'}, ProofShape.BetaRed e e' → P e' → P e)
    (hσ : ∀ i t key, S i t key → Realizes P (σ i) key) :
    Realizes P (e.subst σ) o := by
  induction H generalizing σ with
  | var _ _ h => exact hσ _ _ _ h
  | app _ _ _ ihf ihx =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => ihx key hk hσ)
  | @lam Δ D b A B keys S o HT HK HB ih =>
    simp only [Realizes]
    intro a ha
    have H := ih (σ := σ.cons a) (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back hP (E ▸ (ProofShape.BetaRed.beta (A := D.subst σ))) H

/-- A head demand consumes a fixed number of arguments without inspecting
them. The result alone is observed. -/
def spineDemand : Nat → Ob
  | 0 => .pi
  | n+1 => .app [] (spineDemand n)

/-- The corresponding dependent type profile ignores all parameter domains. -/
def spineProfile : Nat → Profile
  | 0 => .sort
  | n+1 => .arrow .ignored (spineProfile n)

omit [Params] in
/-- The fixed head demand is valid at every arity. -/
theorem spineDemand_valid (n : Nat) : Demand (spineProfile n) (spineDemand n) := by
  induction n with
  | zero => exact .sort
  | succ n ih => exact .fn (by simp) ih

/-- The operational result retains the variable head and exact spine length,
while permitting arbitrary argument expressions at the exposed endpoint. -/
def HeadResult (i n : Nat) (e : ProofShape) : Prop :=
  ∃ args, args.length = n ∧ ProofShape.BetaRed e (ProofShape.mkApps (.bvar i) args)

omit [Params] in
/-- Completing the remaining applications realizes a head demand. -/
theorem head_spine_realizes (h : args.length + k = n) :
    Realizes (HeadResult i n) (ProofShape.mkApps (.bvar i) args) (spineDemand k) := by
  induction k generalizing args with
  | zero =>
    simp only [spineDemand, Realizes, HeadResult]
    exact ⟨args, by simpa using h, .refl⟩
  | succ k ih =>
    simp only [spineDemand, Realizes]
    intro a _
    have R := ih (args := args ++ [a]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa only [ProofShape.mkApps_snoc] using R

/-- An observation supplied only by one free head reads that exact head and
arity after beta cleanup. The exposed arguments need no native certificates. -/
theorem Obs.head_readout
    (H : Obs Δ S e t .pi)
    (hS : ∀ j t key, S j t key → j = i ∧ key = spineDemand n) : HeadResult i n e := by
  have HR := H.realizes (P := HeadResult i n) (σ := ProofShape.Subst.id)
    (fun R H => by obtain ⟨args, hn, RB⟩ := H; exact ⟨args, hn, R.trans RB⟩)
    (fun j t key hj => by
      obtain ⟨rfl, rfl⟩ := hS j t key hj
      exact head_spine_realizes (args := []) (by simp))
  simpa only [ProofShape.subst_id, Realizes] using HR

end Lean4Lean.VEnv.Strengthening.DemandProfile
