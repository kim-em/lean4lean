import Lean4Lean.Theory.Typing.Strengthening.ProofErasureK

/-! # Weakening finite erased computation

Raw binder insertion preserves the erased rules, including the finite-stage
endpoint certificates of canonical Eq computation. Proof markers stay closed;
no typed representative or context assumption is needed for this direction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Independent binder insertions commute in erased syntax. -/
theorem liftN_comm (e : ProofShape) (n m k j : Nat) (h : j ≤ k) :
    (e.liftN n k).liftN m j = (e.liftN m j).liftN n (k + m) := by
  induction e generalizing k j with simp [liftN, *]
  | bvar i =>
    simp only [liftVar]
    by_cases h1 : i < k <;> by_cases h2 : i < j <;>
      simp [h1, h2] <;> (try split) <;> (try split) <;> omega
  | lam _ _ _ ih | forallE _ _ _ ih => rw [Nat.add_right_comm]

/-- Erased substitution commutes with insertion above its argument position. -/
theorem liftN_instN (e a : ProofShape) (n k j : Nat) :
    (e.inst a j).liftN n (k+j) = (e.liftN n (k+j+1)).inst (a.liftN n k) j := by
  induction e generalizing j with simp [liftN, inst, *]
  | bvar i =>
    by_cases hij : i < j
    · simp [hij, liftVar_lt (show i < k+j+1 by omega), liftN,
        liftVar_lt (show i < k+j by omega)]
    by_cases heq : i = j
    · subst i
      simp only [Nat.lt_irrefl, if_false, if_true,
        liftVar_lt (show j < k+j+1 by omega)]
      exact (liftN_comm a n j k 0 (Nat.zero_le _)).symm
    · simp only [hij, heq, if_false]
      simp only [liftVar]
      split <;> rename_i hi
      · simp only [liftN, liftVar]
        rw [if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [liftN, liftVar]
        rw [if_neg (by omega)]
        congr 1
        omega
  | lam _ _ _ ih | forallE _ _ _ ih => simpa [Nat.add_assoc] using ih (j+1)

/-- Erased beta computation weakens at every insertion depth. -/
theorem BetaRed.liftN (H : BetaRed e out) : BetaRed (e.liftN n k) (out.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | @beta A b a =>
    simpa only [Nat.add_zero] using
      (liftN_instN b a n k 0).symm ▸ (BetaRed.beta (A := A.liftN n k)
        (b := b.liftN n (k+1)) (a := a.liftN n k))

/-- Weakening primitives suffices to weaken compatible finite computation. -/
theorem Compute.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : Compute Step e out) : Compute Step (e.liftN n k) (out.liftN n k) := by
  induction H generalizing k with
  | base h => exact .base (hstep h)
  | beta h => exact .beta h.liftN
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

/-- Insertion acts pointwise on application spines. -/
theorem liftN_mkApps (f : ProofShape) (args : List ProofShape) :
    (mkApps f args).liftN n k = mkApps (f.liftN n k) (args.map (·.liftN n k)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- Visible matching survives insertion, with every capture inserted equally. -/
theorem Matches.liftN (H : Matches p e ls captures) :
    Matches p (e.liftN n k) ls (fun i => (captures i).liftN n k) := by
  induction H with
  | @const c ls =>
    have congr_captures {p : Pattern} {e : ProofShape} {ls : List VLevel} {c d : p.Path → ProofShape}
        (H : Matches p e ls c) (hc : ∀ i, c i = d i) : Matches p e ls d := by
      cases funext hc
      exact H
    apply congr_captures (Matches.const (c := c) (ls := ls))
    intro i
    exact nomatch i
  | @var f f' levels captures a H ih =>
    have hh : (fun i => (Option.elim i a captures).liftN n k) =
        (fun i => Option.elim i (a.liftN n k) (fun j => (captures j).liftN n k)) := by
      funext i
      cases i <;> rfl
    exact hh.symm ▸ Matches.var (a := a.liftN n k) ih
  | @app f f' levels captures a a' levels' captures' Hf Ha ihf iha =>
    have hh : (fun i => (Sum.elim captures captures' i).liftN n k) =
        Sum.elim (fun j => (captures j).liftN n k) (fun j => (captures' j).liftN n k) := by
      funext i
      cases i <;> rfl
    exact hh.symm ▸ Matches.app ihf iha
end ProofShape

variable [Params]

/-- Closed declaration and saturated projection primitives weaken syntactically. -/
theorem ProofShape.Primitive.liftN (H : ProofShape.Primitive D e out) :
    ProofShape.Primitive D (e.liftN n k) (out.liftN n k) := by
  cases H with
  | delta hd =>
    rw [proofErase_closed_liftN ((D.closed hd).mono (Nat.zero_le k))]
    exact .delta hd
  | projIota hi hl hg =>
    simp only [ProofShape.liftN, ProofShape.liftN_mkApps]
    apply ProofShape.Primitive.projIota hi (by simpa only [List.length_map] using hl)
    simp only [List.getElem?_map, hg, Option.map_some]

/-- Capture selectors and applications retain their checks and shifted matches. -/
theorem ProofShape.CapturePrimitive.liftN (H : ProofShape.CapturePrimitive e out) :
    ProofShape.CapturePrimitive (e.liftN n k) (out.liftN n k) := by
  cases H with
  | select hp hc hm => exact .select hp hc hm.liftN
  | apply hp hc hm => exact .apply hp hc hm.liftN

/-- Closed RHS templates keep their head erasure and shift only the captures. -/
theorem ProofShape.TemplatePrimitive.liftN (H : ProofShape.TemplatePrimitive e out) :
    ProofShape.TemplatePrimitive (e.liftN n k) (out.liftN n k) := by
  cases H with
  | intro hp hc ht hm =>
    have hcl := (ht.closedN' henv.ordered.closed (by trivial)).1
    rw [ProofShape.liftN_mkApps, proofErase_closed_liftN (hcl.mono (Nat.zero_le k))]
    simp only [List.map_map, Function.comp_def]
    exact .intro hp hc ht hm.liftN

/-- Every primitive of the concrete visible fragment weakens. -/
theorem erased_iota_primitive_liftN (H : ErasedIotaPrimitive D a b) :
    ErasedIotaPrimitive D (a.liftN n k) (b.liftN n k) := by
  rcases H with (H | H) | H
  · exact .inl (.inl H.liftN)
  · exact .inl (.inr H.liftN)
  · exact .inr H.liftN

omit [Params] in
/-- A K guard weakens whenever its preceding-stage computations weaken. -/
theorem ProofShape.KPrimitive.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : ProofShape.KPrimitive Step e out) :
    ProofShape.KPrimitive Step (e.liftN n k) (out.liftN n k) := by
  cases H with
  | intro Ha Hb =>
    simpa only [ProofShape.eqRec, ProofShape.liftN] using
      (ProofShape.KPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (Ha.liftN hstep (n := n) (k := k)) (Hb.liftN hstep (n := n) (k := k)))

/-- All finite erased K stages weaken, including their nested guard paths. -/
theorem erased_K_stage_liftN : ∀ stage {a b n k}, ErasedKStage D stage a b →
    ErasedKStage D stage (a.liftN n k) (b.liftN n k) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_liftN H
  | succ stage ih =>
    intro a b n k H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.liftN ih))

/-- Finite compatible erased computations keep their stage under insertion. -/
theorem erased_K_compute_liftN (H : ProofShape.Compute (ErasedKStage D stage) a b) :
    ProofShape.Compute (ErasedKStage D stage) (a.liftN n k) (b.liftN n k) :=
  H.liftN (erased_K_stage_liftN stage)

end Lean4Lean.VEnv.Strengthening
