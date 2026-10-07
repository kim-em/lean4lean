import Lean4Lean.Theory.Typing.ShapeModel.RuleValidNativeSem

/-!
# Proof fields of singleton eliminations are bottom

For the unread fields of a singleton-eliminating native rule (fields that do not occur as literal
indices of the constructor's result), the generated constructor typing makes the field type a
proposition in the context of the parameters and the earlier fields, in the header environment of
the installation. Under a valuation fitting the rule's binder telescope (parameters, motives,
minors, fields, the fields lifted over the motives and minors), the key of such a field is
therefore bottom:

* `Interp.liftN_iff`: interpretation of a lifted expression is interpretation under the valuation
  with the inserted keys removed;
* `Valuation.Fits.peel`, `Valuation.Fits.unlift`: a valuation fitting a telescope restricts to one
  fitting a prefix, and to one fitting the telescope with inserted binders removed;
* `proof_key_le_bot`: soundness of a proposition typing and proof irrelevance.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- The substitution performing `liftN n · k`. -/
def liftSubst (n k : Nat) : VExpr.Subst := fun i => .bvar (liftVar n i k)

theorem liftSubst_lift (n k : Nat) : (liftSubst n k).lift = liftSubst n (k + 1) := by
  funext i
  cases i with
  | zero => simp [VExpr.Subst.lift, liftSubst, liftVar]
  | succ i =>
    show VExpr.liftN 1 (.bvar (liftVar n i k)) = VExpr.bvar (liftVar n (i + 1) (k + 1))
    simp only [VExpr.liftN, VExpr.bvar.injEq]
    by_cases h : i < k
    · rw [liftVar_lt h, liftVar_le (Nat.zero_le i), liftVar_lt (show i + 1 < k + 1 by omega)]
      omega
    · rw [liftVar_le (show k ≤ i by omega), liftVar_le (Nat.zero_le _),
        liftVar_le (show k + 1 ≤ i + 1 by omega)]
      omega

theorem liftN_eq_subst (e : VExpr) (n k : Nat) : e.liftN n k = e.subst (liftSubst n k) := by
  induction e generalizing k with
  | bvar i => rfl
  | sort | const | elim => rfl
  | app f a ihf iha => simp only [VExpr.liftN, VExpr.subst, ihf, iha]
  | lam A B ihA ihB => simp only [VExpr.liftN, VExpr.subst, ihA, ihB, liftSubst_lift]
  | forallE A B ihA ihB => simp only [VExpr.liftN, VExpr.subst, ihA, ihB, liftSubst_lift]
  | proj s i e ih => simp only [VExpr.liftN, VExpr.subst, ih]

theorem Interp.liftN_iff {e : VExpr} {n k : Nat} {ρ : Valuation} {m : TShape} :
    Interp env ρ m (e.liftN n k) ↔ Interp env (fun i => ρ (liftVar n i k)) m e := by
  rw [liftN_eq_subst, Interp.subst]
  refine ⟨fun ⟨ρ', H, h⟩ => H.mono_l fun i => Interp.bvar_iff.1 (h i),
    fun H => ⟨_, H, fun i => Interp.bvar_iff.2 .rfl⟩⟩

theorem Valuation.Fits.cons_inv {Δ : List VExpr} {A : VExpr} {σ : Valuation}
    (W : Valuation.Fits env [] (A :: Δ) σ) :
    ∃ ρ x a, σ = ρ.push x ∧ Valuation.Fits env [] Δ ρ ∧
      (∀ {a}, Interp env ρ a A → ∃ a', a ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType .type) ∧
      Interp env ρ a A ∧ x.HasType a := by
  cases W with
  | cons W h1 h2 h3 => exact ⟨_, _, _, rfl, W, h1, h2, h3⟩

theorem Valuation.Fits.peel {Rest : List VExpr} :
    ∀ {Zs : List VExpr} {σ : Valuation}, Valuation.Fits env [] (Zs ++ Rest) σ →
      Valuation.Fits env [] Rest (fun k => σ (Zs.length + k))
  | [], σ, W => by simpa using W
  | Z :: Zs, σ, W => by
    obtain ⟨ρ, x, a, rfl, W', -⟩ := Valuation.Fits.cons_inv W
    have := Valuation.Fits.peel (Zs := Zs) W'
    have e : (fun k => (ρ.push x) ((Z :: Zs).length + k)) = fun k => ρ (Zs.length + k) := by
      funext k; rw [List.length_cons, show Zs.length + 1 + k = (Zs.length + k) + 1 by omega]; rfl
    rw [e]; exact this

/-- Removing binders inserted between a prefix `Rs` (innermost first, each lifted over the
inserted binders) and an outer context. -/
theorem Valuation.Fits.unlift {Ms Rest : List VExpr} :
    ∀ {Rs : List VExpr} {σ : Valuation},
      Valuation.Fits env [] (Rs.mapIdx (fun t R => R.liftN Ms.length (Rs.length - 1 - t)) ++
        Ms ++ Rest) σ →
      Valuation.Fits env [] (Rs ++ Rest) (fun i => σ (liftVar Ms.length i Rs.length))
  | [], σ, W => by
    have := Valuation.Fits.peel (Zs := Ms) (by simpa using W)
    simpa [liftVar, Nat.add_comm] using this
  | R :: Rs, σ, W => by
    simp only [List.mapIdx_cons, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero,
      List.cons_append] at W
    obtain ⟨ρ, x, a, rfl, W', h1, h2, h3⟩ := Valuation.Fits.cons_inv W
    have e : (fun i R => VExpr.liftN Ms.length R (Rs.length - (i + 1))) =
        fun i R => VExpr.liftN Ms.length R (Rs.length - 1 - i) := by
      funext i R; congr 1; omega
    rw [e] at W'
    have IH := Valuation.Fits.unlift (Rs := Rs) W'
    have hv : (fun i => (ρ.push x) (liftVar Ms.length i (Rs.length + 1))) =
        Valuation.push (fun i => ρ (liftVar Ms.length i Rs.length)) x := by
      funext i
      cases i with
      | zero =>
        show (ρ.push x) (liftVar Ms.length 0 (Rs.length + 1)) = x
        rw [liftVar_lt (by omega)]; rfl
      | succ i =>
        show (ρ.push x) (liftVar Ms.length (i + 1) (Rs.length + 1)) =
          ρ (liftVar Ms.length i Rs.length)
        by_cases h : i < Rs.length
        · rw [liftVar_lt (by omega), liftVar_lt h]; rfl
        · rw [liftVar_le (by omega), liftVar_le (by omega),
            show Ms.length + (i + 1) = (Ms.length + i) + 1 by omega]; rfl
    simp only [List.cons_append, List.length_cons]
    rw [hv]
    refine .cons IH (fun ha => ?_) (Interp.liftN_iff.1 h2) h3
    obtain ⟨a', h1', h2', h3'⟩ := h1 (Interp.liftN_iff.2 ha)
    exact ⟨a', h1', Interp.liftN_iff.1 h2', h3'⟩

end

theorem OnCtx.instL' {E : VEnv} {U U' : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ : List VExpr}, OnCtx Γ (E.IsType U) → OnCtx (Γ.map (·.instL ls)) (E.IsType U')
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨OnCtx.instL' hls h1, _, VEnv.HasType.instL hls h2⟩

theorem OnCtx.append_right' {P : List VExpr → VExpr → Prop} :
    ∀ {xs ys : List VExpr}, OnCtx (xs ++ ys) P → OnCtx ys P
  | [], _, h => h
  | _ :: xs, _, h => OnCtx.append_right' (xs := xs) h.1

theorem Good.of_parts {E E' : VEnv} (h : Good env E) (hd : ∀ df, E'.defeqs df → E.defeqs df)
    (he : ∀ {b s}, E'.eliminators b s → E.eliminators b s)
    (hp : ∀ {s info}, E'.projections s info → E.projections s info) : Good env E' :=
  letI := envSig env
  ⟨fun df h' => h.1 df (hd df h'), fun hb => h.2.1 (he hb), fun h' => h.2.2 (hp h')⟩

/-- A key fitting a proposition in a context typed in a good environment is bottom. -/
theorem proof_key_le_bot (H : env.WF) {E : VEnv} (hgood : Good env E) (hle : E ≤ env)
    (hE : E.Ordered) {U : Nat} {Γ : List VExpr} {A : VExpr} (hΓ : OnCtx Γ (E.IsType U))
    (hA : E.HasType U Γ A (.sort .zero)) (ls : List VLevel) :
    letI := envSig env
    ∀ {ρ : Valuation} {a x : TShape}, Valuation.Fits env [] (Γ.map (·.instL ls)) ρ →
      Interp env ρ a (A.instL ls) → x.HasType a → x ≤ .bot := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  intro ρ a x W ha hx
  obtain ⟨U', hU'⟩ := exists_levels_wf ls
  have hΓ' := OnCtx.instL' hU' hΓ
  have hA' := VEnv.HasType.instL hU' hA
  have D := VEnv.IsDefEq.strong hE hΓ' hA'
  have hS := (hgood.sound H hle hE D).left.sound
  obtain ⟨_, _, b1, -, b3, b4⟩ := hS W ha
  have b4' := TShape.HasType.mono_r b3.le_sort .sort b4
  exact b4'.proofIrrel (fun _ => rfl) (b4'.mono_r b1 hx)

end Lean4Lean.ShapeModel
