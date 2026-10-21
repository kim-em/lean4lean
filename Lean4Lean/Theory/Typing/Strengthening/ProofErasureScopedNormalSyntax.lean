import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine

/-! # Normality at the actual binder contexts

Primitive exclusion is needed only at the context of each occurrence. This
permits typed exclusion arguments under a specific binder, rather than asking
for exclusion at every unrelated raw context. A fixed eta function can then
be removed from a spine without any recovery premise on the consumed argument.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private compute_spine from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine

/-- Syntactic normality with each body checked under its actual annotation. -/
def ScopedNormalSyntax (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (e : ProofShape) : Prop :=
  (∀ out, ¬ Step Δ e out) ∧ match e with
  | .app f a => (∀ A b, f ≠ .lam A b) ∧ ScopedNormalSyntax Step Δ f ∧ ScopedNormalSyntax Step Δ a
  | .proj _ _ m => ScopedNormalSyntax Step Δ m
  | .lam A b | .forallE A b => ScopedNormalSyntax Step Δ A ∧ ScopedNormalSyntax Step (A :: Δ) b
  | _ => True

private theorem scoped_normal_no_step (H : ScopedNormalSyntax Step Δ e) : ¬ Step Δ e out := by
  cases e <;> exact H.1 out

/-- Scoped normality in particular excludes every beta redex. -/
theorem ScopedNormalSyntax.beta_normal (H : ScopedNormalSyntax Step Δ e) :
    NormalSyntax (fun _ _ => False) e := by
  induction e generalizing Δ with
  | app f a ihf iha => exact ⟨fun _ h => h, H.2.1, ihf H.2.2.1, iha H.2.2.2⟩
  | proj s i m ih => exact ⟨fun _ h => h, ih H.2⟩
  | lam A b ihA ihb | forallE A b ihA ihb =>
    exact ⟨fun _ h => h, ihA H.2.1, ihb H.2.2⟩
  | proof | bvar | sort | const => exact ⟨fun _ h => h, trivial⟩

/-- A scoped-normal source is fixed by every compatible computation path.
No closure of primitives under context conversion or substitution is needed. -/
theorem ScopedCompute.fixed_of_scoped_normal
    (R : ScopedCompute Step Δ a b) (H : ScopedNormalSyntax Step Δ a) : b = a := by
  induction R with
  | base R => exact (scoped_normal_no_step H R).elim
  | beta R => exact R.fixed_of_normal H.beta_normal
  | trans _ _ ih₁ ih₂ =>
    have E := ih₁ H
    exact (ih₂ (E.symm ▸ H)).trans E
  | app _ _ ihf iha => exact congr (congrArg ProofShape.app (ihf H.2.2.1)) (iha H.2.2.2)
  | proj _ ih => exact congrArg _ (ih H.2)
  | lam _ _ ihA ihb => exact congr (congrArg ProofShape.lam (ihA H.2.1)) (ihb H.2.2)
  | forallE _ _ ihA ihb => exact congr (congrArg ProofShape.forallE (ihA H.2.1)) (ihb H.2.2)

/-- If an eta-expanded function is fixed before application, its consumed
argument needs no recovery. First-head beta retains arbitrary computation of
that argument, every pending argument, and the exact continuation to a sort. -/
theorem ScopedCompute.fixed_eta_spine_sort_iff
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hfix : ∀ {out}, ScopedCompute Step Δ (.lam A (.app (f.liftN 1) (.bvar 0))) out →
      out = .lam A (.app (f.liftN 1) (.bvar 0))) :
    ScopedCompute Step Δ (mkApps (.lam A (.app (f.liftN 1) (.bvar 0))) (x :: xs)) (.sort v) ↔
      ScopedCompute Step Δ (mkApps (.app f x) xs) (.sort v) := by
  have inst_body (x : ProofShape) : (ProofShape.app (f.liftN 1) (.bvar 0)).inst x = .app f x := by
    simp only [inst_eq_subst, ProofShape.subst, Subst.liftN, Subst.one,
      lift_subst_cons, subst_id, Subst.cons]
  constructor
  · intro R
    obtain ⟨A', body, x', xs', RF, RX, RT⟩ := R.lambda_spine_sort hhead
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj (hfix RF)
    cases RX with
    | cons RX RXS =>
      rw [inst_body] at RT
      exact (compute_spine (.app .refl RX) RXS).trans RT
  · intro R
    have RB : ScopedCompute Step Δ (.app (.lam A (.app (f.liftN 1) (.bvar 0))) x) (.app f x) :=
      inst_body x ▸ ScopedCompute.beta .beta
    exact (compute_spine RB (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans R

end Lean4Lean.VEnv.Strengthening.ProofShape
