import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.RestorationNaturality

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

private theorem forall₂_get {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ (i : Nat)
      (h : i < a.length) (h' : i < b.length), R a[i] b[i]
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ H, i + 1, hi, hi' =>
    forall₂_get H i (by simpa using hi) (by simpa using hi')

private theorem forall₂_take_drop {R : α → β → Prop}
    (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.take n) (b.take n) ∧ List.Forall₂ R (a.drop n) (b.drop n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih =>
    cases n with
    | zero => exact ⟨.nil, .cons h hs⟩
    | succ n => exact ⟨.cons h (ih n).1, (ih n).2⟩

private theorem forall₂_append {R : α → β → Prop}
    (H : List.Forall₂ R a b) (H' : List.Forall₂ R a' b') :
    List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h hs ih => exact .cons h ih


theorem EqUpToLevels.mkApps_args (H : EqUpToLevels U fn fn')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (VExpr.mkApps fn args) (VExpr.mkApps fn' args') := by
  induction ha generalizing fn fn' with
  | nil => exact H
  | cons h hs ih => exact ih (.app H h)

theorem EqUpToLevels.subst_args (H : EqUpToLevels U e e')
    (hσ : ∀ i, EqUpToLevels U (σ i) (σ' i)) :
    EqUpToLevels U (e.subst σ) (e'.subst σ') := by
  induction H generalizing σ σ' with
  | bvar => exact hσ _
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | proj _ ih => exact .proj (ih hσ)
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    constructor
    · exact ih1 hσ
    · apply ih2
      intro i
      cases i with
      | zero => exact .bvar
      | succ i => exact (hσ i).weakN

theorem EqUpToLevels.instantiateParams_args (H : EqUpToLevels U e e')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (instantiateParams e args) (instantiateParams e' args') := by
  apply H.subst_args
  intro i
  have hlen := Lean4Lean.List.Forall₂.length_eq ha
  simp only [← hlen]
  split
  · rename_i hi
    exact forall₂_get ha _ (by omega) (by omega)
  · exact .bvar

end Lean4Lean.VEnv
namespace Lean4Lean.InductiveSignature
open VEnv

private theorem HeadSpecialization.apply_levels {levels levels' : List VLevel} (h : HeadSpecialization)
    (hl : ∀ level ∈ levels, level.WF U) (hr : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : h.apply levels args = some output) :
    ∃ output', h.apply levels' args' = some output' ∧ EqUpToLevels U output output' := by
  have hllen := Lean4Lean.List.Forall₂.length_eq he
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  unfold HeadSpecialization.apply at H ⊢
  simp only [← hllen, ← halen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  cases H
  refine ⟨_, rfl, EqUpToLevels.mkApps_args ?_ ?_⟩
  · refine .const (by simp [VLevel.WF.inst hl]) (by simp [VLevel.WF.inst hr]) ?_
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.rfl (fun _ _ => VLevel.inst_congr rfl he)
  · have ht : List.Forall₂ (EqUpToLevels U) (args.take h.nparams) (args'.take h.nparams) := by
      exact (forall₂_take_drop ha _).1
    have hd : List.Forall₂ (EqUpToLevels U) (args.drop h.nparams) (args'.drop h.nparams) := by
      exact (forall₂_take_drop ha _).2
    have hparams : List.Forall₂ (EqUpToLevels U)
        (h.arguments.map fun arg => instantiateParams (arg.instL levels) (args.take h.nparams))
        (h.arguments.map fun arg => instantiateParams (arg.instL levels') (args'.take h.nparams)) := by
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.rfl fun _ _ =>
        (EqUpToLevels.instL_expr _ hl hr he).instantiateParams_args ht
    exact forall₂_append hparams hd

/-- Successful restoration preserves structural equality up to equivalent
universes, including specialized head parameters and trailing indices. -/
theorem Restoration.expr_levels (r : Restoration)
    (H : EqUpToLevels U e e') (hg : r.expr e = some output) :
    ∃ output', r.expr e' = some output' ∧ EqUpToLevels U output output' := by
  suffices ∀ args args', List.Forall₂ (EqUpToLevels U) args args' →
      ∀ output, Restoration.expr.go r e args = some output →
        ∃ output', Restoration.expr.go r e' args' = some output' ∧ EqUpToLevels U output output' from
    this [] [] .nil output hg
  clear hg output
  induction H with
  | bvar =>
    intro args args' ha output hg
    cases hg
    exact ⟨_, rfl, EqUpToLevels.mkApps_args .bvar ha⟩
  | sort hl hr he =>
    intro args args' ha output hg
    cases hg
    exact ⟨_, rfl, EqUpToLevels.mkApps_args (.sort hl hr he) ha⟩
  | elim hl hr he =>
    intro args args' ha output hg
    cases hg
    exact ⟨_, rfl, EqUpToLevels.mkApps_args (.elim hl hr he) ha⟩
  | const hl hr he =>
    intro args args' ha output hg
    simp only [Restoration.expr.go] at hg ⊢
    split at hg
    · rename_i h hfind
      exact h.apply_levels hl hr he ha hg
    · rename_i hfind
      cases hg
      exact ⟨_, rfl, EqUpToLevels.mkApps_args (.const hl hr he) ha⟩
  | app _ _ ihf iha =>
    intro args args' ha output hg
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨arg, harg, hfn⟩ := hg
    obtain ⟨arg', harg', har⟩ := iha [] [] .nil arg harg
    obtain ⟨out, hf, ho⟩ := ihf (_ :: args) (_ :: args') (.cons har ha) output hfn
    exact ⟨out, by simp only [Restoration.expr.go, bind, harg', Option.bind_some, hf], ho⟩
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    intro args args' ha output hg
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨d, hd, b, hb, hg⟩ := hg
    cases hg
    obtain ⟨d', hd', hed⟩ := ihd [] [] .nil d hd
    obtain ⟨b', hb', heb⟩ := ihb [] [] .nil b hb
    first
    | exact ⟨_, by simp only [Restoration.expr.go, bind, hd', hb', Option.bind_some]; rfl,
        EqUpToLevels.mkApps_args (.lam hed heb) ha⟩
    | exact ⟨_, by simp only [Restoration.expr.go, bind, hd', hb', Option.bind_some]; rfl,
        EqUpToLevels.mkApps_args (.forallE hed heb) ha⟩
  | proj _ ih =>
    intro args args' ha output hg
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨major, hm, hg⟩ := hg
    cases hg
    obtain ⟨major', hm', he⟩ := ih [] [] .nil major hm
    exact ⟨_, by simp only [Restoration.expr.go, bind, hm', Option.bind_some]; rfl,
      EqUpToLevels.mkApps_args (.proj he) ha⟩

end Lean4Lean.InductiveSignature
