import Lean4Lean.Theory.Typing.ChurchRosser

/-! # Finite developments of explicitly marked beta redexes

`Term.beta A b a` marks the displayed redex `(λ x : A. b) a`. Ordinary `app` and
`lam` nodes are unmarked. Substitution copies marks but never creates a mark at an
ordinary application. `Step` contracts one mark, at any position including annotations.

The interpretation `weight` expands marked binders while charging for their arguments
and annotations even when discarded. It therefore accounts for duplication, and every
development step strictly decreases it. This establishes finite developments without
normalization of the underlying lambda calculus. It does not establish termination of
repeatedly marking newly created redexes, or repair of a confluence join.
-/

namespace Lean4Lean.VEnv.Strengthening.Developments

/-- Syntax with an additional constructor for a marked beta redex. -/
inductive Term where
  | bvar (i : Nat)
  | sort (u : VLevel)
  | const (c : Name) (us : List VLevel)
  | app (f a : Term)
  | lam (A b : Term)
  | forallE (A b : Term)
  | proj (c : Name) (i : Nat) (m : Term)
  | beta (A b a : Term)
  deriving DecidableEq

namespace Term

def cons (ρ : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => ρ n

def up (ρ : Nat → Nat) : Nat → Nat := cons (fun n => ρ n + 1) 0

/-- Renaming retains every mark. -/
def ren : Term → (Nat → Nat) → Term
  | .bvar i, ρ => .bvar (ρ i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, ρ => .app (ren f ρ) (ren a ρ)
  | .lam A b, ρ => .lam (ren A ρ) (ren b (up ρ))
  | .forallE A b, ρ => .forallE (ren A ρ) (ren b (up ρ))
  | .proj c i m, ρ => .proj c i (ren m ρ)
  | .beta A b a, ρ => .beta (ren A ρ) (ren b (up ρ)) (ren a ρ)

def upSub (σ : Nat → Term) : Nat → Term := cons (fun n => (σ n).ren Nat.succ) (.bvar 0)

/-- Substitution preserves the distinction between old and newly created redexes. -/
def subst : Term → (Nat → Term) → Term
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, σ => .app (subst f σ) (subst a σ)
  | .lam A b, σ => .lam (subst A σ) (subst b (upSub σ))
  | .forallE A b, σ => .forallE (subst A σ) (subst b (upSub σ))
  | .proj c i m, σ => .proj c i (subst m σ)
  | .beta A b a, σ => .beta (subst A σ) (subst b (upSub σ)) (subst a σ)

def inst (b a : Term) : Term := b.subst (cons .bvar a)

/-- Expansion cost with variable costs supplied by `ρ`. The extra argument cost in a
marked redex is essential: reduction inside an argument discarded by its body still
strictly decreases the weight. -/
def weight : Term → (Nat → Nat) → Nat
  | .bvar i, ρ => ρ i
  | .sort _, _ | .const .., _ => 1
  | .app f a, ρ => weight f ρ + weight a ρ + 1
  | .lam A b, ρ | .forallE A b, ρ => weight A ρ + weight b (cons ρ 1) + 1
  | .proj _ _ m, ρ => weight m ρ + 1
  | .beta A b a, ρ => weight A ρ + weight b (cons ρ (weight a ρ)) + weight a ρ + 1

theorem weight_mono (t : Term) {ρ τ : Nat → Nat} (h : ∀ n, ρ n ≤ τ n) :
    t.weight ρ ≤ t.weight τ := by
  induction t generalizing ρ τ with
  | bvar i => exact h i
  | sort | const => exact Nat.le_refl _
  | app f a ihf iha => exact Nat.add_le_add_right (Nat.add_le_add (ihf h) (iha h)) 1
  | proj c i m ih => exact Nat.add_le_add_right (ih h) 1
  | lam A b ihA ihb | forallE A b ihA ihb =>
    exact Nat.add_le_add_right (Nat.add_le_add (ihA h)
      (ihb (fun n => by cases n <;> simp [cons, h]))) 1
  | beta A b a ihA ihb iha =>
    have hb := ihb (ρ := cons ρ (a.weight ρ)) (τ := cons τ (a.weight τ))
      (fun n => by cases n with | zero => exact iha h | succ n => exact h n)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (ihA h) hb) (iha h)) 1

theorem weight_ren (t : Term) (r ρ : Nat → Nat) :
    (t.ren r).weight ρ = t.weight (fun n => ρ (r n)) := by
  have hup (r ρ : Nat → Nat) (v : Nat) :
      (fun n => cons ρ v (up r n)) = cons (fun n => ρ (r n)) v := by
    funext n; cases n <;> rfl
  induction t generalizing r ρ with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [ren, weight, ihf, iha]
  | proj c i m ih => simp only [ren, weight, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [ren, weight, ihA, ihb, hup]
  | beta A b a ihA ihb iha => simp only [ren, weight, ihA, ihb, iha, hup]

theorem weight_subst (t : Term) (σ : Nat → Term) (ρ : Nat → Nat) :
    (t.subst σ).weight ρ = t.weight (fun n => (σ n).weight ρ) := by
  have hup (σ : Nat → Term) (ρ : Nat → Nat) (v : Nat) :
      (fun n => (upSub σ n).weight (cons ρ v)) = cons (fun n => (σ n).weight ρ) v := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact weight_ren (σ n) Nat.succ (cons ρ v)
  induction t generalizing σ ρ with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [subst, weight, ihf, iha]
  | proj c i m ih => simp only [subst, weight, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [subst, weight, ihA, ihb, hup]
  | beta A b a ihA ihb iha => simp only [subst, weight, ihA, ihb, iha, hup]

theorem weight_inst (b a : Term) (ρ : Nat → Nat) :
    (b.inst a).weight ρ = b.weight (cons ρ (a.weight ρ)) := by
  rw [inst, weight_subst]
  congr 1
  funext n; cases n <;> rfl

/-- One contraction of an existing mark, anywhere in a term. -/
inductive Step : Term → Term → Prop where
  | beta : Step (.beta A b a) (b.inst a)
  | appL : Step f f' → Step (.app f a) (.app f' a)
  | appR : Step a a' → Step (.app f a) (.app f a')
  | lamA : Step A A' → Step (.lam A b) (.lam A' b)
  | lamB : Step b b' → Step (.lam A b) (.lam A b')
  | forallA : Step A A' → Step (.forallE A b) (.forallE A' b)
  | forallB : Step b b' → Step (.forallE A b) (.forallE A b')
  | proj : Step m m' → Step (.proj c i m) (.proj c i m')
  | betaA : Step A A' → Step (.beta A b a) (.beta A' b a)
  | betaB : Step b b' → Step (.beta A b a) (.beta A b' a)
  | betaArg : Step a a' → Step (.beta A b a) (.beta A b a')

/-- The weight decreases for every valuation, including when an argument containing
marks is duplicated by contraction. -/
theorem Step.weight_lt (h : Step t t') (ρ : Nat → Nat) : t'.weight ρ < t.weight ρ := by
  induction h generalizing ρ with
  | beta => simp only [weight, weight_inst]; omega
  | appL _ ih | appR _ ih | lamA _ ih | forallA _ ih | proj _ ih | betaA _ ih =>
    have := ih ρ
    simp only [weight]
    omega
  | lamB _ ih | forallB _ ih =>
    have := ih (cons ρ 1)
    simp only [weight]
    omega
  | @betaB b b' A a h ih =>
    have := ih (cons ρ (a.weight ρ))
    simp only [weight]
    omega
  | @betaArg a a' A b h ih =>
    have ha := ih ρ
    have hb := b.weight_mono (ρ := cons ρ (a'.weight ρ)) (τ := cons ρ (a.weight ρ))
      (fun n => by cases n with | zero => exact Nat.le_of_lt ha | succ n => exact Nat.le_refl _)
    simp only [weight]
    omega

/-- Every sequence contracting only residuals of the initial marks terminates.
The relation is oriented from a reduct to its source, as required by `WellFounded`. -/
theorem finite_developments : WellFounded (fun t' t => Step t t') :=
  Subrelation.wf (fun h => h.weight_lt (fun _ => 0))
    (measure (fun t : Term => t.weight (fun _ => 0))).wf

/-- Forget marks, recovering the actual object-language expression. -/
def erase : Term → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app f.erase a.erase
  | .lam A b => .lam A.erase b.erase
  | .forallE A b => .forallE A.erase b.erase
  | .proj c i m => .proj c i m.erase
  | .beta A b a => .app (.lam A.erase b.erase) a.erase

theorem erase_ren (t : Term) (r : Nat → Nat) :
    (t.ren r).erase = t.erase.subst (fun n => .bvar (r n)) := by
  have hup (r : Nat → Nat) :
      (fun n => VExpr.bvar (up r n)) = VExpr.Subst.lift (fun n => .bvar (r n)) := by
    funext n
    cases n <;> simp [up, cons, VExpr.Subst.lift, VExpr.lift, VExpr.liftN]
  induction t generalizing r with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [ren, erase, VExpr.subst, ihf, iha]
  | proj c i m ih => simp only [ren, erase, VExpr.subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [ren, erase, VExpr.subst, ihA, ihb, hup]
  | beta A b a ihA ihb iha =>
    simp only [ren, erase, VExpr.subst, ihA, ihb, iha, hup]

theorem erase_ren_succ (t : Term) : (t.ren Nat.succ).erase = t.erase.lift := by
  rw [erase_ren, VExpr.lift_eq_lift']
  have h := VExpr.lift'_subst (e := t.erase) (σ := .id) (ρ := .skip .refl)
  rw [VExpr.subst_id] at h
  exact h.symm

theorem erase_subst (t : Term) (σ : Nat → Term) :
    (t.subst σ).erase = t.erase.subst (fun n => (σ n).erase) := by
  have hup (σ : Nat → Term) :
      (fun n => (upSub σ n).erase) = VExpr.Subst.lift (fun n => (σ n).erase) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact erase_ren_succ (σ n)
  induction t generalizing σ with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [subst, erase, VExpr.subst, ihf, iha]
  | proj c i m ih => simp only [subst, erase, VExpr.subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [subst, erase, VExpr.subst, ihA, ihb, hup]
  | beta A b a ihA ihb iha =>
    simp only [subst, erase, VExpr.subst, ihA, ihb, iha, hup]

theorem erase_inst (b a : Term) : (b.inst a).erase = b.erase.inst a.erase := by
  rw [inst, erase_subst, VExpr.inst_eq]
  congr 1
  funext n; cases n <;> rfl

/-- A marked development is a core parallel reduction in every context. -/
theorem Step.parRed [Params] (h : Step t t') (Γ : List VExpr) :
    ParRed Γ t.erase t'.erase := by
  induction h generalizing Γ with
  | beta => simpa only [erase, erase_inst] using ParRed.beta (Γ := Γ) .rfl .rfl
  | appL _ ih => exact .app (ih _) .rfl
  | appR _ ih => exact .app .rfl (ih _)
  | lamA _ ih => exact .lam (ih _) .rfl
  | lamB _ ih => exact .lam .rfl (ih _)
  | forallA _ ih => exact .forallE (ih _) .rfl
  | forallB _ ih => exact .forallE .rfl (ih _)
  | proj _ ih => exact .proj (ih _)
  | betaA _ ih => exact .app (.lam (ih _) .rfl) .rfl
  | betaB _ ih => exact .app (.lam .rfl (ih _)) .rfl
  | betaArg _ ih => exact .app .rfl (ih _)

/-- Existing typing is preserved by a marked development step at its original type. -/
theorem Step.defeq [Params] (h : Step t t')
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (ht : Params.env.HasType Params.univs Γ t.erase A) :
    Params.env.IsDefEq Params.univs Γ t.erase t'.erase A :=
  (h.parRed Γ).defeq hΓ ht

/-- Complete development of the current marks. A redex created by substitution remains
an ordinary application in the resulting `VExpr`. -/
def develop : Term → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app f.develop a.develop
  | .lam A b => .lam A.develop b.develop
  | .forallE A b => .forallE A.develop b.develop
  | .proj c i m => .proj c i m.develop
  | .beta _ b a => b.develop.inst a.develop

theorem develop_ren (t : Term) (r : Nat → Nat) :
    (t.ren r).develop = t.develop.subst (fun n => .bvar (r n)) := by
  have hup (r : Nat → Nat) :
      (fun n => VExpr.bvar (up r n)) = VExpr.Subst.lift (fun n => .bvar (r n)) := by
    funext n
    cases n <;> simp [up, cons, VExpr.Subst.lift, VExpr.lift, VExpr.liftN]
  induction t generalizing r with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [ren, develop, VExpr.subst, ihf, iha]
  | proj c i m ih => simp only [ren, develop, VExpr.subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [ren, develop, VExpr.subst, ihA, ihb, hup]
  | beta A b a ihA ihb iha =>
    simp only [ren, develop, ihb, iha, hup]
    exact VExpr.subst_inst.symm

theorem develop_ren_succ (t : Term) : (t.ren Nat.succ).develop = t.develop.lift := by
  rw [develop_ren, VExpr.lift_eq_lift']
  have h := VExpr.lift'_subst (e := t.develop) (σ := .id) (ρ := .skip .refl)
  rw [VExpr.subst_id] at h
  exact h.symm

theorem develop_subst (t : Term) (σ : Nat → Term) :
    (t.subst σ).develop = t.develop.subst (fun n => (σ n).develop) := by
  have hup (σ : Nat → Term) :
      (fun n => (upSub σ n).develop) = VExpr.Subst.lift (fun n => (σ n).develop) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact develop_ren_succ (σ n)
  induction t generalizing σ with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [subst, develop, VExpr.subst, ihf, iha]
  | proj c i m ih => simp only [subst, develop, VExpr.subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [subst, develop, VExpr.subst, ihA, ihb, hup]
  | beta A b a ihA ihb iha =>
    simp only [subst, develop, ihb, iha, hup]
    exact VExpr.subst_inst.symm

theorem develop_inst (b a : Term) : (b.inst a).develop = b.develop.inst a.develop := by
  rw [inst, develop_subst, VExpr.inst_eq]
  congr 1
  funext n; cases n <;> rfl

/-- All orders of developing a fixed marking have the same complete development. -/
theorem Step.develop_eq (h : Step t t') : t.develop = t'.develop := by
  induction h with
  | beta => exact (develop_inst _ _).symm
  | appL _ ih | appR _ ih | lamA _ ih | lamB _ ih | forallA _ ih | forallB _ ih
  | proj _ ih | betaB _ ih | betaArg _ ih => simp only [develop, ih]
  | betaA => rfl

/-- No marked node occurs in the syntax; ordinary beta-redexes are allowed. -/
def MarkFree : Term → Prop
  | .bvar _ | .sort _ | .const .. => True
  | .app f a => f.MarkFree ∧ a.MarkFree
  | .lam A b | .forallE A b => A.MarkFree ∧ b.MarkFree
  | .proj _ _ m => m.MarkFree
  | .beta .. => False

theorem MarkFree.not_step (h : t.MarkFree) : ¬ Step t t' := by
  intro hs
  induction hs with
  | beta => exact h
  | appL _ ih | lamA _ ih | forallA _ ih => exact ih h.1
  | appR _ ih | lamB _ ih | forallB _ ih => exact ih h.2
  | proj _ ih => exact ih h
  | betaA | betaB | betaArg => exact h

theorem step_of_not_markFree (h : ¬ t.MarkFree) : ∃ t', Step t t' := by
  classical
  induction t with
  | bvar | sort | const => exact (h trivial).elim
  | beta => exact ⟨_, .beta⟩
  | proj c i m ih => obtain ⟨m', hm⟩ := ih h; exact ⟨_, .proj hm⟩
  | app f a ihf iha =>
    by_cases hf : f.MarkFree
    · obtain ⟨a', ha⟩ := iha (fun ha => h ⟨hf, ha⟩); exact ⟨_, .appR ha⟩
    · obtain ⟨f', hf⟩ := ihf hf; exact ⟨_, .appL hf⟩
  | lam A b ihA ihb =>
    by_cases hA : A.MarkFree
    · obtain ⟨b', hb⟩ := ihb (fun hb => h ⟨hA, hb⟩); exact ⟨_, .lamB hb⟩
    · obtain ⟨A', hA⟩ := ihA hA; exact ⟨_, .lamA hA⟩
  | forallE A b ihA ihb =>
    by_cases hA : A.MarkFree
    · obtain ⟨b', hb⟩ := ihb (fun hb => h ⟨hA, hb⟩); exact ⟨_, .forallB hb⟩
    · obtain ⟨A', hA⟩ := ihA hA; exact ⟨_, .forallA hA⟩

theorem MarkFree.develop_eq_erase {t : Term} (h : t.MarkFree) : t.develop = t.erase := by
  induction t with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [develop, erase, ihf h.1, iha h.2]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [develop, erase, ihA h.1, ihb h.2]
  | proj c i m ih => simp only [develop, erase, ih h]
  | beta => exact h.elim

/-- A sequence of contractions of existing marks. -/
abbrev Steps := ReflTransGen Step

/-- Every marking has a complete finite development. -/
theorem exists_complete (t : Term) : ∃ t', Steps t t' ∧ t'.MarkFree := by
  classical
  induction t using finite_developments.induction with
  | h t ih =>
    by_cases ht : t.MarkFree
    · exact ⟨t, .rfl, ht⟩
    · obtain ⟨s, hs⟩ := step_of_not_markFree ht
      obtain ⟨t', ht', hn⟩ := ih s hs
      exact ⟨t', (ReflTransGen.tail .rfl hs).trans ht', hn⟩

theorem Steps.develop_eq (h : Steps t t') : t.develop = t'.develop := by
  induction h with
  | rfl => rfl
  | tail _ hs ih => exact ih.trans hs.develop_eq

/-- The erasure of any complete development is the structurally computed result. -/
theorem complete_unique (h : Steps t t') (hn : t'.MarkFree) : t'.erase = t.develop :=
  hn.develop_eq_erase.symm.trans h.develop_eq.symm

theorem Steps.defeq [Params] (h : Steps t t')
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (ht : Params.env.HasType Params.univs Γ t.erase A) :
    Params.env.IsDefEq Params.univs Γ t.erase t'.erase A := by
  induction h with
  | rfl => exact ht
  | tail _ hs ih => exact ih.trans (hs.defeq hΓ ih.hasType.2)

/-- Complete development preserves the original type, in the actual calculus. -/
theorem develop_defeq [Params] {t : Term} (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (ht : Params.env.HasType Params.univs Γ t.erase A) :
    Params.env.IsDefEq Params.univs Γ t.erase t.develop A := by
  obtain ⟨t', hs, hn⟩ := exists_complete t
  simpa only [complete_unique hs hn] using hs.defeq hΓ ht

private def markRoot : Term → Term → Term
  | .lam A b, a => .beta A b a
  | f, a => .app f a

private theorem erase_markRoot (f a : Term) : (markRoot f a).erase = .app f.erase a.erase := by
  cases f <;> rfl

/-- Mark all syntactically present beta redexes. This does not mark future redexes. -/
def markAll : VExpr → Term
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => markRoot (markAll f) (markAll a)
  | .lam A b => .lam (markAll A) (markAll b)
  | .forallE A b => .forallE (markAll A) (markAll b)
  | .proj c i m => .proj c i (markAll m)

theorem erase_markAll (e : VExpr) : (markAll e).erase = e := by
  induction e with
  | bvar | sort | const => rfl
  | app f a ihf iha => simp only [markAll, erase_markRoot, ihf, iha]
  | lam A b ihA ihb | forallE A b ihA ihb => simp only [markAll, erase, ihA, ihb]
  | proj c i m ih => simp only [markAll, erase, ih]

/-- One complete-development round: newly created redexes may remain afterward. -/
def round (e : VExpr) : VExpr := (markAll e).develop

theorem round_app_lam (A b a : VExpr) :
    round (.app (.lam A b) a) = (round b).inst (round a) := rfl

theorem round_app_app (f a b : VExpr) :
    round (.app (.app f a) b) = .app (round (.app f a)) (round b) := by
  change (markRoot (markRoot (markAll f) (markAll a)) (markAll b)).develop =
    .app (markRoot (markAll f) (markAll a)).develop (markAll b).develop
  cases markAll f <;> rfl

theorem round_defeq [Params] (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (ht : Params.env.HasType Params.univs Γ e A) :
    Params.env.IsDefEq Params.univs Γ e (round e) A := by
  have ht' : Params.env.HasType Params.univs Γ (markAll e).erase A := by
    simpa only [erase_markAll] using ht
  simpa only [erase_markAll, round] using develop_defeq hΓ ht'

end Term
end Lean4Lean.VEnv.Strengthening.Developments
