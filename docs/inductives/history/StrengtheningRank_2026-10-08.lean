import Lean4Lean.Theory.Typing.Lemmas

/-! A fully counted nondependent Pi fragment used to test the proposed
size-first rank. This is NOT a complete certified equality calculus. -/
namespace Lean4Lean.StrengtheningRank
open VEnv VExpr

def S1 : VExpr := .sort (.succ .zero)
def arr (a b : VExpr) : VExpr := .forallE a b.lift

/-- No declarative typing/equality premises or conversion escape hatch.
The sort equivalence imax 1 1 = 1 is built into the pi rule. -/
inductive Cert : Nat → List VExpr → VExpr → VExpr → Prop where
  | var : Lookup Γ i S1 → Cert 1 Γ (.bvar i) S1
  | prop : Cert 1 Γ (.sort .zero) S1
  | pi : Cert n Γ a S1 → Cert m Γ b S1 → Cert (n + m + 1) Γ (arr a b) S1

/-- Certified reflexivity and beta for this fragment; every typing premise
is a Cert. This deliberately omits the full calculus's conversion and rules. -/
inductive CertEq : Nat → List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl : Cert n Γ e A → CertEq (n+1) Γ e e A
  | beta : Cert n (S1 :: Γ) b S1 → Cert m Γ a S1 →
      CertEq (n+m+1) Γ (.app (.lam S1 b) a) (b.inst a) S1

def nodes : VExpr → Nat
  | .app a b | .lam a b | .forallE a b => nodes a + nodes b + 1
  | .proj _ _ e => nodes e + 1
  | _ => 1

theorem nodes_lift (e : VExpr) (n k : Nat) : nodes (e.liftN n k) = nodes e := by
  induction e generalizing k <;> simp [VExpr.liftN, nodes, *]

theorem Cert.exact_size (h : Cert n Γ e A) : nodes e = n := by
  induction h with
  | var => rfl
  | prop => rfl
  | pi _ _ ha hb => simp [arr, nodes, lift, nodes_lift, ha, hb]

theorem Cert.positive (h : Cert n Γ e A) : 0 < n := by
  cases h <;> omega

theorem Cert.sound {env : VEnv} (henv : env.Ordered) (h : Cert n Γ e A) :
    env.HasType U Γ e A := by
  induction h with
  | var h => exact .bvar h
  | prop => exact .sort trivial
  | pi _ _ ha hb =>
    have ht := HasType.forallE ha (hb.weakN henv (Ctx.LiftN.one (A := _)))
    exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) ht

theorem CertEq.sound {env : VEnv} (henv : env.Ordered) (h : CertEq n Γ a b A) :
    env.IsDefEq U Γ a b A := by
  cases h with
  | refl h => exact h.sound henv
  | beta hb ha => exact .beta (hb.sound henv) (ha.sound henv)

theorem arr_subst (a b : VExpr) (σ : VExpr.Subst) :
    (arr a b).subst σ = arr (a.subst σ) (b.subst σ) := by
  simp only [arr, VExpr.subst, VExpr.lift_subst_lift]

theorem arr_lift (a b : VExpr) (n k : Nat) :
    (arr a b).liftN n k = arr (a.liftN n k) (b.liftN n k) := by
  simp only [arr, VExpr.liftN]
  rw [VExpr.lift_liftN']

theorem Cert.weakN (W : Ctx.LiftN p k Γ Δ) (h : Cert n Γ e A) :
    Cert n Δ (e.liftN p k) (A.liftN p k) := by
  induction h with
  | var h => exact .var (h.weakN W)
  | prop => exact .prop
  | pi _ _ ha hb => rw [arr_lift]; exact .pi (ha W) (hb W)

/-- The substitution budget includes every possible substituted variable
certificate. The output bound is n*M, not a bound depending only on n. -/
def SubBudget (M : Nat) (Γ Δ : List VExpr) (σ : VExpr.Subst) : Prop :=
  ∀ i, Lookup Γ i S1 → ∃ m, m ≤ M ∧ Cert m Δ (σ i) S1

theorem Cert.subst (h : Cert n Γ e S1) (hM : 1 ≤ M)
    (hσ : SubBudget M Γ Δ σ) :
    ∃ r, r ≤ n * M ∧ Cert r Δ (e.subst σ) S1 := by
  generalize hA : S1 = A at h
  induction h with
  | var h => simpa using hσ _ h
  | prop => exact ⟨1, by simpa using hM, .prop⟩
  | @pi n Γ a m b ha hb iha ihb =>
    obtain ⟨r, hr, ha'⟩ := iha hσ rfl
    obtain ⟨s, hs, hb'⟩ := ihb hσ rfl
    refine ⟨r + s + 1, ?_, ?_⟩
    · calc
        r + s + 1 ≤ n * M + m * M + M := Nat.add_le_add (Nat.add_le_add hr hs) hM
        _ = (n + m + 1) * M := by simp [Nat.add_mul]
    · rw [arr_subst]; exact .pi ha' hb'

def tower : Nat → VExpr
  | 0 => .sort .zero
  | n + 1 => arr (.sort .zero) (tower n)

theorem tower_cert (n : Nat) (Γ : List VExpr) : Cert (2*n+1) Γ (tower n) S1 := by
  induction n with
  | zero => exact .prop
  | succ n ih =>
    have hn : 2*(n+1)+1 = 1+(2*n+1)+1 := by omega
    rw [hn]; exact .pi .prop ih

def twice : VExpr := arr (.bvar 0) (.bvar 0)

theorem twice_cert : Cert 3 [S1] twice S1 := .pi (.var .zero) (.var .zero)

theorem twice_subst (q : VExpr) : twice.subst (Subst.id.cons q) = arr q q := rfl

theorem duplication_exact (N : Nat) :
    Cert (4*N+3) [] (twice.subst (Subst.id.cons (tower N))) S1 ∧
    ∀ r, Cert r [] (twice.subst (Subst.id.cons (tower N))) S1 → r = 4*N+3 := by
  have h : Cert (4*N+3) [] (arr (tower N) (tower N)) S1 := by
    have hn : 4*N+3 = (2*N+1)+(2*N+1)+1 := by omega
    rw [hn]; exact .pi (tower_cert N []) (tower_cert N [])
  constructor
  · exact h
  · intro r hr
    exact hr.exact_size.symm.trans h.exact_size

/-- Principal substitution can exceed source + argument + ANY FIXED overhead.
This rules out a decrease on that size component, regardless of the secondary
component. It does not rule out a cut-rank-first or ordinal termination proof. -/
theorem no_additive_size_decrease (C : Nat) :
    ∃ n m r q,
      Cert n [S1] twice S1 ∧ Cert m [] q S1 ∧
      Cert r [] (twice.subst (Subst.id.cons q)) S1 ∧
      n + m + C < r ∧
      ∀ s, Cert s [] (twice.subst (Subst.id.cons q)) S1 → s = r := by
  refine ⟨3, 2*(C+2)+1, 4*(C+2)+3, tower (C+2), twice_cert,
    tower_cert _ [], (duplication_exact _).1, ?_, (duplication_exact _).2⟩
  omega

/-- The duplication is the contractum of an actual certified beta rule. -/
theorem beta_duplication (N : Nat) :
    CertEq (2*N+5) [] (.app (.lam S1 twice) (tower N))
      (twice.inst (tower N)) S1 := by
  have hn : 2*N+5 = 3+(2*N+1)+1 := by omega
  rw [hn]; exact .beta twice_cert (tower_cert N [])

theorem beta_contractum_size (N r : Nat)
    (h : Cert r [] (twice.inst (tower N)) S1) : r = 4*N+3 := by
  rw [VExpr.inst_eq] at h
  exact (duplication_exact N).2 r h

theorem beta_size_increases (N r : Nat) (hN : 2 ≤ N)
    (h : Cert r [] (twice.inst (tower N)) S1) : 2*N+5 < r := by
  have := beta_contractum_size N r h
  omega

theorem no_size_first_lex_decrease (C x y : Nat) :
    ¬ Prod.Lex (· < ·) (· < ·)
      (4*(C+2)+3, x) (3 + (2*(C+2)+1) + C, y) := by
  generalize hn : 4*(C+2)+3 = n
  generalize hm : 3 + (2*(C+2)+1) + C = m
  intro h
  cases h <;> omega

#print axioms beta_contractum_size
#print axioms beta_size_increases
#print axioms CertEq.sound
#print axioms beta_duplication
#print axioms Cert.sound
#print axioms Cert.weakN
#print axioms Cert.subst
#print axioms duplication_exact
#print axioms no_additive_size_decrease
#print axioms no_size_first_lex_decrease
end Lean4Lean.StrengtheningRank
