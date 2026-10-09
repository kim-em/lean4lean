import Lean4Lean.Theory.Typing.Strengthening.Pilot

/-! Round 6. Reified, cut-type-decorated pilot certificates, and counterexamples
 to the requested subformula property. The metadata do not add inference rules:
 erasure forgets them and produces exactly a pilot certificate. -/
set_option maxHeartbeats 2000000

namespace Lean4Lean.Round6
open VEnv VExpr

def nodes : VExpr → Nat
  | .app a b | .lam a b | .forallE a b => nodes a + nodes b + 1
  | .proj _ _ e => nodes e + 1
  | _ => 1

abbrev Complexity := Nat × Nat
def ComplexityLT : Complexity → Complexity → Prop := Prod.Lex (· < ·) (· < ·)
def ComplexityLE (a b : Complexity) : Prop := a = b ∨ ComplexityLT a b

/-- The sort level of the COMMON TYPE, evaluated at a fixed universe assignment.
No syntactic ordering of universe expressions is asserted. -/
def complexity (ρ : List Nat) (u : VLevel) (T : VExpr) : Complexity :=
  (u.eval ρ, nodes T)

/-- Typing metadata, not new pilot premises. A decorated cut explicitly chooses
its common type and its sort. Raw pilot conversions need not even be typed. -/
structure CutAt (env : VEnv) (U : Nat) (Γ : List VExpr) (a b : VExpr) where
  type : VExpr
  level : VLevel
  left : env.HasType U Γ a type
  right : env.HasType U Γ b type
  sort : env.HasType U Γ type (.sort level)

def CutAt.label (ρ : List Nat) (c : CutAt env U Γ a b) : Complexity :=
  complexity ρ c.level c.type

variable (env : VEnv) (U : Nat)

inductive DCert : CKind → List VExpr → VExpr → VExpr → Type
  -- synthesis
  | ty_bvar : Lookup Γ i A → DCert .ty Γ (.bvar i) A
  | ty_sort : l.WF U → DCert .ty Γ (.sort l) (.sort (.succ l))
  | ty_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
      DCert .ty Γ (.const c ls) (ci.type.instL ls)
  | ty_app : DCert .ty Γ f F → DCert .red Γ F (.forallE A B) → DCert .ty Γ a A' →
      DCert .conv Γ A' A → DCert .ty Γ (.app f a) (B.inst a)
  | ty_lam : DCert .ty Γ A S → DCert .red Γ S (.sort u) → DCert .ty (A::Γ) b B →
      DCert .ty Γ (.lam A b) (.forallE A B)
  | ty_forallE : DCert .ty Γ A S → DCert .red Γ S (.sort u) → DCert .ty (A::Γ) B S' →
      DCert .red (A::Γ) S' (.sort v) → DCert .ty Γ (.forallE A B) (.sort (.imax u v))
  -- parallel step
  | step_bvar : DCert .step Γ (.bvar i) (.bvar i)
  | step_sort : DCert .step Γ (.sort l) (.sort l)
  | step_const : DCert .step Γ (.const c ls) (.const c ls)
  | step_app : DCert .step Γ f f' → DCert .step Γ a a' → DCert .step Γ (.app f a) (.app f' a')
  | step_lam : DCert .step Γ A A' → DCert .step (A::Γ) b b' →
      DCert .step Γ (.lam A b) (.lam A' b')
  | step_forallE : DCert .step Γ A A' → DCert .step (A::Γ) B B' →
      DCert .step Γ (.forallE A B) (.forallE A' B')
  | step_beta : CutAt env U Γ (.app (.lam A b) a) (b'.inst a') → DCert .step (A::Γ) b b' → DCert .step Γ a a' →
      DCert .step Γ (.app (.lam A b) a) (b'.inst a')
  | step_extra : env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
      DCert .step Γ (df.lhs.instL ls) (df.rhs.instL ls)
  | step_eta : DCert .ty Γ e F → DCert .red Γ F (.forallE A B) →
      DCert .step Γ e (.lam A (.app e.lift (.bvar 0)))
  -- reduction
  | red_refl : DCert .red Γ e e
  | red_step : DCert .step Γ a b → DCert .red Γ b c → DCert .red Γ a c
  -- normal equality
  | norm_bvar : DCert .norm Γ (.bvar i) (.bvar i)
  | norm_sort : l₁.WF U → l₂.WF U → l₁ ≈ l₂ → DCert .norm Γ (.sort l₁) (.sort l₂)
  | norm_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      DCert .norm Γ (.const c ls) (.const c ls')
  | norm_app : DCert .norm Γ f f' → DCert .norm Γ a a' → DCert .norm Γ (.app f a) (.app f' a')
  | norm_lam : DCert .conv Γ A A' → DCert .norm (A::Γ) b b' →
      DCert .norm Γ (.lam A b) (.lam A' b')
  | norm_forallE : DCert .conv Γ A A' → DCert .norm (A::Γ) B B' →
      DCert .norm Γ (.forallE A B) (.forallE A' B')
  | norm_etaL : DCert .ty Γ e' F → DCert .red Γ F (.forallE A' B) → DCert .conv Γ A A' →
      DCert .norm (A::Γ) e (.app e'.lift (.bvar 0)) → DCert .norm Γ (.lam A e) e'
  | norm_etaR : DCert .ty Γ e F → DCert .red Γ F (.forallE A' B) → DCert .conv Γ A A' →
      DCert .norm (A::Γ) (.app e.lift (.bvar 0)) e' → DCert .norm Γ e (.lam A e')
  | norm_etaBoth : DCert .ty Γ e F → DCert .red Γ F (.forallE A B) → DCert .ty Γ e' F' →
      DCert .red Γ F' (.forallE A' B') → DCert .conv Γ A A' →
      DCert .norm (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
      DCert .norm Γ e e'
  | norm_proofIrrel : DCert .ty Γ h p → DCert .ty Γ h' p' → DCert .conv Γ p p' →
      DCert .ty Γ p S → DCert .red Γ S (.sort .zero) → DCert .norm Γ h h'
  -- conversion
  | conv_mk : CutAt env U Γ a b → DCert .red Γ a a' → DCert .red Γ b b' → DCert .norm Γ a' b' → DCert .conv Γ a b


variable {env : VEnv} {U : Nat}

theorem DCert.erase (h : DCert env U j Γ a b) : Cert env U j Γ a b := by
  induction h with
  | ty_bvar h0 => exact .ty_bvar h0
  | ty_sort h0 => exact .ty_sort h0
  | ty_const h0 h1 h2 => exact .ty_const h0 h1 h2
  | ty_app h0 h1 h2 h3 ih0 ih1 ih2 ih3 => exact .ty_app ih0 ih1 ih2 ih3
  | ty_lam h0 h1 h2 ih0 ih1 ih2 => exact .ty_lam ih0 ih1 ih2
  | ty_forallE h0 h1 h2 h3 ih0 ih1 ih2 ih3 => exact .ty_forallE ih0 ih1 ih2 ih3
  | step_bvar  => exact .step_bvar 
  | step_sort  => exact .step_sort 
  | step_const  => exact .step_const 
  | step_app h0 h1 ih0 ih1 => exact .step_app ih0 ih1
  | step_lam h0 h1 ih0 ih1 => exact .step_lam ih0 ih1
  | step_forallE h0 h1 ih0 ih1 => exact .step_forallE ih0 ih1
  | step_beta h0 h1 h2 ih1 ih2 => exact .step_beta ih1 ih2
  | step_extra h0 h1 h2 => exact .step_extra h0 h1 h2
  | step_eta h0 h1 ih0 ih1 => exact .step_eta ih0 ih1
  | red_refl  => exact .red_refl 
  | red_step h0 h1 ih0 ih1 => exact .red_step ih0 ih1
  | norm_bvar  => exact .norm_bvar 
  | norm_sort h0 h1 h2 => exact .norm_sort h0 h1 h2
  | norm_const h0 h1 h2 h3 h4 => exact .norm_const h0 h1 h2 h3 h4
  | norm_app h0 h1 ih0 ih1 => exact .norm_app ih0 ih1
  | norm_lam h0 h1 ih0 ih1 => exact .norm_lam ih0 ih1
  | norm_forallE h0 h1 ih0 ih1 => exact .norm_forallE ih0 ih1
  | norm_etaL h0 h1 h2 h3 ih0 ih1 ih2 ih3 => exact .norm_etaL ih0 ih1 ih2 ih3
  | norm_etaR h0 h1 h2 h3 ih0 ih1 ih2 ih3 => exact .norm_etaR ih0 ih1 ih2 ih3
  | norm_etaBoth h0 h1 h2 h3 h4 h5 ih0 ih1 ih2 ih3 ih4 ih5 => exact .norm_etaBoth ih0 ih1 ih2 ih3 ih4 ih5
  | norm_proofIrrel h0 h1 h2 h3 h4 ih0 ih1 ih2 ih3 ih4 => exact .norm_proofIrrel ih0 ih1 ih2 ih3 ih4
  | conv_mk h0 h1 h2 h3 ih1 ih2 ih3 => exact .conv_mk ih1 ih2 ih3

def DCert.size : DCert env U j Γ a b → Nat
  | .ty_bvar _ => 1
  | .ty_sort _ => 1
  | .ty_const _ _ _ => 1
  | .ty_app h0 h1 h2 h3 => 1 + h0.size + h1.size + h2.size + h3.size
  | .ty_lam h0 h1 h2 => 1 + h0.size + h1.size + h2.size
  | .ty_forallE h0 h1 h2 h3 => 1 + h0.size + h1.size + h2.size + h3.size
  | .step_bvar  => 1
  | .step_sort  => 1
  | .step_const  => 1
  | .step_app h0 h1 => 1 + h0.size + h1.size
  | .step_lam h0 h1 => 1 + h0.size + h1.size
  | .step_forallE h0 h1 => 1 + h0.size + h1.size
  | .step_beta _ h1 h2 => 1 + h1.size + h2.size
  | .step_extra _ _ _ => 1
  | .step_eta h0 h1 => 1 + h0.size + h1.size
  | .red_refl  => 1
  | .red_step h0 h1 => 1 + h0.size + h1.size
  | .norm_bvar  => 1
  | .norm_sort _ _ _ => 1
  | .norm_const _ _ _ _ _ => 1
  | .norm_app h0 h1 => 1 + h0.size + h1.size
  | .norm_lam h0 h1 => 1 + h0.size + h1.size
  | .norm_forallE h0 h1 => 1 + h0.size + h1.size
  | .norm_etaL h0 h1 h2 h3 => 1 + h0.size + h1.size + h2.size + h3.size
  | .norm_etaR h0 h1 h2 h3 => 1 + h0.size + h1.size + h2.size + h3.size
  | .norm_etaBoth h0 h1 h2 h3 h4 h5 => 1 + h0.size + h1.size + h2.size + h3.size + h4.size + h5.size
  | .norm_proofIrrel h0 h1 h2 h3 h4 => 1 + h0.size + h1.size + h2.size + h3.size + h4.size
  | .conv_mk _ h1 h2 h3 => 1 + h1.size + h2.size + h3.size

def DCert.cuts (ρ : List Nat) : DCert env U j Γ a b → List Complexity
  | .ty_bvar _ => []
  | .ty_sort _ => []
  | .ty_const _ _ _ => []
  | .ty_app h0 h1 h2 h3 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ
  | .ty_lam h0 h1 h2 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ
  | .ty_forallE h0 h1 h2 h3 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ
  | .step_bvar  => []
  | .step_sort  => []
  | .step_const  => []
  | .step_app h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .step_lam h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .step_forallE h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .step_beta h0 h1 h2 => [h0.label ρ] ++ h1.cuts ρ ++ h2.cuts ρ
  | .step_extra _ _ _ => []
  | .step_eta h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .red_refl  => []
  | .red_step h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .norm_bvar  => []
  | .norm_sort _ _ _ => []
  | .norm_const _ _ _ _ _ => []
  | .norm_app h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .norm_lam h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .norm_forallE h0 h1 => h0.cuts ρ ++ h1.cuts ρ
  | .norm_etaL h0 h1 h2 h3 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ
  | .norm_etaR h0 h1 h2 h3 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ
  | .norm_etaBoth h0 h1 h2 h3 h4 h5 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ ++ h4.cuts ρ ++ h5.cuts ρ
  | .norm_proofIrrel h0 h1 h2 h3 h4 => h0.cuts ρ ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ ++ h4.cuts ρ
  | .conv_mk h0 h1 h2 h3 => [h0.label ρ] ++ h1.cuts ρ ++ h2.cuts ρ ++ h3.cuts ρ

/-- Multisets represented by lists modulo permutation; every replacement is STRICT. -/
def MultiLT (xs ys : List Complexity) : Prop :=
  ∃ keep removed added, ys.Perm (keep ++ removed) ∧ xs.Perm (keep ++ added) ∧
    removed ≠ [] ∧ ∀ x ∈ added, ∃ y ∈ removed, ComplexityLT x y

def maxComplexity (xs : List Complexity) : Complexity :=
  xs.foldr (fun a b => if a.1 < b.1 then b else
    if b.1 < a.1 then a else (a.1, max a.2 b.2)) (0,0)

abbrev Rank := Complexity × (List Complexity × Nat)
def RankLT (a b : Rank) : Prop :=
  ComplexityLT a.1 b.1 ∨ (a.1 = b.1 ∧
    (MultiLT a.2.1 b.2.1 ∨ (a.2.1.Perm b.2.1 ∧ a.2.2 < b.2.2)))
def DCert.rank (ρ : List Nat) (h : DCert env U j Γ a b) : Rank :=
  (maxComplexity (h.cuts ρ), h.cuts ρ, h.size)

theorem complexity_wf : WellFounded ComplexityLT :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

@[simp] theorem nodes_lift (e : VExpr) : nodes (e.liftN n k) = nodes e := by
  induction e generalizing k <;> simp_all [liftN, nodes]

theorem complexity_lift (ρ : List Nat) (u : VLevel) (e : VExpr) :
    complexity ρ u (e.liftN n k) = complexity ρ u e := by simp [complexity]

/-- Three proof variables of a fresh proposition. Context entries use de Bruijn indices. -/
def proofCtx : List VExpr := [.bvar 2, .bvar 1, .bvar 0, .sort .zero]
def P : VExpr := .bvar 3

theorem proofCtx_wf : OnCtx proofCtx (env.IsType U) :=
  ⟨⟨⟨⟨⟨⟩, _, .sort trivial⟩, _, .bvar .zero⟩, _, .bvar (.succ .zero)⟩,
    _, .bvar (.succ (.succ .zero))⟩

theorem p_lookup : Lookup proofCtx 3 (.sort .zero) := .succ (.succ (.succ .zero))
theorem h0_lookup : Lookup proofCtx 0 P := .zero
theorem h1_lookup : Lookup proofCtx 1 P := .succ .zero
theorem h2_lookup : Lookup proofCtx 2 P := .succ (.succ .zero)

def propCut : CutAt env U proofCtx P P :=
  ⟨.sort .zero, .succ .zero, .bvar p_lookup, .bvar p_lookup, .sort trivial⟩

def proofCut (hi : Lookup proofCtx i P) (hj : Lookup proofCtx j P) :
    CutAt env U proofCtx (.bvar i) (.bvar j) :=
  ⟨P, .zero, .bvar hi, .bvar hj, .bvar p_lookup⟩

def propRefl : DCert env U .conv proofCtx P P :=
  .conv_mk propCut .red_refl .red_refl .norm_bvar

def proofCompare (hi : Lookup proofCtx i P) (hj : Lookup proofCtx j P) :
    DCert env U .conv proofCtx (.bvar i) (.bvar j) :=
  .conv_mk (proofCut hi hj) .red_refl .red_refl
    (.norm_proofIrrel (.ty_bvar hi) (.ty_bvar hj) propRefl
      (.ty_bvar p_lookup) .red_refl)

/-- The hidden comparison is one universe ABOVE the enclosing comparison. -/
theorem proofIrrel_subformula_false (ρ : List Nat) :
    (proofCut (env := env) (U := U) h0_lookup h1_lookup).label ρ = (0,1) ∧
    (propCut (env := env) (U := U)).label ρ = (1,1) ∧
    ¬ ComplexityLE ((propCut (env := env) (U := U)).label ρ)
      ((proofCut (env := env) (U := U) h0_lookup h1_lookup).label ρ) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  rcases h with h | h
  · cases h
  · cases h <;> contradiction

theorem proofCompare_profile (ρ : List Nat) :
    (proofCompare (env := env) (U := U) h0_lookup h1_lookup).cuts ρ = [(0,1),(1,1)] := rfl

theorem proofCompare_rank (ρ : List Nat) :
    (proofCompare (env := env) (U := U) h0_lookup h1_lookup).rank ρ =
      ((1,1), [(0,1),(1,1)], 12) := rfl

/-- Concrete composable inputs and their actual composition in the pilot. -/
theorem proof_pair :
    CConv env U proofCtx (.bvar 0) (.bvar 1) ∧
    CConv env U proofCtx (.bvar 1) (.bvar 2) ∧
    CConv env U proofCtx (.bvar 0) (.bvar 2) :=
  ⟨(proofCompare h0_lookup h1_lookup).erase,
    (proofCompare h1_lookup h2_lookup).erase,
    (proofCompare h0_lookup h2_lookup).erase⟩

/-- Proof irrelevance prevents extracting a derivation-sensitive size from `Cert` itself. -/
theorem raw_certificates_equal (h k : Cert env U j Γ a b) : h = k := rfl

def S0 : VExpr := .sort .zero
def S1 : VExpr := .sort (.succ .zero)
def S2 : VExpr := .sort (.succ (.succ .zero))
def piLevel : VLevel := .imax (.succ .zero) (.succ .zero)
def piSort : VExpr := .sort piLevel

def sort1Cut : CutAt env U Γ S1 S1 :=
  ⟨S2, .succ (.succ (.succ .zero)), .sort trivial, .sort trivial, .sort trivial⟩
def sort1Refl : DCert env U .conv Γ S1 S1 :=
  .conv_mk sort1Cut .red_refl .red_refl (.norm_sort trivial trivial rfl)

def nested : Nat → VExpr
  | 0 => S0
  | n+1 => .app (.lam S1 (.bvar 0)) (nested n)

def nestedTy (n : Nat) : DCert env U .ty Γ (nested n) S1 :=
  match n with
  | 0 => .ty_sort trivial
  | n+1 => .ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl (.ty_bvar .zero))
      .red_refl (nestedTy n) sort1Refl

def twice : VExpr := .forallE (.bvar 0) (.bvar 1)
def twiceTy : DCert env U .ty (S1 :: Γ) twice piSort :=
  .ty_forallE (.ty_bvar .zero) .red_refl (.ty_bvar (.succ .zero)) .red_refl

def dupSource (n : Nat) : VExpr := .app (.lam S1 twice) (nested n)
def dupTarget (n : Nat) : VExpr := .forallE (nested n) (nested n)
def dupSourceTy (n : Nat) : DCert env U .ty Γ (dupSource n) piSort :=
  .ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl twiceTy) .red_refl
    (nestedTy n) sort1Refl

def dupTargetTy (n : Nat) : DCert env U .ty Γ (dupTarget n) piSort :=
  .ty_forallE (nestedTy n) .red_refl (nestedTy n) .red_refl

/-- With common-type labels, the original binder-duplication test has EQUAL rank.
These profiles count EVERY hidden conversion in the actual typing certificates. -/
theorem duplication_equal_rank (ρ : List Nat) :
    (dupSourceTy (env := env) (U := U) (Γ := []) 1).rank ρ =
      ((3,1), [(3,1),(3,1)], 25) ∧
    (dupTargetTy (env := env) (U := U) (Γ := []) 1).rank ρ =
      ((3,1), [(3,1),(3,1)], 25)  := by
  constructor <;> simp [DCert.rank, DCert.cuts, DCert.size, dupSourceTy, dupTargetTy,
    twiceTy, nestedTy, sort1Refl, sort1Cut, CutAt.label, complexity, nodes, S2,
    VLevel.eval, maxComplexity]

theorem duplication_more_cuts (ρ : List Nat) :
    (dupSourceTy (env := env) (U := U) (Γ := []) 2).rank ρ =
      ((3,1), [(3,1),(3,1),(3,1)], 35) ∧
    (dupTargetTy (env := env) (U := U) (Γ := []) 2).rank ρ =
      ((3,1), [(3,1),(3,1),(3,1),(3,1)], 45)  := by
  constructor <;> simp [DCert.rank, DCert.cuts, DCert.size, dupSourceTy, dupTargetTy,
    twiceTy, nestedTy, sort1Refl, sort1Cut, CutAt.label, complexity, nodes, S2,
    VLevel.eval, maxComplexity]

theorem complexity_irrefl (x : Complexity) : ¬ ComplexityLT x x := by
  intro h; cases h <;> omega

/-- Strict multiset replacement cannot duplicate maximal, equal labels for free. -/
theorem multilt_replicate_length (h : MultiLT xs (List.replicate n x))
    (hx : ∀ y ∈ xs, y = x) : xs.length < n := by
  obtain ⟨keep, removed, added, hp, hq, hr, ha⟩ := h
  have had : added = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro y hy
    obtain ⟨z, hz, hlt⟩ := ha y hy
    have hyx := hx y (hq.mem_iff.mpr (List.mem_append.mpr (.inr hy)))
    have hzx : z = x := (List.mem_replicate.mp
      (hp.mem_iff.mpr (List.mem_append.mpr (.inr hz)))).2
    subst y; subst z
    exact complexity_irrefl x hlt
  have hp' := hp.length_eq
  have hq' := hq.length_eq
  have hr' : 0 < removed.length := List.length_pos_iff.mpr hr
  simp [had] at hp' hq'
  omega

theorem duplication_not_decreasing (ρ : List Nat) :
    ¬ RankLT ((dupTargetTy (env := env) (U := U) (Γ := []) 2).rank ρ)
      ((dupSourceTy (env := env) (U := U) (Γ := []) 2).rank ρ) := by
  rw [(duplication_more_cuts (env := env) (U := U) ρ).1,
    (duplication_more_cuts (env := env) (U := U) ρ).2]
  intro h
  rcases h with h | ⟨_, h | ⟨h, hs⟩⟩
  · exact complexity_irrefl _ h
  · have hn := multilt_replicate_length (n := 3) (x := (3,1)) h
      (by simp)
    contradiction
  · exact (by decide : ¬ (45 < 35)) hs

theorem nestedRefl (n : Nat) : CStep env U Γ (nested n) (nested n) :=
  match n with
  | 0 => .step_sort
  | n+1 => .step_app (.step_lam .step_sort .step_bvar) (nestedRefl n)

theorem duplication_beta : CStep env U [] (dupSource 2) (dupTarget 2) :=
  .step_beta (.step_forallE .step_bvar .step_bvar) (nestedRefl 2)

/-- The instance of a variable type is larger, at exactly the same universe. -/
def instanceType : VExpr := .forallE S0 S0
def instanceTy : DCert env U .ty [] instanceType piSort :=
  .ty_forallE (.ty_sort trivial) .red_refl (.ty_sort trivial) .red_refl

theorem instance_subformula_false (ρ : List Nat) :
    (instanceTy (env := env) (U := U)).cuts ρ = [] ∧
    complexity ρ piLevel (.bvar 0) = (1,1) ∧
    complexity ρ piLevel ((.bvar 0 : VExpr).inst instanceType) = (1,3) ∧
    ¬ ComplexityLE (complexity ρ piLevel ((.bvar 0 : VExpr).inst instanceType))
      (complexity ρ piLevel (.bvar 0)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change ¬ ComplexityLE (1,3) (1,1)
  intro h
  rcases h with h | h
  · cases h
  · cases h <;> omega

/-- The round-5 synthesis correction compares sorts AT Sort 2, whose universe is 3. -/
def synthesisCorrection : CutAt env U [] piSort S1 :=
  ⟨S2, .succ (.succ (.succ .zero)),
    .defeqDF (A := .sort (.succ piLevel))
      (.sortDF ⟨trivial,trivial⟩ trivial rfl)
      (show env.HasType U [] piSort (.sort (.succ piLevel)) from .sort ⟨trivial,trivial⟩),
    .sort trivial, .sort trivial⟩

def synthesisCorrectionCert : DCert env U .conv [] piSort S1 :=
  .conv_mk synthesisCorrection .red_refl .red_refl
    (.norm_sort ⟨trivial,trivial⟩ trivial rfl)

theorem synthesis_correction_higher (ρ : List Nat) :
    (synthesisCorrection (env := env) (U := U)).label ρ = (3,1) ∧
    complexity ρ (.succ (.succ .zero)) S1 = (2,1) ∧
    ComplexityLT (complexity ρ (.succ (.succ .zero)) S1)
      ((synthesisCorrection (env := env) (U := U)).label ρ) :=
  ⟨rfl, rfl, .left _ _ (by change 2 < 3; decide)⟩

/-- With no installed equations, variables/sorts whose lookup types are also
variables/sorts cannot eta-expand or otherwise reduce. -/
def Atomic : VExpr → Prop
  | .bvar _ | .sort _ => True
  | _ => False

def AtomicCtx (Γ : List VExpr) : Prop := ∀ i A, Lookup Γ i A → Atomic A

def AtomicClaim : CKind → List VExpr → VExpr → VExpr → Prop
  | .ty, Γ, a, b => AtomicCtx Γ → Atomic a → Atomic b
  | .step, Γ, a, b | .red, Γ, a, b => AtomicCtx Γ → Atomic a → b = a
  | _, _, _, _ => True

theorem atomic_claim (h : Cert .empty U j Γ a b) : AtomicClaim j Γ a b := by
  induction h with
  | ty_bvar h => exact fun hΓ _ => hΓ _ _ h
  | ty_sort => exact fun _ _ => trivial
  | ty_const | ty_app | ty_lam | ty_forallE => exact fun _ h => h.elim
  | step_bvar | step_sort => exact fun _ _ => rfl
  | step_const | step_app | step_lam | step_forallE | step_beta => exact fun _ h => h.elim
  | step_extra h => exact h.elim
  | step_eta _ _ ihT ihR =>
    intro hΓ ha
    have hF := ihT hΓ ha
    have heq := ihR hΓ hF
    rw [← heq] at hF
    exact hF.elim
  | red_refl => exact fun _ _ => rfl
  | red_step _ _ ihS ihR =>
    intro hΓ ha
    have h1 := ihS hΓ ha
    subst h1
    exact ihR hΓ ha
  | norm_bvar | norm_sort | norm_const | norm_app | norm_lam | norm_forallE |
    norm_etaL | norm_etaR | norm_etaBoth | norm_proofIrrel | conv_mk => trivial

theorem atomic_lift (h : Atomic A) : Atomic (A.liftN n k) := by
  cases A <;> simp_all [Atomic, liftN]

theorem lookup_atomic (hΓ : ∀ A ∈ Γ, Atomic A) (h : Lookup Γ i A) : Atomic A := by
  induction h with
  | zero => exact atomic_lift (hΓ _ (by simp))
  | succ h ih => exact atomic_lift (ih (fun A h => hΓ A (by simp [h])))

theorem proofCtx_atomic : AtomicCtx proofCtx := by
  intro i A h
  exact lookup_atomic (by simp [proofCtx, Atomic]) h

/-- Any common type of the proposition P itself lies in universe 1. This does
not assume the metadata choose the syntactically smallest common type. -/
theorem propCut_level (henv : env.WF) (ρ : List Nat) (c : CutAt env U proofCtx P P) :
    c.level.eval ρ = 1 := by
  have hp : env.HasType U proofCtx P S0 := .bvar p_lookup
  have he := hp.uniqU henv proofCtx_wf c.left
  have ht : env.HasType U proofCtx S0 (.sort c.level) :=
    (he.of_r henv proofCtx_wf c.sort).hasType.1
  have hs : env.HasType U proofCtx S0 S1 := .sort trivial
  have hl := (ht.uniqU henv proofCtx_wf hs).sort_inv henv proofCtx_wf
  exact congrFun hl ρ

theorem nodes_pos (e : VExpr) : 1 ≤ nodes e := by cases e <;> simp [nodes] <;> omega

theorem propCut_at_least (henv : env.WF) (ρ : List Nat) (c : CutAt env U proofCtx P P) :
    ComplexityLE (1,1) (c.label ρ) := by
  have hu := propCut_level henv ρ c
  have hn := nodes_pos c.type
  change (1,1) = (c.level.eval ρ, nodes c.type) ∨
    ComplexityLT (1,1) (c.level.eval ρ, nodes c.type)
  rw [hu]
  by_cases h : nodes c.type = 1
  · exact Or.inl (by rw [h])
  · exact Or.inr (.right _ (by omega))

theorem proof0_synthesis (h : DCert env U .ty proofCtx (.bvar 0) T) : T = P := by
  cases h with
  | ty_bvar h => cases h; rfl

theorem proof2_synthesis (h : DCert env U .ty proofCtx (.bvar 2) T) : T = P := by
  cases h with
  | ty_bvar h => cases h with
    | succ h => cases h with
      | succ h => cases h; rfl

/-- A NormalEq boundary between these two distinct proof variables MUST use
proof irrelevance, and its hidden proposition comparison has complexity ≥ (1,1). -/
theorem norm_boundary_requires_cut (ρ : List Nat)
    (h : DCert .empty U .norm proofCtx (.bvar 0) (.bvar 2)) :
    ∃ c ∈ h.cuts ρ, ComplexityLE (1,1) c := by
  cases h with
  | norm_etaBoth ht hr ht' hr' hc hn =>
    have ha := atomic_claim ht.erase proofCtx_atomic trivial
    have he := atomic_claim hr.erase proofCtx_atomic ha
    rw [← he] at ha
    exact ha.elim
  | norm_proofIrrel ht ht' hc hs hz =>
    have he := proof0_synthesis ht
    have he' := proof2_synthesis ht'
    subst he; subst he'
    cases hc with
    | conv_mk c hl hr hn =>
      refine ⟨c.label ρ, ?_, propCut_at_least ⟨[], .empty⟩ ρ c⟩
      simp [DCert.cuts]

/-- This quantifies over EVERY decorated composition certificate, including
ones using different reduction witnesses and different common-type metadata. -/
theorem composition_requires_cut (ρ : List Nat)
    (h : DCert .empty U .conv proofCtx (.bvar 0) (.bvar 2)) :
    ∃ c ∈ h.cuts ρ, ComplexityLE (1,1) c := by
  cases h with
  | conv_mk c hl hr hn =>
    have he := atomic_claim hl.erase proofCtx_atomic trivial
    have he' := atomic_claim hr.erase proofCtx_atomic trivial
    subst he; subst he'
    obtain ⟨d, hd, hle⟩ := norm_boundary_requires_cut ρ hn
    exact ⟨d, by simp [DCert.cuts, hd], hle⟩

/-- The requested exact pair: each input has maximum (1,1), and every
composition needs a cut ≥ (1,1). A composition EXISTS (proof_pair); this
lower bound is not a failure of transitivity or a refutation of all size inductions. -/
theorem exact_pair_composition_lower_bound (ρ : List Nat) :
    let h01 := proofCompare (env := VEnv.empty) (U := U) h0_lookup h1_lookup
    let h12 := proofCompare (env := VEnv.empty) (U := U) h1_lookup h2_lookup
    maxComplexity (h01.cuts ρ) = (1,1) ∧ maxComplexity (h12.cuts ρ) = (1,1) ∧
    ∀ h : DCert .empty U .conv proofCtx (.bvar 0) (.bvar 2),
      ∃ c ∈ h.cuts ρ,
        ComplexityLE (maxComplexity (h01.cuts ρ)) c ∧
        ComplexityLE (maxComplexity (h12.cuts ρ)) c := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  obtain ⟨c, hc, hle⟩ := composition_requires_cut ρ h
  exact ⟨c, hc, hle, hle⟩

def CutAt.weakN (henv : env.WF) (c : CutAt env U Γ a b)
    (W : Ctx.LiftN n k Γ Δ) : CutAt env U Δ (a.liftN n k) (b.liftN n k) :=
  ⟨c.type.liftN n k, c.level, c.left.weakN henv.ordered W,
    c.right.weakN henv.ordered W, c.sort.weakN henv.ordered W⟩

@[simp] theorem CutAt.weakN_label (henv : env.WF) (c : CutAt env U Γ a b)
    (W : Ctx.LiftN n k Γ Δ) (ρ : List Nat) : (c.weakN henv W).label ρ = c.label ρ :=
  complexity_lift ρ c.level c.type

def DCert.cast (h : DCert env U j Γ a b) (ha : a = a') (hb : b = b') :
    DCert env U j Γ a' b' := ha ▸ hb ▸ h
@[simp] theorem DCert.cast_cuts (h : DCert env U j Γ a b) (ha : a = a') (hb : b = b') :
    (h.cast ha hb).cuts ρ = h.cuts ρ := by cases ha; cases hb; rfl
@[simp] theorem DCert.cast_size (h : DCert env U j Γ a b) (ha : a = a') (hb : b = b') :
    (h.cast ha hb).size = h.size := by cases ha; cases hb; rfl

def CutAt.cast (c : CutAt env U Γ a b) (ha : a = a') (hb : b = b') :
    CutAt env U Γ a' b' := ha ▸ hb ▸ c
@[simp] theorem CutAt.cast_label (c : CutAt env U Γ a b) (ha : a = a') (hb : b = b') :
    (c.cast ha hb).label ρ = c.label ρ := by cases ha; cases hb; rfl

theorem DCert.transport (ha : a = a') (hb : b = b')
    (h : ∃ d : DCert env U j Γ a b, d.cuts ρ = xs ∧ d.size = sz) :
    ∃ d : DCert env U j Γ a' b', d.cuts ρ = xs ∧ d.size = sz := by
  cases ha; cases hb; exact h

theorem CutAt.transport (ha : a = a') (hb : b = b') (c : CutAt env U Γ a b) :
    ∃ d : CutAt env U Γ a' b', d.label ρ = c.label ρ := by
  cases ha; cases hb; exact ⟨c, rfl⟩

set_option linter.unusedSimpArgs false in
/-- Full pilot weakening, preserving the entire profile and certificate size. -/
theorem DCert.weakN_rank (henv : env.WF) (ρ : List Nat) (h : DCert env U j Γ a b)
    (W : Ctx.LiftN n k Γ Δ) :
    ∃ h' : DCert env U j Δ (a.liftN n k) (b.liftN n k),
      h'.cuts ρ = h.cuts ρ ∧ h'.size = h.size := by
  induction h generalizing k Δ with
  | ty_bvar h => exact ⟨.ty_bvar (h.weakN W), rfl, rfl⟩
  | ty_sort h => exact ⟨.ty_sort h, rfl, rfl⟩
  | ty_const h1 h2 h3 =>
    refine ⟨(DCert.ty_const (Γ := Δ) h1 h2 h3).cast rfl
      (((henv.ordered.closedC h1).instL).liftN_eq (Nat.zero_le k)).symm, ?_, ?_⟩ <;>
      simp only [liftN, DCert.cast_cuts, DCert.cast_size, DCert.cuts, DCert.size]
  | ty_app _ _ _ _ ih0 ih1 ih2 ih3 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    obtain ⟨g3, hc3, hs3⟩ := ih3 W
    simp only [liftN] at *
    refine ⟨(DCert.ty_app g0 g1 g2 g3).cast rfl (liftN_inst_hi ..).symm, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | ty_lam _ _ _ ih0 ih1 ih2 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W.succ
    refine ⟨.ty_lam g0 g1 g2, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | ty_forallE _ _ _ _ ih0 ih1 ih2 ih3 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W.succ
    obtain ⟨g3, hc3, hs3⟩ := ih3 W.succ
    refine ⟨.ty_forallE g0 g1 g2 g3, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_app _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    refine ⟨.step_app g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_lam _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W.succ
    refine ⟨.step_lam g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_forallE _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W.succ
    refine ⟨.step_forallE g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_beta c _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W.succ
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨c', hc⟩ := CutAt.transport (ρ := ρ) rfl (liftN_inst_hi ..) (c.weakN henv W)
    have hc' : c'.label ρ = c.label ρ := hc.trans (CutAt.weakN_label henv c W ρ)
    apply DCert.transport rfl (liftN_inst_hi ..).symm
    refine ⟨.step_beta c' g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_eta _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    apply DCert.transport rfl (liftN_etaExpand ..).symm
    refine ⟨.step_eta g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | red_step _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    refine ⟨.red_step g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_app _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    refine ⟨.norm_app g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_lam _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W.succ
    refine ⟨.norm_lam g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_forallE _ _ ih0 ih1 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W.succ
    refine ⟨.norm_forallE g0 g1, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_etaL _ _ _ _ ih0 ih1 ih2 ih3 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    obtain ⟨g3, hc3, hs3⟩ := ih3 W.succ
    obtain ⟨t3, hc3', hs3'⟩ := DCert.transport rfl (liftN_etaBody _) ⟨g3, hc3, hs3⟩
    refine ⟨.norm_etaL g0 g1 g2 t3, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_etaR _ _ _ _ ih0 ih1 ih2 ih3 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    obtain ⟨g3, hc3, hs3⟩ := ih3 W.succ
    obtain ⟨t3, hc3', hs3'⟩ := DCert.transport (liftN_etaBody _) rfl ⟨g3, hc3, hs3⟩
    refine ⟨.norm_etaR g0 g1 g2 t3, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_etaBoth _ _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 ih5 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    obtain ⟨g3, hc3, hs3⟩ := ih3 W
    obtain ⟨g4, hc4, hs4⟩ := ih4 W
    obtain ⟨g5, hc5, hs5⟩ := ih5 W.succ
    obtain ⟨t5, hc5', hs5'⟩ := DCert.transport (liftN_etaBody _) (liftN_etaBody _) ⟨g5, hc5, hs5⟩
    refine ⟨.norm_etaBoth g0 g1 g2 g3 g4 t5, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | norm_proofIrrel _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    obtain ⟨g3, hc3, hs3⟩ := ih3 W
    obtain ⟨g4, hc4, hs4⟩ := ih4 W
    refine ⟨.norm_proofIrrel g0 g1 g2 g3 g4, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | conv_mk c _ _ _ ih0 ih1 ih2 =>
    obtain ⟨g0, hc0, hs0⟩ := ih0 W
    obtain ⟨g1, hc1, hs1⟩ := ih1 W
    obtain ⟨g2, hc2, hs2⟩ := ih2 W
    refine ⟨.conv_mk (c.weakN henv W) g0 g1 g2, ?_, ?_⟩ <;>
      simp_all only [liftN, DCert.cuts, DCert.size, CutAt.weakN_label,
        DCert.cast_cuts, DCert.cast_size, CutAt.cast_label]
  | step_bvar => exact ⟨.step_bvar, rfl, rfl⟩
  | step_sort => exact ⟨.step_sort, rfl, rfl⟩
  | step_const => exact ⟨.step_const, rfl, rfl⟩
  | step_extra h1 h2 h3 =>
    have ⟨hl, hr⟩ := henv.ordered.defEqWF h1
    refine ⟨(DCert.step_extra (Γ := Δ) h1 h2 h3).cast
      (((hl.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k)).symm
      (((hr.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k)).symm, ?_, ?_⟩ <;>
      simp only [liftN, DCert.cast_cuts, DCert.cast_size, DCert.cuts, DCert.size]
  | red_refl => exact ⟨.red_refl, rfl, rfl⟩
  | norm_bvar => exact ⟨.norm_bvar, rfl, rfl⟩
  | norm_sort h1 h2 h3 => exact ⟨.norm_sort h1 h2 h3, rfl, rfl⟩
  | norm_const h1 h2 h3 h4 h5 => exact ⟨.norm_const h1 h2 h3 h4 h5, rfl, rfl⟩

/-- The proposed strict budget, applied to every recorded cut. -/
def BelowBudget (ρ : List Nat) (q : Complexity) (h : DCert env U j Γ a b) : Prop :=
  ∀ c ∈ h.cuts ρ, ComplexityLT c q

def beforeSubCut : CutAt env U [.bvar 0, piSort] (.bvar 0) (.bvar 0) :=
  ⟨.bvar 1, piLevel, .bvar .zero, .bvar .zero, .bvar (.succ .zero)⟩
def afterSubCut : CutAt env U [instanceType] (.bvar 0) (.bvar 0) :=
  ⟨instanceType, piLevel, .bvar .zero, .bvar .zero,
    .forallE (.sort trivial) (.sort trivial)⟩
def beforeSub : DCert env U .conv [.bvar 0, piSort] (.bvar 0) (.bvar 0) :=
  .conv_mk beforeSubCut .red_refl .red_refl .norm_bvar
def afterSub : DCert env U .conv [instanceType] (.bvar 0) (.bvar 0) :=
  .conv_mk afterSubCut .red_refl .red_refl .norm_bvar

/-- This is an actual single-variable substitution at depth one. The replacement
has NO cuts and checks exactly at Q=piSort. Nevertheless the dependent common
type's complexity, and hence the whole rank of this reflexive comparison, rises. -/
theorem budget_does_not_imply_rank_nonincrease (ρ : List Nat) :
    Ctx.InstN [] instanceType piSort 1 [.bvar 0, piSort] [instanceType] ∧
    BelowBudget ρ (complexity ρ (.succ piLevel) piSort)
      (instanceTy (env := env) (U := U)) ∧
    (beforeSub (env := env) (U := U)).rank ρ = ((1,1), [(1,1)], 4) ∧
    (afterSub (env := env) (U := U)).rank ρ = ((1,3), [(1,3)], 4) ∧
    RankLT ((beforeSub (env := env) (U := U)).rank ρ)
      ((afterSub (env := env) (U := U)).rank ρ) := by
  refine ⟨.succ .zero, ?_, rfl, rfl, ?_⟩
  · simp [BelowBudget, instanceTy, DCert.cuts]
  · exact Or.inl (.right _ (by change 1 < 3; decide))

/-- The explicit output certificate is at precisely the substituted input type. -/
theorem substitution_metadata :
    (beforeSubCut (env := env) (U := U)).type.inst instanceType 1 =
      (afterSubCut (env := env) (U := U)).type := rfl

def tower : Nat → VExpr
  | 0 => S0
  | n+1 => .forallE S0 (tower n)
def towerLevel : Nat → VLevel
  | 0 => .succ .zero
  | n+1 => .imax (.succ .zero) (towerLevel n)

theorem towerLevel_wf (n : Nat) : (towerLevel n).WF U := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨trivial, ih⟩

theorem towerLevel_eval (ρ : List Nat) (n : Nat) : (towerLevel n).eval ρ = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [towerLevel, VLevel.eval, ih, Lean.Nat.imax]

def towerTy (n : Nat) : DCert env U .ty Γ (tower n) (.sort (towerLevel n)) :=
  match n with
  | 0 => .ty_sort trivial
  | n+1 => .ty_forallE (.ty_sort trivial) .red_refl (towerTy n) .red_refl

def towerAlignment (n : Nat) : CutAt env U Γ (.sort (towerLevel n)) S1 :=
  ⟨S2, .succ (.succ (.succ .zero)),
    .defeqDF (A := .sort (.succ (towerLevel n)))
      (.sortDF (towerLevel_wf n) trivial
        (by funext ρ; simp [VLevel.eval, towerLevel_eval]))
      (show env.HasType U Γ (.sort (towerLevel n)) (.sort (.succ (towerLevel n))) from
        .sort (towerLevel_wf n)), .sort trivial, .sort trivial⟩

def towerConv (n : Nat) : DCert env U .conv Γ (.sort (towerLevel n)) S1 :=
  .conv_mk (towerAlignment n) .red_refl .red_refl
    (.norm_sort (towerLevel_wf n) trivial (funext (fun ρ => towerLevel_eval ρ n)))

def towerSourceTy (n : Nat) :
    DCert env U .ty Γ (.app (.lam S1 twice) (tower n)) piSort :=
  .ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl twiceTy)
    .red_refl (towerTy n) (towerConv n)
def towerTargetTy (n : Nat) :
    DCert env U .ty Γ (.forallE (tower n) (tower n))
      (.sort (.imax (towerLevel n) (towerLevel n))) :=
  .ty_forallE (towerTy n) .red_refl (towerTy n) .red_refl

theorem towerTy_cuts (ρ : List Nat) (n : Nat) :
    (towerTy (env := env) (U := U) (Γ := Γ) n).cuts ρ = [] := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih => simp [towerTy, DCert.cuts, ih]

theorem twice_tower_decreases (ρ : List Nat) (n : Nat) :
    RankLT ((towerTargetTy (env := env) (U := U) (Γ := []) n).rank ρ)
      ((towerSourceTy (env := env) (U := U) (Γ := []) n).rank ρ) := by
  apply Or.inl
  have hs : (towerSourceTy (env := env) (U := U) (Γ := []) n).cuts ρ = [(3,1)] := by
    simp [towerSourceTy, DCert.cuts, twiceTy, towerTy_cuts, towerConv,
      towerAlignment, CutAt.label, complexity, VLevel.eval, nodes, S2]
  have ht : (towerTargetTy (env := env) (U := U) (Γ := []) n).cuts ρ = [] := by
    simp [towerTargetTy, DCert.cuts, towerTy_cuts]
  change ComplexityLT (maxComplexity _) (maxComplexity _)
  rw [hs, ht]
  exact .left _ _ (by decide)

def hiddenSourceTy (n : Nat) :
    DCert env U .ty Γ (.app (.lam S1 (nested n)) S0) S1 :=
  .ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl (nestedTy n))
    .red_refl (.ty_sort trivial) sort1Refl

theorem nestedTy_cuts (ρ : List Nat) (n : Nat) :
    (nestedTy (env := env) (U := U) (Γ := Γ) n).cuts ρ = List.replicate n (3,1) := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih =>
    simp [nestedTy, DCert.cuts, sort1Refl, sort1Cut, CutAt.label,
      complexity, VLevel.eval, nodes, S2, ih, List.replicate_succ']

theorem max_replicate (n : Nat) : maxComplexity (List.replicate (n+1) (3,1)) = (3,1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change (if 3 < (maxComplexity (List.replicate (n+1) (3,1))).1 then
      maxComplexity (List.replicate (n+1) (3,1)) else
      if (maxComplexity (List.replicate (n+1) (3,1))).1 < 3 then (3,1) else
      (3, max 1 (maxComplexity (List.replicate (n+1) (3,1))).2)) = (3,1)
    rw [ih]
    rfl

theorem hiddenSourceTy_cuts (ρ : List Nat) (n : Nat) :
    (hiddenSourceTy (env := env) (U := U) (Γ := Γ) n).cuts ρ = List.replicate (n+1) (3,1) := by
  simp [hiddenSourceTy, DCert.cuts, nestedTy_cuts, sort1Refl, sort1Cut,
    CutAt.label, complexity, VLevel.eval, nodes, S2, List.replicate_succ']

theorem nested_decreases (ρ : List Nat) (n : Nat) :
    RankLT ((nestedTy (env := env) (U := U) (Γ := []) n).rank ρ)
      ((hiddenSourceTy (env := env) (U := U) (Γ := []) n).rank ρ) := by
  cases n with
  | zero => exact Or.inl (.left _ _ (by change 0 < 3; decide))
  | succ n =>
    apply Or.inr
    constructor
    · simp only [DCert.rank, nestedTy_cuts, hiddenSourceTy_cuts, max_replicate]
    · apply Or.inl
      simp only [DCert.rank]
      rw [nestedTy_cuts, hiddenSourceTy_cuts]
      refine ⟨List.replicate (n+1) (3,1), [(3,1)], [], ?_, ?_, by simp, ?_⟩
      · rw [← List.replicate_succ']
      · simp
      · simp

theorem DCert.weakN_rank_eq (henv : env.WF) (ρ : List Nat) (h : DCert env U j Γ a b)
    (W : Ctx.LiftN n k Γ Δ) :
    ∃ h' : DCert env U j Δ (a.liftN n k) (b.liftN n k), h'.rank ρ = h.rank ρ := by
  obtain ⟨h', hc, hs⟩ := h.weakN_rank henv ρ W
  exact ⟨h', by simp only [DCert.rank, hc, hs]⟩

/-- Even taking the maximum of all hidden cut types does not give the strict
principal decrease requested at the proof-irrelevance boundary. -/
theorem proofIrrel_principal_not_strict (ρ : List Nat) :
    ¬ ComplexityLT (maxComplexity ((propRefl (env := env) (U := U)).cuts ρ))
      (maxComplexity ((proofCompare (env := env) (U := U) h0_lookup h1_lookup).cuts ρ)) := by
  exact complexity_irrefl (1,1)

theorem tower_closed (n k : Nat) : (tower n).ClosedN k := by
  induction n generalizing k with
  | zero => trivial
  | succ n ih => exact ⟨trivial, ih (k+1)⟩

theorem nested_closed (n k : Nat) : (nested n).ClosedN k := by
  induction n generalizing k with
  | zero => trivial
  | succ n ih => exact ⟨⟨trivial, Nat.zero_lt_succ k⟩, ih k⟩

theorem towerRefl (n : Nat) : CStep env U Γ (tower n) (tower n) :=
  match n with
  | 0 => .step_sort
  | n+1 => .step_forallE .step_sort (towerRefl n)

theorem twice_tower_beta (n : Nat) :
    CStep env U [] (.app (.lam S1 twice) (tower n)) (.forallE (tower n) (tower n)) := by
  have h : CStep env U [] (.app (.lam S1 twice) (tower n)) (twice.inst (tower n)) :=
    .step_beta (.step_forallE .step_bvar .step_bvar) (towerRefl n)
  simpa only [twice, inst, instVar_succ, instVar_zero, (tower_closed n 0).lift_eq] using h

theorem nested_beta (n : Nat) :
    CStep env U [] (.app (.lam S1 (nested n)) S0) (nested n) := by
  have h : CStep env U [] (.app (.lam S1 (nested n)) S0) ((nested n).inst S0) :=
    .step_beta (nestedRefl n) .step_sort
  rw [(nested_closed n 0).instN_eq (Nat.zero_le 0)] at h
  exact h

#print axioms DCert.erase
#print axioms complexity_wf
#print axioms nodes_lift
#print axioms complexity_lift
#print axioms proofCtx_wf
#print axioms p_lookup
#print axioms h0_lookup
#print axioms h1_lookup
#print axioms h2_lookup
#print axioms proofIrrel_subformula_false
#print axioms proofCompare_profile
#print axioms proofCompare_rank
#print axioms proof_pair
#print axioms raw_certificates_equal
#print axioms duplication_equal_rank
#print axioms duplication_more_cuts
#print axioms complexity_irrefl
#print axioms multilt_replicate_length
#print axioms duplication_not_decreasing
#print axioms nestedRefl
#print axioms duplication_beta
#print axioms instance_subformula_false
#print axioms synthesis_correction_higher
#print axioms atomic_claim
#print axioms atomic_lift
#print axioms lookup_atomic
#print axioms proofCtx_atomic
#print axioms propCut_level
#print axioms nodes_pos
#print axioms propCut_at_least
#print axioms proof0_synthesis
#print axioms proof2_synthesis
#print axioms norm_boundary_requires_cut
#print axioms composition_requires_cut
#print axioms exact_pair_composition_lower_bound
#print axioms CutAt.weakN_label
#print axioms DCert.cast_cuts
#print axioms DCert.cast_size
#print axioms CutAt.cast_label
#print axioms DCert.transport
#print axioms CutAt.transport
#print axioms DCert.weakN_rank
#print axioms budget_does_not_imply_rank_nonincrease
#print axioms substitution_metadata
#print axioms towerLevel_wf
#print axioms towerLevel_eval
#print axioms towerTy_cuts
#print axioms twice_tower_decreases
#print axioms nestedTy_cuts
#print axioms max_replicate
#print axioms hiddenSourceTy_cuts
#print axioms nested_decreases
#print axioms DCert.weakN_rank_eq
#print axioms proofIrrel_principal_not_strict

#print axioms tower_closed
#print axioms nested_closed
#print axioms towerRefl
#print axioms twice_tower_beta
#print axioms nested_beta

end Lean4Lean.Round6
