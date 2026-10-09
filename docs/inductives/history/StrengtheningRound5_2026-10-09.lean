import Lean4Lean.Theory.Typing.Strengthening.Pilot

/-! Round 5. Full pilot weakening, and diagnostics for a depth/type-size rank.
The syntactic rank below is NOT a rank of all hidden side-condition certificates.
No transitivity or completeness theorem is asserted. -/
namespace Lean4Lean.Round5
open VEnv VExpr

/-- Weakening for every constructor of the actual pilot. -/
theorem pilot_weakN (henv : env.WF) (h : Cert env U j Γ a b)
    (W : Ctx.LiftN n k Γ Δ) :
    Cert env U j Δ (a.liftN n k) (b.liftN n k) := by
  induction h generalizing k Δ with
  | ty_bvar h => exact .ty_bvar (h.weakN W)
  | ty_sort h => exact .ty_sort h
  | ty_const h1 h2 h3 =>
    simpa only [liftN, ((henv.ordered.closedC h1).instL).liftN_eq (Nat.zero_le k)] using
      (Cert.ty_const (Γ := Δ) h1 h2 h3)
  | ty_app _ _ _ _ ihf ihF iha ihA =>
    simpa only [liftN, liftN_inst_hi] using
      Cert.ty_app (ihf W) (ihF W) (iha W) (ihA W)
  | ty_lam _ _ _ ihA ihS ihb => exact .ty_lam (ihA W) (ihS W) (ihb W.succ)
  | ty_forallE _ _ _ _ ihA ihS ihB ihS' =>
    exact .ty_forallE (ihA W) (ihS W) (ihB W.succ) (ihS' W.succ)
  | step_bvar => exact .step_bvar
  | step_sort => exact .step_sort
  | step_const => exact .step_const
  | step_app _ _ ihf iha => exact .step_app (ihf W) (iha W)
  | step_lam _ _ ihA ihb => exact .step_lam (ihA W) (ihb W.succ)
  | step_forallE _ _ ihA ihB => exact .step_forallE (ihA W) (ihB W.succ)
  | step_beta _ _ ihb iha =>
    simpa only [liftN, liftN_inst_hi] using Cert.step_beta (ihb W.succ) (iha W)
  | step_extra h1 h2 h3 =>
    have ⟨hl, hr⟩ := henv.ordered.defEqWF h1
    simpa only [((hl.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k),
      ((hr.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k)] using
      (Cert.step_extra (Γ := Δ) h1 h2 h3)
  | step_eta _ _ ihe ihF =>
    simpa only [liftN_etaExpand] using Cert.step_eta (ihe W) (ihF W)
  | red_refl => exact .red_refl
  | red_step _ _ ih1 ih2 => exact .red_step (ih1 W) (ih2 W)
  | norm_bvar => exact .norm_bvar
  | norm_sort h1 h2 h3 => exact .norm_sort h1 h2 h3
  | norm_const h1 h2 h3 h4 h5 => exact .norm_const h1 h2 h3 h4 h5
  | norm_app _ _ ihf iha => exact .norm_app (ihf W) (iha W)
  | norm_lam _ _ ihA ihb => exact .norm_lam (ihA W) (ihb W.succ)
  | norm_forallE _ _ ihA ihB => exact .norm_forallE (ihA W) (ihB W.succ)
  | norm_etaL _ _ _ _ ihe ihF ihA ihb =>
    have hb := ihb W.succ
    rw [liftN_etaBody] at hb
    exact .norm_etaL (ihe W) (ihF W) (ihA W) hb
  | norm_etaR _ _ _ _ ihe ihF ihA ihb =>
    have hb := ihb W.succ
    rw [liftN_etaBody] at hb
    exact .norm_etaR (ihe W) (ihF W) (ihA W) hb
  | norm_etaBoth _ _ _ _ _ _ ihe ihF ihe' ihF' ihA ihb =>
    have hb := ihb W.succ
    simp only [liftN_etaBody] at hb
    exact .norm_etaBoth (ihe W) (ihF W) (ihe' W) (ihF' W) (ihA W) hb
  | norm_proofIrrel _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .norm_proofIrrel (ih1 W) (ih2 W) (ih3 W) (ih4 W) (ih5 W)
  | conv_mk _ _ _ ih1 ih2 ih3 => exact .conv_mk (ih1 W) (ih2 W) (ih3 W)

/-- Syntax size; universe-level syntax is deliberately not counted. -/
def nodes : VExpr → Nat
  | .app a b | .lam a b | .forallE a b => nodes a + nodes b + 1
  | .proj _ _ e => nodes e + 1
  | _ => 1

/-- Maximum number of enclosing lambda/Pi binders. -/
def binders : VExpr → Nat
  | .app a b => max (binders a) (binders b)
  | .lam a b | .forallE a b => max (binders a) (binders b + 1)
  | .proj _ _ e => binders e
  | _ => 0

/-- Raising a nonempty cut profile by one binder. -/
def under (n : Nat) : Nat := if n = 0 then 0 else n + 1

/-- Maximum (one plus) binder depth of a syntactic beta redex, including hidden ones. -/
def cutDepth : VExpr → Nat
  | .app (.lam A b) a => max 1 (max (cutDepth A) (max (under (cutDepth b)) (cutDepth a)))
  | .app f a => max (cutDepth f) (cutDepth a)
  | .lam A b | .forallE A b => max (cutDepth A) (under (cutDepth b))
  | .proj _ _ e => cutDepth e
  | _ => 0

/-- Maximum size of a beta binder type. This is the substitution cut type,
not the absent common comparison type of a pilot conversion. -/
def cutTypeSize : VExpr → Nat
  | .app (.lam A b) a => max (nodes A) (max (cutTypeSize A) (max (cutTypeSize b) (cutTypeSize a)))
  | .app f a => max (cutTypeSize f) (cutTypeSize a)
  | .lam A b | .forallE A b => max (cutTypeSize A) (cutTypeSize b)
  | .proj _ _ e => cutTypeSize e
  | _ => 0

/-- Lexicographic order: binder depth, binder-type size, syntax size. -/
abbrev Rank := Nat × (Nat × Nat)
def LT : Rank → Rank → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
def rank (e : VExpr) : Rank := (cutDepth e, cutTypeSize e, nodes e)

theorem rank_wf : WellFounded LT :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

@[simp] theorem nodes_lift (e : VExpr) : nodes (e.liftN n k) = nodes e := by
  induction e generalizing k <;> simp_all [liftN, nodes]
@[simp] theorem binders_lift (e : VExpr) : binders (e.liftN n k) = binders e := by
  induction e generalizing k <;> simp_all [liftN, binders]
@[simp] theorem cutDepth_lift (e : VExpr) : cutDepth (e.liftN n k) = cutDepth e := by
  induction e generalizing k with
  | app f a ihf iha => cases f <;> simp_all [liftN, cutDepth, ← Nat.max_assoc]
  | _ => simp_all [liftN, cutDepth]
@[simp] theorem cutTypeSize_lift (e : VExpr) : cutTypeSize (e.liftN n k) = cutTypeSize e := by
  induction e generalizing k with
  | app f a ihf iha => cases f <;> simp_all [liftN, cutTypeSize, ← Nat.max_assoc]
  | _ => simp_all [liftN, cutTypeSize]
@[simp] theorem rank_lift (e : VExpr) : rank (e.liftN n k) = rank e := by simp [rank]

/-- This attaches the endpoint diagnostic to an ACTUAL pilot certificate.
It intentionally makes no claim to count the certificate's hidden premises. -/
def sourceRank (_h : Cert env U j Γ a b) : Rank := rank a

theorem pilot_weakN_rank (henv : env.WF) (h : Cert env U j Γ a b)
    (W : Ctx.LiftN n k Γ Δ) : sourceRank (pilot_weakN henv h W) = sourceRank h :=
  rank_lift a

/-- A uniform substitution budget includes BOTH argument depth and argument size. -/
def SubBudget (D S : Nat) (σ : Subst) : Prop :=
  1 ≤ S ∧ ∀ i, binders (σ i) ≤ D ∧ nodes (σ i) ≤ S

theorem SubBudget.lift (h : SubBudget D S σ) : SubBudget D S σ.lift := by
  refine ⟨h.1, ?_⟩
  intro i
  cases i with
  | zero => exact ⟨Nat.zero_le _, h.1⟩
  | succ i => simpa [Subst.lift] using h.2 i

theorem nodes_subst (h : SubBudget D S σ) : nodes (e.subst σ) ≤ nodes e * S := by
  induction e generalizing σ with
  | bvar i => simpa [nodes] using (h.2 i).2
  | app a b iha ihb =>
    have ha := iha h; have hb := ihb h; have hS := h.1
    simp only [subst, nodes, Nat.add_mul, Nat.one_mul] at *
    omega
  | lam a b iha ihb | forallE a b iha ihb =>
    have ha := iha h; have hb := ihb h.lift; have hS := h.1
    simp only [subst, nodes, Nat.add_mul, Nat.one_mul] at *
    omega
  | proj s i e ih =>
    have he := ih h; have hS := h.1
    simp only [subst, nodes, Nat.add_mul, Nat.one_mul] at *
    omega
  | _ => simpa [subst, nodes] using h.1

theorem binders_subst (h : SubBudget D S σ) : binders (e.subst σ) ≤ binders e + D := by
  induction e generalizing σ with
  | bvar i => simpa [binders] using (h.2 i).1
  | app a b iha ihb =>
    have ha := iha h; have hb := ihb h
    simp only [subst, binders] at *
    omega
  | lam a b iha ihb | forallE a b iha ihb =>
    have ha := iha h; have hb := ihb h.lift
    simp only [subst, binders] at *
    omega
  | proj s i e ih => exact ih h
  | _ => simp [subst, binders]

theorem cutDepth_bound (e : VExpr) : cutDepth e ≤ binders e + 1 := by
  induction e with
  | app f a ihf iha =>
    cases f <;> simp only [cutDepth, binders, ← Nat.max_assoc] at * <;> omega
  | _ => simp only [cutDepth, binders, under] at * <;> (try split) <;> omega

theorem nodes_pos (e : VExpr) : 1 ≤ nodes e := by cases e <;> simp [nodes] <;> omega

theorem cutTypeSize_bound (e : VExpr) : cutTypeSize e ≤ nodes e := by
  induction e with
  | app f a ihf iha =>
    cases f <;> simp_all [cutTypeSize, nodes] <;> omega
  | _ => simp_all [cutTypeSize, nodes] <;> omega

/-- Explicit growth bound; it is not a strict decrease or certified-substitution theorem. -/
theorem rank_subst_bound (h : SubBudget D S σ) :
    (rank (e.subst σ)).1 ≤ binders e + D + 1 ∧
    (rank (e.subst σ)).2.1 ≤ nodes e * S ∧
    (rank (e.subst σ)).2.2 ≤ nodes e * S := by
  exact ⟨Nat.le_trans (cutDepth_bound _) (Nat.add_le_add_right (binders_subst h) 1),
    Nat.le_trans (cutTypeSize_bound _) (nodes_subst h), nodes_subst h⟩

abbrev P : VExpr := .sort .zero
abbrev S1 : VExpr := .sort (.succ .zero)
def arr (a b : VExpr) : VExpr := .forallE a b.lift
def tower : Nat → VExpr | 0 => P | n+1 => arr P (tower n)
def twice : VExpr := arr (.bvar 0) (.bvar 0)
def nested : Nat → VExpr | 0 => P | n+1 => .app (.lam S1 (.bvar 0)) (nested n)

@[simp] theorem tower_depth (N : Nat) : cutDepth (tower N) = 0 := by
  induction N <;> simp_all [tower, arr, cutDepth, under]
@[simp] theorem tower_cutType (N : Nat) : cutTypeSize (tower N) = 0 := by
  induction N <;> simp_all [tower, arr, cutTypeSize]
@[simp] theorem nested_depth (N : Nat) : cutDepth (nested (N+1)) = 1 := by
  induction N <;> simp_all [nested, cutDepth, under]
@[simp] theorem nested_type (N : Nat) : cutTypeSize (nested (N+1)) = 1 := by
  induction N <;> simp_all [nested, cutTypeSize, nodes]

@[simp] theorem twice_inst (a : VExpr) : twice.inst a = arr a a := by
  simp [twice, arr, lift, liftN, inst, instVar]

theorem twice_tower_decreases (N : Nat) :
    LT (rank (twice.inst (tower N))) (rank (.app (.lam S1 twice) (tower N))) := by
  rw [twice_inst]
  apply Prod.Lex.left
  simp [twice, arr, cutDepth, under, lift, liftN]

theorem nested_decreases (N : Nat) :
    LT (rank ((nested N).lift.inst P)) (rank (.app (.lam S1 (nested N).lift) P)) := by
  rw [inst_lift]
  apply Prod.Lex.left
  cases N <;> simp [nested, cutDepth, under]

/-- New problem: duplication inserts the argument under the Pi codomain binder.
Even ONE argument redex raises the maximum cut depth from zero to one. -/
theorem duplicated_argument_increases (N : Nat) :
    (rank (.app (.lam S1 twice) (nested (N+1)))).1 = 1 ∧
    (rank (twice.inst (nested (N+1)))).1 = 2 ∧
    ¬ LT (rank (twice.inst (nested (N+1))))
      (rank (.app (.lam S1 twice) (nested (N+1)))) := by
  have hs : (rank (.app (.lam S1 twice) (nested (N+1)))).1 = 1 := by
    simp [rank, twice, arr, cutDepth, under, lift, liftN]
  have ht : (rank (twice.inst (nested (N+1)))).1 = 2 := by
    simp [rank, arr, cutDepth, under]
  refine ⟨hs, ht, ?_⟩
  have mono : ∀ {r s : Rank}, LT r s → r.1 ≤ s.1 := by
    intro r s h
    cases h with
    | left _ _ h => exact Nat.le_of_lt h
    | right _ _ => exact Nat.le_refl _
  intro h
  have hm := mono h
  rw [hs, ht] at hm
  omega

/-- Literal same-type substitution for pilot synthesis is false. -/
theorem no_exact_pi_synthesis : ¬ CTy env U Γ (.forallE P P) S1 := by
  intro h
  cases h

theorem exact_synthesis_substitution_false :
    CTy env U [S1] (.bvar 0) S1 ∧
    CTy env U [] (.forallE P P) (.sort (.imax (.succ .zero) (.succ .zero))) ∧
    CConv env U [] (.sort (.imax (.succ .zero) (.succ .zero))) S1 ∧
    ¬ CTy env U [] ((.bvar 0 : VExpr).inst (.forallE P P)) (S1.inst (.forallE P P)) := by
  refine ⟨.ty_bvar .zero, .ty_forallE (.ty_sort trivial) .red_refl
    (.ty_sort trivial) .red_refl, .conv_mk .red_refl .red_refl
    (.norm_sort ⟨trivial, trivial⟩ trivial rfl), ?_⟩
  simpa [inst, instVar] using (no_exact_pi_synthesis (env := env) (U := U) (Γ := []))

/-! The multiset diagnostic retains EVERY syntactic beta cut, with its depth
and binder-type size; the following obstruction is not due to taking maxima. -/
abbrev Label := Nat × Nat
def LabelLT : Label → Label → Prop := Prod.Lex (· < ·) (· < ·)
def profile (d : Nat) : VExpr → List Label
  | .app (.lam A b) a => (d, nodes A) ::
      (profile d A ++ profile (d+1) b ++ profile d a)
  | .app f a => profile d f ++ profile d a
  | .lam A b | .forallE A b => profile d A ++ profile (d+1) b
  | .proj _ _ e => profile d e
  | _ => []

@[simp] theorem profile_lift (e : VExpr) : profile d (e.liftN n k) = profile d e := by
  induction e generalizing d k with
  | app f a ihf iha =>
    cases f <;> simp_all [liftN, profile]
  | _ => simp_all [liftN, profile]

@[simp] theorem profile_nested (N : Nat) : profile d (nested N) = List.replicate N (d,1) := by
  induction N <;> simp_all [nested, profile, nodes, List.replicate_succ]
@[simp] theorem profile_tower (N : Nat) : profile d (tower N) = [] := by
  induction N generalizing d <;> simp_all [tower, arr, profile]

/-- Standard strict multiset replacement, represented by lists modulo permutation. -/
def MultiLT (xs ys : List Label) : Prop :=
  ∃ keep removed added, ys.Perm (keep ++ removed) ∧ xs.Perm (keep ++ added) ∧
    removed ≠ [] ∧ ∀ x ∈ added, ∃ y ∈ removed, LabelLT x y

theorem label_depth_mono (h : LabelLT x y) : x.1 ≤ y.1 := by
  cases h with
  | left _ _ h => exact Nat.le_of_lt h
  | right _ _ => exact Nat.le_refl _

theorem multilt_depth_bound (h : MultiLT xs ys) (hy : ∀ y ∈ ys, y.1 ≤ D) :
    ∀ x ∈ xs, x.1 ≤ D := by
  obtain ⟨keep, removed, added, hp, hq, _, hlt⟩ := h
  intro x hx
  have hx' := hq.mem_iff.mp hx
  rcases List.mem_append.mp hx' with hk | ha
  · exact hy x (hp.mem_iff.mpr (List.mem_append.mpr (.inl hk)))
  · obtain ⟨y, hyr, hxy⟩ := hlt x ha
    exact Nat.le_trans (label_depth_mono hxy)
      (hy y (hp.mem_iff.mpr (List.mem_append.mpr (.inr hyr))))

/-- The source has two depth-zero cuts; the target has one depth-one cut. -/
theorem multiset_duplication_failure :
    profile 0 (.app (.lam S1 twice) (nested 1)) = [(0,1), (0,1)] ∧
    profile 0 (twice.inst (nested 1)) = [(0,1), (1,1)] ∧
    ¬ MultiLT (profile 0 (twice.inst (nested 1)))
      (profile 0 (.app (.lam S1 twice) (nested 1))) := by
  have hs : profile 0 (.app (.lam S1 twice) (nested 1)) = [(0,1), (0,1)] := rfl
  have ht : profile 0 (twice.inst (nested 1)) = [(0,1), (1,1)] := by
    rw [twice_inst]; rfl
  refine ⟨hs, ht, ?_⟩
  rw [hs, ht]
  intro h
  have hb := multilt_depth_bound (D := 0) h (by simp)
  have := hb (1,1) (by simp)
  omega

theorem multiset_old_tests (N : Nat) :
    MultiLT (profile 0 (twice.inst (tower N)))
      (profile 0 (.app (.lam S1 twice) (tower N))) ∧
    MultiLT (profile 0 ((nested N).lift.inst P))
      (profile 0 (.app (.lam S1 (nested N).lift) P)) := by
  constructor
  · rw [twice_inst]
    simp only [arr, profile, profile_lift, profile_tower,
      twice, lift, liftN, liftVar, nodes, List.append_nil]
    exact ⟨[], [(0,1)], [], .refl _, .refl _, by simp, by simp⟩
  · rw [inst_lift]
    simp only [profile, profile_lift, profile_nested, nodes, List.nil_append, List.append_nil]
    refine ⟨[], (0,1) :: List.replicate N (1,1), List.replicate N (0,1),
      .refl _, .refl _, by simp, ?_⟩
    intro x hx
    have hx' := List.mem_replicate.mp hx
    obtain ⟨hn, rfl⟩ := hx'
    refine ⟨(1,1), List.mem_cons.mpr (.inr ?_), ?_⟩
    · exact List.mem_replicate.mpr ⟨hn, rfl⟩
    · exact Prod.Lex.left _ _ (by decide)

/-- A small syntax predicate used ONLY to construct actual pilot witnesses. -/
inductive Core (U : Nat) : VExpr → Prop where
  | var : Core U (.bvar i)
  | sort : l.WF U → Core U (.sort l)
  | app : Core U f → Core U a → Core U (.app f a)
  | lam : Core U A → Core U b → Core U (.lam A b)
  | pi : Core U A → Core U b → Core U (.forallE A b)

theorem Core.weak (h : Core U e) : Core U (e.liftN n k) := by
  induction h generalizing k with
  | var => exact .var
  | sort h => exact .sort h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2

theorem Core.refl (h : Core U e) : CStep env U Γ e e ∧ CNorm env U Γ e e := by
  induction h generalizing Γ with
  | var => exact ⟨.step_bvar, .norm_bvar⟩
  | sort h => exact ⟨.step_sort, .norm_sort h h rfl⟩
  | app _ _ ih1 ih2 => exact ⟨.step_app ih1.1 ih2.1, .norm_app ih1.2 ih2.2⟩
  | lam _ _ ih1 ih2 => exact ⟨.step_lam ih1.1 ih2.1,
      .norm_lam (.conv_mk .red_refl .red_refl ih1.2) ih2.2⟩
  | pi _ _ ih1 ih2 => exact ⟨.step_forallE ih1.1 ih2.1,
      .norm_forallE (.conv_mk .red_refl .red_refl ih1.2) ih2.2⟩

theorem Core.convRefl (h : Core U e) : CConv env U Γ e e :=
  .conv_mk .red_refl .red_refl h.refl.2

theorem core_nested (N : Nat) : Core U (nested N) := by
  induction N with
  | zero => exact .sort trivial
  | succ N ih => exact .app (.lam (.sort trivial) .var) ih

theorem core_tower (N : Nat) : Core U (tower N) := by
  induction N with
  | zero => exact .sort trivial
  | succ N ih => exact .pi (.sort trivial) ih.weak

theorem core_twice : Core U twice := .pi .var .var

theorem nested_ty (N : Nat) : CTy env U Γ (nested N) S1 := by
  induction N with
  | zero => exact .ty_sort trivial
  | succ N ih =>
    exact .ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl (.ty_bvar .zero))
      .red_refl ih ((Core.sort (l := .succ .zero) trivial).convRefl)

theorem twice_ty : CTy env U [S1] twice (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .ty_forallE (.ty_bvar .zero) .red_refl (.ty_bvar (.succ .zero)) .red_refl

/-- Actual pilot certificates for the two old contraction tests. -/
theorem old_tests_pilot (N : Nat) :
    CStep env U [] (.app (.lam S1 twice) (tower N)) (twice.inst (tower N)) ∧
    CStep env U [] (.app (.lam S1 (nested N).lift) P) (nested N) := by
  refine ⟨.step_beta core_twice.refl.1 (core_tower N).refl.1, ?_⟩
  simpa only [inst_lift] using
    (Cert.step_beta (Γ := []) (A := S1) (core_nested N).weak.refl.1
      (Core.sort (l := .zero) trivial).refl.1 :
      CStep env U [] (.app (.lam S1 (nested N).lift) P) ((nested N).lift.inst P))

/-- The new obstruction is a well-typed, actual PILOT beta contraction, in every env.
This is not a claim about a pair of conversions or about admissible transitivity. -/
theorem duplication_pilot (henv : env.WF) (N : Nat) :
    CTy env U [] (.app (.lam S1 twice) (nested (N+1)))
      (.sort (.imax (.succ .zero) (.succ .zero))) ∧
    CTy env U [] (twice.inst (nested (N+1)))
      (.sort (.imax (.succ .zero) (.succ .zero))) ∧
    CConv env U [] (.app (.lam S1 twice) (nested (N+1))) (twice.inst (nested (N+1))) := by
  have hs : CStep env U [] (.app (.lam S1 twice) (nested (N+1)))
      (twice.inst (nested (N+1))) := .step_beta core_twice.refl.1 (core_nested _).refl.1
  have ht : Core U (twice.inst (nested (N+1))) := by
    rw [twice_inst]; exact .pi (core_nested _) (core_nested _).weak
  refine ⟨.ty_app (.ty_lam (.ty_sort (l := .succ .zero) trivial) .red_refl twice_ty) .red_refl
    (nested_ty _) ((Core.sort (l := .succ .zero) trivial).convRefl), ?_,
    .conv_mk (.red_step hs .red_refl) .red_refl ht.refl.2⟩
  rw [twice_inst]
  exact .ty_forallE (nested_ty _) .red_refl
    (pilot_weakN henv (nested_ty _) (.one (A := nested (N+1)))) .red_refl

/-- This quantifies over actual pilot certificates, but is ONLY an endpoint-rank
obstruction for beta contraction, not the requested obstruction to composition. -/
theorem no_smaller_pilot_contractum (N : Nat)
    (h : CTy env U [] (.app (.lam S1 twice) (nested (N+1))) T)
    (h' : CTy env U [] (twice.inst (nested (N+1))) T') :
    ¬ LT (sourceRank h') (sourceRank h) := (duplicated_argument_increases N).2.2

#print axioms pilot_weakN
#print axioms rank_wf
#print axioms nodes_lift
#print axioms binders_lift
#print axioms cutDepth_lift
#print axioms cutTypeSize_lift
#print axioms rank_lift
#print axioms pilot_weakN_rank
#print axioms SubBudget.lift
#print axioms nodes_subst
#print axioms binders_subst
#print axioms cutDepth_bound
#print axioms nodes_pos
#print axioms cutTypeSize_bound
#print axioms rank_subst_bound
#print axioms tower_depth
#print axioms tower_cutType
#print axioms nested_depth
#print axioms nested_type
#print axioms twice_inst
#print axioms twice_tower_decreases
#print axioms nested_decreases
#print axioms duplicated_argument_increases
#print axioms no_exact_pi_synthesis
#print axioms exact_synthesis_substitution_false
#print axioms profile_lift
#print axioms profile_nested
#print axioms profile_tower
#print axioms label_depth_mono
#print axioms multilt_depth_bound
#print axioms multiset_duplication_failure
#print axioms multiset_old_tests
#print axioms Core.weak
#print axioms Core.refl
#print axioms Core.convRefl
#print axioms core_nested
#print axioms core_tower
#print axioms core_twice
#print axioms nested_ty
#print axioms twice_ty
#print axioms old_tests_pilot
#print axioms duplication_pilot
#print axioms no_smaller_pilot_contractum
end Lean4Lean.Round5
