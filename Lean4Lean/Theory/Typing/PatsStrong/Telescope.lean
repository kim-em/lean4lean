import Lean4Lean.Theory.Typing.Strong

/-! # Telescope instantiation in the strong system

Step (iii) of the `patsStrong` argument (PORT_PLAN §4.3): the generic typing of an ι rule
lives in the telescope context of the rule's holes (parameters, motives, minors, fields) and
has to be instantiated by the actual arguments of a redex. #43 does simultaneous substitution
in the strong system through `IsDefEqStrong.substEq'`, which takes `OrderedStrong env` — i.e.
`PatsStrongOn env`, the obligation itself — only because `Ctx.SubstEq` types the substituted
terms in the weak system and strengthens them with `IsDefEq.strong`. Single-variable
instantiation (`IsDefEqStrong.instN`) needs `Ordered env` alone, so a telescope is
instantiated one outermost variable at a time (`VExpr.instOuter`, as on the
`agent/verify-inductives` branch) with no appeal to `PatsStrongOn`. This is the one
substitution theorem the `patsStrong` proof may use at the environment it is proving
`PatsStrongOn` for. -/

namespace Lean4Lean

namespace VExpr

/-- Instantiate the outermost binders of a telescope body one at a time: the first argument
replaces the outermost variable (de Bruijn index `args.length - 1`), and so on. -/
def instOuter : VExpr → List VExpr → VExpr
  | body, [] => body
  | body, a :: as => instOuter (body.inst a as.length) as

@[simp] theorem instOuter_nil (body : VExpr) : body.instOuter [] = body := rfl

@[simp] theorem instOuter_cons (body a : VExpr) (as : List VExpr) :
    body.instOuter (a :: as) = (body.inst a as.length).instOuter as := rfl

@[simp] theorem instOuter_app (f a : VExpr) (args : List VExpr) :
    (f.app a).instOuter args = (f.instOuter args).app (a.instOuter args) := by
  induction args generalizing f a with
  | nil => rfl
  | cons _ _ ih => simp [inst, ih]

@[simp] theorem instOuter_sort (u : VLevel) (args : List VExpr) :
    (sort u).instOuter args = sort u := by
  induction args <;> simp [inst, *]

theorem instOuter_mkApps (fn : VExpr) (xs args : List VExpr) :
    (fn.mkApps xs).instOuter args = (fn.instOuter args).mkApps (xs.map (·.instOuter args)) := by
  induction xs generalizing fn with
  | nil => rfl
  | cons x xs ih => simp [mkApps_cons, ih]

/-- A closed term is unchanged by telescope instantiation. -/
theorem ClosedN.instOuter_eq {X : VExpr} (h : X.ClosedN 0) (args : List VExpr) :
    X.instOuter args = X := by
  induction args generalizing X with
  | nil => rfl
  | cons a as ih => rw [instOuter_cons, h.instN_eq (Nat.zero_le _), ih h]

/-- Instantiating the `n` outermost binders of an `n`-fold lift undoes the lift. -/
theorem instOuter_liftN (X : VExpr) : ∀ (args : List VExpr), (X.liftN args.length).instOuter args = X
  | [] => by simp
  | a :: as => by
    rw [instOuter_cons, List.length_cons, inst_liftN_lo]
    exact instOuter_liftN X as

theorem bvarsDesc_succ (lo n : Nat) : bvarsDesc lo (n+1) = bvar (lo + n) :: bvarsDesc lo n := by
  simp [bvarsDesc, List.range_succ]

theorem bvarsDesc_add (lo n m : Nat) : bvarsDesc lo (n + m) = bvarsDesc (lo + m) n ++ bvarsDesc lo m := by
  induction n with
  | zero => simp [bvarsDesc]
  | succ n ih =>
    rw [Nat.add_right_comm, bvarsDesc_succ, bvarsDesc_succ, ih, List.cons_append]
    congr 2; omega

/-- The variables of a telescope context, instantiated by the arguments, are the arguments. -/
theorem instOuter_bvarsDesc : ∀ (args : List VExpr),
    (bvarsDesc 0 args.length).map (·.instOuter args) = args
  | [] => by simp [bvarsDesc]
  | a :: as => by
    rw [List.length_cons, bvarsDesc_succ, List.map_cons, instOuter_cons, Nat.zero_add]
    simp only [inst, instVar, Nat.lt_irrefl, if_false, if_true]
    rw [instOuter_liftN]
    congr 1
    conv => rhs; rw [← instOuter_bvarsDesc as]
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < as.length ∧ bvar i = x := by simpa [bvarsDesc] using hx
    simp [inst, instVar, hi]

/-- The context of the de Bruijn prefix `Δ` after the variable below it is instantiated by
`e₀`: entry `Δ[p]` sits under `Δ.length - 1 - p` binders. -/
def instTail (e₀ : VExpr) : List VExpr → List VExpr
  | [] => []
  | A :: Δ => A.inst e₀ Δ.length :: instTail e₀ Δ

@[simp] theorem instTail_length (e₀ : VExpr) : ∀ (Δ : List VExpr), (instTail e₀ Δ).length = Δ.length
  | [] => rfl
  | _ :: Δ => by simp [instTail, instTail_length e₀ Δ]

theorem instTail_getElem (e₀ : VExpr) : ∀ (Δ : List VExpr) (p : Nat) (hp : p < Δ.length),
    (instTail e₀ Δ)[p]'(by simp [hp]) = Δ[p].inst e₀ (Δ.length - 1 - p)
  | A :: Δ, 0, _ => by simp [instTail]
  | A :: Δ, p+1, hp => by
    simp only [instTail, List.getElem_cons_succ, List.length_cons]
    rw [instTail_getElem e₀ Δ p (by simpa using hp)]
    congr 1; simp only [List.length_cons] at hp ⊢; omega

/-- A telescope `ds` (outermost first) after its enclosing variable is instantiated by `a`:
`ds[j]` sits under `j` binders of the telescope. -/
def instDoms (a : VExpr) (ds : List VExpr) : List VExpr := (instTail a ds.reverse).reverse

@[simp] theorem instDoms_length (a : VExpr) (ds : List VExpr) : (instDoms a ds).length = ds.length := by
  simp [instDoms]

theorem instDoms_reverse (a : VExpr) (ds : List VExpr) : (instDoms a ds).reverse = instTail a ds.reverse := by
  simp [instDoms]

theorem instDoms_getElem (a : VExpr) (ds : List VExpr) (j : Nat) (hj : j < ds.length) :
    (instDoms a ds)[j]'(by simp [hj]) = ds[j].inst a j := by
  simp only [instDoms]
  rw [List.getElem_reverse, instTail_getElem, List.getElem_reverse]
  · simp only [List.length_reverse, instTail_length]
    congr 2 <;> omega
  all_goals simp; omega

end VExpr

/-- Instantiating the variable below a de Bruijn prefix `Δ`, in one `Ctx.InstN` step per
entry of `Δ`. -/
theorem Ctx.InstN.append {Γ₀ : List VExpr} {e₀ A₀ : VExpr} :
    ∀ (Δ : List VExpr), Ctx.InstN Γ₀ e₀ A₀ Δ.length (Δ ++ A₀ :: Γ₀) (VExpr.instTail e₀ Δ ++ Γ₀)
  | [] => .zero
  | _ :: Δ => .succ (append Δ)

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Instantiating the variable below a de Bruijn prefix preserves `CtxStrong`: each entry of
the prefix is instantiated by `IsDefEqStrong.instN` in the already-instantiated context below
it. Needs `Ordered env` only. -/
theorem CtxStrong.instTail (henv : Ordered env) {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (hΓ₀ : CtxStrong env U Γ₀) (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) :
    ∀ {Δ : List VExpr}, CtxStrong env U (Δ ++ A₀ :: Γ₀) → CtxStrong env U (VExpr.instTail e₀ Δ ++ Γ₀)
  | [], h => h.1
  | _ :: Δ, ⟨h, u, hA⟩ =>
    have ih := CtxStrong.instTail henv hΓ₀ h₀ (Δ := Δ) h
    ⟨ih, u, IsDefEqStrong.instN henv h₀ hΓ₀ (Ctx.InstN.append Δ) hA ih⟩

/-- **Telescope instantiation in the strong system.** A strong judgement in the context
`doms.reverse ++ Γ` of a telescope `doms` (outermost domain first) over `Γ`, instantiated by
arguments `args` each strongly typed in `Γ` at its domain instantiated by the earlier
arguments, is a strong judgement in `Γ`. The strong counterpart of the branch's
`IsDefEqU.instOuter_telescope` (`RecursorLemmas.lean`), assuming `Ordered env` only: it goes
through `IsDefEqStrong.instN` once per argument and never through `substEq'`. -/
theorem IsDefEqStrong.instOuter_telescope (henv : Ordered env) :
    ∀ {args doms : List VExpr} {Γ : List VExpr} {e₁ e₂ A : VExpr},
      CtxStrong env U Γ → CtxStrong env U (doms.reverse ++ Γ) →
      env.IsDefEqStrong U (doms.reverse ++ Γ) e₁ e₂ A → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.IsDefEqStrong U Γ args[j] args[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEqStrong U Γ (e₁.instOuter args) (e₂.instOuter args) (A.instOuter args)
  | [], doms, Γ, e₁, e₂, A, _, _, H, hlen, _ => by
    cases doms with
    | nil => simpa using H
    | cons => simp at hlen
  | a :: as, doms, Γ, e₁, e₂, A, hΓ, hΓg, H, hlen, hty => by
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hctx : (d :: ds).reverse ++ Γ = ds.reverse ++ d :: Γ := by
        rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [hctx] at H hΓg
      have h₀ : env.IsDefEqStrong U Γ a a d := by
        have := hty 0 (by simp) (by simp)
        simpa only [List.getElem_cons_zero, List.take_zero, VExpr.instOuter_nil] using this
      have hΓ' := CtxStrong.instTail henv hΓ h₀ hΓg
      have H' := IsDefEqStrong.instN henv h₀ hΓ (Ctx.InstN.append ds.reverse) H hΓ'
      rw [List.length_reverse, ← hlen] at H'
      rw [← VExpr.instDoms_reverse] at H' hΓ'
      simp only [VExpr.instOuter_cons]
      refine IsDefEqStrong.instOuter_telescope henv hΓ hΓ' H' (by simp [hlen]) ?_
      intro j hj hj'
      have hj'' : j < ds.length := by simpa using hj'
      rw [VExpr.instDoms_getElem a ds j hj'']
      have := hty (j+1) (by simpa using hj) (by simpa using hj'')
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at this
      exact this

end VEnv
end Lean4Lean
