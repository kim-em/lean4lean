import Lean4Lean.Theory.Typing.IotaLemmas

/-!
# Iota reduction from the shape of a stored recursor rule

A recursor rule is stored as a closed lambda-wrapped equation whose left-hand side is the recursor
applied to its parameters, motives, minors, indices, and a constructor application. This file shows
that such a rule, applied to the actual arguments of a recursor application whose major premise
reduces to a constructor application, yields the instantiated right-hand side. Everything is
derived from the syntactic shape of the rule together with unique typing and injectivity of the
inductive type constant: the arguments are typed at the rule's binders because the pattern
variables of the left-hand side are typed at the recursor's own telescope.
-/

namespace Lean4Lean

namespace VExpr

/-- The simultaneous substitution performed by `instOuter`: the first argument replaces the
outermost variable. -/
def Subst.ofList (args : List VExpr) : Subst := fun k =>
  if h : k < args.length then args[args.length - 1 - k] else .bvar (k - args.length)

theorem Subst.liftN_apply (σ : Subst) (n k : Nat) :
    σ.liftN n k = if k < n then .bvar k else (σ (k - n)).liftN n := by
  induction n generalizing k with
  | zero => simp [Subst.liftN, liftN_zero]
  | succ n ih =>
    cases k with
    | zero => simp [Subst.liftN, Subst.lift]
    | succ k =>
      simp only [Subst.liftN, Subst.lift, ih, Nat.succ_lt_succ_iff, Nat.succ_sub_succ]
      split
      · show VExpr.liftN 1 (bvar k) = bvar (k + 1)
        rw [VExpr.liftN, liftVar_base']
      · rw [← liftN_succ]

theorem instOuter_eq_subst_aux (a : VExpr) (as : List VExpr) :
    (a.liftN as.length).subst (Subst.ofList as) = a := by
  rw [liftN_subst]
  conv => rhs; rw [← subst_id (e := a)]
  congr 1
  funext k
  simp only [Subst.lift_l, Subst.id, Lift.liftVar_consN_skipN, liftVar_base', Subst.ofList]
  rw [dif_neg (by omega)]
  congr 1; omega

theorem instOuter_eq_subst (body : VExpr) (args : List VExpr) :
    body.instOuter args = body.subst (Subst.ofList args) := by
  induction args generalizing body with
  | nil =>
    have : Subst.ofList [] = Subst.id := by funext k; simp [Subst.ofList, Subst.id]
    simp [this]
  | cons a as ih =>
    rw [instOuter_cons, ih, instN_eq, subst_subst]
    congr 1
    funext k
    simp only [Subst.comp, Subst.liftN_apply, Subst.ofList, List.length_cons]
    by_cases hk : k < as.length
    · rw [if_pos hk]
      simp only [subst_bvar, Subst.ofList, dif_pos hk, dif_pos (Nat.lt_succ_of_lt hk)]
      rw [List.getElem_cons]
      split
      · omega
      · congr 1; omega
    · rw [if_neg hk]
      by_cases hk' : k = as.length
      · subst hk'
        simp only [Subst.one, Subst.cons, Nat.sub_self, dif_pos (Nat.lt_succ_self _),
          Nat.add_sub_cancel, List.getElem_cons_zero]
        rw [instOuter_eq_subst_aux]
      · have hk2 : as.length < k := by omega
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨d, hd⟩ : ∃ d, k' + 1 - as.length = d + 1 := ⟨k' - as.length, by omega⟩
        rw [hd]
        simp only [Subst.one, Subst.cons, Subst.id, liftN, liftVar_base', subst_bvar, Subst.ofList]
        rw [dif_neg (by omega), dif_neg (by omega)]
        congr 1
        omega

/-- Two substitutions agreeing below the closure bound act identically. -/
theorem subst_congr_closedN {e : VExpr} (he : e.ClosedN k) {σ σ' : Subst}
    (h : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with (simp [ClosedN] at he; simp only [subst])
  | bvar i => exact h _ he
  | app _ _ ih1 ih2 => rw [ih1 he.1 h, ih2 he.2 h]
  | proj _ _ _ ihe => rw [ihe he h]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    rw [ih1 he.1 h, ih2 he.2 (σ' := σ'.lift)]
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp only [Subst.lift]; rw [h i (by omega)]

def Subst.shift (n : Nat) : Subst := fun i => .bvar (i + n)

theorem liftN_eq_subst (e : VExpr) (n : Nat) :
    e.liftN n = e.subst (Subst.shift n) := by
  have := liftN_subst (e := e) (n := n) (k := 0) (σ := Subst.id)
  rw [subst_id] at this
  rw [this]
  congr 1
  funext i
  simp [Subst.lift_l, Subst.id, Lift.liftVar_skipN, Subst.shift]

theorem Subst.ofList_lt (args : List VExpr) (h : k < args.length) :
    Subst.ofList args k = args[args.length - 1 - k] := dif_pos h

theorem Subst.ofList_ge (args : List VExpr) (h : args.length ≤ k) :
    Subst.ofList args k = .bvar (k - args.length) := dif_neg (Nat.not_lt.2 h)

/-- Instantiating an instantiation is instantiating at the instantiated arguments. -/
theorem instOuter_instOuter (X : VExpr) (vs args : List VExpr) (hX : X.ClosedN vs.length) :
    (X.instOuter vs).instOuter args = X.instOuter (vs.map (·.instOuter args)) := by
  simp only [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (vs.map _) (by simpa using hi), List.getElem_map]

/-- Lifting an instantiation lifts the arguments. -/
theorem liftN_instOuter (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length) (n : Nat) :
    (X.instOuter args).liftN n = X.instOuter (args.map (·.liftN n)) := by
  simp only [instOuter_eq_subst, liftN_eq_subst]
  rw [subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map]

/-- Instantiating at the variables of an enclosing context is a lift. -/
theorem instOuter_range_bvar (X : VExpr) (j n : Nat) (hX : X.ClosedN j) (hj : j ≤ n) :
    X.instOuter ((List.range j).map fun k => VExpr.bvar (n - 1 - k)) = X.liftN (n - j) := by
  simp only [instOuter_eq_subst, liftN_eq_subst]
  apply subst_congr_closedN hX
  intro i hi
  rw [Subst.ofList_lt _ (by simpa using hi)]
  simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range, Subst.shift]
  congr 1
  omega

/-- The first `n` of `total` binders, seen from under all `total` binders: the outermost binder
first. -/
def bvarRange (n total : Nat) : List VExpr :=
  (List.range n).map fun j => VExpr.bvar (total - 1 - j)

@[simp] theorem bvarRange_length (n total : Nat) : (bvarRange n total).length = n := by
  simp [bvarRange]

theorem bvarRange_getElem (n total : Nat) (j : Nat) (h : j < n) :
    (bvarRange n total)[j]'(by simpa using h) = VExpr.bvar (total - 1 - j) := by
  simp [bvarRange]

theorem bvarRange_take (n total k : Nat) (h : k ≤ n) :
    (bvarRange n total).take k = bvarRange k total := by
  simp only [bvarRange, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bvarRange_zero (total : Nat) : bvarRange 0 total = [] := rfl

@[simp] theorem instL_bvarRange (n total : Nat) (ls : List VLevel) :
    (bvarRange n total).map (VExpr.instL ls) = bvarRange n total := by
  simp [bvarRange, List.map_map, Function.comp_def, VExpr.instL]

theorem bvarRange_map_liftN (n total k : Nat) (h : n ≤ total) :
    (bvarRange n total).map (VExpr.liftN k) = bvarRange n (total + k) := by
  simp only [bvarRange, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  simp only [Function.comp_def, VExpr.liftN, liftVar_base']
  congr 1
  omega

/-- Instantiating the variables of a binder range selects the corresponding arguments. -/
theorem instOuter_bvarRange (n total : Nat) (args : List VExpr) (hn : n ≤ total)
    (htot : total ≤ args.length) :
    (bvarRange n total).map (·.instOuter args) = (args.drop (args.length - total)).take n := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.length_map, bvarRange_length] at h1
    simp only [List.getElem_map, bvarRange_getElem n total j h1]
    rw [instOuter_bvar args (by omega), List.getElem_take, List.getElem_drop]
    congr 1
    omega

theorem instOuter_range_bvar' (X : VExpr) (j n : Nat) (hX : X.ClosedN j) (hj : j ≤ n) :
    X.instOuter (bvarRange j n) = X.liftN (n - j) :=
  instOuter_range_bvar X j n hX hj

theorem _root_.Lean4Lean.Lookup.of_getElem : ∀ {Γ : List VExpr} {i : Nat} (h : i < Γ.length),
    Lookup Γ i (Γ[i].liftN (i + 1))
  | _ :: _, 0, _ => .zero
  | _ :: Γ, i + 1, h => by
    have := Lookup.of_getElem (Γ := Γ) (i := i) (by simpa using h)
    simp only [List.getElem_cons_succ]
    rw [VExpr.liftN_succ]
    exact .succ this

/-- The variable for the `j`-th binder of a reversed telescope. -/
theorem _root_.Lean4Lean.Lookup.reverse_append (doms Γ : List VExpr) (j : Nat)
    (hj : j < doms.length) :
    Lookup (doms.reverse ++ Γ) (doms.length - 1 - j) (doms[j].liftN (doms.length - j)) := by
  have := Lookup.of_getElem (Γ := doms.reverse ++ Γ) (i := doms.length - 1 - j) (by simp; omega)
  rw [List.getElem_append_left (by simp; omega), List.getElem_reverse] at this
  have e1 : doms.length - 1 - (doms.length - 1 - j) = j := by omega
  have e2 : doms.length - 1 - j + 1 = doms.length - j := by omega
  have e3 : doms[doms.length - 1 - (doms.length - 1 - j)]'(by omega) = doms[j] := by
    congr 1
  rwa [e3, e2] at this

theorem ClosedN.of_mkApps_fn {fn : VExpr} {args : List VExpr}
    (h : (VExpr.mkApps fn args).ClosedN k) : fn.ClosedN k := by
  induction args generalizing fn with
  | nil => exact h
  | cons a as ih => exact (ih h).1

theorem ClosedN.of_mkApps_arg {fn : VExpr} {args : List VExpr}
    (h : (VExpr.mkApps fn args).ClosedN k) : ∀ a ∈ args, a.ClosedN k := by
  induction args generalizing fn with
  | nil => simp
  | cons a as ih =>
    simp only [VExpr.mkApps, List.foldl_cons] at h
    have := ih h
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact (ClosedN.of_mkApps_fn h).2
    · exact this b hb

end VExpr
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Peeling a lambda telescope typed at the matching forall telescope. -/
theorem HasType.wrapLams_inv (henv : VEnv.WF env) :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body T : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (VExpr.wrapLams doms body) (VExpr.wrapForalls doms T) →
      OnCtx (doms.reverse ++ Γ) (env.IsType U) ∧
      env.HasType U (doms.reverse ++ Γ) body T := by
  intro doms
  induction doms with
  | nil => intro Γ body T hΓ H; exact ⟨hΓ, H⟩
  | cons d ds ih =>
    intro Γ body T hΓ H
    change env.HasType U Γ (.lam d (VExpr.wrapLams ds body)) (.forallE d (VExpr.wrapForalls ds T)) at H
    have ⟨B, hB, hbody⟩ := H.lam_inv' henv hΓ
    have hd : env.IsType U Γ d := (IsType.forallE_inv henv.ordered (H.isType henv.ordered hΓ)).1
    have hΓ' : OnCtx (d :: Γ) (env.IsType U) := And.intro hΓ hd
    have ⟨_, _, hBT⟩ := hB.forallE_inv henv hΓ
    have hbody' := hbody.defeqU_r henv hΓ' ⟨_, hBT⟩
    have := ih hΓ' hbody'
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Every domain of a well-formed telescope is closed under the binders before it. -/
theorem IsType.wrapForalls_inv (henv : VEnv.WF env) :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body : VExpr},
      OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls doms body) →
      OnCtx (doms.reverse ++ Γ) (env.IsType U) ∧
      env.IsType U (doms.reverse ++ Γ) body := by
  intro doms
  induction doms with
  | nil => intro Γ body hΓ H; exact ⟨hΓ, H⟩
  | cons d ds ih =>
    intro Γ body hΓ H
    change env.IsType U Γ (.forallE d (VExpr.wrapForalls ds body)) at H
    have ⟨hd, hrest⟩ := IsType.forallE_inv henv.ordered H
    have hΓ' : OnCtx (d :: Γ) (env.IsType U) := And.intro hΓ hd
    have := ih hΓ' hrest
    simpa [List.reverse_cons, List.append_assoc] using this

theorem _root_.Lean4Lean.OnCtx.getElem_closedN (henv : VEnv.WF env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (i : Nat) (hi : i < Γ.length) :
    Γ[i].ClosedN (Γ.length - 1 - i) := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons A Γ ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
      have ⟨_, h⟩ := hΓ.2
      exact h.closedN henv.ordered (CtxWF.closed henv.ordered hΓ.1)
    | succ i =>
      simp only [List.getElem_cons_succ, List.length_cons]
      have := ih hΓ.1 i (by simp at hi; omega)
      rwa [show Γ.length + 1 - 1 - (i + 1) = Γ.length - 1 - i by omega]

/-- The domains of a closed telescope are closed under the binders before them. -/
theorem _root_.Lean4Lean.OnCtx.reverse_getElem_closedN (henv : VEnv.WF env) {doms Γ : List VExpr}
    (hΓ : OnCtx (doms.reverse ++ Γ) (env.IsType U)) (j : Nat) (hj : j < doms.length) :
    doms[j].ClosedN (j + Γ.length) := by
  have := hΓ.getElem_closedN henv (doms.length - 1 - j) (by simp; omega)
  rw [List.getElem_append_left (by simp; omega), List.getElem_reverse] at this
  simp only [List.length_append, List.length_reverse] at this
  have e1 : doms.length - 1 - (doms.length - 1 - j) = j := by omega
  have e2 : doms.length + Γ.length - 1 - (doms.length - 1 - j) = j + Γ.length := by omega
  rw [e2] at this
  have e3 : doms[doms.length - 1 - (doms.length - 1 - j)] = doms[j] := by simp only [e1]
  rwa [e3] at this

/-- Instantiating a reversed domain list one binder at a time. -/
theorem _root_.Lean4Lean.Ctx.InstN.reverse (ds : List VExpr) :
    ∀ {k Γ₁ Γ₂}, Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ₂ →
      Ctx.InstN Γ₀ e₀ A₀ (ds.length + k) (ds.reverse ++ Γ₁)
        ((VExpr.instDomains ds e₀ k).reverse ++ Γ₂) := by
  induction ds with
  | nil => intro k Γ₁ Γ₂ W; simpa [VExpr.instDomains] using W
  | cons d ds ih =>
    intro k Γ₁ Γ₂ W
    have := ih (k := k + 1) (Γ₁ := d :: Γ₁) (Γ₂ := d.inst e₀ k :: Γ₂) (.succ W)
    simp only [List.length_cons, VExpr.instDomains, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    rwa [show ds.length + 1 + k = ds.length + (k + 1) by omega]

/-- A defeq under a telescope, instantiated at arguments typed along the telescope. -/
theorem IsDefEqU.instOuter_telescope (henv : VEnv.WF env) :
    ∀ {doms args : List VExpr} {Γ : List VExpr} {X Y : VExpr},
      env.IsDefEqU U (doms.reverse ++ Γ) X Y → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEqU U Γ (X.instOuter args) (Y.instOuter args) := by
  intro doms args
  induction args generalizing doms with
  | nil =>
    intro Γ X Y H hlen _
    cases doms with
    | nil => simpa using H
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro Γ X Y H hlen hty
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons] at hlen
      have ha : env.HasType U Γ a d := by
        have := hty 0 (by simp) (by simp)
        simpa only [List.getElem_cons_zero, List.take_zero, VExpr.instOuter_nil] using this
      have W : Ctx.InstN Γ a d (ds.length + 0) (ds.reverse ++ d :: Γ)
          ((VExpr.instDomains ds a 0).reverse ++ Γ) := Ctx.InstN.reverse ds .zero
      have H' : env.IsDefEqU U (ds.reverse ++ d :: Γ) X Y := by
        simpa [List.reverse_cons, List.append_assoc] using H
      obtain ⟨A, H'⟩ := H'
      have H'' := H'.instN henv.ordered ha W
      simp only [VExpr.instOuter_cons]
      rw [show as.length = ds.length + 0 by omega]
      refine ih (doms := VExpr.instDomains ds a 0) ⟨_, H''⟩ (by simpa using hlen) ?_
      intro j hj hj'
      have := hty (j + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take] at this
      rw [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')]
      rwa [show min j as.length = 0 + j by omega] at this

/-- Left congruence of an application spine: the head may be replaced by a definitionally equal
head as long as the spine is well formed. -/
theorem IsDefEqU.mkApps_congr_left (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {f f' : VExpr},
      env.IsDefEqU U Γ f f' → VExpr.WF env U Γ (VExpr.mkApps f args) →
      env.IsDefEqU U Γ (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  intro args
  induction args with
  | nil => intro f f' H _; simpa [VExpr.mkApps] using H
  | cons a as ih =>
    intro f f' H hwf
    simp only [VExpr.mkApps, List.foldl_cons] at hwf ⊢
    have hfa : VExpr.WF env U Γ (.app f a) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f a) hwf
    have ⟨A, B, hf, ha⟩ := hfa.app_inv henv.ordered hΓ
    have hff' : env.IsDefEq U Γ f f' (.forallE A B) := H.of_l henv hΓ hf
    exact ih ⟨_, hff'.appDF ha⟩ hwf

end VEnv

/-! ## Shapes of recursors, constructors, and iota rules -/

/-- The syntactic shape of a recursor's type: a telescope of parameters, motives, minors,
indices, and the major premise, whose domain is the inductive type applied to the parameter and
index variables. -/
structure VRecursorShape (env : VEnv) (recName : Name)
    (recUvars nparams nmotives nminors nindices : Nat) (indName : Name) (indLevels : List VLevel)
    where
  type : VExpr
  const : env.constants recName = some ⟨recUvars, type⟩
  doms : List VExpr
  result : VExpr
  type_eq : type = VExpr.wrapForalls doms result
  doms_length : doms.length = nparams + nmotives + nminors + nindices + 1
  major_eq : doms[nparams + nmotives + nminors + nindices]? =
    some (VExpr.mkApps (.const indName indLevels)
      (VExpr.bvarRange nparams (nparams + nmotives + nminors + nindices) ++
        VExpr.bvarRange nindices nindices))

/-- The syntactic shape of a constructor's type: a telescope of parameters and fields whose result
is the inductive type at the universe parameters, applied to the parameter variables and index
expressions. -/
structure VConstructorShape (env : VEnv) (ctorName : Name) (ctorUvars nparams nfields : Nat)
    (indName : Name) where
  type : VExpr
  const : env.constants ctorName = some ⟨ctorUvars, type⟩
  doms : List VExpr
  indices : List VExpr
  type_eq : type = VExpr.wrapForalls doms
    (VExpr.mkApps (.const indName (VLevel.params ctorUvars))
      (VExpr.bvarRange nparams (nparams + nfields) ++ indices))
  doms_length : doms.length = nparams + nfields

/-- The syntactic shape of a stored iota rule: a closed lambda-wrapped equation over parameters,
motives, minors, and fields, whose left-hand side is the recursor applied to the parameter,
motive, and minor variables, index expressions, and the constructor applied to the parameter and
field variables. -/
structure VIotaRuleShape (env : VEnv) (recName : Name)
    (recUvars nparams nmotives nminors nindices : Nat) (ctorName : Name) (ctorLevels : List VLevel)
    (nfields : Nat) (df : VDefEq) where
  defeq : env.defeqs df
  uvars : df.uvars = recUvars
  doms : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_eq : df.lhs = VExpr.wrapLams doms lhsBody
  rhs_eq : df.rhs = VExpr.wrapLams doms rhsBody
  type_eq : df.type = VExpr.wrapForalls doms typeBody
  doms_length : doms.length = nparams + nmotives + nminors + nfields
  indexArgs : List VExpr
  indexArgs_length : indexArgs.length = nindices
  lhs_pattern : lhsBody = VExpr.mkApps (.const recName (VLevel.params recUvars))
    (VExpr.bvarRange (nparams + nmotives + nminors) doms.length ++ indexArgs ++
      [VExpr.mkApps (.const ctorName ctorLevels)
        (VExpr.bvarRange nparams doms.length ++ VExpr.bvarRange nfields nfields)])

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- A recursor application spine types its arguments along the recursor telescope; in particular
the major premise is typed at the inductive type applied to the parameters and indices. -/
theorem VRecursorShape.spine_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VRecursorShape env recName recUvars nparams nmotives nminors nindices indName indLevels)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major]))) :
    (∀ j (hj : j < pre.length) (hj' : j < (H.doms.map (VExpr.instL ls)).length),
      env.HasType U Γ pre[j] ((H.doms.map (VExpr.instL ls))[j].instOuter (pre.take j))) ∧
    env.HasType U Γ major (VExpr.mkApps (.const indName (indLevels.map (VLevel.inst ls)))
      (pre.take nparams ++ pre.drop (nparams + nmotives + nminors))) := by
  have hc := HasType.const (Γ := Γ) H.const hls (by simpa using hlsl)
  rw [H.type_eq, VExpr.instL_wrapForalls] at hc
  have hlen : (pre ++ [major]).length = (H.doms.map (VExpr.instL ls)).length := by
    simp [hpre, H.doms_length]
  have ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hc hwf hlen
  refine ⟨fun j hj hj' => ?_, ?_⟩
  · have := hargs j (by simp; omega) hj'
    rwa [List.getElem_append_left hj, List.take_append_of_le_length (by omega)] at this
  · have := hargs pre.length (by simp) (by simp [hpre, H.doms_length])
    rw [List.getElem_append_right (Nat.le_refl _), List.take_left, List.getElem_map] at this
    simp only [Nat.sub_self, List.getElem_singleton] at this
    have hmaj : H.doms[pre.length]'(by simp [hpre, H.doms_length]) =
        VExpr.mkApps (.const indName indLevels)
          (VExpr.bvarRange nparams (nparams + nmotives + nminors + nindices) ++
            VExpr.bvarRange nindices nindices) := by
      rw [List.getElem_eq_iff, ← H.major_eq, hpre]
    rw [hmaj] at this
    simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, VExpr.instL_bvarRange,
      VExpr.instOuter_mkApps, VExpr.instOuter_const] at this
    rw [VExpr.instOuter_bvarRange _ _ _ (by omega) (by omega),
      VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega)] at this
    rw [hpre, Nat.sub_self, List.drop_zero] at this
    rw [show nparams + nmotives + nminors + nindices - nindices = nparams + nmotives + nminors by
      omega] at this
    rwa [List.take_of_length_le (l := pre.drop (nparams + nmotives + nminors)) (i := nindices)
      (by simp; omega)] at this

/-- A constructor application spine types its arguments along the constructor telescope and has
the inductive type at the instantiated indices. -/
theorem VConstructorShape.spine_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VConstructorShape env ctorName ctorUvars nparams nfields indName)
    (hls : ∀ l ∈ cls, l.WF U) (hlsl : cls.length = ctorUvars)
    {P fields : List VExpr} (hP : P.length = nparams) (hf : fields.length = nfields)
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const ctorName cls) (P ++ fields))) :
    (∀ j (hj : j < (P ++ fields).length) (hj' : j < (H.doms.map (VExpr.instL cls)).length),
      env.HasType U Γ (P ++ fields)[j]
        ((H.doms.map (VExpr.instL cls))[j].instOuter ((P ++ fields).take j))) ∧
    env.HasType U Γ (VExpr.mkApps (.const ctorName cls) (P ++ fields))
      (VExpr.mkApps (.const indName cls)
        (P ++ H.indices.map fun e => (e.instL cls).instOuter (P ++ fields))) := by
  have hc := HasType.const (Γ := Γ) H.const hls (by simpa using hlsl)
  rw [H.type_eq, VExpr.instL_wrapForalls] at hc
  have hlen : (P ++ fields).length = (H.doms.map (VExpr.instL cls)).length := by
    simp [hP, hf, H.doms_length]
  have ⟨hargs, hres⟩ := HasType.mkApps_wrapForalls henv hΓ hc hwf hlen
  refine ⟨hargs, ?_⟩
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, VExpr.instL_bvarRange,
    VExpr.instOuter_mkApps, VExpr.instOuter_const, List.map_map, Function.comp_def,
    VLevel.params_map_inst cls hlsl] at hres
  rw [VExpr.instOuter_bvarRange _ _ _ (by omega) (by simp; omega)] at hres
  simp only [List.length_append, hP, hf, Nat.sub_self, List.drop_zero] at hres
  rwa [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hres

/-- The bodies of a stored iota rule are typed under its telescope, at any universe levels. -/
theorem VIotaRuleShape.body_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VIotaRuleShape env recName recUvars nparams nmotives nminors nindices ctorName ctorLevels
      nfields df)
    (hls : ∀ l ∈ ls, l.WF U) :
    OnCtx ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (env.IsType U) ∧
    env.HasType U ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (H.lhsBody.instL ls)
      (H.typeBody.instL ls) ∧
    env.HasType U ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (H.rhsBody.instL ls)
      (H.typeBody.instL ls) := by
  have ⟨hl, hr⟩ := henv.ordered.defEqWF H.defeq
  rw [H.lhs_eq, H.type_eq] at hl
  rw [H.rhs_eq, H.type_eq] at hr
  have hl' := (hl.instL hls).weak0 henv.ordered (Γ := Γ)
  have hr' := (hr.instL hls).weak0 henv.ordered (Γ := Γ)
  simp only [VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hl' hr'
  have ⟨h1, h2⟩ := HasType.wrapLams_inv henv hΓ hl'
  exact ⟨h1, h2, (HasType.wrapLams_inv henv hΓ hr').2⟩

end VEnv

end Lean4Lean
