import Lean4Lean.Theory.Typing.CanonicalEqTyping
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.CaseMajorDomain
import Lean4Lean.Theory.Inductive.ProjectionProgram

/-! # Extraction of singleton proof fields along type casts

For a large-eliminating inductive proposition with one constructor, every data
field occurs literally as an index ("singleton elimination"), so the data of a
proof `m : I ps idx` can be read from `idx`. A proof field is extracted from `m`
itself by eliminating into `Prop`. The motive must be well typed at *generic*
indices `is'`, where the index slot of a data field has type `IdxTy(is')`, which in
general is not the field's declared type `A(…)` (the strengthening countermodel,
`docs/inductives/STRENGTHENING.md`). The motive therefore abstracts, for each earlier
field, either an equation between the two *types* (data field) or a proof (proof field),
and reads each data field through a cast along its equation:

```text
cast telescope, field i < j:
  data i (slot k): e_i : @Eq (Sort u_i) IdxTy_k(ps, is'_<k) A_i(ps, σ_<i)
                   σ_i := typeCast u_i _ _ e_i is'_k
  proof i:         z_i : A_i(ps, σ_<i)
                   σ_i := z_i
target:            A_j(ps, σ_<j)
```

In the constructor branch every equation relates definitionally equal types, so
each cast computes by K (`IsDefEq.typeCast_refl`); at an aligned occurrence the
equations are proved by `Eq.refl`.

This file contains the syntax (`CastSpec`, `CastSpec.tel`) and its behaviour under
substitution. All telescopes are closed: `fields[i]` is scoped over the parameters
and the earlier fields, `indices[k]` over the parameters and the earlier indices.
The construction is parametric in the *providers*: the parameter arguments `pa` and
the index arguments `ia`, given at the base of the cast telescope and lifted beneath
its binders. The generic motive, the constructor branch and an actual occurrence are
the three instances. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

namespace VExpr

theorem instOuter_subst_closed (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length)
    (τ : Subst) : (X.instOuter args).subst τ = X.instOuter (args.map (fun x : VExpr => x.subst τ)) := by
  simp only [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map]

@[simp] theorem eqApp_subst (w α a b) (τ : Subst) :
    (eqApp w α a b).subst τ = eqApp w (α.subst τ) (a.subst τ) (b.subst τ) := rfl

end VExpr

/-- Pure syntax of a singleton family's field and index telescopes. -/
structure CastSpec where
  /-- `fields[i]` is scoped over `params ++ fields.take i`. -/
  fields : List VExpr
  /-- `indices[k]` is scoped over `params ++ indices.take k`. -/
  indices : List VExpr
  /-- `slot[i] = some k`: field `i` is data and occurs literally as index `k`;
  `none`: field `i` is a proof. -/
  slot : List (Option Nat)
  /-- The sort of each data field (unused for proof fields). -/
  sorts : List VLevel

namespace CastSpec
variable (S : CastSpec)

/-- One step of the cast telescope at depth `i` (the number of cast binders already
opened), given the substitution `σ` for the first `i` fields at that depth. Returns the
new binder domain and the value of field `i` beneath the new binder. -/
def step (pa ia : List VExpr) (i : Nat) (σ : List VExpr) : VExpr × VExpr :=
  let pai := pa.map (fun x : VExpr => x.liftN i)
  let Y := (S.fields.getD i default).instOuter (pai ++ σ)
  match S.slot.getD i none with
  | some k =>
    let X := (S.indices.getD k default).instOuter (pai ++ (ia.take k).map (fun x : VExpr => x.liftN i))
    let u := S.sorts.getD i .zero
    (VExpr.eqApp (.succ u) (.sort u) X Y,
      VExpr.typeCast u X.lift Y.lift (.bvar 0) ((ia.getD k default).liftN (i + 1)))
  | none => (Y, .bvar 0)

/-- The cast telescope for the first `i` fields: its domains (the `l`-th scoped at
depth `l`) and the substitution for those fields at depth `i`. -/
def tel (pa ia : List VExpr) : Nat → List VExpr × List VExpr
  | 0 => ([], [])
  | i + 1 =>
    let (doms, σ) := tel pa ia i
    let (dom, val) := S.step pa ia i σ
    (doms ++ [dom], σ.map (·.lift) ++ [val])

/-- The target of proof field `j`: its declared type at the cast data. -/
def target (pa ia : List VExpr) (j : Nat) : VExpr :=
  (S.fields.getD j default).instOuter (pa.map (·.liftN j) ++ (S.tel pa ia j).2)

theorem tel_length (pa ia : List VExpr) (i : Nat) :
    (S.tel pa ia i).1.length = i ∧ (S.tel pa ia i).2.length = i := by
  induction i with
  | zero => simp [tel]
  | succ i ih => simp [tel, ih]

/-- Scoping data of a cast specification over `P` parameters. -/
structure Scoped (P : Nat) : Prop where
  fields : ∀ i (h : i < S.fields.length), (S.fields[i]).ClosedN (P + i)
  indices : ∀ k (h : k < S.indices.length), (S.indices[k]).ClosedN (P + k)
  slot_lt : ∀ i k, S.slot.getD i none = some k → k < S.indices.length

theorem Scoped.fields_getD {S : CastSpec} (H : S.Scoped P) (i : Nat) :
    (S.fields.getD i default).ClosedN (P + i) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < S.fields.length
  · simpa [List.getElem?_eq_getElem hi] using H.fields i hi
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem Scoped.indices_getD {S : CastSpec} (H : S.Scoped P) (k : Nat) :
    (S.indices.getD k default).ClosedN (P + k) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < S.indices.length
  · simpa [List.getElem?_eq_getElem hk] using H.indices k hk
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hk)]

end CastSpec

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Arguments typed along a telescope. -/
def TelInst (env : VEnv) (U : Nat) (Γ doms args : List VExpr) : Prop :=
  args.length = doms.length ∧ ∀ j (hj : j < args.length) (hj' : j < doms.length),
    env.HasType U Γ args[j] (doms[j].instOuter (args.take j))

theorem getD_of_lt {l : List α} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem subst_liftN_lift (σ : VExpr.Subst) : ∀ l, σ.lift.liftN l = σ.liftN (l + 1)
  | 0 => rfl
  | l + 1 => by simp only [VExpr.Subst.liftN, subst_liftN_lift σ l]

theorem subst_wrapForalls (τ : VExpr.Subst) :
    ∀ (doms : List VExpr) (B : VExpr), (VExpr.wrapForalls doms B).subst τ =
      VExpr.wrapForalls (doms.mapIdx fun l d => d.subst (τ.liftN l)) (B.subst (τ.liftN doms.length))
  | [], B => rfl
  | d :: ds, B => by
    show VExpr.forallE (d.subst τ) ((VExpr.wrapForalls ds B).subst τ.lift) = _
    rw [subst_wrapForalls τ.lift ds B]
    simp only [List.mapIdx_cons, subst_liftN_lift, List.length_cons]
    rfl

theorem subst_wrapLams (τ : VExpr.Subst) :
    ∀ (doms : List VExpr) (B : VExpr), (VExpr.wrapLams doms B).subst τ =
      VExpr.wrapLams (doms.mapIdx fun l d => d.subst (τ.liftN l)) (B.subst (τ.liftN doms.length))
  | [], B => rfl
  | d :: ds, B => by
    show VExpr.lam (d.subst τ) ((VExpr.wrapLams ds B).subst τ.lift) = _
    rw [subst_wrapLams τ.lift ds B]
    simp only [List.mapIdx_cons, subst_liftN_lift, List.length_cons]
    rfl

theorem liftN_eq_subst_shift (e : VExpr) (r j : Nat) :
    e.liftN r j = e.subst ((VExpr.Subst.shift r).liftN j) := by
  have h := VExpr.liftN_subst (e := e) (n := r) (k := j) (σ := VExpr.Subst.id)
  rw [VExpr.subst_id] at h
  rw [h]
  congr 1
  funext i
  simp only [VExpr.Subst.lift_l, VExpr.Subst.id, Lift.liftVar_consN_skipN,
    VExpr.Subst.liftN_apply, VExpr.Subst.shift]
  by_cases hi : i < j
  · rw [liftVar_lt hi, if_pos hi]
  · rw [liftVar_le (Nat.le_of_not_gt hi), if_neg hi]
    simp only [VExpr.liftN, liftVar_base']
    congr 1; omega

theorem liftN_wrapForalls (doms : List VExpr) (B : VExpr) (r : Nat) :
    (VExpr.wrapForalls doms B).liftN r =
      VExpr.wrapForalls (doms.mapIdx fun l d => d.liftN r l) (B.liftN r doms.length) := by
  rw [liftN_eq_subst_shift _ r 0, subst_wrapForalls]
  simp only [VExpr.Subst.liftN, liftN_eq_subst_shift]

theorem liftN_wrapLams (doms : List VExpr) (B : VExpr) (r : Nat) :
    (VExpr.wrapLams doms B).liftN r =
      VExpr.wrapLams (doms.mapIdx fun l d => d.liftN r l) (B.liftN r doms.length) := by
  rw [liftN_eq_subst_shift _ r 0, subst_wrapLams]
  simp only [VExpr.Subst.liftN, liftN_eq_subst_shift]

/-- Instantiating the top binders of a term lifted past them: the lifted parameters become
the variables of the enclosing context. -/
theorem liftN_instOuter_params {X : VExpr} {args : List VExpr} (hX : X.ClosedN (P + args.length))
    (r : Nat) :
    (X.liftN r args.length).instOuter args = X.instOuter (bvarRange P (P + r) ++ args) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  by_cases hik : i < args.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ hik, VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_ge _ (by omega),
      VExpr.Subst.ofList_lt _ (by simp; omega), List.getElem_append_left (by simp; omega),
      bvarRange_getElem _ _ _ (by simp; omega)]
    congr 1; simp; omega

theorem instOuter_closed0 {e : VExpr} (h : e.ClosedN 0) (args : List VExpr) :
    e.instOuter args = e := by
  rw [VExpr.instOuter_eq_subst]; exact h.subst_eq .zero

theorem _root_.Lean4Lean.VExpr.Subst.ofList_snoc_tail (args : List VExpr) (a : VExpr) :
    (VExpr.Subst.ofList (args ++ [a])).tail = VExpr.Subst.ofList args := by
  funext k
  simp only [VExpr.Subst.tail, VExpr.Subst.ofList, List.length_append, List.length_singleton]
  by_cases hk : k < args.length
  · rw [dif_pos (by omega), dif_pos hk, List.getElem_append_left (by omega)]
    congr 1; omega
  · rw [dif_neg (by omega), dif_neg hk]; congr 1; omega

theorem _root_.Lean4Lean.VExpr.Subst.ofList_snoc_head (args : List VExpr) (a : VExpr) :
    (VExpr.Subst.ofList (args ++ [a])).head = a := by
  simp [VExpr.Subst.head, VExpr.Subst.ofList]

theorem snoc_induction {α} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => simpa using nil
  | cons a t ih => simpa using snoc _ a ih

/-- Pointwise definitionally equal arguments along a closed telescope form a
substitution between its context and the target context. -/
theorem substEq_ofTel :
    ∀ {doms args args' : List VExpr}, OnCtx doms.reverse (env.IsType U) →
      args.length = doms.length → args'.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < args'.length) (hd : j < doms.length),
        env.IsDefEq U Γ args[j] args'[j] (doms[j].instOuter (args.take j))) →
      Ctx.SubstEq env U Γ (VExpr.Subst.ofList args) (VExpr.Subst.ofList args') doms.reverse := by
  intro doms
  induction doms using snoc_induction with
  | nil => intro _ _ _ _ _ _; exact .nil
  | snoc ds d ih =>
    intro args args' hctx hl hl' hpt
    obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] := by
      rcases List.eq_nil_or_concat args with h | ⟨as, a, h⟩
      · subst h; simp at hl
      · exact ⟨as, a, by simpa using h⟩
    obtain ⟨bs, b, rfl⟩ : ∃ bs b, args' = bs ++ [b] := by
      rcases List.eq_nil_or_concat args' with h | ⟨bs, b, h⟩
      · subst h; simp at hl'
      · exact ⟨bs, b, by simpa using h⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl hl'
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at hctx ⊢
    obtain ⟨hctx', _, hd⟩ := hctx
    refine .cons ?_ hd ?_
    · rw [VExpr.Subst.ofList_snoc_tail, VExpr.Subst.ofList_snoc_tail]
      exact ih hctx' hl hl' fun j hj hj' hd' => by
        have := hpt j (by simp; omega) (by simp; omega) (by simp; omega)
        rwa [List.getElem_append_left hj, List.getElem_append_left hj',
          List.getElem_append_left hd', List.take_append_of_le_length (Nat.le_of_lt hj)] at this
    · rw [VExpr.Subst.ofList_snoc_head, VExpr.Subst.ofList_snoc_head,
        VExpr.Subst.ofList_snoc_tail, ← VExpr.instOuter_eq_subst]
      have := hpt as.length (by simp) (by simp; omega) (by simp; omega)
      rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (by omega),
        List.getElem_append_right (by omega), List.take_left'] at this
      · simpa [hl, hl'] using this
      all_goals simp [hl, hl']

/-- Congruence of instantiation at pointwise definitionally equal arguments. -/
theorem IsDefEq.closed_instOuter_congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {doms : List VExpr} (hΔ : OnCtx doms.reverse (env.IsType U))
    (H : env.IsDefEq U doms.reverse X X' T)
    (hl : args.length = doms.length) (hl' : args'.length = doms.length)
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length) (hd : j < doms.length),
      env.IsDefEq U Γ args[j] args'[j] (doms[j].instOuter (args.take j))) :
    env.IsDefEq U Γ (X.instOuter args) (X'.instOuter args') (T.instOuter args) := by
  have W := substEq_ofTel hΔ hl hl' hpt
  have := IsDefEq.substDF henv.ordered hΔ hΓ W H
  simpa only [VExpr.instOuter_eq_subst] using this

theorem HasType.wrapLams_of :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body T : VExpr},
      OnCtx (doms.reverse ++ Γ) (env.IsType U) → env.HasType U (doms.reverse ++ Γ) body T →
      env.HasType U Γ (VExpr.wrapLams doms body) (VExpr.wrapForalls doms T)
  | [], _, _, _, _, h => h
  | d :: ds, Γ, body, T, hctx, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx h
    have ⟨_, _, hd⟩ := OnCtx.of_append (Γ' := ds.reverse) hctx
    exact .lam hd (HasType.wrapLams_of hctx h)

theorem TelInst.append (HA : TelInst env U Γ A a) (hB : b.length = B.length)
    (hBt : ∀ j, j < B.length →
      env.HasType U Γ (b.getD j default) ((B.getD j default).instOuter (a ++ b.take j))) :
    TelInst env U Γ (A ++ B) (a ++ b) := by
  refine ⟨by simp [HA.1, hB], fun j hj hj' => ?_⟩
  by_cases hja : j < a.length
  · rw [List.getElem_append_left hja, List.getElem_append_left (HA.1 ▸ hja),
      List.take_append_of_le_length (Nat.le_of_lt hja)]
    exact HA.2 j hja (HA.1 ▸ hja)
  · have hm : j - a.length < B.length := by simp at hj'; have := HA.1; omega
    rw [List.getElem_append_right (Nat.le_of_not_gt hja),
      List.getElem_append_right (HA.1 ▸ Nat.le_of_not_gt hja), List.take_append,
      List.take_of_length_le (by omega)]
    have := hBt (j - a.length) hm
    rw [getD_of_lt (by omega), getD_of_lt hm] at this
    simpa [HA.1] using this

theorem TelInst.append_one (H : TelInst env U Γ doms args)
    (ha : env.HasType U Γ a (d.instOuter args)) :
    TelInst env U Γ (doms ++ [d]) (args ++ [a]) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < args.length
  · rw [List.getElem_append_left hlt, List.getElem_append_left (H.1 ▸ hlt),
      List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact H.2 j hlt (H.1 ▸ hlt)
  · have hj' : j = args.length := by omega
    subst hj'
    rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (H.1 ▸ Nat.le_refl _)]
    simpa [H.1] using ha

theorem TelInst.take (H : TelInst env U Γ (doms ++ more) args) :
    TelInst env U Γ doms (args.take doms.length) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_take] at hj
  have hjd : j < doms.length := hj'
  have hja : j < args.length := by have := H.1; simp at this; omega
  have := H.2 j hja (by simp; omega)
  rw [List.getElem_append_left hjd] at this
  simpa [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjd)] using this

/-- Weakening a telescope instance beneath new binders. -/
theorem TelInst.weak (henv : env.Ordered) (D : List VExpr)
    (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j)
    (H : TelInst env U Γ doms args) :
    TelInst env U (D ++ Γ) doms (args.map (fun x : VExpr => x.liftN D.length)) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_map] at hj
  have h := (H.2 j hj hj').weakN henv (Ctx.LiftN.zero D)
  rw [VExpr.liftN_instOuter _ _ (by simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using hcl j hj')] at h
  simpa [List.map_take] using h

/-- The variables of a closed telescope's own context instantiate it. -/
theorem TelInst.ident (Γ : List VExpr) (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j) :
    TelInst env U (doms.reverse ++ Γ) doms (bvarRange doms.length doms.length) := by
  refine ⟨by simp, fun j hj hj' => ?_⟩
  simp only [bvarRange_length] at hj
  rw [bvarRange_getElem _ _ _ hj, bvarRange_take _ _ _ (Nat.le_of_lt hj),
    VExpr.instOuter_range_bvar' _ _ _ (hcl j hj') (Nat.le_of_lt hj)]
  exact .bvar (Lookup.reverse_append doms Γ j hj')

theorem HasType.mkApps_of_tel (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f (VExpr.wrapForalls doms B)) (H : TelInst env U Γ doms args) :
    env.HasType U Γ (VExpr.mkApps f args) (B.instOuter args) :=
  IsDefEq.mkApps_congr henv hΓ hf H.1 rfl fun j hj hj' _ => H.2 j hj hj'

/-- A telescope over the parameters, lifted past `r` binders and instantiated at its own
arguments, is the telescope instantiated at the lifted parameters. -/
theorem TelInst.unlift {D : List VExpr} (hcl : ∀ j (h : j < D.length), (D[j]).ClosedN (P + j))
    (hP : params.length = P)
    (H : TelInst env U Γ (params ++ D) (bvarRange P (P + r) ++ args)) :
    TelInst env U Γ (D.mapIdx fun l d => d.liftN r l) args := by
  have hlen : args.length = D.length := by have := H.1; simp [hP] at this; omega
  refine ⟨by simp [hlen], fun j hj hj' => ?_⟩
  have hjD : j < D.length := by simpa using hj'
  have := H.2 (P + j) (by simp; omega) (by simp [hP]; omega)
  rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp [hP])] at this
  rw [List.take_append, List.take_of_length_le (by simp)] at this
  simp only [bvarRange_length, Nat.add_sub_cancel_left, hP] at this
  have htl : (args.take j).length = j := by simp; omega
  have e : (D[j].liftN r j).instOuter (args.take j) =
      D[j].instOuter (bvarRange P (P + r) ++ args.take j) := by
    have := liftN_instOuter_params (P := P) (X := D[j]) (args := args.take j)
      (by rw [htl]; exact hcl j hjD) r
    rwa [htl] at this
  rw [List.getElem_mapIdx, e]
  exact this

end VEnv

namespace CastSpec
open VEnv
variable {env : VEnv} {U : Nat}

theorem bvarRange_append (a b t : Nat) (h : a + b ≤ t) :
    bvarRange (a + b) t = bvarRange a t ++ bvarRange b (t - a) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [bvarRange_length] at h1
    by_cases hj : j < a
    · rw [List.getElem_append_left (by simpa using hj), bvarRange_getElem _ _ _ h1,
        bvarRange_getElem _ _ _ hj]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hj), bvarRange_getElem _ _ _ h1]
      simp only [bvarRange_length]
      rw [bvarRange_getElem _ _ _ (by omega)]
      congr 1; omega

theorem bvarRange_split (P r : Nat) :
    bvarRange (P + r) (P + r) = bvarRange P (P + r) ++ bvarRange r r := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [bvarRange_length] at h1
    by_cases hj : j < P
    · rw [List.getElem_append_left (by simpa using hj), bvarRange_getElem _ _ _ h1,
        bvarRange_getElem _ _ _ hj]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hj), bvarRange_getElem _ _ _ h1]
      simp only [bvarRange_length]
      rw [bvarRange_getElem _ _ _ (by omega)]
      congr 1; omega

end CastSpec

/-- The syntax of a singleton family's elimination into `Prop`, at fixed universe levels:
the family and constructor heads (closed terms applied to parameters and indices), the
constructor's result indices (scoped over the parameters and fields), the eliminator head
specialized to motive universe zero, and how a minor premise is built from a motive and a
branch over the fields (for native recursors this adds the unused induction hypotheses). -/
structure PropElim where
  family : VExpr
  ctor : VExpr
  ctorIndices : List VExpr
  elimHead : VExpr
  minorOf : VExpr → VExpr → VExpr

namespace PropElim
variable (S : CastSpec) (params : List VExpr) (E : PropElim)

/-- The major premise's type, scoped over the parameters and the indices. -/
def majorTy : VExpr :=
  VExpr.mkApps E.family
    (bvarRange params.length (params.length + S.indices.length) ++
      bvarRange S.indices.length S.indices.length)

/-- Providers of the generic motive: the parameters and indices beneath the major. -/
def genericPa : List VExpr :=
  bvarRange params.length (params.length + S.indices.length + 1)
def genericIa : List VExpr := bvarRange S.indices.length (S.indices.length + 1)

/-- Providers of the constructor branch: the parameters beneath the fields, and the
constructor's own indices. -/
def branchPa : List VExpr := bvarRange params.length (params.length + S.fields.length)

/-- The motive extracting proof field `j`, scoped over the parameters. -/
def motive (j : Nat) : VExpr :=
  VExpr.wrapLams (S.indices ++ [majorTy S params E])
    (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j))

/-- The branch returning field `j`, scoped over the parameters and the fields. -/
def branch (j : Nat) : VExpr :=
  VExpr.wrapLams (S.tel (branchPa S params) E.ctorIndices j).1 (.bvar (S.fields.length - 1))

/-- The closed extraction function for proof field `j`: a function of the parameters,
the indices, the major premise and the cast telescope. -/
def value (j : Nat) : VExpr :=
  VExpr.wrapLams (params ++ S.indices ++ [majorTy S params E])
    (VExpr.mkApps E.elimHead
      (genericPa S params ++
        [(motive S params E j).liftN (S.indices.length + 1),
          (E.minorOf (motive S params E j) (branch S params E j)).liftN (S.indices.length + 1)] ++
        bvarRange (S.indices.length + 1) (S.indices.length + 1)))

/-- The cast arguments (`.1`) and the reconstructed fields (`.2`) at an occurrence with
parameters `ps`, indices `idx` and major `m`. A data field is read from its index; the cast
argument for it is `Eq.refl` at the index's type. A proof field is the extraction function
applied to the occurrence and to the earlier cast arguments. -/
def occ (ps idx : List VExpr) (m : VExpr) : Nat → List VExpr × List VExpr
  | 0 => ([], [])
  | i + 1 =>
    let (t, c) := occ ps idx m i
    match S.slot.getD i none with
    | some k =>
      (t ++ [VExpr.eqReflApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero))
          ((S.indices.getD k default).instOuter (ps ++ idx.take k))],
        c ++ [idx.getD k default])
    | none =>
      (t ++ [VExpr.mkApps (value S params E i) (ps ++ idx ++ [m] ++ t)],
        c ++ [VExpr.mkApps (value S params E i) (ps ++ idx ++ [m] ++ t)])

theorem occ_length (ps idx : List VExpr) (m : VExpr) (i : Nat) :
    (occ S params E ps idx m i).1.length = i ∧ (occ S params E ps idx m i).2.length = i := by
  induction i with
  | zero => simp [occ]
  | succ i ih =>
    simp only [occ]
    split <;> simp [ih]

end PropElim
end Lean4Lean
