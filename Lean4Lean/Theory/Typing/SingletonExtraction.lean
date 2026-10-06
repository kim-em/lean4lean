import Lean4Lean.Theory.Typing.CanonicalEqTyping
import Lean4Lean.Theory.Typing.RecursorLemmas

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

theorem liftN_subst_liftN' (e : VExpr) (σ : Subst) (n : Nat) :
    (e.liftN n).subst (σ.liftN n) = (e.subst σ).liftN n := by
  induction n with
  | zero => simp only [Subst.liftN, liftN_zero]
  | succ n ih =>
    rw [liftN_succ, Subst.liftN, lift_subst_lift, ih, ← liftN_succ]

@[simp] theorem eqApp_subst (w α a b) (τ : Subst) :
    (eqApp w α a b).subst τ = eqApp w (α.subst τ) (a.subst τ) (b.subst τ) := rfl

@[simp] theorem castMotive_subst (u X) (τ : Subst) :
    (castMotive u X).subst τ = castMotive u (X.subst τ) := by
  simp only [castMotive, subst, eqApp, lift_subst_lift]
  rfl

@[simp] theorem typeCast_subst (u X Y e x) (τ : Subst) :
    (typeCast u X Y e x).subst τ =
      typeCast u (X.subst τ) (Y.subst τ) (e.subst τ) (x.subst τ) := by
  simp [typeCast, eqRecApp]

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

/-- The cast telescope commutes with substitution of its providers. -/
theorem step_subst {S : CastSpec} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (i : Nat) (σ : List VExpr) (hσ : σ.length = i) (τ : Subst) :
    (S.step pa ia i σ).1.subst (τ.liftN i) =
        (S.step (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i (σ.map (fun x : VExpr => x.subst (τ.liftN i)))).1 ∧
      (S.step pa ia i σ).2.subst (τ.liftN (i + 1)) =
        (S.step (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i (σ.map (fun x : VExpr => x.subst (τ.liftN i)))).2 := by
  have hY := instOuter_subst_closed (S.fields.getD i default) (pa.map (fun x : VExpr => x.liftN i) ++ σ)
    (by simpa [hσ] using H.fields_getD i) (τ.liftN i)
  have hpa : (pa.map (fun x : VExpr => x.liftN i)).map (fun x : VExpr => x.subst (τ.liftN i)) =
      (pa.map (fun x : VExpr => x.subst τ)).map (fun x : VExpr => x.liftN i) := by
    simp [List.map_map, Function.comp_def, liftN_subst_liftN']
  unfold step
  cases hs : S.slot.getD i none with
  | none =>
    refine ⟨?_, rfl⟩
    simp only [hY, List.map_append, hpa]
  | some k =>
    have hk := H.slot_lt i k hs
    have hX := instOuter_subst_closed (S.indices.getD k default)
      (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i))
      (by simpa [hia, Nat.min_eq_left (Nat.le_of_lt hk)] using H.indices_getD k) (τ.liftN i)
    have hia' : ((ia.take k).map (fun x : VExpr => x.liftN i)).map (fun x : VExpr => x.subst (τ.liftN i)) =
        ((ia.map (fun x : VExpr => x.subst τ)).take k).map (fun x : VExpr => x.liftN i) := by
      simp [List.map_map, Function.comp_def, liftN_subst_liftN', List.map_take]
    have hget : ((ia.getD k default).liftN (i + 1)).subst (τ.liftN (i + 1)) =
        ((ia.map (fun x : VExpr => x.subst τ)).getD k default).liftN (i + 1) := by
      rw [liftN_subst_liftN']
      congr 1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hia ▸ hk)]
    refine ⟨?_, ?_⟩
    · simp only [VExpr.eqApp_subst, hY, hX, List.map_append, hpa, hia']
      rfl
    · simp only [VExpr.typeCast_subst, hget]
      simp only [Subst.liftN, lift_subst_lift, hY, hX, List.map_append, hpa, hia']
      rfl

theorem tel_subst {S : CastSpec} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (τ : Subst) (i : Nat) :
    (S.tel pa ia i).1.mapIdx (fun l d => d.subst (τ.liftN l)) =
        (S.tel (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i).1 ∧
      (S.tel pa ia i).2.map (fun x : VExpr => x.subst (τ.liftN i)) =
        (S.tel (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i).2 := by
  induction i with
  | zero => simp [tel]
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlen := (S.tel_length pa ia i).2
    have hstep := step_subst H hia i (S.tel pa ia i).2 hlen τ
    simp only [tel, List.mapIdx_append, List.map_append, List.map_map, ← ih1, ← ih2]
    rw [← hstep.1, ← hstep.2]
    simp only [(S.tel_length pa ia i).1, List.mapIdx_cons, List.mapIdx_nil, Nat.zero_add,
      List.length_mapIdx]
    constructor
    · first | rfl | trivial
    · congr 1
      apply List.map_congr_left
      intro x _
      exact lift_subst_lift

theorem target_subst {S : CastSpec} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (τ : Subst) (j : Nat) :
    (S.target pa ia j).subst (τ.liftN j) =
      S.target (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) j := by
  unfold target
  rw [instOuter_subst_closed _ _ (by simpa [(S.tel_length pa ia j).2] using H.fields_getD j)]
  rw [← (tel_subst H hia τ j).2]
  simp [List.map_map, Function.comp_def, liftN_subst_liftN']

end CastSpec

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Arguments typed along a telescope. -/
def TelInst (env : VEnv) (U : Nat) (Γ doms args : List VExpr) : Prop :=
  args.length = doms.length ∧ ∀ j (hj : j < args.length) (hj' : j < doms.length),
    env.HasType U Γ args[j] (doms[j].instOuter (args.take j))

/-- Instantiating a term typed in a closed context at arguments typed along that context. -/
theorem HasType.closed_instOuter (henv : env.WF)
    {doms : List VExpr} (hΔ : OnCtx doms.reverse (env.IsType U))
    (H : env.HasType U doms.reverse X T) (hargs : TelInst env U Γ doms args) :
    env.HasType U Γ (X.instOuter args) (T.instOuter args) := by
  have hclosed := CtxWF.closed henv.ordered hΔ
  have hX : X.ClosedN doms.reverse.length := (H.closedN' henv.ordered.closed hclosed).1
  have hT : T.ClosedN doms.reverse.length := (H.closedN' henv.ordered.closed hclosed).2.2
  have W := Ctx.LiftN.right hclosed Γ
  have H' := H.weakN henv.ordered W
  rw [hX.liftN_eq (Nat.le_refl _), hT.liftN_eq (Nat.le_refl _)] at H'
  exact IsDefEq.instOuter_telescope henv (doms := doms) (args := args)
    H' hargs.1 hargs.2

theorem TelInst.nil : TelInst env U Γ [] [] := ⟨rfl, fun _ h => by simp at h⟩

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

end VEnv

namespace CastSpec
open VEnv
variable {env : VEnv} {U : Nat}

/-- The sort of field `i`: its declared sort for data, `Prop` for proofs. -/
def fieldSort (S : CastSpec) (i : Nat) : VLevel :=
  match S.slot.getD i none with
  | some _ => S.sorts.getD i .zero
  | none => .zero

/-- Typing of a singleton family's closed telescopes, at fixed universe levels. -/
structure Typed (env : VEnv) (U : Nat) (S : CastSpec) (params : List VExpr) : Prop where
  scope : S.Scoped params.length
  params_closed : ∀ j (h : j < params.length), (params[j]).ClosedN j
  fieldsCtx : ∀ i, i ≤ S.fields.length →
    OnCtx (params ++ S.fields.take i).reverse (env.IsType U)
  indicesCtx : ∀ k, k ≤ S.indices.length →
    OnCtx (params ++ S.indices.take k).reverse (env.IsType U)
  fieldSort : ∀ i (h : i < S.fields.length),
    env.HasType U (params ++ S.fields.take i).reverse S.fields[i] (.sort (S.fieldSort i))
  slotSort : ∀ i k, S.slot.getD i none = some k → ∀ h : k < S.indices.length,
    env.HasType U (params ++ S.indices.take k).reverse S.indices[k] (.sort (S.sorts.getD i .zero))
  sortWF : ∀ i, (S.sorts.getD i .zero).WF U

theorem Typed.prefix_closed {S : CastSpec} (T : S.Typed env U params)
    (hrest : ∀ i (h : i < rest.length), (rest[i]).ClosedN (params.length + i)) :
    ∀ j (h : j < (params ++ rest).length), ((params ++ rest)[j]).ClosedN j := by
  intro j h
  by_cases hj : j < params.length
  · rw [List.getElem_append_left hj]; exact T.params_closed j hj
  · rw [List.getElem_append_right (Nat.le_of_not_gt hj)]
    have := hrest (j - params.length) (by simp at h; omega)
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_gt hj)] at this

theorem getD_of_lt {l : List α} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The cast telescope is well formed and its substitution is a typed instance of the
field telescope, at any providers typed as parameter and index instances. -/
theorem tel_typed (henv : env.WF) (heq : env.HasCanonicalEq) {S : CastSpec}
    (T : S.Typed env U params) (hΔ : OnCtx Δ (env.IsType U))
    (hpa : TelInst env U Δ params pa)
    (hia : TelInst env U Δ (params ++ S.indices) (pa ++ ia)) (hialen : ia.length = S.indices.length) :
    ∀ i, i ≤ S.fields.length →
      OnCtx ((S.tel pa ia i).1.reverse ++ Δ) (env.IsType U) ∧
      TelInst env U ((S.tel pa ia i).1.reverse ++ Δ) (params ++ S.fields.take i)
        (pa.map (fun x : VExpr => x.liftN i) ++ (S.tel pa ia i).2) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [tel] using And.intro hΔ hpa
  | succ i ih =>
    intro hi
    obtain ⟨hctx, hinst⟩ := ih (Nat.le_of_succ_le hi)
    have hi' : i < S.fields.length := hi
    obtain ⟨hdl, hσl⟩ := S.tel_length pa ia i
    generalize hdoms : (S.tel pa ia i).1 = doms at hctx hinst hdl
    generalize hσ : (S.tel pa ia i).2 = σ at hinst hσl
    have htel : S.tel pa ia (i + 1) =
        (doms ++ [(S.step pa ia i σ).1], σ.map (·.lift) ++ [(S.step pa ia i σ).2]) := by
      simp [tel, hdoms, hσ]
    rw [htel]
    -- the declared type of field `i` at the current substitution
    have hY : env.HasType U (doms.reverse ++ Δ)
        ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ))
        (.sort (S.fieldSort i)) := by
      rw [getD_of_lt hi']
      simpa using HasType.closed_instOuter henv (T.fieldsCtx i (Nat.le_of_lt hi'))
        (T.fieldSort i hi') hinst
    have hfcl : ∀ j (h : j < (params ++ S.fields.take i).length),
        ((params ++ S.fields.take i)[j]).ClosedN j :=
      T.prefix_closed (fun l h => by
        simp only [List.length_take] at h
        rw [List.getElem_take]; exact T.scope.fields l (by omega))
    have hlifts : (pa.map (fun x : VExpr => x.liftN i) ++ σ).map (fun x : VExpr => x.liftN 1) =
        pa.map (fun x : VExpr => x.liftN (i + 1)) ++ σ.map (·.lift) := by
      simp [List.map_map, Function.comp_def, liftN_liftN]
    have hfields : params ++ S.fields.take (i + 1) = (params ++ S.fields.take i) ++ [S.fields[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']; simp
    have hctxEq : (doms ++ [(S.step pa ia i σ).1]).reverse ++ Δ =
        (S.step pa ia i σ).1 :: (doms.reverse ++ Δ) := by simp
    rw [hctxEq, hfields]
    dsimp only
    rw [← List.append_assoc]
    -- the old substitution, weakened beneath the new binder
    have hold := TelInst.weak henv.ordered [(S.step pa ia i σ).1] hfcl hinst
    simp only [List.length_singleton, hlifts] at hold
    have hYl : ∀ D : VExpr, env.HasType U (D :: (doms.reverse ++ Δ))
        ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ)).lift
        (.sort (S.fieldSort i)) := fun D => hY.weak henv.ordered
    have hYeq : ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ)).lift =
        S.fields[i].instOuter (pa.map (fun x : VExpr => x.liftN (i + 1)) ++ σ.map (·.lift)) := by
      rw [getD_of_lt hi']
      show VExpr.liftN 1 _ 0 = _
      rw [VExpr.liftN_instOuter _ _ (by
        simpa [hσl, hpa.1] using T.scope.fields i hi'), hlifts]
    cases hs : S.slot.getD i none with
    | none =>
      have hsort : S.fieldSort i = .zero := by unfold fieldSort; rw [hs]
      rw [hsort] at hY
      have hstep : S.step pa ia i σ =
          ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ), .bvar 0) := by
        unfold step; rw [hs]
      rw [hstep] at hold ⊢
      refine ⟨⟨hctx, _, hY⟩, ?_⟩
      apply TelInst.append_one hold
      rw [← hYeq]
      exact .bvar .zero
    | some k =>
      have hk := T.scope.slot_lt i k hs
      have hsort : S.fieldSort i = S.sorts.getD i .zero := by unfold fieldSort; rw [hs]
      rw [hsort] at hY
      have hu := T.sortWF i
      -- the index slot's type at the current depth
      have hicl : ∀ j (h : j < (params ++ S.indices).length), ((params ++ S.indices)[j]).ClosedN j :=
        T.prefix_closed (fun l h => T.scope.indices l h)
      have hiw := TelInst.weak henv.ordered doms.reverse hicl hia
      simp only [List.length_reverse, hdl] at hiw
      have hsplit : params ++ S.indices = (params ++ S.indices.take k) ++ S.indices.drop k := by
        simp [List.append_assoc]
      rw [hsplit] at hiw
      have hix := hiw.take
      have htake : ((pa ++ ia).map (fun x : VExpr => x.liftN i)).take
          (params ++ S.indices.take k).length =
          pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i) := by
        simp only [List.map_append, List.take_append, List.length_append, List.length_take,
          ← hpa.1, List.length_map, Nat.min_eq_left (Nat.le_of_lt (hialen ▸ hk)), Nat.add_sub_cancel_left]
        rw [List.take_of_length_le (by simp)]
        simp [List.map_take, hialen]
      rw [htake] at hix
      have hX := HasType.closed_instOuter henv (T.indicesCtx k (Nat.le_of_lt hk))
        (T.slotSort i k hs hk) hix
      simp only [VExpr.instOuter_sort] at hX
      -- the index argument itself, at the current depth
      have hxi : env.HasType U (doms.reverse ++ Δ) ((ia[k]'(hialen ▸ hk)).liftN i)
          (S.indices[k].instOuter
            (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i))) := by
        have hlenP : (params ++ S.indices.take k).length = params.length + k := by
          simp [Nat.min_eq_left (Nat.le_of_lt hk)]
        have := hiw.2 (params.length + k) (by simp [hpa.1, hialen]; omega)
          (by simp; omega)
        rw [← htake] at *
        simpa [List.getElem_append_right, hpa.1, List.getElem_map, List.getElem_drop,
          Nat.min_eq_left (Nat.le_of_lt hk), List.take_take] using this
      generalize hXdef : S.indices[k].instOuter
        (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i)) = X
        at hX hxi
      generalize hYdef : (S.fields.getD i default).instOuter
        (pa.map (fun x : VExpr => x.liftN i) ++ σ) = Y at hY hYeq
      have hstep : S.step pa ia i σ =
          (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y,
            VExpr.typeCast (S.sorts.getD i .zero) X.lift Y.lift (.bvar 0)
              ((ia[k]'(hialen ▸ hk)).liftN (i + 1))) := by
        unfold step; rw [hs]
        simp only [← hXdef, ← hYdef, getD_of_lt hk, getD_of_lt (hialen ▸ hk)]
      rw [hstep] at hold ⊢
      have hsu : (VLevel.succ (S.sorts.getD i .zero)).WF U := hu
      have hdom := HasType.eqApp heq hsu (.sort hu) hX hY
      refine ⟨⟨hctx, _, hdom⟩, ?_⟩
      apply TelInst.append_one hold
      rw [← hYeq]
      have hX' := hX.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      have hY' := hY.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      have he : env.HasType U (VExpr.eqApp (.succ (S.sorts.getD i .zero))
          (.sort (S.sorts.getD i .zero)) X Y :: (doms.reverse ++ Δ)) (.bvar 0)
          (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X.lift Y.lift) := by
        have := IsDefEq.bvar (env := env) (uvars := U) (Lookup.zero (ty := VExpr.eqApp
          (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y)
          (Γ := doms.reverse ++ Δ))
        simpa [VEnv.HasType, VExpr.eqApp, VExpr.liftN] using this
      have hx := hxi.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      rw [show ((ia[k]'(hialen ▸ hk)).liftN i).lift = (ia[k]'(hialen ▸ hk)).liftN (i + 1) from
        liftN_liftN ..] at hx
      exact HasType.typeCast henv.ordered heq hu (by simpa [VEnv.HasType, VExpr.liftN] using hX') hY' he hx

end CastSpec
end Lean4Lean
