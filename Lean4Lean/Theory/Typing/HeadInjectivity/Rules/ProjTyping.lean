import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ProjOrigin
import Lean4Lean.Theory.Typing.Strong

/-! # Declarative typing of projections of a never-zero structure

For a projection-registered structure `S` whose result sort is never zero at universe levels
`ls`:
* every projection of a typed major is typable at the field type that `fieldType` computes
  (`VEnv.proj_typed`, L2), with congruence in the major;
* a projection of a constructor spine is definitionally equal to the field
  (`VEnv.proj_spine`, L3).

The proofs walk the closed constructor telescope with simultaneous substitutions
(`argSubst`), so no `instOuter` (and none of the uniqueness-dependent modules) is used. -/

namespace Lean4Lean
open VExpr

/-- The substitution instantiating a closed telescope's first `as.length` binders by `as`
(the first argument replaces the outermost binder). -/
def VExpr.argSubst (as : List VExpr) : VExpr.Subst := as.foldl VExpr.Subst.cons .id

theorem VExpr.argSubst_append_one (as : List VExpr) (a : VExpr) :
    argSubst (as ++ [a]) = (argSubst as).cons a := by
  simp [argSubst, List.foldl_append]

theorem VExpr.foldl_cons_apply : ∀ (as : List VExpr) (σ : VExpr.Subst) (m : Nat),
    (as.foldl VExpr.Subst.cons σ) m =
      if h : m < as.length then as[as.length - 1 - m] else σ (m - as.length)
  | [], _, m => by simp
  | a :: as, σ, m => by
    simp only [List.foldl_cons, List.length_cons]
    rw [VExpr.foldl_cons_apply as]
    by_cases hm : m < as.length
    · rw [dif_pos hm, dif_pos (by omega)]
      simp only [show as.length + 1 - 1 - m = (as.length - 1 - m) + 1 by omega,
        List.getElem_cons_succ]
    · rw [dif_neg hm]
      by_cases hm' : m = as.length
      · subst hm'
        rw [dif_pos (by omega)]
        simp [VExpr.Subst.cons]
      · rw [dif_neg (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, m - as.length = d + 1 := ⟨m - as.length - 1, by omega⟩
        rw [hd]
        show σ d = _
        congr 1; omega

theorem VExpr.argSubst_lt (as : List VExpr) {m : Nat} (h : m < as.length) :
    argSubst as m = as[as.length - 1 - m] := by
  rw [argSubst, foldl_cons_apply, dif_pos h]

theorem VExpr.subst_wrapForalls_cons (d : VExpr) (ds : List VExpr) (R : VExpr)
    (σ : VExpr.Subst) :
    (VExpr.wrapForalls (d :: ds) R).subst σ =
      .forallE (d.subst σ) ((VExpr.wrapForalls ds R).subst σ.lift) := rfl

theorem VExpr.instL_wrapForalls_pt (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls ds body).instL ls =
      VExpr.wrapForalls (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢
    rw [ih]

/-- Instantiating the parameters of a substituted telescope. -/
theorem VProjectionInfo.ipp_wrapForalls :
    ∀ (as ds : List VExpr) (R : VExpr) (σ : VExpr.Subst), as.length ≤ ds.length →
      VProjectionInfo.instantiateProjectionParameters ((VExpr.wrapForalls ds R).subst σ) as =
        some ((VExpr.wrapForalls (ds.drop as.length) R).subst (as.foldl VExpr.Subst.cons σ))
  | [], ds, R, σ, _ => by simp [VProjectionInfo.instantiateProjectionParameters]
  | a :: as, [], R, σ, h => by simp at h
  | a :: as, d :: ds, R, σ, h => by
    rw [VExpr.subst_wrapForalls_cons]
    show VProjectionInfo.instantiateProjectionParameters
      (((VExpr.wrapForalls ds R).subst σ.lift).inst a) as = _
    rw [VExpr.inst_lift_cons,
      VProjectionInfo.ipp_wrapForalls as ds R _ (by simp at h; omega)]
    simp

/-- Walking the fields of a substituted telescope, each earlier field instantiated by its
projection. -/
theorem VProjectionInfo.ipf_wrapForalls (S : Name) (w R : VExpr) :
    ∀ (n : Nat) (ds : List VExpr) (σ : VExpr.Subst) (cur fuel : Nat) (h : n < ds.length),
      n < fuel →
      VProjectionInfo.instantiateProjectionFields S w (cur + n) cur fuel
          ((VExpr.wrapForalls ds R).subst σ) =
        some ((ds[n]).subst
          (((List.range n).map fun k => VExpr.proj S (cur + k) w).foldl VExpr.Subst.cons σ))
  | n, [], _, _, _, h, _ => by simp at h
  | n, d :: ds, σ, cur, 0, _, hf => by omega
  | 0, d :: ds, σ, cur, fuel + 1, _, _ => by
    rw [VExpr.subst_wrapForalls_cons]
    simp [VProjectionInfo.instantiateProjectionFields]
  | n + 1, d :: ds, σ, cur, fuel + 1, h, hf => by
    rw [VExpr.subst_wrapForalls_cons]
    simp only [VProjectionInfo.instantiateProjectionFields, show cur + (n + 1) ≠ cur by omega,
      if_false]
    rw [VExpr.inst_lift_cons, show cur + (n + 1) = (cur + 1) + n by omega,
      VProjectionInfo.ipf_wrapForalls S w R n ds _ (cur + 1) fuel (by simp at h; omega)
        (by omega)]
    simp only [List.getElem_cons_succ, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.foldl_cons, Function.comp_def, Nat.add_zero]
    congr 4
    funext k; congr 1; omega

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- The binder domains of a well-formed Pi telescope are types in their prefix contexts. -/
theorem IsType.wrapForalls_doms (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {R : VExpr}, env.IsType U Γ (VExpr.wrapForalls ds R) →
      ∀ k (hk : k < ds.length), ∃ u, env.HasType U ((ds.take k).reverse ++ Γ) ds[k] (.sort u)
  | [], _, _, _, k, hk => by simp at hk
  | d :: ds, Γ, R, h, k, hk => by
    obtain ⟨⟨u, hd⟩, hB⟩ := IsType.forallE_inv henv h
    cases k with
    | zero => exact ⟨u, by simpa using hd⟩
    | succ k =>
      obtain ⟨v, hv⟩ := IsType.wrapForalls_doms henv hB k (by simp at hk; omega)
      exact ⟨v, by simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hv⟩

/-- The prefix contexts of a well-formed Pi telescope are well formed. -/
theorem IsType.wrapForalls_ctx (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {R : VExpr}, OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls ds R) →
      ∀ k, k ≤ ds.length → OnCtx ((ds.take k).reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ, _, k, hk => by simpa using hΓ
  | d :: ds, Γ, R, hΓ, h, k, hk => by
    obtain ⟨⟨u, hd⟩, hB⟩ := IsType.forallE_inv henv h
    cases k with
    | zero => simpa using hΓ
    | succ k =>
      have := IsType.wrapForalls_ctx henv (Γ := d :: Γ) ⟨hΓ, u, hd⟩ hB k (by simp at hk; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

/-- `args` are typed along the Pi type `T`, leaving `R`. -/
inductive ArgsTyped (env : VEnv) (U : Nat) (Δ : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | nil : ArgsTyped env U Δ T [] T
  | cons : env.HasType U Δ a A → ArgsTyped env U Δ (B.inst a) as R →
    ArgsTyped env U Δ (.forallE A B) (a :: as) R

/-- Arguments typed along a substituted closed telescope extend the substitution. -/
theorem ArgsTyped.substEq {Δ D : List VExpr} {R0 : VExpr}
    (hD : ∀ k (hk : k < D.length), ∃ u, env.HasType U (D.take k).reverse D[k] (.sort u))
    (hR0 : ∀ (σ : VExpr.Subst) A B, R0.subst σ ≠ .forallE A B) :
    ∀ (as pre : List VExpr) {Tail : VExpr},
      Ctx.SubstEq env U Δ (VExpr.argSubst pre) (VExpr.argSubst pre) (D.take pre.length).reverse →
      pre.length ≤ D.length →
      ArgsTyped env U Δ ((VExpr.wrapForalls (D.drop pre.length) R0).subst (VExpr.argSubst pre))
        as Tail →
      pre.length + as.length ≤ D.length ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (pre ++ as)) (VExpr.argSubst (pre ++ as))
        (D.take (pre ++ as).length).reverse ∧
      Tail = (VExpr.wrapForalls (D.drop (pre ++ as).length) R0).subst (VExpr.argSubst (pre ++ as))
  | [], pre, Tail, W, hle, H => by
    generalize hX : (VExpr.wrapForalls (D.drop pre.length) R0).subst (VExpr.argSubst pre) = X at H
    cases H
    subst hX
    exact ⟨by simpa using hle, by simpa using W, by simp⟩
  | a :: as, pre, Tail, W, hle, H => by
    by_cases hk : pre.length < D.length
    · rw [List.drop_eq_getElem_cons hk, VExpr.subst_wrapForalls_cons] at H
      cases H with
      | cons ha H' =>
        rw [VExpr.inst_lift_cons, ← VExpr.argSubst_append_one] at H'
        obtain ⟨u, hu⟩ := hD pre.length hk
        have W' : Ctx.SubstEq env U Δ (VExpr.argSubst (pre ++ [a])) (VExpr.argSubst (pre ++ [a]))
            (D.take (pre ++ [a]).length).reverse := by
          rw [List.length_append, List.length_singleton, List.take_succ_eq_append_getElem hk,
            List.reverse_append, List.reverse_singleton, List.singleton_append,
            VExpr.argSubst_append_one]
          exact .cons (by rw [VExpr.Subst.cons_tail]; exact W) hu
            (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact ha)
        have := ArgsTyped.substEq hD hR0 as (pre ++ [a]) W' (by simp; omega)
          (by simpa using H')
        simp only [List.append_assoc, List.singleton_append, List.length_append,
          List.length_singleton, List.length_cons] at this ⊢
        exact ⟨by omega, this.2.1, this.2.2⟩
    · have hD0 : D.drop pre.length = [] := List.drop_eq_nil_of_le (by omega)
      rw [hD0] at H
      cases h : (VExpr.wrapForalls [] R0).subst (VExpr.argSubst pre) with
      | forallE A B => exact absurd h (hR0 _ A B)
      | _ => rw [h] at H; cases H

theorem forallArity_mkApps_const (c : Name) (lsR : List VLevel) (args : List VExpr) :
    (VExpr.mkApps (.const c lsR) args).forallArity = 0 := by
  cases h : VExpr.mkApps (.const c lsR) args with
  | forallE A B => exact absurd h (VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) args)
  | _ => rfl

theorem subst_mkApps_const_ne_forallE (c : Name) (lsR : List VLevel) (args : List VExpr)
    (σ : VExpr.Subst) (A B : VExpr) :
    (VExpr.mkApps (.const c lsR) args).subst σ ≠ .forallE A B := by
  rw [VExpr.subst_mkApps]; exact VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) _

/-- The projection-registered constructor telescope at universe levels, as a closed telescope. -/
structure ProjTele (env : VEnv) (U : Nat) (S : Name) (info : VProjectionInfo)
    (ls : List VLevel) (D : List VExpr) (R0 : VExpr) : Prop where
  shape : info.ctorType.instL ls = VExpr.wrapForalls D R0
  head : ∃ c lsR args, R0 = VExpr.mkApps (.const c lsR) args
  doms : ∀ k (hk : k < D.length), ∃ u, env.HasType U (D.take k).reverse D[k] (.sort u)
  ctx : ∀ k, k ≤ D.length → OnCtx (D.take k).reverse (env.IsType U)
  numFields : info.numFields = D.length - info.nparams

theorem ProjTele.of (henv : env.Ordered) {S : Name} {info : VProjectionInfo} {doms : List VExpr}
    {c : Name} {lsR : List VLevel} {args : List VExpr}
    (hshape : info.ctorType = VExpr.wrapForalls doms (VExpr.mkApps (.const c lsR) args))
    (hwf : env.IsType info.uvars [] info.ctorType)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ProjTele env U S info ls (doms.map (·.instL ls))
      ((VExpr.mkApps (.const c lsR) args).instL ls) := by
  have hT := IsType.instL hls hwf
  rw [hshape, VExpr.instL_wrapForalls_pt] at hT
  refine ⟨by rw [hshape, VExpr.instL_wrapForalls_pt], ⟨c, _, _, VExpr.instL_mkApps _ _⟩,
    fun k hk => ?_, fun k hk => ?_, ?_⟩
  · obtain ⟨u, h⟩ := IsType.wrapForalls_doms henv hT k hk
    exact ⟨u, by simpa using h⟩
  · simpa using IsType.wrapForalls_ctx henv (Γ := []) trivial hT k hk
  · simp [VProjectionInfo.numFields, hshape, forallArity_mkApps_const]

/-- The projections of the first `j` fields of a major. -/
def projsOf (S : Name) (w : VExpr) (j : Nat) : List VExpr :=
  (List.range j).map fun k => VExpr.proj S k w

theorem projsOf_succ (S : Name) (w : VExpr) (j : Nat) :
    projsOf S w (j + 1) = projsOf S w j ++ [.proj S j w] := by
  simp [projsOf, List.range_succ]

/-- The field type of field `j`, at parameters `ps` and a major `w`, is the `j`-th field domain
instantiated at the parameters and the earlier projections. -/
theorem ProjTele.fieldType {S : Name} {info : VProjectionInfo} {ls : List VLevel}
    {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    (hlen : ls.length = info.uvars) {ps : List VExpr} (hpl : ps.length = info.nparams)
    (w : VExpr) {j : Nat} (hj : info.nparams + j < D.length) :
    info.fieldType S ls ps j w =
      some ((D[info.nparams + j]).subst (VExpr.argSubst (ps ++ projsOf S w j))) := by
  have hT : info.ctorType.instL ls = (VExpr.wrapForalls D R0).subst (VExpr.argSubst []) := by
    rw [T.shape]; exact VExpr.subst_id.symm
  simp only [VProjectionInfo.fieldType, hlen, hpl, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, if_false, hT]
  rw [VProjectionInfo.ipp_wrapForalls ps D R0 _ (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have := VProjectionInfo.ipf_wrapForalls S w R0 j (D.drop ps.length)
    (ps.foldl VExpr.Subst.cons (VExpr.argSubst [])) 0 (j + 1) (by simp; omega) (by omega)
  simp only [Nat.zero_add] at this
  rw [this, List.getElem_drop]
  simp only [hpl, Nat.zero_add, VExpr.argSubst, List.foldl_append, List.foldl_nil, projsOf]

/-- **L2: projections of a typed major.** For a structure whose result sort is never zero at
`ls`, every projection of a major typed at `S ls (ps ++ idx')` is typed at its field type, and
is congruent in the major. -/
theorem proj_typed (henv : env.Ordered) {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = info.uvars) (hnz : (info.resultLevel.inst ls).IsNeverZero)
    {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    {ps : List VExpr} {Tail : VExpr} (hps : ArgsTyped env U Δ (info.ctorType.instL ls) ps Tail)
    (hpl : ps.length = info.nparams) {w : VExpr} {idx' : List VExpr}
    (hidx : idx'.length = info.nindices)
    (hw : env.HasType U Δ w (VExpr.mkApps (.const S ls) (ps ++ idx'))) :
    ∀ i, i < info.numFields → ∃ F, info.fieldType S ls ps i w = some F ∧
      (∃ u, env.HasType U Δ F (.sort u)) ∧ env.HasType U Δ (.proj S i w) F ∧
      ∀ w', env.IsDefEq U Δ w w' (VExpr.mkApps (.const S ls) (ps ++ idx')) →
        env.IsDefEq U Δ (.proj S i w) (.proj S i w') F := by
  obtain ⟨c, lsR, args, hR0⟩ := T.head
  have hR0' : ∀ (σ : VExpr.Subst) A B, R0.subst σ ≠ .forallE A B := by
    rw [hR0]; exact subst_mkApps_const_ne_forallE c lsR args
  have hT : info.ctorType.instL ls = (VExpr.wrapForalls (D.drop ([] : List VExpr).length) R0).subst
      (VExpr.argSubst []) := by
    rw [T.shape]; exact VExpr.subst_id.symm
  rw [hT] at hps
  obtain ⟨hle, W0, -⟩ := ArgsTyped.substEq T.doms hR0' ps [] .nil (by simp) hps
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hle W0
  rw [T.numFields]
  -- the fields, one at a time
  have key : ∀ j, info.nparams + j ≤ D.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst (ps ++ projsOf S w j))
        (VExpr.argSubst (ps ++ projsOf S w j)) (D.take (info.nparams + j)).reverse ∧
      ∀ i, i < j → ∃ F, info.fieldType S ls ps i w = some F ∧
        (∃ u, env.HasType U Δ F (.sort u)) ∧ env.HasType U Δ (.proj S i w) F ∧
        ∀ w', env.IsDefEq U Δ w w' (VExpr.mkApps (.const S ls) (ps ++ idx')) →
          env.IsDefEq U Δ (.proj S i w) (.proj S i w') F := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simpa [projsOf, ← hpl] using W0, fun i hi => absurd hi (by omega)⟩
    | succ j ih =>
      intro hj
      obtain ⟨W, hprev⟩ := ih (by omega)
      have hk : info.nparams + j < D.length := by omega
      obtain ⟨u, hu⟩ := T.doms _ hk
      have hF := hu.subst henv W hΔ
      simp only [VExpr.subst] at hF
      have hft := T.fieldType hlen hpl w hk
      have hcong : ∀ w', env.IsDefEq U Δ w w' (VExpr.mkApps (.const S ls) (ps ++ idx')) →
          env.IsDefEq U Δ (.proj S j w) (.proj S j w')
            ((D[info.nparams + j]).subst (VExpr.argSubst (ps ++ projsOf S w j))) :=
        fun w' hww' => .projDF hp hls hlen hpl hidx hft hF hw hww' hcl (.inl hnz)
      have hproj := hcong w hw
      refine ⟨?_, fun i hi => ?_⟩
      · rw [projsOf_succ, ← List.append_assoc, show info.nparams + (j + 1) =
          (info.nparams + j) + 1 by omega, List.take_succ_eq_append_getElem hk,
          List.reverse_append, List.reverse_singleton, List.singleton_append,
          VExpr.argSubst_append_one]
        exact .cons (by rw [VExpr.Subst.cons_tail]; exact W) hu
          (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact hproj)
      · by_cases hij : i < j
        · exact hprev i hij
        · obtain rfl : i = j := by omega
          exact ⟨_, hft, ⟨u, hF⟩, hproj, hcong⟩
  intro i hi
  exact (key (i + 1) (by omega)).2 i (by omega)

end VEnv


end Lean4Lean
