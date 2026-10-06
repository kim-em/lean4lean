import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleLemmas

/-! # Soundness of a pattern rule (the `extra` case at rules with a constructor major)

`sound_pat`: for a stored rule `lhs ≡ rhs` whose left-hand side is a lambda telescope over a
constant head applied to leading arguments and a constructor major, given the rule's
syntactic facts (pattern, binder coverage, the family of the major domain in the head's type,
the constructor's family, rule uniqueness per head and constructor, and in mode C the
propositional typing of the major-only fields), the soundness of the instantiated rule
follows from the soundness and semantic typing (`HTS`) of its typing premises
(`docs/inductives/PHASE1B_NOTES.md`, section 10.2, "Soundness of the rule cases"). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The family of the major domain of the head's type (section 10.2): the head's type is a
telescope of `k+1` domains whose last is an application of a rigid family `I`, the family's
type is a telescope ending in a sort, and the constructor `ctor` returns `I`. -/
def HeadFam (env : VEnv) (n : Name) (k : Nat) (ctor : Name) : Prop :=
  ∃ ci dsH RH I lsI iargs cI dsI w, env.constants n = some ci ∧
    ci.type = .wrapForalls dsH RH ∧ dsH.length = k + 1 ∧
    dsH[k]? = some (.mkApps (.const I lsI) iargs) ∧ env.constants I = some cI ∧
    cI.type = .wrapForalls dsI (.sort w) ∧ dsI.length = iargs.length ∧ env.Rigid I ∧
    CtorFam env ctor I

theorem wrapForalls_append (a b : List VExpr) (R : VExpr) :
    VExpr.wrapForalls (a ++ b) R = VExpr.wrapForalls a (VExpr.wrapForalls b R) := by
  simp [VExpr.wrapForalls, List.foldr_append]

theorem DomsSD.left : ∀ {pre post : List VExpr} {Γ},
    DomsSD env U Δ Γ (pre ++ post) → DomsSD env U Δ Γ pre
  | [], _, _, _ => .nil
  | _ :: _, _, _, .cons h h' => .cons h (DomsSD.left h')

theorem TypeChain.tyCls_subst (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ v v Γ) (h : env.TypeChain U Γ X Y) :
    TyCls env U Δ (X.subst v) = TyCls env U Δ (Y.subst v) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W)
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W))

/-- All constructor observations of a constructor spine with the keys `keys`. -/
def ctorObs (c : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) : List Ob :=
  .ctorHead c ℓs keys.length :: (List.range keys.length).flatMap fun i =>
    match keys[i]? with
    | some k => .ctorArg i k.2.1 :: k.2.2.map (.ctorArgOb i (keys.take i))
    | none => []

theorem ctorObs_end (h : r ∈ ctorObs c ℓs keys) : CtorEnd c ℓs keys r := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range] at h
  rcases h with rfl | ⟨i, hi, h⟩
  · exact .inl rfl
  · rw [List.getElem?_eq_getElem hi] at h
    simp only [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨k, hk, rfl⟩
    · exact .inr (.inl ⟨i, hi, rfl⟩)
    · exact .inr (.inr ⟨i, hi, k, hk, rfl⟩)

theorem mem_ctorObs_head : .ctorHead c ℓs keys.length ∈ ctorObs c ℓs keys := List.mem_cons_self ..

theorem mem_ctorObs_arg (hi : i < keys.length) :
    .ctorArg i (keys[i]).2.1 ∈ ctorObs c ℓs keys := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine .inr ⟨i, hi, ?_⟩
  rw [List.getElem?_eq_getElem hi]; exact List.mem_cons_self ..

theorem mem_ctorObs_argOb (hi : i < keys.length) (hk : k ∈ (keys[i]).2.2) :
    .ctorArgOb i (keys.take i) k ∈ ctorObs c ℓs keys := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine .inr ⟨i, hi, ?_⟩
  rw [List.getElem?_eq_getElem hi]
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem hk)

/-- The instantiated pattern of a rule. -/
theorem pat_instL {df : VDefEq} {fs : List Nat}
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body) (hlsP : lsP.map (·.inst ls) = ls) :
    df.lhs.instL ls = .wrapLams (doms.map (·.instL ls)) (.mkApps (.const n ls)
      (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
        (ms.map (·.instL ls) ++ fs.map .bvar)])) ∧
    df.rhs.instL ls = .wrapLams (doms.map (·.instL ls)) (body.instL ls) := by
  refine ⟨?_, by rw [hr, instL_wrapLams']⟩
  rw [hl, instL_wrapLams']
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, hlsP]

/-- Demands for the arguments of a spine: a bare rule variable demands its observations. -/
def argDemand (doms : Nat) (Lx : Nat → List Ob) : VExpr → List Ob
  | .bvar x => if x < doms then Lx x else []
  | _ => []

theorem argDemand_ok {vS : ObSets} {Lx : Nat → List Ob} (hLx : ∀ x < nd, vS x = listSet (Lx x))
    (σ : VExpr.Subst) : ∀ args : List VExpr, List.Forall₂ (fun K a => ∀ y ∈ K, Obs' σ vS a y)
      (args.map (argDemand nd Lx)) args
  | [] => .nil
  | a :: as => by
    refine .cons ?_ (argDemand_ok hLx σ as)
    intro y hy
    cases a with
    | bvar x =>
      simp only [argDemand] at hy
      split at hy
      · rename_i hx; exact .bvar (by rw [hLx x hx]; exact hy)
      · cases hy
    | _ => cases hy

theorem closedN_wrapLams : ∀ {ds : List VExpr} {b : VExpr} {k : Nat},
    (VExpr.wrapLams ds b).ClosedN k →
      b.ClosedN (k + ds.length) ∧ ∀ i (h : i < ds.length), (ds[i]).ClosedN (k + i)
  | [], _, _, h => ⟨h, nofun⟩
  | d :: ds, b, k, h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := closedN_wrapLams (ds := ds) h2
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h3, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := h4 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem binderTy_closed {doms : List VExpr} (h : ∀ i (h : i < doms.length), (doms[i]).ClosedN i)
    (hx : x < doms.length) : (binderTy doms ls x).ClosedN doms.length := by
  have hx' : x < doms.reverse.length := by simpa using hx
  simp only [binderTy, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx',
    Option.getD_some, List.getElem_reverse]
  have := (h (doms.length - 1 - x) (by omega)).liftN (n := x+1) (j := 0)
  have e : doms.length - 1 - x + (x + 1) = doms.length := by omega
  rw [e] at this
  exact this.instL

/-- The body of a semantically typed lambda telescope is sound, and its domains are. -/
theorem HTS.wrapLams_body : ∀ {ds : List VExpr} {Γ b P},
    HTS env U Δ Γ (.wrapLams ds b) P → SoundAt env U Δ Γ (.wrapLams ds b) (.wrapLams ds b) P →
    ∃ B, SoundAt env U Δ (ds.reverse ++ Γ) b b B ∧ DomsSD env U Δ Γ ds
  | [], _, _, _, _, h => ⟨_, h, .nil⟩
  | A :: ds, Γ, b, P, H, _ => by
    obtain ⟨B, u, v, -, hA, hb, hsb, -, -⟩ := H.lam_inv rfl
    obtain ⟨B', h1, h2⟩ := HTS.wrapLams_body hb hsb.2
    exact ⟨B', by simpa [List.reverse_cons, List.append_assoc] using h1, .cons hA h2⟩

theorem liftN_subst_shift (D : VExpr) (σ : VExpr.Subst) :
    ∀ x, (D.liftN (x+1)).subst σ = D.subst fun i => σ (i + (x+1))
  | 0 => by
    rw [show D.liftN 1 = D.lift from rfl, VExpr.lift_subst]; rfl
  | x+1 => by
    rw [show D.liftN (x+1+1) = (D.liftN (x+1)).lift by
      rw [VExpr.lift, VExpr.liftN_liftN]]
    rw [VExpr.lift_subst, liftN_subst_shift D σ.tail x]
    rfl

theorem wrap_le (h : o ≼ o') : wrap ks o ≼ wrap ks o' := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact Ob.Le.app' Covers.refl ih

theorem SubstEq.entry_typed : ∀ {L : List VExpr} {v : VExpr.Subst} {x : Nat},
    Ctx.SubstEq env U Δ v v (L ++ Γ) → (hx : x < L.length) →
    ∃ u, env.HasType U (L.drop (x+1) ++ Γ) (L[x]) (.sort u)
  | A :: L, v, 0, .cons _ hA _, _ => ⟨_, hA⟩
  | A :: L, v, x+1, .cons W _ _, hx => SubstEq.entry_typed W (by simpa using hx)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

omit henv hΔ in
theorem forall₂_split' {R : α → β → Prop} :
    ∀ {l₁ : List α} {as : List β} {a : β}, List.Forall₂ R l₁ (as ++ [a]) →
      ∃ l x, l₁ = l ++ [x] ∧ List.Forall₂ R l as ∧ R x a :=
  forall₂_split

/-- The domain class of a bare-variable argument is the class of the variable's type. -/
theorem bvar_dom_cls (W : Ctx.SubstEq env U Δ v v Γ) (H : HTS env U Δ Γ (.bvar x) A')
    (hL : Lookup Γ x A) : TyCls env U Δ (A'.subst v) = TyCls env U Δ (A.subst v) := by
  obtain ⟨A₀, hL₀, h⟩ := H.bvar_chain rfl
  cases hL.uniq hL₀
  rcases h with rfl | h
  · rfl
  · exact (TypeChain.tyCls_subst henv hΔ W h).symm

/-- The family indicator at the major domain: a rigid observation of the major's family,
under the key prefix of a typed head chain. -/
theorem major_indicator {ci : VConstant} {ls : List VLevel} {uH : VLevel}
    (hT : HTS env U Δ [] (ci.type.instL ls) (.sort uH))
    (eH : ci.type = .wrapForalls dsH RH) (hlen : dsH.length = k + 1)
    (hk : dsH[k]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    {keys : List Key} (hkeys : keys.length = k + 1)
    (hτ₀ : ∀ τ ∈ τ₀, Obs' .id .empty (ci.type.instL ls) τ)
    (hty : TypedOb env U Δ (wrap keys o) τ₀) :
    Obs' .id .empty (ci.type.instL ls) (piCodChain (keys.take k)
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length))) := by
  have eT : ci.type.instL ls = .wrapForalls (dsH.map (·.instL ls)) (RH.instL ls) := by
    rw [eH, instL_wrapForalls'']
  have hk' : k < dsH.length := by omega
  have hsplit : dsH.map (·.instL ls) =
      (dsH.take k).map (·.instL ls) ++ [(VExpr.mkApps (.const I lsI) iargs).instL ls] := by
    conv => lhs; rw [← List.take_append_drop k dsH]
    rw [List.map_append]; congr 1
    rw [List.drop_eq_getElem_cons hk', List.drop_eq_nil_of_le (by omega)]
    simp only [List.map_cons, List.map_nil]
    rw [List.getElem?_eq_getElem hk'] at hk; injection hk with hk; rw [hk]
  rw [eT] at hT hτ₀ ⊢
  have hpi := hT.piSD
  obtain ⟨σH, SH, hkH, -⟩ := tele_unwind henv hΔ hpi .nil TV.empty
    (by simp [hkeys, hlen]) hty hτ₀
  rw [hsplit] at hkH hT
  have hkeys' : keys = keys.take k ++ keys.drop k := (List.take_append_drop k keys).symm
  rw [hkeys'] at hkH
  obtain ⟨σ₁, S₁, hk1, -⟩ := hkH.split (by simp; omega)
  have hpi' := hT.piSD
  obtain ⟨W₁, tv₁⟩ := hk1.typed' henv hΔ (DomsSD.left hpi'.doms) .nil TV.empty
  obtain ⟨u, hA, -⟩ := HTS.tele_dom (pre := (dsH.take k).map (·.instL ls)) (post := [])
    (by simpa using hT)
  simp only [VExpr.instL, List.append_nil] at hA W₁ tv₁
  have hr := (spine_rigid_obs henv hΔ hA W₁ tv₁ hIrig).2
  simp only [List.length_map] at hr
  have hd : Obs' σ₁ S₁ (.wrapForalls [(VExpr.mkApps (.const I lsI) iargs).instL ls] (RH.instL ls))
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length)) := by
    simp only [VExpr.wrapForalls, List.foldr_cons, List.foldr_nil, VExpr.instL_mkApps,
      VExpr.instL]
    exact Obs.piDomOb hr
  have := tele_obs hk1 hd
  rw [hsplit, wrapForalls_append]
  exact this

/-- Binding a variable that occurs bare among the leading arguments, from its key at its
first occurrence. -/
theorem bind_lead {doms lead : List VExpr} {ls : List VLevel} {v : VExpr.Subst} {vS : ObSets}
    {infoL : List (Key × VExpr)} {Lx : Nat → List Ob} {x i : Nat}
    (Wv : Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ))
    (hLx : ∀ x < doms.length, vS x = listSet (Lx x)) (hx : x < doms.length)
    (hinfoL : List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS) infoL
      (lead.map (·.instL ls)))
    (hKsi : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      ((lead.map (·.instL ls)).map (argDemand doms.length Lx)) infoL)
    (hi : lead[i]? = some (.bvar x)) :
    ∃ k : Key, (infoL.map (·.1))[i]? = some k ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst v)) k.2.1 ∧ k.2.1 (v x) ∧
      vS x = listSet k.2.2 := by
  have hil : i < lead.length := (List.getElem?_eq_some_iff.1 hi).1
  have hlen := List.Forall₂.length_eq hinfoL
  have hi' : i < infoL.length := by simp at hlen; omega
  have ha : (lead.map (·.instL ls))[i]'(by simpa using hil) = .bvar x := by
    simp only [List.getElem_map]
    rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
  obtain ⟨_, hkd⟩ := forall₂_getElem hinfoL i hi'
  obtain ⟨_, hks⟩ := forall₂_getElem hKsi i (by simpa using hil)
  rw [ha] at hkd
  simp only [List.getElem_map, ha, argDemand, hx, ite_true] at hks
  obtain ⟨h1, h2, h3, h4, -⟩ := hkd
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
  have eD := bvar_dom_cls henv hΔ Wv h4 hL
  have hvx := (Wv.lookup hL).hasType.1
  refine ⟨(infoL[i]).1, by simp [hi'], ?_, ?_, ?_⟩
  · rw [h1, h3, eD]; exact .of_hasType hvx
  · rw [h1]; exact ElCls.self
  · rw [hLx x hx]
    funext y; apply propext; constructor
    · exact fun h => hks y h
    · intro h; have := Obs.bvar_iff.1 (h2 y h); rwa [hLx x hx] at this

/-- Binding a field variable from the constructor observations of the major. -/
theorem bind_field {doms margs : List VExpr} {ls : List VLevel} {v : VExpr.Subst} {vS : ObSets}
    {cinfo : List (Key × VExpr)} {Lx : Nat → List Ob} {x q : Nat} {c : Name}
    {ℓs : List (List Nat → Nat)}
    (Wv : Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ))
    (hx : x < doms.length)
    (hcinfo : List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS) cinfo
      margs)
    (hcKs : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      (margs.map (argDemand doms.length Lx)) cinfo)
    (hq : margs[q]? = some (.bvar x)) :
    ∃ cl, .ctorArg q cl ∈ ctorObs c ℓs (cinfo.map (·.1)) ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst v)) cl ∧ cl (v x) ∧
      ∀ k ∈ Lx x, .ctorArgOb q ((cinfo.map (·.1)).take q) k ∈ ctorObs c ℓs (cinfo.map (·.1)) := by
  have hql : q < margs.length := (List.getElem?_eq_some_iff.1 hq).1
  have hlen := List.Forall₂.length_eq hcinfo
  have hq' : q < cinfo.length := by omega
  have ha : margs[q] = .bvar x := (List.getElem?_eq_some_iff.1 hq).2
  obtain ⟨_, hkd⟩ := forall₂_getElem hcinfo q hq'
  obtain ⟨_, hks⟩ := forall₂_getElem hcKs q (by simpa using hql)
  rw [ha] at hkd
  simp only [List.getElem_map, ha, argDemand, hx, ite_true] at hks
  obtain ⟨h1, -, h3, h4, -⟩ := hkd
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
  have eD := bvar_dom_cls henv hΔ Wv h4 hL
  have hvx := (Wv.lookup hL).hasType.1
  have hq'' : q < (cinfo.map (·.1)).length := by simpa using hq'
  refine ⟨(cinfo[q]).1.2.1, ?_, ?_, ?_, fun k hk => ?_⟩
  · have := mem_ctorObs_arg (c := c) (ℓs := ℓs) hq''; simpa using this
  · rw [h1, h3, eD]; exact .of_hasType hvx
  · rw [h1]; exact ElCls.self
  · have := mem_ctorObs_argOb (c := c) (ℓs := ℓs) hq'' (k := k) (by simpa using hks k hk)
    simpa using this

/-- **Right to left** for a pattern rule: every observation of the right side is one of the
left side. -/
theorem pat_rhs_sub {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls)
    (hhead : HeadFam env n lead.length ctor)
    (hcis : IsCtor env ctor)
    (hpf : RuleMode env n lead.length ls true → ∀ x < doms.length,
      (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
      ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → TypedOb env U Δ τ [.sort fun _ => 0])
    (hL : HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.rhs.instL ls)) (Obs' σ S (df.lhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
  intro o ho
  refine ⟨o, ?_, .refl⟩
  obtain ⟨τs, hτs, hty⟩ := (hR σ σ S W tv tv).2.2.1 o ho
  rw [eR] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eL] at hL ⊢
  obtain ⟨T', hX, hdoms, τc, hτc, hpty⟩ := hL.lamSpine henv hΔ rfl W tv hk hτs hty
  obtain ⟨Wv, tvv⟩ := hk.typed' henv hΔ hdoms W tv
  have hinner := hk.inner
  obtain ⟨Lx, hLx⟩ : ∃ Lx : Nat → List Ob, ∀ x < doms.length, vS x = listSet (Lx x) :=
    ⟨fun x => if h : x < doms.length then Classical.choose (hinner x (by simpa using h))
      else [], fun x hx => by
        simp only [hx, dite_true]; exact Classical.choose_spec (hinner x (by simpa using hx))⟩
  -- the first pass of the head spine
  have hKs := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
    (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
      (ms.map (·.instL ls) ++ fs.map .bvar)])
  rw [List.map_append] at hKs
  obtain ⟨ci, info, hci, -, ⟨uH, hHT, -⟩, hinfo, hKsi, P1, -, dP2⟩ :=
    hX.spine henv hΔ rfl Wv tvv _ hKs τc hτc
  obtain ⟨infoL, kaM, rfl, hinfoL, hkaM⟩ := forall₂_split hinfo
  obtain ⟨KsL, KsM, eKs, hKsiL, -⟩ := forall₂_split' hKsi
  obtain ⟨rfl, -⟩ := List.append_inj' eKs rfl
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 p hpty
  obtain ⟨ci', dsH, RH, I, lsI, iargs, cI, dsI, w, hci', eH, hlenH, hkH, hI, hIty, hIlen, hIrig,
    hcf⟩ := hhead
  cases hci.symm.trans hci'
  have hlenL : infoL.length = lead.length := by
    have := List.Forall₂.length_eq hinfoL; simpa using this
  have hind := major_indicator henv hΔ hHT eH hlenH hkH hIrig
    (keys := (infoL ++ [kaM]).map (·.1)) (by simp [hlenL]) hτ₀ hty₀
  rw [show ((infoL ++ [kaM]).map (·.1)).take lead.length = infoL.map (·.1) by
    simp [List.map_append, hlenL]] at hind
  obtain ⟨xr, hxr, lr⟩ := dP2 infoL kaM [] rfl _ hind
  rw [lr.rigid_inv] at hxr
  have hMS : MajorSort env n lead.length ls ((w.inst (lsI.map (·.inst ls))).eval) :=
    ⟨ci, dsH, RH, I, lsI, iargs, cI, dsI, w, hci, eH, hlenH, hkH, hI, hIty, hIlen, rfl⟩
  have firstOcc : ∀ x : Nat, (∃ i : Nat, lead[i]? = some (VExpr.bvar x)) →
      ∃ i : Nat, lead[i]? = some (VExpr.bvar x) ∧ ∀ j < i, lead[j]? ≠ some (VExpr.bvar x) := by
    intro x ⟨i₀, hi₀⟩
    have hmem : VExpr.bvar x ∈ lead := List.mem_of_getElem? hi₀
    obtain ⟨i, hi⟩ : ∃ i, lead.idxOf? (VExpr.bvar x) = some i := by
      cases h : lead.idxOf? (VExpr.bvar x) with
      | none => exact absurd hmem (by simpa using h)
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hil, h1, h2⟩ := List.idxOf?_eq_some_iff.1 hi
    refine ⟨i, List.getElem?_eq_some_iff.2 ⟨hil, h1⟩, fun j hj e => ?_⟩
    obtain ⟨hjl, e⟩ := List.getElem?_eq_some_iff.1 e
    exact h2 j hj e
  have fieldIdx : ∀ x : Nat, x ∈ fs → ∃ j : Nat, fs[j]? = some x := fun x hx => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    exact ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, e⟩⟩
  -- the common conclusion from a rule clause instance
  have finish : ∀ (infoL' : List (Key × VExpr)) (kaM' : Key × VExpr) (S' : ObSets) (mC : Bool)
      (τ₀' : List Ob),
      List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS)
        (infoL' ++ [kaM']) (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]) →
      (∀ τ ∈ τ₀', Obs' .id .empty (ci.type.instL ls) τ) →
      TypedOb env U Δ (wrap ((infoL' ++ [kaM']).map (·.1)) p) τ₀' →
      RuleMode env n lead.length ls mC →
      (mC = false → ∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ kaM'.1.2.2) →
      RuleBind env U Δ doms ls lead ms.length fs mC (infoL'.map (·.1)) kaM'.1.2.2 v S' →
      (∀ x o, vS x o → S' x o) →
      Obs' σ S (.wrapLams (doms.map (·.instL ls)) (.mkApps (.const n ls)
        (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]))) (wrap lk p) := by
    intro infoL' kaM' S' mC τ₀' hinfo' hτ₀' hty₀' hmode hhd hbind hS'
    have hlen' : infoL'.length = lead.length := by
      have := List.Forall₂.length_eq hinfo'; simpa using this
    have hc := Obs.rule (σ := v) (S := vS) (Dm := kaM'.1.1) (cm := kaM'.1.2.1) (Km := kaM'.1.2.2)
      (lkeys := infoL'.map (·.1)) hdf hl hr hci hτ₀' (by simpa using hty₀') (by simp [hlen'])
      hmode hhd hbind (hp.mono hS')
    have hXo := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo') (by simpa using hc)
    exact Obs.wrapLams_iff.2 ⟨lk, v, vS, p, hk, rfl, hXo⟩
  by_cases hm : (w.inst (lsI.map (·.inst ls))).eval = fun _ => 0
  · -- mode C: the major is ignored, its only own fields are proofs
    have hmode : RuleMode env n lead.length ls true := ⟨_, hMS, by simp [hm]⟩
    refine finish infoL kaM vS true τ₀ (forall₂_append_single' hinfoL hkaM) hτ₀ hty₀ hmode
      nofun ?_ fun _ _ h => h
    intro x hx
    by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
    · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL hKsiL hi
      exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, hk4⟩
    · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
      have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
        exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
      obtain ⟨j, hj⟩ := fieldIdx x hxf
      obtain ⟨hP, hprop⟩ := hpf hmode x hx hnb v vS Wv tvv
      have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
      refine .inr ⟨hnb, j, hj, .inr ⟨rfl, ⟨_, .self, (Wv.lookup hL).hasType.1⟩, hP, ?_⟩⟩
      funext k; apply propext; constructor
      · intro hk
        obtain ⟨τs', hτs', htk⟩ := tvv x _ hL k hk
        exact htk.not_prop fun τ hτ => hprop τ (hτs' τ hτ)
      · nofun
  · -- mode AB: the major's constructor observations
    have hmode : RuleMode env n lead.length ls false := ⟨_, hMS, by simp [hm]⟩
    obtain ⟨-, -, -, hHTSm, -⟩ := hkaM
    have hKc := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
      (ms.map (·.instL ls) ++ fs.map .bvar)
    obtain ⟨cc, cinfo, hcc, -, -, hcinfo, hcKs, cP1, -, -⟩ :=
      hHTSm.spine henv hΔ rfl Wv tvv _ hKc
        [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length]
        (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hxr)
    have hCT : CtorTyped env ctor [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length] :=
      ⟨I, _, _, List.mem_singleton_self _, hcf, cI, dsI, w, hI, hIty, hIlen, by
        rw [← VLevel.eval_inst_eq_evalAt]; exact hm⟩
    have hcobs : ∀ r ∈ ctorObs ctor ((lsC.map (·.inst ls)).map (·.eval)) (cinfo.map (·.1)),
        Obs' v vS (.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)) r := by
      intro r hr
      have hend := ctorObs_end hr
      have hrty : TypedOb env U Δ r [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length] := by
        rcases hend with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
        · exact .ctorHead hCT
        · exact .ctorArg hCT
        · exact .ctorArgOb hCT
      obtain ⟨τ₀c, h1, h2⟩ := cP1 r hrty
      exact obs_mkApps_of_wrap (KeyData.forall₂_keys hcinfo) (.ctor hcis hcc h1 h2 hend)
    have hKs2 := forall₂_append_single' (argDemand_ok (env := env) (U := U) (Δ := Δ)
      (nd := doms.length) hLx v (lead.map (·.instL ls))) hcobs
    obtain ⟨ci2, info2, hci2, -, -, hinfo2, hKsi2, P12, -, -⟩ :=
      hX.spine henv hΔ rfl Wv tvv _ hKs2 τc hτc
    cases hci.symm.trans hci2
    obtain ⟨infoL2, kaM2, rfl, hinfoL2, -⟩ := forall₂_split hinfo2
    obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := forall₂_split' hKsi2
    obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
    cases e2
    obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 p hpty
    have hclen : (cinfo.map (·.1)).length = ms.length + fs.length := by
      have := List.Forall₂.length_eq hcinfo; simp at this ⊢; omega
    have hmarg : ∀ j x, fs[j]? = some x →
        (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms.length + j]? = some (.bvar x) := by
      intro j x hj
      rw [List.getElem?_append_right (by simp)]
      simp [hj]
    classical
    let S' : ObSets := fun x =>
      if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ fs then
        fun k => ∃ pre, .ctorArgOb (ms.length + fs.idxOf x) pre k ∈ kaM2.1.2.2
      else vS x
    have hfsj : ∀ x, x ∈ fs → fs[fs.idxOf x]? = some x := fun x hx =>
      List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_of_mem hx, List.getElem_idxOf _⟩
    refine finish infoL2 kaM2 S' false τ₀2 hinfo2 hτ₀2 hty₀2 hmode
      (fun _ => ⟨_, hKsM2 _ (hclen ▸ mem_ctorObs_head)⟩) ?_ ?_
    · intro x hx
      by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
      · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL2 hKsiL2 hi
        have : S' x = vS x := by
          simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
        exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, this.trans hk4⟩
      · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
        have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
          obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
          exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
        obtain ⟨cl, hcl, hcty, hcm, -⟩ := bind_field (c := ctor)
          (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
          (hmarg _ _ (hfsj x hxf))
        refine .inr ⟨hnb, fs.idxOf x, hfsj x hxf, .inl ⟨rfl, cl, hKsM2 _ hcl, hcty, hcm, ?_⟩⟩
        simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
    · intro x o ho
      simp only [S']
      split
      · rename_i hMF
        obtain ⟨hx, hnb, hxf⟩ := hMF
        obtain ⟨_, -, -, -, hall⟩ := bind_field (c := ctor)
          (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
          (hmarg _ _ (hfsj x hxf))
        rw [hLx x hx] at ho
        exact ⟨_, hKsM2 _ (hall o ho)⟩
      · exact ho

/-- **Left to right** for a pattern rule: every observation of the left side is subsumed by
one of the right side. -/
theorem pat_lhs_sub {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c) (hdr : env.DefRules)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const n lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧
        ((ctor' = ctor ∨ RuleMode env n lead.length ls true) → df' = df))
    (hRH : HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.lhs.instL ls)) (Obs' σ S (df.rhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
  intro o ho
  rw [eL] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eR] at hRH hR ⊢
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hR
  obtain ⟨Wv, tvv⟩ := hk.typed' henv hΔ hdomsR W tv
  obtain ⟨keys, hkeys, hc⟩ := wrap_of_obs_mkApps' hp
  have headOf : df.lhs.stripLams.getAppFnArgs.1 = .const n lsP := by
    rw [hl]; exact VExpr.stripLams_wrapLams_mkApps_head
  rcases Obs.const_iff.1 hc with ⟨_, _, _, _, _, hrig, _⟩ | ⟨df', _, _, hdf', hlhs', _⟩ |
    ⟨_, _, _, _, _, hcn, _⟩ |
    ⟨df'', doms'', lsP'', lead'', ctor'', lsC'', ms'', fs'', body'', ci, τs, lkeys, Dm, cm, Km,
      p'', mC, τ, S'', e, hdf'', hl'', hr'', -, -, -, hlen'', hmode, hhd, hbind, hbody⟩
  · exact absurd headOf (hrig df hdf lsP)
  · have := hdr.excl df' df hdf' hdf n _ lsP hlhs' headOf
    subst this
    exact absurd (hl.symm.trans hlhs') VExpr.wrapLams_mkApps_snoc_ne_const
  · exact absurd headOf (hctor n hcn df hdf lsP)
  obtain ⟨hleadlen, huq⟩ := huniq df'' doms'' lsP'' lead'' ctor'' lsC'' ms'' fs'' body'' hdf'' hl'' hr''
  have hklen : keys.length = lead.length + 1 := by
    have := List.Forall₂.length_eq hkeys; simpa using this
  obtain ⟨ekeys, rfl⟩ := wrap_inj_len (by simp [hklen, hlen'', hleadlen]) e
  subst ekeys
  obtain ⟨lkeys', mk, ekl, hkeysL, hkM⟩ := forall₂_split hkeys
  obtain ⟨rfl, emk⟩ := List.append_inj' ekl (by simp [hlen'', hleadlen])
  cases emk
  obtain ⟨-, hKmcov⟩ := hkM
  -- the clause's rule is the given one
  have hdf_eq : df'' = df := by
    apply huq
    cases mC with
    | true => exact .inr (by rw [← hleadlen]; exact hmode)
    | false =>
      refine .inl ?_
      obtain ⟨ℓs, hmem⟩ := hhd rfl
      obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
      rw [ly.ctorHead_inv] at hy
      obtain ⟨_, _, hend⟩ := ctor_spine_inv hcrig hy (.inl ⟨_, _, _, rfl⟩)
      rcases hend with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩
      · injection h
      · cases h
      · cases h
  subst hdf_eq
  obtain ⟨rfl, -, -, rfl, emaj⟩ := wrapLams_pat_inj (hl''.symm.trans hl)
  obtain ⟨rfl, rfl, emargs⟩ := mkApps_const_inj emaj
  obtain ⟨-, rfl⟩ := wrapLams_inj_len rfl (hr''.symm.trans hr)
  -- closedness
  have hbcl : (body''.instL ls).ClosedN doms''.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms'' body'').ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms''.length), (doms''[i]).ClosedN i := by
    have := (closedN_wrapLams (hl ▸ hlcl :
      (VExpr.wrapLams doms'' (.mkApps (.const n lsP)
        (lead'' ++ [.mkApps (.const ctor'' lsC'') (ms ++ fs.map .bvar)]))).ClosedN 0)).2
    simpa using this
  -- the major's arguments
  have hmargs : ∀ j x, fs''[j]? = some x →
      (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms''.length + j]? = some (.bvar x) := by
    intro j x hj
    have e1 : ms.map (·.instL ls) ++ fs.map VExpr.bvar =
        (ms'' ++ fs''.map VExpr.bvar).map (·.instL ls) := by
      rw [emargs]; simp [List.map_append, VExpr.instL]
    rw [e1, List.getElem?_map, List.getElem?_append_right (by simp)]
    simp [hj, VExpr.instL]
  -- facts about the constructor observations of the major
  have argOf : ∀ j x cl, fs''[j]? = some x → .ctorArg (ms''.length + j) cl ∈ Km → cl (v x) := by
    intro j x cl hj hcl
    obtain ⟨y, hy, ly⟩ := hKmcov _ hcl
    rw [ly.ctorArg_inv] at hy
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inl ⟨_, _, rfl⟩))
    rcases hend with h | ⟨i, hi, h⟩ | ⟨_, _, _, _, h⟩
    · cases h
    · injection h with e1 e2; subst e1; subst e2
      obtain ⟨_, hci', -⟩ := forall₂_getElem hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      rw [hci', ha]; exact ElCls.self
    · cases h
  have argObOf : ∀ j x pre k, fs''[j]? = some x →
      .ctorArgOb (ms''.length + j) pre k ∈ Km → ∃ k', vS x k' ∧ k' ≼ k := by
    intro j x pre k hj hk
    obtain ⟨y, hy, ly⟩ := hKmcov _ hk
    obtain ⟨k₀, rfl, l₀⟩ := ly.ctorArgOb_inv
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inr ⟨_, _, _, rfl⟩))
    rcases hend with h | ⟨_, _, h⟩ | ⟨i, hi, k', hk', h⟩
    · cases h
    · cases h
    · injection h with e1 e2 e3; subst e1
      obtain ⟨_, -, hcov⟩ := forall₂_getElem hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      obtain ⟨k₁, hk₁, l₁⟩ := hcov k' hk'
      rw [ha] at hk₁
      exact ⟨k₁, Obs.bvar_iff.1 hk₁, l₁.trans (e3 ▸ l₀)⟩
  -- the binding, restricted to the rule's variables
  classical
  let τ' : VExpr.Subst := fun x => if x < doms''.length then τ x else v x
  let S' : ObSets := fun x => if x < doms''.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms''.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms''.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body''.instL ls) p :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms''.length
    · simp only [S', hx, if_true] at ho
      rcases hbind x hx with ⟨i, k, hi, -, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, -, hS⟩⟩
      · rw [hkS] at ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨_, -, hcov⟩ := forall₂_getElem hkeysL i hil
        have hk : lkeys[i] = k := by
          have := List.getElem?_eq_some_iff.1 hki; exact this.2
        rw [hk] at hcov
        obtain ⟨o', ho', l⟩ := hcov o ho
        have ha : (lead''.map (·.instL ls))[i]'(by
            have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
          simp only [List.getElem_map]
          rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
        rw [ha] at ho'
        exact ⟨o', Obs.bvar_iff.1 ho', l⟩
      · rw [hS] at ho
        obtain ⟨pre, hpre⟩ := ho
        exact argObOf j x pre o hj hpre
      · rw [hS] at ho; cases ho
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the actual variables
  have hL := fun x (hx : x < doms''.length) => lookup_binderTy (Γ := Γ) (ls := ls) hx
  have hbcl' : ∀ x, x < doms''.length →
      (binderTy doms'' ls x).subst τ = (binderTy doms'' ls x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have W' : Ctx.SubstEq env U Δ τ' v ((doms''.map (·.instL ls)).reverse ++ Γ) := by
    refine SubstEq.of_heads_ind Wv (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms''.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv.lookup (hL x hx')).hasType.1
    rcases hbind x hx' with ⟨i, k, hi, -, hki, hkt, hkm, -⟩ |
      ⟨-, j, hj, ⟨-, cl, hcl, hct, hcm, -⟩ | ⟨-, ⟨X, hX, hτX⟩, ⟨P, hP, hPs⟩, -⟩⟩
    · have hil : i < lkeys.length := by
        have := List.Forall₂.length_eq hkeysL
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
      obtain ⟨_, hcls, -⟩ := forall₂_getElem hkeysL i hil
      have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
      have ha : (lead''.map (·.instL ls))[i]'(by
          have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
        simp only [List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
      rw [hk, ha] at hcls
      have hvk : k.2.1 (v x) := by rw [hcls]; exact ElCls.self
      exact hkt.defeq henv hΔ hkm hvk
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- mode C: both are proofs of the proposition `P`
      have hD := SubstEq.entry_typed Wv hx
      obtain ⟨uD, hDt⟩ := hD
      have hDD := hDt.substDF henv hW.wf hΔ hW
      have eA : (binderTy doms'' ls x) =
          ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
            (lookup_append _ x hx)
      have e1 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) τ' x
      have e2 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) v x
      rw [← eA] at e1 e2
      have hvx' : env.HasType U Δ (v x) ((binderTy doms'' ls x).subst τ) := by
        rw [hbcl' x hx', e1]; rw [e2] at hvx; exact hDD.symm.defeqDF hvx
      have hτx : env.HasType U Δ (τ x) ((binderTy doms'' ls x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq' henv hΔ hP hτx
      have h2 := TyCls.defeq' henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
  have hctx := DomsSD.ctxSD (L := []) (Γ := Γ) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvτ := TV.transfer henv hΔ hctx W' (fun x hx => hτ'2 x (by simpa using hx)) tvv
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS W' tvτ tvv).1 p₁ hp₁
  exact ⟨wrap lk p₂, Obs.wrapLams_iff.2 ⟨lk, v, vS, p₂, hk, rfl, hp₂⟩, wrap_le (l₂.trans l₁)⟩

/-- **Soundness of a pattern rule.** -/
theorem sound_pat {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hhead : HeadFam env n lead.length ctor)
    (hcis : IsCtor env ctor) (hcrig : env.Rigid ctor)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hdr : env.DefRules)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const n lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧
        ((ctor' = ctor ∨ RuleMode env n lead.length ls true) → df' = df))
    (hpf : RuleMode env n lead.length ls true → ∀ x < doms.length,
      (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
      ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → TypedOb env U Δ τ [.sort fun _ => 0])
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls)) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  have hLc := hlcl.instL (ls := ls)
  have hRc := hrcl.instL (ls := ls)
  refine ⟨fun o h => ?_, fun o h => ?_, (ihL.1 σ σ S W.left tv tv).2.2.1,
    (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  · obtain ⟨o', h1, l⟩ := pat_lhs_sub henv hΔ hdf hl hr hlsP hlcl hrcl hcrig hctor hdr huniq
      ihR.2 ihR.1 W.left tv o h
    exact ⟨o', (Obs.closed_iff_id hRc).2 ((Obs.closed_iff_id hRc).1 h1), l⟩
  · obtain ⟨o', h1, l⟩ := pat_rhs_sub henv hΔ hdf hl hr hcov hlsP hhead hcis hpf ihL.2 ihR.1
      W' tv' o h
    exact ⟨o', (Obs.closed_iff_id hLc).2 ((Obs.closed_iff_id hLc).1 h1), l⟩

end

end Model
end VEnv
end Lean4Lean
