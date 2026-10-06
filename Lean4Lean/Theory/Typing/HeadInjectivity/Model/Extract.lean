import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound
import Lean4Lean.Theory.Typing.HeadInjectivity.Core

/-! # Chain-level head injectivity for rule-free environments (milestone M2)

`VEnv.WF.headInjectivityCore_of_noRules`: in a well-formed environment without
definitional rules, projections or eliminators, the hypothesis `HeadInjectivityCore` of the
syntactic layer holds (`docs/inductives/PHASE1B_NOTES.md`, sections 3 and 9.3).

All observations are taken at the identity valuation `(id, ∅)` of the chain's own context
(`Δ = Γ`); a chain is turned into `Ob.Sub` inclusions link by link (`chain_sub`, from
`sound`).

* `sort_sort`: the `sort` observation.
* `forallE_chain`, with two observations (review point R5): the domain class at the identity
  valuation gives `TypeChain Γ A A'`; then, in `A :: Γ` and for the weakened chain, the
  codomain class at the fresh-variable key `bvar 0` gives `TypeChain (A :: Γ) B B'`.
* `rigid_rigid`/`former_args`: a sort-typed spine `mkApps (const c ls) args` has the
  observations `rigid c (ls.map eval) n` and `rigidArg i cᵢ` (`spine_typed`: the spine
  observations of the head are typed, by the strong typing derivation of the spine and the
  typing invariant of soundness); on the other side of the chain they force the same head,
  levels and arity, and each argument into the class of the corresponding left argument,
  which the collapse lemma turns into a definitional equality. For `former_args`, the
  domain classes of the left spine observation are those of the syntactic telescope
  (`tele_spine`), because the observation is typed at the observations of the constant's
  type. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat}

/-! ## List helpers -/

theorem forall₂_getElem {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length),
      ∃ h₂ : i < l₂.length, R l₁[i] l₂[i]
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons h _, 0, _ => ⟨Nat.zero_lt_succ _, h⟩
  | _, _, .cons _ H, i+1, h₁ =>
    let ⟨h₂, h⟩ := forall₂_getElem H i (Nat.lt_of_succ_lt_succ h₁); ⟨Nat.succ_lt_succ h₂, h⟩

theorem forall₂_of_getElem {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | _ :: _, _ :: _, h, H =>
    .cons (H 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (forall₂_of_getElem (Nat.succ.inj h) fun i h₁ h₂ =>
        H (i+1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂))

theorem forall₂_zip {R : γ → α → Prop} {R' : γ → β → Prop} {P : α → β → Prop}
    (H : ∀ k a b, R k a → R' k b → P a b) :
    ∀ {ks : List γ} {l₁ : List α} {l₂ : List β},
      List.Forall₂ R ks l₁ → List.Forall₂ R' ks l₂ → List.Forall₂ P l₁ l₂
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 H1, .cons h2 H2 => .cons (H _ _ _ h1 h2) (forall₂_zip H H1 H2)

theorem forall₂_imp {R R' : α → β → Prop} (H : ∀ a b, R a b → R' a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R' l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h H' => .cons (H _ _ h) (forall₂_imp H H')

theorem forall₂_append_single {R : α → β → Prop} (H : List.Forall₂ R l₁ l₂) (h : R a b) :
    List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction H with
  | nil => exact .cons h .nil
  | cons h' _ ih => exact .cons h' ih

theorem forall₂_equiv_of_map_eval :
    ∀ {ls ls' : List VLevel}, ls.map (·.eval) = ls'.map (·.eval) → List.Forall₂ (· ≈ ·) ls ls'
  | [], [], _ => .nil
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_equiv_of_map_eval h.2)

theorem mkApps_concat (f : VExpr) (as : List VExpr) (a : VExpr) :
    VExpr.mkApps f (as ++ [a]) = .app (VExpr.mkApps f as) a := by
  simp [VExpr.mkApps, List.foldl_append]

theorem mkApps_const_inv (h : e = VExpr.mkApps (.const c ls) args) :
    (args = [] ∧ e = .const c ls) ∨
      ∃ as a, args = as ++ [a] ∧ e = .app (VExpr.mkApps (.const c ls) as) a := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · exact .inl ⟨rfl, h⟩
  · refine .inr ⟨as, a, by simp, ?_⟩
    rw [h, List.concat_eq_append, mkApps_concat]

theorem instL_wrapForalls' (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls ds body).instL ls =
      VExpr.wrapForalls (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢
    rw [ih]

/-! ## Observations at the identity valuation -/

/-- Observations at the identity valuation of `Γ`. -/
abbrev OI (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → Ob → Prop :=
  Obs env U Γ VExpr.Subst.id ObSets.empty

/-- Soundness of the observation model for every derivation of `env` (at every target
context): the hypothesis of the extraction, supplied by `Model.sound` under the hypotheses
of each stage. -/
def SoundEnv (env : VEnv) : Prop :=
  ∀ {U Δ Γ t t' T}, OnCtx Δ (env.IsType U) → env.IsDefEqStrong U Γ t t' T →
    SoundAt env U Δ Γ t t' T

/-- Soundness at the identity valuation. -/
theorem sound_id (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqStrong U Γ t t' T) :
    Ob.Sub (OI env U Γ t) (OI env U Γ t') ∧ Ob.Sub (OI env U Γ t') (OI env U Γ t) ∧
    (∀ o, OI env U Γ t o → TypedAt env U Γ VExpr.Subst.id ObSets.empty T o) ∧
    (∀ o, OI env U Γ t' o → TypedAt env U Γ VExpr.Subst.id ObSets.empty T o) :=
  hnr hΓ H .id .id .empty (Ctx.SubstEq.id henv hΓ) TV.empty TV.empty

/-- A chain of sort-typed equalities includes the observations of its left end in those of
its right end (up to subsumption). -/
theorem chain_sub (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ X Y) : Ob.Sub (OI env U Γ X) (OI env U Γ Y) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact (sound_id henv hnr hΓ (h.strong henv hΓ)).1
  | tail _ h ih =>
    let ⟨_, h⟩ := h; exact ih.trans (sound_id henv hnr hΓ (h.strong henv hΓ)).1

/-! ## Sorts and Pi types -/

theorem sort_sort (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  have := Obs.sort_mem ho
  injection this

theorem forallE_chain (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.forallE A B) (.forallE A' B')) :
    env.TypeChain U Γ A A' ∧ env.TypeChain U (A :: Γ) B B' := by
  have ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := h.isType_l.forallE_inv henv
  have ⟨_, ⟨_, hB'⟩⟩ := h.isType_r.forallE_inv henv
  -- the domain, at the identity valuation
  have hdom : env.TypeChain U Γ A A' := by
    obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (.piDom (A := A) (B := B))
    rw [l.piDom_inv] at ho
    have e := Obs.piDom_mem ho
    simp only [VExpr.subst_id] at e
    have : TyCls env U Γ A A' := e ▸ TyCls.self
    exact (TyCls.mem_iff_chain henv hΓ hA).1 this
  refine ⟨hdom, ?_⟩
  -- the codomain, at the fresh variable of `A :: Γ`
  have hΔ : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
  have hw := h.weakN henv (.one (A := A))
  have hdomw : env.TypeChain U (A :: Γ) A.lift A'.lift := hdom.weakN henv .one
  have h0 : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hc : TypedElCls env U (A :: Γ) (TyCls env U (A :: Γ) ((A.liftN 1).subst .id))
      (ElCls env U (A :: Γ) (TyCls env U (A :: Γ) A.lift) (.bvar 0)) := by
    rw [VExpr.subst_id]; exact .of_hasType h0
  have hobs := Obs.piCod (env := env) (U := U) (Δ := A :: Γ) (σ := .id) (S := .empty)
    (B := B.liftN 1 1) hc ElCls.self
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΔ hw _ hobs
  rw [l.piCod_inv] at ho
  obtain ⟨_, y, hy, eC⟩ := Obs.piCod_mem ho
  have e0 : (B.liftN 1 1).subst (VExpr.Subst.id.cons (.bvar 0)) = B :=
    (VExpr.inst_eq _ _).symm.trans (VExpr.instN_bvar0 B 0)
  rw [e0] at eC
  have hy0 : env.IsDefEq U (A :: Γ) (.bvar 0) y A.lift := ElCls.collapse henv hΔ h0 .self hy
  have hy0' : env.IsDefEq U (A :: Γ) y (.bvar 0) A'.lift := hdomw.defeqDF hy0.symm
  have hBw : env.HasType U (A'.lift :: A :: Γ) (B'.liftN 1 1) (.sort _) :=
    hB'.weakN henv (.succ (.zero [A]))
  have hBB := IsDefEq.instDF henv hΔ hBw hy0'
  rw [VExpr.instN_bvar0] at hBB
  have e2 : (B'.liftN 1 1).subst (VExpr.Subst.id.cons y) = (B'.liftN 1 1).inst y :=
    (VExpr.inst_eq _ _).symm
  rw [e2] at eC
  have e1 : TyCls env U (A :: Γ) B = TyCls env U (A :: Γ) B' :=
    eC.trans (TyCls.eq_of_defeq hBB)
  have : TyCls env U (A :: Γ) B B' := e1 ▸ TyCls.self
  exact (TyCls.mem_iff_chain henv hΔ hB).1 this

/-! ## Rigid spines -/

/-- Unwinding a spine observation of the head along the arguments. -/
theorem obs_mkApps_of_wrap {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys : List Key} {args : List VExpr} {f : VExpr} {o : Ob},
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, Obs env U Δ σ S a x) keys args →
    Obs env U Δ σ S f (wrap keys o) → Obs env U Δ σ S (VExpr.mkApps f args) o
  | _, _, _, _, .nil, h => h
  | _ :: _, a :: as, f, o, .cons ⟨h1, h2⟩ H, h => by
    rw [wrap_cons] at h
    show Obs env U Δ σ S (VExpr.mkApps (.app f a) as) o
    exact obs_mkApps_of_wrap H (.app h h1 h2 Covers.refl)

/-- An observation of an application spine comes from a spine observation of its head. -/
theorem wrap_of_obs_mkApps {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} :
    ∀ {args : List VExpr} {f : VExpr} {o : Ob}, Obs env U Δ σ S (VExpr.mkApps f args) o →
    ∃ keys : List Key, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ))
      keys args ∧ Obs env U Δ σ S f (wrap keys o)
  | [], _, _, h => ⟨[], .nil, h⟩
  | a :: as, f, o, h => by
    obtain ⟨keys, hk, h'⟩ := wrap_of_obs_mkApps (args := as) (f := .app f a) h
    obtain ⟨D, c, K, K', h1, h2, _, _⟩ := Obs.app_iff.1 h'
    exact ⟨(D, c, K) :: keys, .cons h2 hk, h1⟩

/-- The spine observations of a constant end in its own rigid observations. -/
theorem const_wrap_inv {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {keys : List Key}
    (hrig : env.Rigid n) (h : Obs env U Δ σ S (.const n ls) (wrap keys o)) (ho : o.NotApp) :
    RigidEnd n (ls.map (·.eval)) keys o := by
  rcases Obs.const_iff.1 h with ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e ho hr.notApp
    exact hr
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)

/-- Observations of a Pi type at one typed key. -/
theorem pi_list {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {K τk τc : List Ob}
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c) (hy : c y)
    (hτk : ∀ τ ∈ τk, Obs env U Δ σ S A τ) (hkk : ∀ k ∈ K, TypedOb env U Δ k τk)
    (hτc : ∀ τ ∈ τc, Obs env U Δ (σ.cons y) (S.cons (listSet K)) B τ) :
    ∃ τs, (∀ τ ∈ τs, Obs env U Δ σ S (.forallE A B) τ) ∧
      ∀ o, TypedOb env U Δ o τc →
        TypedOb env U Δ (.app (TyCls env U Δ (A.subst σ)) c K o) τs := by
  refine ⟨.piDom (TyCls env U Δ (A.subst σ)) :: (τk.map .piDomOb ++ τc.map (.piCodOb c K)),
    ?_, fun o ho => ?_⟩
  · intro τ hτ
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hτ
    rcases hτ with rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact .piDom
    · exact .piDomOb (hτk x hx)
    · exact .piCodOb hc hτk hkk hy (hτc x hx)
  · refine .app (τd := τk) (τc := τc) (List.mem_cons_self ..) (fun x hx => ?_) hkk hc
      (fun x hx => ⟨K, ?_, Covers.refl⟩) ho
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hx))

/-- The keys of a left spine: each argument class is the class of the argument at the
domain class, which is the type class of a type of the argument, and the key observations
are observations of the argument. -/
def KeyedArgs (env : VEnv) (U : Nat) (Γ : List VExpr) (keys : List Key) (args : List VExpr) :
    Prop :=
  List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 a ∧
    (∀ x ∈ k.2.2, OI env U Γ a x) ∧ ∃ X, env.HasType U Γ a X ∧ k.1 = TyCls env U Γ X) keys args

/-- **Typed spine observations**: for a strongly typed spine `mkApps (const c ls) args : T`
and observations `τs` of `T`, there are keys for the arguments such that every observation
typed at `τs`, wrapped in the keys, is typed at observations of the constant's type (so,
for a rigid end, it passes the filter of the constant clause). -/
theorem spine_typed (henv : env.Ordered) (hnr : SoundEnv env)
    (H : env.HasTypeStrong U Γ e T b) : OnCtx Γ (env.IsType U) →
    ∀ args, e = VExpr.mkApps (.const c ls) args → ∀ τs, (∀ τ ∈ τs, OI env U Γ T τ) →
    ∃ ci keys, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ KeyedArgs env U Γ keys args ∧
      ∀ o, TypedOb env U Γ o τs →
        ∃ τs₀, (∀ τ ∈ τs₀, OI env U Γ (ci.type.instL ls) τ) ∧
          TypedOb env U Γ (wrap keys o) τs₀ := by
  induction H with
  | bvar | sort' | elim | proj | lam | forallE =>
    intro _ args he; rcases mkApps_const_inv he with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | const hci hls =>
    intro _ args he τs hτs
    rcases mkApps_const_inv he with ⟨rfl, h⟩ | ⟨_, _, _, h⟩
    · cases h; exact ⟨_, [], hci, hls, .nil, fun o ho => ⟨τs, hτs, ho⟩⟩
    · cases h
  | @app Γ A u B v f a _ _ _ _ _ _ ha _ _ _ _ ihf _ _ =>
    intro hΓ args he τs hτs
    rcases mkApps_const_inv he with ⟨_, h⟩ | ⟨as, a₀, rfl, h⟩
    · cases h
    injection h with hf ha0
    subst ha0
    have haw : env.HasType U Γ a A := ha.refl.defeq
    have Ha := sound_id henv hnr hΓ ha.refl
    have hτ' : ∀ τ ∈ τs, Obs env U Γ (VExpr.Subst.id.cons (a.subst .id))
        (ObSets.empty.cons (OI env U Γ a)) B τ := fun τ hτ => Obs.inst_iff.1 (hτs τ hτ)
    obtain ⟨K, hK, hKτ⟩ := Obs.collect (Q := OI env U Γ a)
      (P := fun K τ => Obs env U Γ (VExpr.Subst.id.cons (a.subst .id))
        (ObSets.empty.cons (listSet K)) B τ)
      (fun _ _ _ hKK h => h.mono fun i o h => by
        cases i with
        | zero => exact hKK _ h
        | succ i => exact h)
      fun τ hτ => (hτ' τ hτ).compact0
    obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge fun k hk => Ha.2.2.1 k (hK k hk)
    have hc : TypedElCls env U Γ (TyCls env U Γ (A.subst .id))
        (ElCls env U Γ (TyCls env U Γ (A.subst .id)) (a.subst .id)) := by
      simp only [VExpr.subst_id]; exact .of_hasType haw
    obtain ⟨τPi, hτPi, hwrap⟩ := pi_list hc ElCls.self hτk hkk hKτ
    simp only [VExpr.subst_id] at hwrap
    obtain ⟨ci, keys₀, hci, hls, hkeys, hQ⟩ := ihf hΓ as hf τPi hτPi
    refine ⟨ci, keys₀ ++ [(TyCls env U Γ A, ElCls env U Γ (TyCls env U Γ A) a, K)], hci, hls,
      forall₂_append_single hkeys ⟨rfl, hK, A, haw, rfl⟩, fun o ho => ?_⟩
    rw [wrap_append]
    exact hQ _ (hwrap o ho)
  | defeq _ hAB _ _ _ _ _ ih =>
    intro hΓ args heq τs hτs
    have hS := (sound_id henv hnr hΓ hAB).2.1
    obtain ⟨τs', h1, h2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => hS τ (hτs τ hτ)
    obtain ⟨ci, keys, hci, hls, hk, hQ⟩ := ih hΓ args heq τs' h1
    exact ⟨ci, keys, hci, hls, hk, fun o ho => hQ o (ho.strengthen h2)⟩
  | base _ ih => exact ih

/-- The analysis of a chain between two rigid spines: same head, same levels, and each
right argument in the class of the corresponding left argument (at the left spine's keys,
whose spine observation is typed at the observations of the head's type). -/
theorem rigid_analysis (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (hrig' : env.Rigid c')
    (h : env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args')) :
    ∃ ci keys, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ KeyedArgs env U Γ keys args ∧
      (∃ τs₀, (∀ τ ∈ τs₀, OI env U Γ (ci.type.instL ls) τ) ∧
        TypedOb env U Γ (wrap keys (.rigid c (ls.map (·.eval)) keys.length)) τs₀) ∧
      c = c' ∧ ls.map (·.eval) = ls'.map (·.eval) ∧
      List.Forall₂ (fun (k : Key) a' => k.2.1 a') keys args' := by
  obtain ⟨u, hu⟩ := h.isType_l
  have Hs := (hu.strong henv hΓ).hasType'.1
  obtain ⟨ci, keys, hci, hls, hkeys, hQ⟩ := spine_typed henv hnr Hs hΓ args rfl
    [.sort u.eval] fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort
  have hk' : List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 (a.subst .id) ∧
      ∀ x ∈ k.2.2, OI env U Γ a x) keys args :=
    forall₂_imp (fun k a ⟨h1, h2, _⟩ => ⟨by rw [VExpr.subst_id]; exact h1, h2⟩) hkeys
  have hsort : ∀ r, RigidEnd c (ls.map (·.eval)) keys r → TypedOb env U Γ r [.sort u.eval] := by
    intro r hr
    rcases hr with rfl | ⟨_, _, rfl⟩
    · exact .rigid (List.mem_singleton_self _)
    · exact .rigidArg (List.mem_singleton_self _)
  have hL : ∀ r, RigidEnd c (ls.map (·.eval)) keys r →
      OI env U Γ (.mkApps (.const c ls) args) r := by
    intro r hr
    obtain ⟨τs₀, h1, h2⟩ := hQ r (hsort r hr)
    exact obs_mkApps_of_wrap hk' (.const hrig hci h1 h2 hr)
  have hR : ∀ r, RigidEnd c (ls.map (·.eval)) keys r → ∃ keys' : List Key,
      List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 (a.subst .id)) keys' args' ∧
      RigidEnd c' (ls'.map (·.eval)) keys' r := by
    intro r hr
    obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (hL r hr)
    have : o = r := by
      rcases hr with rfl | ⟨_, _, rfl⟩
      · exact l.rigid_inv
      · exact l.rigidArg_inv
    subst this
    obtain ⟨keys', hk, hw⟩ := wrap_of_obs_mkApps ho
    exact ⟨keys', hk, const_wrap_inv hrig' hw hr.notApp⟩
  have hlen := List.Forall₂.length_eq hkeys
  obtain ⟨keys', hk1, hr1⟩ := hR _ (.inl rfl)
  rcases hr1 with e | ⟨_, _, e⟩
  · injection e with ec eℓ en
    refine ⟨ci, keys, hci, hls, hkeys, hQ _ (hsort _ (.inl rfl)), ec, eℓ, ?_⟩
    refine forall₂_of_getElem (by rw [en, List.Forall₂.length_eq hk1]) fun i h₁ h₂ => ?_
    obtain ⟨keys'', hk2, hr2⟩ := hR _ (.inr ⟨i, h₁, rfl⟩)
    rcases hr2 with e | ⟨j, hj, e⟩
    · cases e
    · injection e with eij ecl
      subst eij
      obtain ⟨_, hcl⟩ := forall₂_getElem hk2 i hj
      rw [ecl, hcl, VExpr.subst_id]; exact ElCls.self
  · cases e

/-- Along a syntactic telescope, the domain classes of a typed spine observation are the
type classes of the instantiated domains, so arguments in the left argument classes are
related at those domains. -/
theorem tele_spine (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (keys : List Key) (ds : List VExpr) (w : VLevel) (Γ' : List VExpr) (σ : VExpr.Subst)
      (args args' : List VExpr) (τs : List Ob) (o : Ob),
    Ctx.SubstEq env U Γ σ σ Γ' → env.IsType U Γ' (VExpr.wrapForalls ds (.sort w)) →
    (∀ τ ∈ τs, ∃ σ'' S'', Ctx.SubstEq env U Γ σ'' σ Γ' ∧
      Obs env U Γ σ'' S'' (VExpr.wrapForalls ds (.sort w)) τ) →
    TypedOb env U Γ (wrap keys o) τs →
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 a ∧
      ∃ X, k.1 X ∧ env.HasType U Γ a X) keys args →
    List.Forall₂ (fun (k : Key) a' => k.2.1 a') keys args' →
    SpineArgsEq env U Γ ((VExpr.wrapForalls ds (.sort w)).subst σ) args args'
  | [], _, _, _, _, _, _, _, _, _, _, _, _, .nil, .nil => .nil
  | ⟨D, c, K⟩ :: keys, ds, w, Γ', σ, _, _, τs, o, W, hT, hτs, hty,
      .cons ⟨hc, X, hX, ha⟩ H1, .cons ha' H2 => by
    cases hty with
    | app hD _ _ _ hcod hty' =>
      obtain ⟨σ'', S'', W'', hobs⟩ := hτs _ hD
      cases ds with
      | nil => cases Obs.sort_mem hobs
      | cons d ds =>
        have hD' := Obs.piDom_mem hobs
        obtain ⟨⟨_, hd⟩, hR⟩ := IsType.forallE_inv henv hT
        have hdd := hd.substDF henv W''.wf hΓ W''
        have eD : D = TyCls env U Γ (d.subst σ) := hD'.trans (TyCls.eq_of_defeq hdd)
        subst eD; dsimp only at hc; subst hc
        have haa := ElCls.collapse henv hΓ ha hX ha'
        refine .cons haa ?_
        rw [VExpr.inst_lift_cons]
        refine tele_spine henv hΓ keys ds w (d :: Γ') (σ.cons _) _ _ _ o
          (.cons W hd haa.hasType.1) hR ?_ hty' H1 H2
        intro x hx
        obtain ⟨K₀, hm, _⟩ := hcod x hx
        obtain ⟨σ₃, S₃, W₃, hobs₃⟩ := hτs _ hm
        obtain ⟨_, _, y, hy, hxR⟩ := Obs.piCodOb_mem hobs₃
        have hdd₃ := hd.substDF henv W₃.wf hΓ W₃
        have hay := ElCls.collapse henv hΓ ha hX hy
        exact ⟨σ₃.cons y, S₃.cons (listSet K₀), .cons W₃ hd (.defeqDF hdd₃.symm hay.symm), hxR⟩

end Model

/-- **Chain-level head injectivity from soundness**: in a well-formed environment for which
the observation model is sound, the hypothesis of the syntactic layer holds. -/
theorem WF.headInjectivityCore_of_sound {env : VEnv} (henv : env.WF) (hnr : Model.SoundEnv env) :
    env.HeadInjectivityCore where
  sort_sort hΓ h := Model.sort_sort henv.ordered hnr hΓ h
  forallE_chain hΓ h := Model.forallE_chain henv.ordered hnr hΓ h
  rigid_rigid hΓ hrig hrig' h := by
    obtain ⟨_, keys, _, _, hkeys, _, ec, eℓ, hk'⟩ :=
      Model.rigid_analysis henv.ordered hnr hΓ hrig hrig' h
    refine ⟨ec, Model.forall₂_equiv_of_map_eval eℓ,
      Model.forall₂_zip (fun k a a' ⟨h1, _, X, hX, h2⟩ h3 => ?_) hkeys hk'⟩
    rw [h1, h2] at h3
    exact ⟨X, Model.ElCls.collapse henv.ordered hΓ hX .self h3⟩
  former_args {U Γ c ci doms w ls ls' args args'} hΓ hrig hci hty h := by
    obtain ⟨ci', keys, hci', hls, hkeys, ⟨τs₀, hτs₀, hty₀⟩, _, _, hk'⟩ :=
      Model.rigid_analysis henv.ordered hnr hΓ hrig hrig h
    cases hci.symm.trans hci'
    have eT : ci.type.instL ls =
        VExpr.wrapForalls (doms.map (·.instL ls)) (.sort (w.inst ls)) := by
      rw [hty, Model.instL_wrapForalls']; rfl
    have hT : env.IsType U [] (VExpr.wrapForalls (doms.map (·.instL ls)) (.sort (w.inst ls))) :=
      eT ▸ IsType.instL hls (henv.ordered.constWF hci)
    have := Model.tele_spine henv.ordered hΓ keys (doms.map (·.instL ls)) (w.inst ls) []
      .id args args' τs₀ _ .nil hT (fun τ hτ => ⟨_, _, .nil, eT ▸ hτs₀ τ hτ⟩) hty₀
      (Model.forall₂_imp (fun k a ⟨h1, _, X, hX, h2⟩ => ⟨h1, X, h2 ▸ .self, hX⟩) hkeys) hk'
    rwa [VExpr.subst_id, ← eT] at this

/-- **Stage A1** (`docs/inductives/PHASE1B_NOTES.md`, section 10.2): chain-level head
injectivity for well-formed environments whose rules are all definitions' delta rules and
which have no projections or eliminators. -/
theorem WF.headInjectivityCore_of_defsOnly {env : VEnv} (henv : env.WF) (hdo : env.DefsOnly) :
    env.HeadInjectivityCore :=
  henv.headInjectivityCore_of_sound fun hΔ H =>
    Model.sound henv.ordered hΔ hdo henv.defRules H

/-- **Chain-level head injectivity for rule-free environments** (milestone M2 of
`docs/inductives/PHASE1B_NOTES.md`, section 9.3). -/
theorem WF.headInjectivityCore_of_noRules {env : VEnv} (henv : env.WF) (hnr : env.NoRules) :
    env.HeadInjectivityCore :=
  henv.headInjectivityCore_of_defsOnly hnr.defsOnly

end VEnv
end Lean4Lean
