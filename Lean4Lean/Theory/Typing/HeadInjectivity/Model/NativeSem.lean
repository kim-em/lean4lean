import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound

/-! # Semantic facts for native recursor rules (stage B)

Generic observation-level lemmas used to discharge the mode hypotheses of `sound_pat` at
native recursor equations (`docs/inductives/PHASE1B_NOTES.md`, section 10.3, D11):

* `typed_wrap_rigid`: the type observations at which a rigid spine observation is typed
  contain a chain ending in its sort;
* `family_sort`: if a closed type `T` is soundly equal to a telescope ending in `Sort l`,
  every sort at the end of a chain observation of `T` is `l`;
* `sound_pat_empty`: soundness of a pattern rule whose right-hand side has no observations
  (small elimination). -/

namespace Lean4Lean

theorem Lookup.append_left' : ∀ {L : List VExpr} {i : Nat} {A : VExpr},
    Lookup L i A → Lookup (L ++ Γ) i A
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (Lookup.append_left' h)

namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem typed_wrap_rigid : ∀ {keys : List Key} {τs : List Ob},
    TypedOb env U Δ cv (wrap keys (.rigid n ℓs m s)) τs →
    ∃ ks : List Key, ks.length = keys.length ∧ piCodChain ks (.sort s) ∈ τs
  | [], τs, h => by
    cases h with
    | rigid h => exact ⟨[], rfl, h⟩
  | k :: keys, τs, h => by
    obtain ⟨D, c, K⟩ := k
    simp only [wrap_cons] at h
    cases h with
    | app _ _ _ _ _ _ hcod hty =>
      obtain ⟨ks, hl, hm⟩ := typed_wrap_rigid hty
      obtain ⟨K₀, hK₀, -⟩ := hcod _ hm
      exact ⟨(D, c, K₀) :: ks, by simp [hl], hK₀⟩

theorem Ob.Le.piCodChain_sort_inv : ∀ {ks : List Key} {o : Ob},
    o ≼ piCodChain ks (.sort z) → ∃ ks' : List Key, ks'.length = ks.length ∧
      o = piCodChain ks' (.sort z)
  | [], o, h => ⟨[], rfl, h.sort_inv⟩
  | k :: ks, o, h => by
    simp only [piCodChain_cons] at h
    obtain ⟨K₀, y, rfl, -, hy⟩ := h.piCodOb_inv
    obtain ⟨ks', hl, rfl⟩ := Ob.Le.piCodChain_sort_inv hy
    exact ⟨(k.1, k.2.1, K₀) :: ks', by simp [hl], rfl⟩

theorem obs_wrapForalls_sort : ∀ {ds : List VExpr} {ks : List Key} {σ : VExpr.Subst}
    {S : ObSets}, Obs' σ S (.wrapForalls ds (.sort l)) (piCodChain ks (.sort z)) → z = l.eval
  | [], [], _, _, h => by
    have := Obs.sort_mem h; simp at this; exact this
  | [], _ :: _, _, _, h => by
    have := Obs.sort_mem h; simp at this
  | _ :: _, [], _, _, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, piCodChain_nil] at h
    cases h
  | _ :: ds, _ :: ks, _, _, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, piCodChain_cons] at h
    obtain ⟨-, -, _, -, h⟩ := Obs.piCodOb_mem h
    exact obs_wrapForalls_sort (ds := ds) (ks := ks) h

/-- A closed type soundly equal to a telescope ending in `Sort l` has only `l` at the end of
its chain observations. -/
theorem family_sort {T X : VExpr} {ds : List VExpr}
    (H : SoundAt env U Δ [] T (.wrapForalls ds (.sort l)) X)
    (h : Obs' .id .empty T (piCodChain ks (.sort z))) : z = l.eval := by
  obtain ⟨o', h1, h2⟩ := (H .id .id .empty .nil TV.empty TV.empty).1 _ h
  obtain ⟨ks', -, rfl⟩ := h2.piCodChain_sort_inv
  exact obs_wrapForalls_sort h1

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Small elimination**: nothing is typed at the observations of a closed Pi telescope whose
codomain applies a bound variable whose binder type is a telescope ending in a sort that is
identically zero (the motive of an eliminator into `Prop`). -/
theorem motive_tele_empty {doms args mds : List VExpr} {T X : VExpr} {m : Nat} {w : VLevel}
    {lk : List Key} {p : Ob} {τs : List Ob}
    (hT : HTS env U Δ [] (.wrapForalls doms T) X) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0) (hlk : lk.length = doms.length)
    (ho : TypedOb env U Δ cv (wrap lk p) τs)
    (hτs : ∀ τ ∈ τs, Obs' .id .empty (.wrapForalls doms T) τ) : False := by
  obtain ⟨σ', S', hk, τc, _, hτc, hp⟩ := tele_unwind henv hΔ hT.piSD .nil TV.empty hlk ho hτs
  obtain ⟨-, tv'⟩ := hk.typed' henv hΔ hT.piSD.doms .nil TV.empty
  rw [List.append_nil] at tv'
  refine hp.not_prop fun τ hτ => ?_
  have h := hτc τ hτ
  rw [eT] at h
  obtain ⟨keys, hkeys, hb⟩ := wrap_of_obs_mkApps h
  obtain ⟨τs', h1, h2⟩ := tv'.2 m _ hm _ (Obs.bvar_iff.1 hb)
  obtain ⟨τc', _, h3, h4⟩ := chain_terminal_sort (env := env) (U := U) (Δ := Δ) (w := w)
    (by rw [hlen]; exact List.Forall₂.length_eq hkeys) h2 (fun τ hτ => ⟨_, _, h1 τ hτ⟩)
  refine ⟨_, h4.strengthen fun k hk => ⟨_, List.mem_singleton_self _, ?_⟩⟩
  rw [h3 k hk, hw]; exact .refl

/-- `motive_tele_empty` in a context with a typed valuation. -/
theorem motive_tele_empty_ctx {doms args mds : List VExpr} {T X : VExpr} {m : Nat} {w : VLevel}
    {lk : List Key} {p : Ob} {τs : List Ob} {σ : VExpr.Subst} {S : ObSets}
    (hT : HTS env U Δ Γ (.wrapForalls doms T) X) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0) (hlk : lk.length = doms.length)
    (ho : TypedOb env U Δ cv (wrap lk p) τs)
    (hτs : ∀ τ ∈ τs, Obs' σ S (.wrapForalls doms T) τ) : False := by
  obtain ⟨σ', S', hk, τc, _, hτc, hp⟩ := tele_unwind henv hΔ hT.piSD W tv hlk ho hτs
  obtain ⟨-, tv'⟩ := hk.typed' henv hΔ hT.piSD.doms W tv
  refine hp.not_prop fun τ hτ => ?_
  have h := hτc τ hτ
  rw [eT] at h
  obtain ⟨keys, hkeys, hb⟩ := wrap_of_obs_mkApps h
  obtain ⟨τs', h1, h2⟩ := tv'.2 m _ (Lookup.append_left' hm) _ (Obs.bvar_iff.1 hb)
  obtain ⟨τc', _, h3, h4⟩ := chain_terminal_sort (env := env) (U := U) (Δ := Δ) (w := w)
    (by rw [hlen]; exact List.Forall₂.length_eq hkeys) h2 (fun τ hτ => ⟨_, _, h1 τ hτ⟩)
  refine ⟨_, h4.strengthen fun k hk => ⟨_, List.mem_singleton_self _, ?_⟩⟩
  rw [h3 k hk, hw]; exact .refl

/-- The right-hand side of a rule whose type is a telescope over a motive into a
proposition, typed in the rule's context, has no observations at typed valuations. -/
theorem rhs_empty_motive_ctx {df : VDefEq} {ls : List VLevel} {doms args mds : List VExpr}
    {T body : VExpr} {m : Nat} {w : VLevel} {u : VLevel}
    (et : df.type.instL ls = .wrapForalls doms T) (er : df.rhs.instL ls = .wrapLams doms body)
    (hT : HTS env U Δ Γ (df.type.instL ls) (.sort u)) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0)
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (o : Ob) :
    ¬ Obs' σ S (df.rhs.instL ls) o := by
  intro ho
  obtain ⟨τs, hτs, hty⟩ := (ihR σ σ S W tv tv).2.2.1 o ho
  rw [er] at ho
  obtain ⟨lk, _, _, p, hk, rfl, -⟩ := Obs.wrapLams_iff.1 ho
  rw [et] at hT
  exact motive_tele_empty_ctx henv hΔ hT W tv eT hm hlen hw hk.length hty
    (fun τ hτ => by have := hτs τ hτ; rw [et] at this; exact this)

/-- The right-hand side of a rule whose type is a closed telescope over a motive into a
proposition has no observations at typed valuations. -/
theorem rhs_empty_motive {df : VDefEq} {ls : List VLevel} {doms args mds : List VExpr}
    {T body : VExpr} {m : Nat} {w : VLevel} {u : VLevel}
    (et : df.type.instL ls = .wrapForalls doms T) (er : df.rhs.instL ls = .wrapLams doms body)
    (hcl : (df.type.instL ls).ClosedN)
    (hT : HTS env U Δ [] (df.type.instL ls) (.sort u)) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0)
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (o : Ob) :
    ¬ Obs' σ S (df.rhs.instL ls) o := by
  intro ho
  obtain ⟨τs, hτs, hty⟩ := (ihR σ σ S W tv tv).2.2.1 o ho
  rw [er] at ho
  obtain ⟨lk, _, _, p, hk, rfl, -⟩ := Obs.wrapLams_iff.1 ho
  rw [et] at hT hcl
  exact motive_tele_empty henv hΔ hT eT hm hlen hw hk.length hty
    (fun τ hτ => by have := hτs τ hτ; rw [et] at this; exact (Obs.closed_iff_id hcl).1 this)

/-- Soundness of a pattern rule whose right-hand side has no observations at typed valuations
(small elimination). -/
theorem sound_pat_empty {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c) (hdr : env.DefRules)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const n lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hE : ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S → ∀ o,
      ¬ Obs' σ S (df.rhs.instL ls) o) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  refine ⟨fun o h => ?_, fun o h => absurd h (hE σ' S W' tv' o),
    (ihL σ σ S W.left tv tv).2.2.1, (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  obtain ⟨o', h1, -⟩ := pat_lhs_sub henv hΔ hdf hl hr hlsP hlcl hrcl hcrig hctor hpctor hdr huniq
    ihR.2 ihR.1 W.left tv o h
  exact absurd h1 (hE σ S W.left tv o')

end

end Model
end VEnv
end Lean4Lean
