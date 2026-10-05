import Lean4Lean.Theory.Typing.HeadReduction

/-! Recovering native family heads across context strengthening. -/

namespace Lean4Lean.VEnv
open VExpr
/-- Only beta contraction at the application head is needed to expose
eta-expanded family heads. Keeping this private relation untyped permits
instantiating the auxiliary eta binders before embedding the result in WHRed. -/
private inductive HeadBeta : VExpr → VExpr → Prop where
  | beta : HeadBeta (.app (.lam A body) arg) (body.inst arg)
  | app : HeadBeta fn fn' → HeadBeta (.app fn arg) (.app fn' arg)

private abbrev HeadBetaS := ReflTransGen HeadBeta

private theorem HeadBeta.inst (H : HeadBeta e e') : HeadBeta (e.inst arg k) (e'.inst arg k) := by
  induction H with
  | beta => rw [(by apply inst_inst_hi : (VExpr.inst ..).inst _ _ = _)]; exact .beta
  | app _ ih => exact .app ih

private theorem HeadBetaS.inst (H : HeadBetaS e e') :
    HeadBetaS (e.inst arg k) (e'.inst arg k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih h.inst

private theorem HeadBetaS.app (H : HeadBetaS fn fn') : HeadBetaS (.app fn arg) (.app fn' arg) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.app h)

private theorem HeadBetaS.mkApps (H : HeadBetaS fn fn') (args : List VExpr) :
    HeadBetaS (VExpr.mkApps fn args) (VExpr.mkApps fn' args) := by
  induction args generalizing fn fn' with
  | nil => exact H
  | cons a args ih => exact ih H.app

variable [Params]
open Params

private theorem HeadBeta.whRed (H : HeadBeta e e') : WHRed Γ e e' := by
  induction H with
  | beta => exact .beta
  | app _ ih => exact .app ih

private theorem HeadBetaS.whRedS (H : HeadBetaS e e') : WHRedS Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih h.whRed

private theorem forall_sort_nonzero (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsType univs Γ (wrapForalls domains (.sort level))) :
    ∃ u, env.HasType univs Γ (wrapForalls domains (.sort level)) (.sort u) ∧ u.IsNeverZero := by
  induction domains generalizing Γ with
  | nil =>
    obtain ⟨_, h⟩ := H
    have hl := h.sort_inv henv.ordered
    exact ⟨.succ level, .sort hl, fun ls => Nat.succ_ne_zero _⟩
  | cons domain domains ih =>
    obtain ⟨⟨u, hd⟩, hb⟩ := H.forallE_inv henv.ordered
    have hΓ' : OnCtx (domain :: Γ) (env.IsType univs) := ⟨hΓ, _, hd⟩
    obtain ⟨v, hv, hn⟩ := ih hΓ' hb
    refine ⟨.imax u v, .forallE hd hv, ?_⟩
    intro ls
    simp only [VLevel.eval]
    simp [Lean.Nat.imax, hn ls]

private theorem forall_sort_not_prop (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.HasType univs Γ (wrapForalls domains (.sort level)) (.sort .zero)) : False := by
  obtain ⟨u, hu, hn⟩ := forall_sort_nonzero hΓ ⟨_, H⟩
  have heq := (hu.uniqU henv hΓ H).sort_inv henv hΓ
  exact hn [] (congrFun heq [])

private theorem family_prefix_type (hΓ : OnCtx Γ (env.IsType univs))
    {domains args : List VExpr} {fn : VExpr}
    (hf : env.HasType univs Γ fn (wrapForalls domains (.sort level)))
    (H : VExpr.WF env univs Γ (mkApps fn args))
    (hlen : args.length ≤ domains.length) :
    ∃ remaining, remaining.length = domains.length - args.length ∧
      env.HasType univs Γ (mkApps fn args) (wrapForalls remaining (.sort level)) := by
  induction args generalizing fn domains with
  | nil => exact ⟨domains, rfl, hf⟩
  | cons a args ih =>
    cases domains with
    | nil => simp at hlen
    | cons domain domains =>
      have hfirst : VExpr.WF env univs Γ (.app fn a) :=
        (show VExpr.WF env univs Γ (mkApps (.app fn a) args) from H).of_mkApps henv.ordered hΓ
      obtain ⟨A, B, hfn, ha⟩ := hfirst.app_inv henv.ordered hΓ
      obtain ⟨⟨_, hA⟩, _⟩ := (hfn.uniqU henv hΓ hf).forallE_inv henv hΓ
      have ha' := ha.defeqU_r henv hΓ ⟨_, hA⟩
      have hnext := hf.app ha'
      change env.HasType univs Γ (.app fn a) ((wrapForalls domains (.sort level)).inst a) at hnext
      rw [wrapForalls_inst] at hnext
      change env.HasType univs Γ (.app fn a)
        (wrapForalls (instDomains domains a 0) (.sort level)) at hnext
      obtain ⟨remaining, hr, ht⟩ := ih hnext H (by simpa using Nat.le_of_succ_le_succ hlen)
      refine ⟨remaining, ?_, ht⟩
      simpa using hr

omit [Params] in
private theorem liftN_forall_sort_shape (domains : List VExpr) (level : VLevel) (n k : Nat) :
    ∃ domains', domains'.length = domains.length ∧
      (wrapForalls domains (.sort level)).liftN n k = wrapForalls domains' (.sort level) := by
  induction domains generalizing k with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons domain domains ih =>
    obtain ⟨domains', hlen, hd⟩ := ih (k + 1)
    exact ⟨domain.liftN n k :: domains', by simp [hlen],
      congrArg (VExpr.forallE (domain.liftN n k)) hd⟩

omit [Params] in
private theorem const_spine_head (name : Name) (levels : List VLevel) (args : List VExpr) :
    (mkApps (.const name levels) args).getAppFnArgs = (.const name levels, args) :=
  InductiveSignature.spine_mkApps_exact _ _ rfl

private theorem normalEq_family_beta (H : NormalEq Γ e e') :
    ∀ {name : Name} {levels : List VLevel} {args domains : List VExpr} {level : VLevel},
      OnCtx Γ (env.IsType univs) →
      e' = mkApps (.const name levels) args →
      env.HasType univs Γ (.const name levels) (wrapForalls domains (.sort level)) →
      args.length ≤ domains.length →
      ∀ extra : List VExpr, extra.length = domains.length - args.length →
      ∃ levels' actualArgs, List.Forall₂ (· ≈ ·) levels' levels ∧
        actualArgs.length = domains.length ∧
        HeadBetaS (mkApps e extra) (mkApps (.const name levels') actualArgs) := by
  induction H with
  | refl ht =>
    intro name levels args domains level hΓ he hconst hlen extra hextra
    rw [he, ← mkApps_append]
    exact ⟨levels, args ++ extra, Lean4Lean.List.Forall₂.rfl fun _ _ => rfl, by simp; omega, .rfl⟩
  | constDF hlookup hl hl' hlen' hlevels =>
    intro name levels args domains level hΓ he hconst hlen extra hextra
    have hh := congrArg VExpr.getAppFnArgs he
    rw [const_spine_head] at hh
    obtain ⟨heq, hargs⟩ := Prod.mk.inj hh
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj heq
    cases hargs
    exact ⟨_, extra, hlevels, by simpa using hextra, .rfl⟩
  | appDF hf₁ hf₂ ha₁ ha₂ hfn harg ihfn iharg =>
    intro name levels args domains level hΓ he hconst hlen extra hextra
    obtain hnil | ⟨preArgs, last, hargs⟩ := List.eq_nil_or_concat args
    · subst args; cases he
    · simp only [List.concat_eq_append] at hargs
      subst args
      rw [mkApps_append] at he
      obtain ⟨hprefix, hlast⟩ := VExpr.app.inj he
      obtain ⟨levels', actualArgs, hlevels, hactual, hred⟩ := ihfn hΓ hprefix hconst (by simp at hlen; omega)
        (_ :: extra) (by simp at hlen hextra ⊢; omega)
      exact ⟨levels', actualArgs, hlevels, hactual, hred⟩
  | @etaL Γ fn A B body hfun hbody ih =>
    intro name levels args domains level hΓ he hconst hlen extra hextra
    obtain ⟨⟨_, hA⟩, _⟩ := hfun.isType henv.ordered hΓ |>.forallE_inv henv.ordered
    have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have hright : VExpr.WF env univs Γ (mkApps (.const name levels) args) := by
      rw [← he]; exact ⟨_, hfun⟩
    obtain ⟨remaining, hremaining, hp⟩ := family_prefix_type hΓ hconst hright hlen
    have hlt : args.length < domains.length := by
      by_cases hn : args.length < domains.length
      · exact hn
      · have hnil : remaining = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [hnil, ← he] at hp
        exact False.elim ((hp.uniqU henv hΓ hfun).sort_forallE_inv henv hΓ)
    cases extra with
    | nil => simp at hextra; omega
    | cons a extra =>
      obtain ⟨domains', hdomains, htype⟩ := liftN_forall_sort_shape domains level 1 0
      have hconst' := hconst.weakN henv.ordered (.zero [A])
      simp only [List.length_singleton] at hconst'
      rw [htype] at hconst'
      have hbodyeq : (.app (VExpr.lift fn ) (.bvar 0)) =
          mkApps (.const name levels) (args.map VExpr.lift ++ [.bvar 0]) := by
        rw [he, lift, liftN_mkApps, mkApps_append]
        rfl
      obtain ⟨levels', actualArgs, hlevels, hactual, hred⟩ := ih hΓ' hbodyeq hconst'
        (by simp [hdomains]; omega) (extra.map VExpr.lift)
        (by simp at hextra ⊢; omega)
      have hred' := hred.inst (arg := a) (k := 0)
      simp only [inst_mkApps, VExpr.inst, List.map_map, Function.comp_def, inst_lift] at hred'
      have hmap : extra.map (fun x : VExpr => x) = extra := by induction extra <;> simp [*]
      rw [hmap] at hred'
      exact ⟨levels', _, hlevels, by simp; omega, (HeadBetaS.mkApps (.tail .rfl .beta) extra).trans hred'⟩
  | @proofIrrel Γ p proof proof' hp hh hh' =>
    intro name levels args domains level hΓ he hconst hlen extra hextra
    have hright : VExpr.WF env univs Γ (mkApps (.const name levels) args) := by
      rw [← he]; exact ⟨_, hh'⟩
    obtain ⟨remaining, _, ht⟩ := family_prefix_type hΓ hconst hright hlen
    rw [← he] at ht
    have hp' := ((hh'.uniqU henv hΓ ht).of_l henv hΓ hp).hasType.2
    exact (forall_sort_not_prop hΓ hp').elim
  | sortDF | elimDF | projDF | lamDF | forallEDF | etaR =>
    intros name levels args domains level hΓ he
    obtain hnil | ⟨preArgs, last, hargs⟩ := List.eq_nil_or_concat args
    · subst args; cases he
    · simp only [List.concat_eq_append] at hargs
      subst args
      rw [mkApps_append] at he
      cases he

private theorem parRedS_rigid_const_spine (hrigid : env.NativeHeadRigid name)
    (H : ParRedS Γ (mkApps (.const name levels) args) out) :
    ∃ args', out = mkApps (.const name levels) args' ∧ args'.length = args.length := by
  induction H with
  | rfl => exact ⟨_, rfl, rfl⟩
  | tail _ h ih =>
    obtain ⟨args', rfl, hlen⟩ := ih
    obtain ⟨args'', he, hargs⟩ := h.rigid_const_spine hrigid
    exact ⟨args'', he, (Lean4Lean.List.Forall₂.length_eq hargs).symm.trans hlen⟩

/-- A type definitionally equal to a saturated rigid family application has
a weak head reduction to the same family. Eta expansions contribute only
beta head reductions; proof irrelevance cannot identify a type-producing
family prefix with a proof. -/
theorem IsDefEq.reduce_familyApp (hΓ : OnCtx Γ (env.IsType univs))
    (hrigid : env.NativeHeadRigid name)
    (hconst : env.HasType univs Γ (.const name levels) (wrapForalls domains (.sort level)))
    (hlen : args.length = domains.length)
    (H : env.IsDefEq univs Γ e (mkApps (.const name levels) args) type) :
    ∃ levels' args', WHRedS Γ e (mkApps (.const name levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨_, _, e', out, hleft, hright, hnormal⟩ := H.church_rosser hΓ
  obtain ⟨rightArgs, rfl, hrightArgs⟩ := parRedS_rigid_const_spine hrigid hright
  obtain ⟨levels', actualArgs, hlevels, hactual, hbeta⟩ :=
    normalEq_family_beta hnormal hΓ rfl hconst (by omega) [] (by simp; omega)
  have hfull := hleft.trans hbeta.whRedS.parRedS
  obtain ⟨sourceArgs, hsource, hargs⟩ := (ParRedS.standard hΓ H.hasType.1 hfull).expose_spine
    (.inl ⟨name, levels', rfl⟩)
  exact ⟨levels', sourceArgs, hsource, hlevels,
    (Lean4Lean.List.Forall₂.length_eq hargs).trans (hactual.trans hlen.symm)⟩

omit [Params] in
private theorem reverse_induction {P : List α → Prop} (hnil : P [])
    (happend : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have h : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => exact hnil
    | cons y ys ih => simpa only [List.reverse_cons] using happend ys.reverse y ih
  simpa only [List.reverse_reverse] using h xs.reverse

omit [Params] in
private theorem lift'_const_spine_inv {expression : VExpr}
    (H : expression.lift' ρ = mkApps (.const name levels) args) :
    ∃ args', expression = mkApps (.const name levels) args' ∧
      args = args'.map (·.lift' ρ) := by
  induction args using reverse_induction generalizing expression with
  | hnil =>
    cases expression <;> cases H
    exact ⟨[], rfl, rfl⟩
  | happend args arg ih =>
    rw [mkApps_append] at H
    change expression.lift' ρ = .app (mkApps (.const name levels) args) arg at H
    cases expression with
    | app fn a =>
      obtain ⟨hefn, hea⟩ := VExpr.app.inj H
      obtain ⟨args', rfl, hargs⟩ := ih hefn
      refine ⟨args' ++ [a], by rw [mkApps_append]; rfl, ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← hargs, hea]
    | _ => cases H

/-- Strengthening the major alone recovers a genuinely scoped family type.
The new implicit arguments are chosen by head reduction of the smaller
inferred type; they need not equal syntactic unliftings of the old witnesses. -/
theorem HasType.familyApp_weak'_inv (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ')
    (hrigid : env.NativeHeadRigid name)
    (hconst : env.HasType univs Γ' (.const name levels) (wrapForalls domains (.sort level)))
    (hlen : args.length = domains.length)
    (H : env.HasType univs Γ' (major.lift' ρ) (mkApps (.const name levels) args)) :
    ∃ levels' args', env.HasType univs Γ major (mkApps (.const name levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length ∧
      env.IsDefEqU univs Γ' (mkApps (.const name levels') (args'.map (·.lift' ρ)))
        (mkApps (.const name levels) args) := by
  have hΓ := hΓ'.weak'_inv henv W
  obtain ⟨smallType, hsmall⟩ := (VExpr.WF.weak'_iff henv hΓ' W).1 ⟨_, H⟩
  have hlarge := hsmall.weak' henv.ordered W
  obtain ⟨_, htypes⟩ := hlarge.uniqU henv hΓ' H
  obtain ⟨levels', largeArgs, hred, hlevels, hargs⟩ :=
    htypes.reduce_familyApp hΓ' hrigid hconst hlen
  obtain ⟨reduced, heq, hsmallRed⟩ := hred.weakU_inv hΓ' W
  obtain ⟨smallArgs, rfl, hlargeArgs⟩ := lift'_const_spine_inv heq.symm
  obtain ⟨u, hsmallType⟩ := hsmall.isType henv.ordered hΓ
  have hsmall' := (show env.HasType univs Γ major smallType from hsmall).defeqU_r
    henv hΓ ⟨_, hsmallRed.defeq hΓ hsmallType⟩
  refine ⟨levels', smallArgs, hsmall', hlevels, ?_, ?_⟩
  · rw [hlargeArgs, List.length_map] at hargs
    exact hargs
  · have hsmallLarge := hsmall'.weak' henv.ordered W
    have heq := hsmallLarge.uniqU henv hΓ' H
    have hlift (fn : VExpr) (xs : List VExpr) :
        (mkApps fn xs).lift' ρ = mkApps (fn.lift' ρ) (xs.map (·.lift' ρ)) := by
      induction xs generalizing fn with
      | nil => rfl
      | cons a xs ih => exact ih (.app fn a)
    simpa only [hlift, VExpr.lift'] using heq

end Lean4Lean.VEnv
