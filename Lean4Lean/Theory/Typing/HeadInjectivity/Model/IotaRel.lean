import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaInstance

/-! # The arguments of an ι instance against the reduct template

Lemmas for establishing `IotaArgRel` (`Model/IotaInstance.lean`) for the rules of ordinary
blocks: argument substitutions through lifts (`argSubst_liftN_mid`), related argument
valuations built position by position (`substEq_argSubst_snoc`), and soundness between
valuations with different observation sets (`SoundAt.sub_sets`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem argSubst_eq_getD (as : List VExpr) (m : Nat) : VExpr.argSubst as m =
    if m < as.length then (as[as.length - 1 - m]?).getD default else .bvar (m - as.length) := by
  split
  · rw [VExpr.argSubst_lt _ (by omega), List.getElem?_eq_getElem (by omega)]; rfl
  · rw [VExpr.argSubst_ge _ (by omega)]

/-- An argument substitution through a lift of the middle block: the lifted variables skip the
middle arguments. -/
theorem argSubst_liftN_mid (e : VExpr) (pre mid post : List VExpr) :
    (e.liftN mid.length post.length).subst (VExpr.argSubst (pre ++ mid ++ post)) =
      e.subst (VExpr.argSubst (pre ++ post)) := by
  rw [VExpr.liftN_subst]
  congr 1
  funext x
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  rw [argSubst_eq_getD, argSubst_eq_getD]
  simp only [List.length_append]
  by_cases hx : x < post.length
  · rw [liftVar_lt hx, if_pos (by omega), if_pos (by omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by omega)]
    congr 2; simp; omega
  · rw [liftVar_le (by omega)]
    by_cases hx' : x < pre.length + post.length
    · rw [if_pos (by omega), if_pos (by omega), List.append_assoc,
        List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      congr 2; omega
    · rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega

/-- Extending related argument valuations by one argument. -/
theorem substEq_argSubst_snoc {D : List VExpr} {as bs : List VExpr} {a b : VExpr}
    (hl : as.length < D.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs) (D.take as.length).reverse)
    (hA : env.HasType U (D.take as.length).reverse D[as.length] (.sort u))
    (h : env.IsDefEq U Δ a b (D[as.length].subst (VExpr.argSubst as))) :
    Ctx.SubstEq env U Δ (VExpr.argSubst (as ++ [a])) (VExpr.argSubst (bs ++ [b]))
      (D.take (as ++ [a]).length).reverse := by
  rw [List.length_append, List.length_singleton, List.take_succ_eq_append_getElem hl,
    List.reverse_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one]
  exact .cons W hA h

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

omit henv hΔ in
/-- The union of two typed valuations' observation sets is typed. -/
theorem TV.union {Γ : List VExpr} {σ : VExpr.Subst} {S₁ S₂ : ObSets}
    (tv₁ : TV env U Δ Γ σ S₁) (tv₂ : TV env U Δ Γ σ S₂) :
    TV env U Δ Γ σ (fun i x => S₁ i x ∨ S₂ i x) := by
  refine ⟨fun i x hx w hw => ?_, fun i A hL x hx => ?_⟩
  · rcases hx with hx | hx
    · exact .inl (tv₁.1 i x hx w hw)
    · exact .inr (tv₂.1 i x hx w hw)
  · rcases hx with hx | hx
    · obtain ⟨τs, h1, h2⟩ := tv₁.2 i A hL x hx
      exact ⟨τs, fun τ hτ => (h1 τ hτ).mono fun _ _ h => .inl h, h2⟩
    · obtain ⟨τs, h1, h2⟩ := tv₂.2 i A hL x hx
      exact ⟨τs, fun τ hτ => (h1 τ hτ).mono fun _ _ h => .inr h, h2⟩

/-- **Soundness between valuations with different observation sets**: the observations of a
soundly typed term at `(σ₁, S₁)` are subsumed by those at a related `(σ₂, S₂)` when every
observation of `S₁` is subsumed by one of `S₂` and both are typed valuations of a sound
context. -/
theorem SoundAt.sub_sets {Γ : List VExpr} {t T : VExpr} (h : SoundAt env U Δ Γ t t T)
    (hctx : CtxSD env U Δ [] Γ)
    {σ₁ σ₂ : VExpr.Subst} {S₁ S₂ : ObSets} (W : Ctx.SubstEq env U Δ σ₁ σ₂ Γ)
    (hout : ∀ x, Γ.length ≤ x → σ₁ x = σ₂ x)
    (tv₁ : TV env U Δ Γ σ₁ S₁) (tv₂ : TV env U Δ Γ σ₂ S₂)
    (hS : ∀ i o, S₁ i o → ∃ o', S₂ i o' ∧ o' ≼ o) :
    Ob.Sub (Obs' σ₁ S₁ t) (Obs' σ₂ S₂ t) := by
  intro o ho
  have W' : Ctx.SubstEq env U Δ σ₁ σ₂ (Γ ++ []) := by simpa using W
  have Ws : Ctx.SubstEq env U Δ σ₂ σ₁ (Γ ++ []) := by simpa using SubstEq.symm henv hΔ W
  have t21 : TV env U Δ Γ σ₁ S₂ := by
    have := TV.transfer henv hΔ (Γ := []) hctx W' (by simpa using hout) (by simpa using tv₂)
    simpa using this
  have t12 : TV env U Δ Γ σ₂ S₁ := by
    have := TV.transfer henv hΔ (Γ := []) hctx Ws (by simpa using fun x hx => (hout x hx).symm)
      (by simpa using tv₁)
    simpa using this
  have tvA := TV.union tv₁ t21
  have tvB := TV.union t12 tv₂
  obtain ⟨o₁, ho₁, l₁⟩ := (h σ₁ σ₂ _ W tvA tvB).1 o (ho.mono fun _ _ h => .inl h)
  obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := S₂) fun i x hx => by
    rcases hx with hx | hx
    · exact hS i x hx
    · exact ⟨x, hx, .refl⟩
  exact ⟨o₂, ho₂, l₂.trans l₁⟩


/-- `rigid_arg_cls_obs` with the domain class of the argument read off the head's telescope. -/
theorem rigid_arg_cls_obs' {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr}
    {u : VLevel} {σ : VExpr.Subst} {S : ObSets} {ci : VConstant} {Dw : List VExpr} {Rw : VExpr}
    (hci : env.constants c = some ci) (hTW : ci.type.instL ls = .wrapForalls Dw Rw)
    (hpi : PiSD env U Δ [] Dw Rw)
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c) {i : Nat} (hi : i < args.length)
    (hiD : i < Dw.length) :
    ∃ A, HTS env U Δ Γ args[i] A ∧ SD env U Δ Γ args[i] args[i] A ∧
      TyCls env U Δ (A.subst σ) =
        TyCls env U Δ (Dw[i].subst (VExpr.argSubst ((args.take i).map (·.subst σ)))) ∧
      Obs' σ S (.mkApps (.const c ls) args)
        (.rigidArg i (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (args[i].subst σ))) := by
  obtain ⟨Th, info, hTh, -, -, hinfo, -, P1, -, -, PT⟩ :=
    H.spineH' henv hΔ rfl ⟨c, ls, rfl⟩ W tv (args.map fun _ => []) (forall₂_nil_lists args)
      [.sort u.eval] (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort)
  obtain ⟨_, _, ci', e0, hci', -, rfl⟩ := hTh
  cases e0
  cases hci.symm.trans hci'
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  have hi' : i < info.length := by omega
  obtain ⟨_, hd⟩ := List.forall₂_getElem_exists hinfo i hi'
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hd
  have hr : RigidEnd c (ls.map (·.eval)) (info.map (·.1)) (.rigidArg i (info[i]).1.2.1) :=
    .inr (.inl ⟨i, by simpa using hi', by simp⟩)
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 _ (.rigidArg (List.mem_singleton_self _))
  obtain ⟨B, hB⟩ := PT i hi'
  have hTW' : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)) :=
    fun o h => ⟨o, by rw [← hTW]; exact h, .refl⟩
  have e := spine_dom_cls henv hΔ hci hTW' hpi (pre := args.take i) (by simp; omega) W tv hB
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at e
  refine ⟨(info[i]).2, h4, h5, e, ?_⟩
  have := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo) (.const hrig hci hτ₀ hty₀ hr)
  rwa [h1, h3] at this

/-- **Related rigid spines along the head's telescope**: two sort-typed spines of the rigid
constant `c` whose observations subsume each other have related argument valuations along the
telescope of `c`'s type, at the levels of the left spine, and mutually subsuming argument
observations. -/
theorem rigid_spines_substEq {Γ₁ Γ₂ : List VExpr} {c : Name} {ls₁ ls₂ : List VLevel}
    {args₁ args₂ : List VExpr} {u₁ u₂ : VLevel} {σ₁ σ₂ : VExpr.Subst} {S₁ S₂ : ObSets}
    {ci : VConstant} {Dw : List VExpr} {Rw : VExpr}
    (hci : env.constants c = some ci) (hTW : ci.type.instL ls₁ = .wrapForalls Dw Rw)
    (hpi : PiSD env U Δ [] Dw Rw)
    (H₁ : HTS env U Δ Γ₁ (.mkApps (.const c ls₁) args₁) (.sort u₁))
    (W₁ : Ctx.SubstEq env U Δ σ₁ σ₁ Γ₁) (tv₁ : TV env U Δ Γ₁ σ₁ S₁)
    (H₂ : HTS env U Δ Γ₂ (.mkApps (.const c ls₂) args₂) (.sort u₂))
    (W₂ : Ctx.SubstEq env U Δ σ₂ σ₂ Γ₂) (tv₂ : TV env U Δ Γ₂ σ₂ S₂) (hrig : env.Rigid c)
    (hsub : Ob.Sub (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁))
      (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂)))
    (hsub' : Ob.Sub (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂))
      (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁)))
    (hlenD : args₁.length ≤ Dw.length) :
    args₁.length = args₂.length ∧ List.Forall₂ (· ≈ ·) ls₁ ls₂ ∧
    Ctx.SubstEq env U Δ (VExpr.argSubst (args₁.map (·.subst σ₁)))
      (VExpr.argSubst (args₂.map (·.subst σ₂))) (Dw.take args₁.length).reverse ∧
    ∀ i (hi : i < args₁.length) (hi' : i < args₂.length),
      Ob.Sub (Obs' σ₁ S₁ args₁[i]) (Obs' σ₂ S₂ args₂[i]) ∧
      Ob.Sub (Obs' σ₂ S₂ args₂[i]) (Obs' σ₁ S₁ args₁[i]) := by
  obtain ⟨hlen, hls, hrel⟩ := rigid_spines_rel henv hΔ H₁ W₁ tv₁ H₂ W₂ tv₂ hrig hsub hsub'
  refine ⟨hlen, hls, ?_, fun i hi hi' => ⟨(hrel i hi hi').1, (hrel i hi hi').2.1⟩⟩
  -- the defeqs at the telescope's domains
  have hdef : ∀ i (hi : i < args₁.length) (hi' : i < args₂.length) (hiD : i < Dw.length),
      env.IsDefEq U Δ (args₁[i].subst σ₁) (args₂[i].subst σ₂)
        (Dw[i].subst (VExpr.argSubst ((args₁.take i).map (·.subst σ₁)))) := by
    intro i hi hi' hiD
    obtain ⟨A, -, hsA, eA, hcls⟩ := rigid_arg_cls_obs' henv hΔ hci hTW hpi H₁ W₁ tv₁ hrig hi hiD
    obtain ⟨o', ho', l⟩ := hsub _ hcls
    rw [l.rigidArg_inv] at ho'
    obtain ⟨keys', hk', hw'⟩ := wrap_of_obs_mkApps ho'
    have hend' := const_wrap_inv hrig hw' (.inr ⟨_, _, rfl⟩)
    obtain ⟨j, hj, e⟩ : ∃ j, ∃ h : j < keys'.length,
        Ob.rigidArg i (ElCls env U Δ (TyCls env U Δ (A.subst σ₁)) (args₁[i].subst σ₁)) =
          .rigidArg j (keys'[j]).2.1 := by
      rcases hend' with ⟨_, e⟩ | ⟨j, hj, e⟩ | ⟨_, _, _, _, e⟩
      · cases e
      · exact ⟨j, hj, e⟩
      · cases e
    injection e with e1 e2
    subst e1
    obtain ⟨_, hcl⟩ := List.forall₂_getElem_exists hk' i hj
    have hmem : ElCls env U Δ (TyCls env U Δ (A.subst σ₁)) (args₁[i].subst σ₁)
        (args₂[i].subst σ₂) := by
      rw [e2, hcl]; exact ElCls.self
    have ha : env.HasType U Δ (args₁[i].subst σ₁) (A.subst σ₁) :=
      hsA.1.defeq.hasType.1.substDF henv W₁.wf hΔ W₁
    have h := ElCls.collapse henv hΔ ha TyCls.self hmem
    have hm : TyCls env U Δ (A.subst σ₁)
        (Dw[i].subst (VExpr.argSubst ((args₁.take i).map (·.subst σ₁)))) := by
      rw [eA]; exact TyCls.self
    exact TyCls.defeq_rev henv hΔ hm h
  -- assemble along the prefixes
  have key : ∀ n, n ≤ args₁.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((args₁.take n).map (·.subst σ₁)))
        (VExpr.argSubst ((args₂.take n).map (·.subst σ₂))) (Dw.take n).reverse := by
    intro n
    induction n with
    | zero => intro _; simpa using (Ctx.SubstEq.nil : Ctx.SubstEq env U Δ _ _ [])
    | succ n ih =>
      intro hn
      have hn₁ : n < args₁.length := by omega
      have hn₂ : n < args₂.length := by omega
      have hnD : n < Dw.length := by omega
      obtain ⟨-, w, hDn⟩ := DomsSD.take_getElem hpi.doms n hnD
      rw [List.append_nil] at hDn
      have := substEq_argSubst_snoc (D := Dw) (as := (args₁.take n).map (·.subst σ₁))
        (bs := (args₂.take n).map (·.subst σ₂)) (a := args₁[n].subst σ₁)
        (b := args₂[n].subst σ₂) (by simp; omega)
        (by simpa [Nat.min_eq_left (Nat.le_of_lt hn₁)] using ih (by omega))
        (by simpa [Nat.min_eq_left (Nat.le_of_lt hn₁)] using hDn.1.defeq.hasType.1)
        (by simpa [Nat.min_eq_left (Nat.le_of_lt hn₁)] using hdef n hn₁ hn₂ hnD)
      rw [List.take_succ_eq_append_getElem hn₁, List.take_succ_eq_append_getElem hn₂,
        List.map_append, List.map_append]
      simpa [Nat.min_eq_left (Nat.le_of_lt hn₁)] using this
  have := key args₁.length (Nat.le_refl _)
  rwa [List.take_length, List.take_of_length_le (by omega)] at this

end

end Model
end VEnv
end Lean4Lean
