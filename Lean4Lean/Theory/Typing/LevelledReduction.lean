import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.LevelledConfluence

/-! # Levelled parallel relations for the full presentation

The full step relation is split into four parallel relations, ordered by
level for the decreasing-diagram criterion of `Lean4Lean.Levelled`:

0. normal equality without eta (`NormalEq₀`): structural, universe levels and
   proof irrelevance;
1. parallel reduction (`ParRed`): beta, native and registered schema patterns;
2. `DeltaPar`: parallel native prefix unfolding, quotient prefix unfolding and
   projection of constructor applications;
3. `EtaPar`: parallel function and structure eta expansion.

Eta expansion sits above beta. An expansion in the function position of a
redex blocks that redex, and the other side of the peak can only recover it by
a beta step followed by the original contraction, so the expansion side must
be allowed any number of lower steps.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- The structure eta expansion of `e` at the given structure. -/
def structExpand (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (params : List VExpr) (e : VExpr) : VExpr :=
  VExpr.mkApps (.const info.ctorName levels)
    (params ++ (List.range info.numFields).map fun index => .proj family index e)

/-- Parallel contraction of native prefix unfoldings, quotient prefix
unfoldings and projections of constructor applications. Arguments are
developed before the redex is contracted. -/
inductive DeltaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : DeltaPar Γ (.bvar i) (.bvar i)
  | sort : DeltaPar Γ (.sort u) (.sort u)
  | const : DeltaPar Γ (.const c ls) (.const c ls)
  | elim : DeltaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : DeltaPar Γ f f' → DeltaPar Γ a a' → DeltaPar Γ (.app f a) (.app f' a')
  | proj : DeltaPar Γ major major' →
      DeltaPar Γ (.proj family index major) (.proj family index major')
  | lam : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.lam A body) (.lam A' body')
  | forallE : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.forallE A body) (.forallE A' body')
  | delta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      NativeDeltaRule env univs recursorData Γ name levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const name levels) args) rhs
  | quotDelta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      QuotDeltaRule env univs Γ levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const ``Quot.lift levels) args) rhs
  | projIota {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      env.projections family info →
      Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName levels) args') : fieldType →
      args'[info.nparams + index]? = some field → Γ ⊢ field : fieldType →
      DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) field

/-- Parallel function and structure eta expansion. The expanded term is
developed before it is expanded. -/
inductive EtaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : EtaPar Γ (.bvar i) (.bvar i)
  | sort : EtaPar Γ (.sort u) (.sort u)
  | const : EtaPar Γ (.const c ls) (.const c ls)
  | elim : EtaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : EtaPar Γ f f' → EtaPar Γ a a' → EtaPar Γ (.app f a) (.app f' a')
  | proj : EtaPar Γ major major' →
      EtaPar Γ (.proj family index major) (.proj family index major')
  | lam : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.lam A body) (.lam A' body')
  | forallE : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.forallE A body) (.forallE A' body')
  | funEta : EtaPar Γ e e' → EtaPar Γ A A' → Γ ⊢ e : .forallE A B →
      EtaPar Γ e (.lam A' (.app e'.lift (.bvar 0)))
  | structEta {params params' : List VExpr} : EtaPar Γ e e' →
      (hlen : params.length = params'.length) →
      (∀ i (hi : i < params.length) (hi' : i < params'.length),
        EtaPar Γ params[i] params'[i]) →
      env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ e : VExpr.mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params e : VExpr.mkApps (.const family levels) params →
      EtaPar Γ e (structExpand family info levels params' e')

section Basic

omit [Params] in
theorem forall₂_of_getElem {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i]) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hlen, H =>
    .cons (H 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using hlen) fun i hi hi' => H (i + 1) (by simpa using hi)
        (by simpa using hi'))
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

omit [Params] in
theorem getElem_of_forall₂ {R : α → β → Prop} {l : List α} {l' : List β}
    (H : List.Forall₂ R l l') : l.length = l'.length ∧
      ∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i] :=
  ⟨Lean4Lean.List.Forall₂.length_eq H, fun _ hi hi' => case_forall₂_get H hi hi'⟩

protected theorem DeltaPar.rfl : ∀ {e}, DeltaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app DeltaPar.rfl DeltaPar.rfl
  | .proj .. => .proj DeltaPar.rfl
  | .lam .. => .lam DeltaPar.rfl DeltaPar.rfl
  | .forallE .. => .forallE DeltaPar.rfl DeltaPar.rfl

protected theorem EtaPar.rfl : ∀ {e}, EtaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app EtaPar.rfl EtaPar.rfl
  | .proj .. => .proj EtaPar.rfl
  | .lam .. => .lam EtaPar.rfl EtaPar.rfl
  | .forallE .. => .forallE EtaPar.rfl EtaPar.rfl

theorem FullReduction.mkApps_args (H : List.Forall₂ (FullReduction Γ) args args') :
    FullReduction Γ (VExpr.mkApps fn args) (VExpr.mkApps fn args') :=
  FullReduction.mkApps .rfl H

theorem DeltaPar.full (H : DeltaPar Γ e e') : FullReduction Γ e e' := by
  induction H with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | proj _ ih => exact ih.proj
  | lam _ _ ih1 ih2 => exact ih1.lam ih2
  | forallE _ _ ih1 ih2 => exact ih1.forallE ih2
  | delta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).tail (.delta hr)
  | quotDelta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).tail (.quotDelta hr)
  | projIota hlen _ hl hs hi ht ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).proj.tail
      (.projIota hl hs hi ht)

theorem FullReduction.structExpand (H : FullReduction Γ e e') :
    FullReduction Γ (structExpand family info levels params e)
      (structExpand family info levels params e') := by
  refine FullReduction.mkApps_args (case_forall₂_append ?_ ?_)
  · exact List.Forall₂.rfl fun _ _ => .rfl
  · induction (List.range info.numFields) with
    | nil => exact .nil
    | cons _ _ ih => exact .cons H.proj ih

theorem EtaPar.full (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaPar Γ e e')
    (he : Γ ⊢ e : T) : FullReduction Γ e e' := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact (ih1 hΓ h1).app (ih2 hΓ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    exact (ih hΓ hm.hasType.2).proj
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact (ih1 hΓ h1).lam (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact (ih1 hΓ h1).forallE (ih2 ⟨hΓ, _, h1⟩ h2)
  | funEta _ _ ht ih ihA =>
    have h := ih hΓ ht
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ; h.forallE_inv henv
    exact (h.tail (.funEta (h.hasType hΓ ht))).trans ((ihA hΓ hA).lam .rfl)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    have h := ih hΓ hs
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    have hps : List.Forall₂ (FullReduction _) _ _ := forall₂_of_getElem hlen fun i hi hi' =>
      ihp i hi hi' hΓ (schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)).choose_spec
    refine (h.tail (.structEta hl hp hi (h.hasType hΓ hs)
      ((FullReduction.structExpand h).hasType hΓ hc))).trans ?_
    exact FullReduction.mkApps_args (case_forall₂_append hps (List.Forall₂.rfl fun _ _ => .rfl))

/-! ### Substitution of definitionally equal arguments -/

theorem _root_.Lean4Lean.Ctx.InstN.substEq (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) :
    Ctx.SubstEq env univs Γ ((VExpr.Subst.one a₁).liftN k) ((VExpr.Subst.one a₂).liftN k) Γ₁ := by
  induction W with
  | zero =>
    obtain ⟨hΓ₀, _, hA⟩ := hΓ₁
    refine .cons (Ctx.SubstEq.id henv.ordered hΓ₀) hA ?_
    show Γ₀ ⊢ a₁ ≡ a₂ : A₀.subst .id
    rw [subst_id]; exact ha
  | succ W ih =>
    obtain ⟨hΓ₁', _, hA⟩ := hΓ₁
    have := (ih hΓ₁').lift henv.ordered hA
    rwa [← instN_eq] at this

theorem HasType.instN_DF (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) (H : Γ₁ ⊢ e : A) : Γ ⊢ e.inst a₁ k ≡ e.inst a₂ k : A.inst a₁ k := by
  have hΓ := (W.wf henv.ordered ha.hasType.1 hΓ₁).2
  simpa only [← instN_eq] using IsDefEq.substDF henv.ordered hΓ₁ hΓ (W.substEq hΓ₁ ha) H

theorem _root_.Lean4Lean.Ctx.InstN.defeqCtx (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) :
    ∃ Γ', Ctx.InstN Γ₀ a₂ A₀ k Γ₁ Γ' ∧ IsDefEqCtx env univs Γ₀ Γ' Γ := by
  induction W with
  | zero => exact ⟨_, .zero, .zero⟩
  | succ W ih =>
    obtain ⟨hΓ₁', _, hA⟩ := hΓ₁
    obtain ⟨Γ', W', hc⟩ := ih hΓ₁'
    exact ⟨_, .succ W', .succ hc (HasType.instN_DF W' hΓ₁' ha.symm hA)⟩

/-! ### Weakening, context conversion and substitution -/

theorem DeltaPar.weakN (W : Ctx.LiftN n k Γ Γ') (H : DeltaPar Γ e e') :
    DeltaPar Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | delta hlen _ hr ih =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .delta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      (hr.weakN henv W)
  | quotDelta hlen _ hr ih =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .quotDelta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      (hr.weakN henv W)
  | projIota hlen _ hl hs hi ht ih =>
    have hs' := hs.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at hs' ⊢
    exact .projIota (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      hl hs' (by simp [hi]) (ht.weakN henv W)

theorem DeltaPar.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : DeltaPar Γ₁ e e') (he : Γ₁ ⊢ e : A) : DeltaPar Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hd) (ih2 (.succ W hd) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hd) (ih2 (.succ W hd) hb)
  | delta hlen _ hr ih =>
    exact .delta hlen (fun i hi hi' => ih i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) he (List.getElem_mem hi)).choose_spec)
      (hr.defeqDFC henv hΓ W)
  | quotDelta hlen _ hr ih =>
    exact .quotDelta hlen (fun i hi hi' => ih i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) he (List.getElem_mem hi)).choose_spec)
      (hr.defeqDFC henv hΓ W)
  | projIota hlen _ hl hs hi ht ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .projIota hlen (fun i hi' hi'' => ih i hi' hi'' W
      (schema_mkApps_arg_type (W.isType' hΓ) hm.hasType.2 (List.getElem_mem hi')).choose_spec)
      hl (hs.defeqDFC henv W) hi (ht.defeqDFC henv W)

theorem DeltaPar.instN (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (H₀ : DeltaPar Γ₀ a₁ a₂) (h₀ : Γ₀ ⊢ a₁ : A₀)
    (H : DeltaPar Γ₁ e e') (he : Γ₁ ⊢ e : T) : DeltaPar Γ (e.inst a₁ k) (e'.inst a₂ k) := by
  have hΓ₀ := (W.wf henv.ordered h₀ hΓ₁).1
  have ha := (DeltaPar.full H₀).defeq hΓ₀ h₀
  have h₂ := ha.hasType.2
  induction H generalizing Γ k T with
  | @bvar _ i =>
    clear he hΓ₁
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact (ih ..).weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ₁
    exact .app (ih1 W hΓ₁ h1) (ih2 W hΓ₁ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ₁
    exact .lam (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | delta hlen _ hr ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    have hr' := (hr.instN henv W' h₂).defeqDFC henv hΓ₀ hc
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .delta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ he (List.getElem_mem (by simpa using hi))).choose_spec)
      hr'
  | quotDelta hlen _ hr ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    have hr' := (hr.instN henv W' h₂).defeqDFC henv hΓ₀ hc
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .quotDelta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ he (List.getElem_mem (by simpa using hi))).choose_spec)
      hr'
  | projIota hlen _ hl hs hi ht ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    have hs' := (hs.instN henv W' h₂).defeqDFC henv hc
    have ht' := (ht.instN henv W' h₂).defeqDFC henv hc
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ hm.hasType.2
            (List.getElem_mem (by simpa using hi))).choose_spec)
      hl hs' (by simp [hi]) ht'

theorem structExpand_liftN :
    (structExpand family info levels params e).liftN n k =
      structExpand family info levels (params.map (·.liftN n k)) (e.liftN n k) := by
  simp [structExpand, VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
    Function.comp_def]

theorem structExpand_inst :
    (structExpand family info levels params e).inst a k =
      structExpand family info levels (params.map (·.inst a k)) (e.inst a k) := by
  simp [structExpand, VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
    Function.comp_def]

theorem EtaPar.weakN (W : Ctx.LiftN n k Γ Γ') (H : EtaPar Γ e e') :
    EtaPar Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | funEta _ _ ht ih ihA =>
    simpa only [VExpr.liftN, ← VExpr.lift_liftN', liftVar_zero] using
      EtaPar.funEta (ih W) (ihA W) (ht.weakN henv W)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    have hs' := hs.weakN henv W
    have hc' := hc.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, structExpand_liftN] at hs' hc' ⊢
    exact .structEta (ih W) (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ihp i (by simpa using hi) (by simpa using hi') W)
      hl (by simpa using hp) hi hs' hc'

theorem EtaPar.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : EtaPar Γ₁ e e') (he : Γ₁ ⊢ e : A) : EtaPar Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hd) (ih2 (.succ W hd) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hd) (ih2 (.succ W hd) hb)
  | funEta _ _ ht ih ihA =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv (W.isType' hΓ); h.forallE_inv henv
    exact .funEta (ih W ht) (ihA W hA) (ht.defeqDFC henv W)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    obtain ⟨_, hT⟩ := hs.isType henv (W.isType' hΓ)
    exact .structEta (ih W hs) hlen (fun i hi hi' => ihp i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) hT (List.getElem_mem hi)).choose_spec)
      hl hp hi (hs.defeqDFC henv W) (hc.defeqDFC henv W)

theorem EtaPar.instN (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (H₀ : EtaPar Γ₀ a₁ a₂) (h₀ : Γ₀ ⊢ a₁ : A₀)
    (H : EtaPar Γ₁ e e') (he : Γ₁ ⊢ e : T) : EtaPar Γ (e.inst a₁ k) (e'.inst a₂ k) := by
  induction H generalizing Γ k T with
  | @bvar _ i =>
    clear he hΓ₁
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact (ih ..).weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ₁
    exact .app (ih1 W hΓ₁ h1) (ih2 W hΓ₁ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ₁
    exact .lam (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | funEta _ _ ht ih ihA =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ₁; h.forallE_inv henv
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, instVar, if_pos (Nat.zero_lt_succ k)] using
      EtaPar.funEta (ih W hΓ₁ ht) (ihA W hΓ₁ hA) (ht.instN henv W h₀)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    obtain ⟨_, hT⟩ := hs.isType henv hΓ₁
    have hs' := hs.instN henv W h₀
    have hc' := hc.instN henv W h₀
    simp only [VExpr.inst_mkApps, VExpr.inst, structExpand_inst] at hs' hc' ⊢
    exact .structEta (ih W hΓ₁ hs) (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ihp i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ hT (List.getElem_mem (by simpa using hi))).choose_spec)
      hl (by simpa using hp) hi hs' hc'

end Basic


section EtaMirror

theorem NormalEqF.structExpand_congr (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ e₁ e₂) (hps : List.Forall₂ (NormalEqF η Γ) ps₁ ps₂)
    (ht : Γ ⊢ structExpand family info levels ps₁ e₁ : T) :
    NormalEqF η Γ (structExpand family info levels ps₁ e₁)
      (structExpand family info levels ps₂ e₂) := by
  unfold VEnv.structExpand at ht ⊢
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  have hfields : List.Forall₂ (NormalEqF η Γ)
      ((List.range info.numFields).map fun index => .proj family index e₁)
      ((List.range info.numFields).map fun index => .proj family index e₂) := by
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    have himem : i ∈ List.range info.numFields := by simpa using hi
    obtain ⟨_, h⟩ := schema_mkApps_arg_type hΓ ht
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, himem, rfl⟩))
    simpa only [List.getElem_map, List.getElem_range] using NormalEqF.projDF h H
  exact NormalEqF.mkApps_spine hΓ (.refl hhead) (case_forall₂_append hps hfields) ht

theorem structExpand_params_typed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ structExpand family info levels ps e : T) : ∀ p ∈ ps, ∃ A, Γ ⊢ p : A :=
  fun _ hp => schema_mkApps_arg_type hΓ ht (List.mem_append_left _ hp)

/-- Typing transports along a normally equal expanded term. -/
theorem structExpand_typed_of_normal (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ e₁ e₂) (ht : Γ ⊢ structExpand family info levels ps e₂ : T) :
    Γ ⊢ structExpand family info levels ps e₁ : T :=
  ht.defeqU_l henv hΓ (NormalEqF.defeq hΓ (NormalEqF.structExpand_congr hΓ (H.symm hΓ)
    (NormalEqF.forall₂_refl (structExpand_params_typed hΓ ht)) ht))

/-- The normal equality of two eta bodies at the same domain. -/
theorem NormalEqF.etaBody (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ e₁ e₂) (h1 : Γ ⊢ e₁ : .forallE D B) (h2 : Γ ⊢ e₂ : .forallE D B)
    (hD : Γ ⊢ D ≡ D₁ : .sort u) (hD' : Γ ⊢ D ≡ D₂ : .sort u) :
    NormalEqF η Γ (.lam D₁ (.app e₁.lift (.bvar 0))) (.lam D₂ (.app e₂.lift (.bvar 0))) :=
  NormalEqF.lamDF hD hD' (NormalEqF.appDF (h1.weak henv) (h2.weak henv) (.bvar .zero)
    (.bvar .zero) (H.weakN .one) (.refl (.bvar .zero)))

theorem EtaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', EtaPar Γ c c' ∧ NormalEq₀ Γ c' b := by
  induction H generalizing c A with
  | bvar | sort | const | elim => exact ⟨c, .rfl, hc⟩
  | @app _ f f' x x' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.app h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.app f x = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .app h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.app h1 h2) l3).hasType hΓ l3)⟩
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      obtain ⟨F, hF, eF⟩ := ih1 hΓ ⟨_, l5⟩ l2
      obtain ⟨X, hX, eX⟩ := ih2 hΓ ⟨_, l6⟩ l4
      exact ⟨_, .app hF hX, .appDF ((EtaPar.full hΓ hF l1).hasType hΓ l1)
        ((EtaPar.full hΓ h1 l2).hasType hΓ l2) ((EtaPar.full hΓ hX l3).hasType hΓ l3)
        ((EtaPar.full hΓ h2 l4).hasType hΓ l4) eF eX⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF => cases hR
  | @proj _ m m' family index h1 ih =>
    have hb := (EtaPar.full hΓ (.proj h1) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.proj family index m = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .proj h1, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.proj h1) l3).hasType hΓ l3)⟩
    | projDF l1 l2 =>
      cases hR
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, hM, eM⟩ := ih hΓ ⟨_, l2⟩ hm.hasType.2
      exact ⟨_, .proj hM, .projDF ((EtaPar.full hΓ (.proj hM) l1).hasType hΓ l1) eM⟩
    | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR
  | @lam _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.lam h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.lam D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .lam h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.lam h1 h2) l3).hasType hΓ l3)⟩
    | lamDF l1 l2 l3 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have l3' := l3.defeqDFC hΓ (.succ .zero l2)
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l3'⟩ ht
      have hDD₁ := l2.symm.trans l1
      have ht₁ := ((NormalEqN.defeq hΓ' l3').of_r henv hΓ' ht).hasType.1
      refine ⟨_, .lam .rfl (hT.defeqDFC hΓ (.succ .zero hDD₁) ht₁), ?_⟩
      have hD2 := l2.hasType.2
      have hDD' := (EtaPar.full hΓ h1 hD2).defeq hΓ hD2
      exact .lamDF hDD₁ hDD' eT
    | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hR
  | @forallE _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.forallE h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.forallE D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .forallE h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.forallE h1 h2) l3).hasType hΓ l3)⟩
    | forallEDF l1 l2 l3 l4 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.forallE_inv henv
      obtain ⟨D₁', hD₁, eD⟩ := ih1 hΓ ⟨_, l2⟩ hD
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have W' := l1.transU_l henv hΓ (NormalEqN.defeq hΓ l2)
      have l4' := l4.defeqDFC hΓ (.succ .zero W')
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l4'⟩ ht
      have l3'' := l3.defeqDFC henv (.succ .zero W')
      have hA₁ := l1.hasType.2
      have hD₁T := (EtaPar.full hΓ hD₁ hA₁).defeq hΓ hA₁
      refine ⟨_, .forallE hD₁ (hT.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''), ?_⟩
      have hT1 := (EtaPar.full hΓ' hT l3'').hasType hΓ' l3''
      exact .forallEDF (W'.symm.trans (l1.trans hD₁T)) eD hT1 eT
    | sortDF | constDF | elimDF | appDF | projDF | lamDF => cases hR
  | funEta H1 HA ht ih ihA =>
    obtain ⟨c₀, hc₀, ec₀⟩ := ih hΓ hc ht
    have hcT := ht.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
    refine ⟨_, .funEta hc₀ HA hcT, ?_⟩
    have ⟨⟨_, hD⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ; h.forallE_inv henv
    have hDD := (EtaPar.full hΓ HA hD).defeq hΓ hD
    exact NormalEqF.etaBody hΓ ec₀ ((EtaPar.full hΓ hc₀ hcT).hasType hΓ hcT)
      ((EtaPar.full hΓ H1 ht).hasType hΓ ht) hDD hDD
  | structEta H1 hlen hps hl hp hi hs hexp ih ihp =>
    obtain ⟨c₀, hc₀, ec₀⟩ := ih hΓ hc hs
    have hcS := hs.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
    have hcexp := structExpand_typed_of_normal hΓ hc hexp
    have hstep := EtaPar.structEta hc₀ hlen hps hl hp hi hcS hcexp
    refine ⟨_, hstep, ?_⟩
    have ht' := (EtaPar.full hΓ hstep hcS).hasType hΓ hcS
    exact NormalEqF.structExpand_congr hΓ ec₀
      (NormalEqF.forall₂_refl (structExpand_params_typed hΓ ht')) ht'

end EtaMirror


section DeltaMirror

omit [Params] in
theorem List.Forall₂.exists_mid {R S U V : α → α → Prop} :
    ∀ {l₁ l l'}, List.Forall₂ R l₁ l → List.Forall₂ S l l' →
      (∀ x y z, y ∈ l → R x y → S y z → ∃ w, U x w ∧ V w z) →
      ∃ ws, List.Forall₂ U l₁ ws ∧ List.Forall₂ V ws l'
  | [], [], [], .nil, .nil, _ => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2, H => by
    obtain ⟨w, hu, hv⟩ := H _ _ _ (List.mem_cons_self ..) h1 h2
    obtain ⟨ws, hus, hvs⟩ := List.Forall₂.exists_mid t1 t2
      fun x y z hy => H x y z (List.mem_cons_of_mem _ hy)
    exact ⟨w :: ws, .cons hu hus, .cons hv hvs⟩

omit [Params] in
theorem mkApps_snoc (f : VExpr) (l : List VExpr) (b : VExpr) :
    VExpr.mkApps f (l ++ [b]) = .app (VExpr.mkApps f l) b := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => exact ih (.app f a)

omit [Params] in
theorem snoc_induction {P : List α → Prop} (nil : P []) (snoc : ∀ l a, P l → P (l ++ [a]))
    (l : List α) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a l ih => rw [List.reverse_cons]; exact snoc _ _ ih

/-- Spine exposure without eta. A term normally equal to a rigid-headed spine
is a proof or literally a spine with an equivalent head. -/
theorem NormalEq₀.spine_expose (hΓ : OnCtx Γ (env.IsType univs)) (hh : RigidHead h)
    (H : NormalEq₀ Γ x (VExpr.mkApps h targs)) (hx : Γ ⊢ x : T) :
    (Γ ⊢ T : .sort .zero) ∨
    ∃ h' targs', HeadEquiv h' h ∧ x = VExpr.mkApps h' targs' ∧
      List.Forall₂ (NormalEq₀ Γ) targs' targs := by
  induction targs using snoc_induction generalizing x T with
  | nil =>
    obtain ⟨n, H⟩ := H
    cases hh with
    | const =>
      generalize hR : VExpr.mkApps (.const _ _) [] = R at H
      cases H with
      | refl _ => subst hR; exact .inr ⟨_, [], RigidHead.const.equiv_rfl, rfl, .nil⟩
      | constDF _ _ _ _ h5 => cases hR; exact .inr ⟨_, [], .const h5, rfl, .nil⟩
      | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
      | _ => cases hR
    | elim =>
      generalize hR : VExpr.mkApps (.elim _ _ _) [] = R at H
      cases H with
      | refl _ => subst hR; exact .inr ⟨_, [], RigidHead.elim.equiv_rfl, rfl, .nil⟩
      | elimDF _ h2 => cases hR; exact .inr ⟨_, [], .elim h2, rfl, .nil⟩
      | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
      | _ => cases hR
  | snoc targs t ih =>
    obtain ⟨n, H⟩ := H
    rw [mkApps_snoc] at H
    generalize hR : VExpr.app (VExpr.mkApps h targs) t = R at H
    cases H with
    | refl _ =>
      subst hR
      have hx' : Γ ⊢ VExpr.mkApps h (targs ++ [t]) : T := by rwa [mkApps_snoc]
      exact .inr ⟨h, targs ++ [t], hh.equiv_rfl, (mkApps_snoc ..).symm,
        NormalEqF.forall₂_refl fun _ hm => schema_mkApps_arg_type hΓ hx' hm⟩
    | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      rcases ih ⟨_, l5⟩ l1 with hp | ⟨h', targs', he, rfl, hargs⟩
      · exact .inl (HasType.mkApps_proof hΓ hp l1 (bs := [_]) hx)
      · exact .inr ⟨h', targs' ++ [_], he, (mkApps_snoc ..).symm,
          case_forall₂_append hargs (.cons ⟨_, l6⟩ .nil)⟩
    | _ => cases hR

theorem NativeDeltaRule.congr₀ (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeDeltaRule env univs recursorData Γ name levels args rhs)
    (hw : ∀ level ∈ levels', level.WF univs) (hls : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (NormalEq₀ Γ) args args') :
    ∃ rhs', NativeDeltaRule env univs recursorData Γ name levels' args' rhs' ∧
      NormalEq₀ Γ rhs rhs' := by
  obtain ⟨rhs₁, h1, e1⟩ := H.congr_normal hΓ ha
  obtain ⟨rhs₂, h2, e2⟩ := h1.congr_levels henv hΓ hw hls
    (eqUpToLevels_forall₂_rfl hΓ (NormalEqF.forall₂_typed_right hΓ ha))
  obtain ⟨_, hd⟩ := h1.defeq henv hΓ
  exact ⟨rhs₂, h2, e1.trans hΓ (NormalEqF.of_levelEquiv hΓ (.of_eqUpToLevels e2) hd.hasType.2)⟩

theorem QuotDeltaRule.congr₀ (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotDeltaRule env univs Γ levels args rhs)
    (hw : ∀ level ∈ levels', level.WF univs) (hls : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (NormalEq₀ Γ) args args') :
    ∃ rhs', QuotDeltaRule env univs Γ levels' args' rhs' ∧ NormalEq₀ Γ rhs rhs' := by
  obtain ⟨rhs₁, h1, e1⟩ := H.congr_normal hΓ ha
  obtain ⟨rhs₂, h2, e2⟩ := h1.congr_levels henv hΓ hw hls
    (eqUpToLevels_forall₂_rfl hΓ (NormalEqF.forall₂_typed_right hΓ ha))
  obtain ⟨_, hd⟩ := h1.defeq henv hΓ
  exact ⟨rhs₂, h2, e1.trans hΓ (NormalEqF.of_levelEquiv hΓ (.of_eqUpToLevels e2) hd.hasType.2)⟩


theorem DeltaPar.mkApps (hf : DeltaPar Γ f f') (H : List.Forall₂ (DeltaPar Γ) args args') :
    DeltaPar Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons h _ ih => exact ih (.app hf h)

theorem DeltaPar.mkApps_args (H : List.Forall₂ (DeltaPar Γ) args args') :
    DeltaPar Γ (VExpr.mkApps f args) (VExpr.mkApps f args') := DeltaPar.mkApps .rfl H

omit [Params] in
theorem forall₂_getElem?_right {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {i : Nat} {y : β}, List.Forall₂ R l l' → l'[i]? = some y →
      ∃ x, l[i]? = some x ∧ R x y
  | _ :: _, _ :: _, 0, _, .cons h _, hy => by cases hy; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ t, hy => by
    simp only [List.getElem?_cons_succ] at hy ⊢; exact forall₂_getElem?_right t hy
  | [], [], _, _, .nil, hy => by cases hy

/-- Pointwise mirrors of developed arguments. -/
theorem DeltaPar.mirror_args (hΓ : OnCtx Γ (env.IsType univs))
    (ha : Γ ⊢ VExpr.mkApps f args : A) (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (ih : ∀ i (hi : i < args.length) (hi' : i < args'.length) {c A}, OnCtx Γ (env.IsType univs) →
      NormalEq₀ Γ c args[i] → Γ ⊢ args[i] : A → ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' args'[i])
    (hrel : List.Forall₂ (NormalEq₀ Γ) args₁ args) :
    ∃ Xs, List.Forall₂ (DeltaPar Γ) args₁ Xs ∧ List.Forall₂ (NormalEq₀ Γ) Xs args' := by
  have hS : List.Forall₂ (fun y z => ∀ {c A}, NormalEq₀ Γ c y → Γ ⊢ y : A →
      ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' z) args args' :=
    forall₂_of_getElem hlen fun i hi hi' _ _ h1 h2 => ih i hi hi' hΓ h1 h2
  exact List.Forall₂.exists_mid hrel hS fun x y z hy h1 h2 =>
    h2 h1 (schema_mkApps_arg_type hΓ ha hy).choose_spec


/-- The induction hypothesis of a mirror for developed arguments. -/
abbrev MirrorArgs (Γ : List VExpr) (args args' : List VExpr) : Prop :=
  ∀ i (hi : i < args.length) (hi' : i < args'.length) {c A}, OnCtx Γ (env.IsType univs) →
    NormalEq₀ Γ c args[i] → Γ ⊢ args[i] : A → ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' args'[i]

theorem DeltaPar.mirror_delta (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hr : NativeDeltaRule env univs recursorData Γ name ls args' rhs)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (VExpr.mkApps (.const name ls) args))
    (ha : Γ ⊢ VExpr.mkApps (.const name ls) args : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' rhs := by
  have hb := (DeltaPar.full (.delta hlen hargs hr)).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  rcases NormalEq₀.spine_expose hΓ .const hc hcT with hp | ⟨h', args₁, he, rfl, hrel⟩
  · exact ⟨c, .rfl, .proofIrrel hp hcT hb⟩
  obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const name ls₁ ∧ List.Forall₂ (· ≈ ·) ls₁ ls := by
    cases he with | const h => exact ⟨_, rfl, h⟩
  obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ ha hlen hargs ih hrel
  obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hcT
  obtain ⟨_, _, hw₁, _⟩ := hh₁.const_inv henv hΓ
  obtain ⟨rhs', hr', e'⟩ := hr.congr₀ hΓ hw₁
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => NormalEqF.symm hΓ h) (Lean4Lean.List.Forall₂.flip eXs))
  have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
  exact ⟨rhs', .delta hl' hx' hr', e'.symm hΓ⟩

theorem DeltaPar.mirror_quotDelta (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hr : QuotDeltaRule env univs Γ ls args' rhs)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (VExpr.mkApps (.const ``Quot.lift ls) args))
    (ha : Γ ⊢ VExpr.mkApps (.const ``Quot.lift ls) args : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' rhs := by
  have hb := (DeltaPar.full (.quotDelta hlen hargs hr)).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  rcases NormalEq₀.spine_expose hΓ .const hc hcT with hp | ⟨h', args₁, he, rfl, hrel⟩
  · exact ⟨c, .rfl, .proofIrrel hp hcT hb⟩
  obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const ``Quot.lift ls₁ ∧
      List.Forall₂ (· ≈ ·) ls₁ ls := by
    cases he with | const h => exact ⟨_, rfl, h⟩
  obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ ha hlen hargs ih hrel
  obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hcT
  obtain ⟨_, _, hw₁, _⟩ := hh₁.const_inv henv hΓ
  obtain ⟨rhs', hr', e'⟩ := hr.congr₀ hΓ hw₁
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => NormalEqF.symm hΓ h) (Lean4Lean.List.Forall₂.flip eXs))
  have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
  exact ⟨rhs', .quotDelta hl' hx' hr', e'.symm hΓ⟩

theorem DeltaPar.mirror_projIota (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' field := by
  have hstep := DeltaPar.projIota hlen hargs hl hs hi ht
  have hb := (DeltaPar.full hstep).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  obtain ⟨n, hc'⟩ := hc
  generalize hR : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = R at hc'
  cases hc' with
  | refl _ => subst hR; exact ⟨_, hstep, .refl hb⟩
  | proofIrrel l1 l2 l3 =>
    subst hR; exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full hstep).hasType hΓ l3)⟩
  | projDF l1 l2 =>
    cases hR
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm₁, _, _⟩ := hcT.proj_inv henv hΓ
    rcases NormalEq₀.spine_expose hΓ .const ⟨_, l2⟩ hm₁.hasType.2 with
      hp | ⟨h', args₁, he, hM, hrel⟩
    · have hA := HasType.proj_result_prop_of_major_proof henv hΓ hcT hp hm₁.hasType.2
      exact ⟨_, .rfl, .proofIrrel hA hcT hb⟩
    subst hM
    obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const info.ctorName ls₁ ∧
        List.Forall₂ (· ≈ ·) ls₁ ls := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ hm.hasType.2 hlen hargs ih hrel
    obtain ⟨X, hX, eX⟩ := forall₂_getElem?_right eXs hi
    have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
    have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls₁) args₁))
        (.proj family index (VExpr.mkApps (.const info.ctorName ls₁) Xs)) :=
      .proj (DeltaPar.mkApps_args hXs)
    have hT := (DeltaPar.full hcong).hasType hΓ hcT
    have hXT := hb.defeqU_l henv hΓ (NormalEqF.defeq hΓ eX).symm
    exact ⟨X, .projIota hl' hx' hl hT hX hXT, eX⟩
  | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR

theorem DeltaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' b := by
  induction H generalizing c A with
  | bvar | sort | const | elim => exact ⟨c, .rfl, hc⟩
  | @app _ f f' x x' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.app h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.app f x = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .app h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.app h1 h2)).hasType hΓ l3)⟩
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      obtain ⟨F, hF, eF⟩ := ih1 hΓ ⟨_, l5⟩ l2
      obtain ⟨X, hX, eX⟩ := ih2 hΓ ⟨_, l6⟩ l4
      exact ⟨_, .app hF hX, .appDF ((DeltaPar.full hF).hasType hΓ l1)
        ((DeltaPar.full h1).hasType hΓ l2) ((DeltaPar.full hX).hasType hΓ l3)
        ((DeltaPar.full h2).hasType hΓ l4) eF eX⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF => cases hR
  | @proj _ m m' family index h1 ih =>
    have hb := (DeltaPar.full (.proj h1)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.proj family index m = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .proj h1, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.proj h1)).hasType hΓ l3)⟩
    | projDF l1 l2 =>
      cases hR
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, hM, eM⟩ := ih hΓ ⟨_, l2⟩ hm.hasType.2
      exact ⟨_, .proj hM, .projDF ((DeltaPar.full (.proj hM)).hasType hΓ l1) eM⟩
    | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR
  | @lam _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.lam h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.lam D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .lam h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.lam h1 h2)).hasType hΓ l3)⟩
    | lamDF l1 l2 l3 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have l3' := l3.defeqDFC hΓ (.succ .zero l2)
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l3'⟩ ht
      have hDD₁ := l2.symm.trans l1
      have ht₁ := ((NormalEqN.defeq hΓ' l3').of_r henv hΓ' ht).hasType.1
      refine ⟨_, .lam .rfl (hT.defeqDFC hΓ (.succ .zero hDD₁) ht₁), ?_⟩
      have hD2 := l2.hasType.2
      have hDD' := (DeltaPar.full h1).defeq hΓ hD2
      exact .lamDF hDD₁ hDD' eT
    | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hR
  | @forallE _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.forallE h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.forallE D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .forallE h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.forallE h1 h2)).hasType hΓ l3)⟩
    | forallEDF l1 l2 l3 l4 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.forallE_inv henv
      obtain ⟨D₁', hD₁, eD⟩ := ih1 hΓ ⟨_, l2⟩ hD
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have W' := l1.transU_l henv hΓ (NormalEqN.defeq hΓ l2)
      have l4' := l4.defeqDFC hΓ (.succ .zero W')
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l4'⟩ ht
      have l3'' := l3.defeqDFC henv (.succ .zero W')
      have hA₁ := l1.hasType.2
      have hD₁T := (DeltaPar.full hD₁).defeq hΓ hA₁
      refine ⟨_, .forallE hD₁ (hT.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''), ?_⟩
      have hT1 := (DeltaPar.full hT).hasType hΓ' l3''
      exact .forallEDF (W'.symm.trans (l1.trans hD₁T)) eD hT1 eT
    | sortDF | constDF | elimDF | appDF | projDF | lamDF => cases hR
  | delta hlen hargs hr ih => exact DeltaPar.mirror_delta hΓ hlen hargs hr ih hc ha
  | quotDelta hlen hargs hr ih => exact DeltaPar.mirror_quotDelta hΓ hlen hargs hr ih hc ha
  | projIota hlen hargs hl hs hi ht ih =>
    exact DeltaPar.mirror_projIota hΓ hlen hargs hl hs hi ht ih hc ha

end DeltaMirror

section Levels

/-- The untyped level relations. -/
def LevelStep (Γ : List VExpr) : Nat → VExpr → VExpr → Prop
  | 0 => NormalEq₀ Γ
  | 1 => ParRed Γ
  | 2 => DeltaPar Γ
  | 3 => EtaPar Γ
  | _ + 4 => fun _ _ => False

/-- Some step below level `n`. -/
def Below (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop := ∃ k, k < n ∧ LevelStep Γ k a b

/-- The level relations restricted to typed sources, for the abstract criterion. -/
def LevelRel (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop :=
  (∃ A, Γ ⊢ a : A) ∧ LevelStep Γ n a b

theorem LevelStep.full (hΓ : OnCtx Γ (env.IsType univs)) (hn : 0 < n)
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : FullReduction Γ a b := by
  match n, H with
  | 1, H => exact .tail .rfl (.core H)
  | 2, H => exact DeltaPar.full H
  | 3, H => exact EtaPar.full hΓ H ha

theorem LevelStep.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  match n, H with
  | 0, H => exact ((NormalEqF.defeq hΓ H).of_l henv hΓ ha).hasType.2
  | n + 1, H => exact (LevelStep.full hΓ (Nat.succ_pos _) H ha).hasType hΓ ha

theorem Below.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  induction H with
  | rfl => exact ha
  | tail _ h ih => obtain ⟨_, _, h⟩ := h; exact h.hasType hΓ ih

theorem Below.loStar (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    Levelled.LoStar (LevelRel Γ) n a b := by
  induction H with
  | rfl => exact .rfl
  | tail h₁ h ih =>
    obtain ⟨k, hk, h⟩ := h
    exact .tail ih ⟨k, hk, ⟨_, Below.hasType hΓ h₁ ha⟩, h⟩

theorem Below.ofLoStar (H : Levelled.LoStar (LevelRel Γ) n a b) :
    ReflTransGen (Below Γ n) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => obtain ⟨k, hk, _, h⟩ := h; exact .tail ih ⟨k, hk, h⟩

theorem Below.mono (h : n ≤ m) (H : ReflTransGen (Below Γ n) a b) :
    ReflTransGen (Below Γ m) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h' ih => obtain ⟨k, hk, h'⟩ := h'; exact .tail ih ⟨k, by omega, h'⟩

theorem Below.single (hk : k < n) (H : LevelStep Γ k a b) : ReflTransGen (Below Γ n) a b :=
  .tail .rfl ⟨k, hk, H⟩

/-- Pushing the normal equalities of a levelled reduction to its end. -/
theorem Below.full (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    ∃ a', FullReduction Γ a a' ∧ NormalEq Γ a' b := by
  induction H with
  | rfl => exact ⟨_, .rfl, .refl ha⟩
  | tail h₁ h ih =>
    obtain ⟨a', hr, he⟩ := ih
    obtain ⟨k, _, h⟩ := h
    have hm := Below.hasType hΓ h₁ ha
    cases k with
    | zero => exact ⟨a', hr, he.trans hΓ (NormalEqF.toNormalEq h)⟩
    | succ k =>
      obtain ⟨out, h1, h2⟩ := he.fullReduction hΓ (h.full hΓ (Nat.succ_pos _) hm)
      exact ⟨out, hr.trans h1, h2⟩

/-! ### Local diagrams -/

theorem levelZero_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (LevelRel Γ 0) := by
  have key : ∀ {a b}, ReflTransGen (LevelRel Γ 0) a b → a = b ∨ NormalEq₀ Γ a b := by
    intro a b H
    induction H with
    | rfl => exact .inl rfl
    | tail _ h ih =>
      obtain ⟨_, h⟩ := h
      rcases ih with rfl | ih
      · exact .inr h
      · exact .inr (ih.trans hΓ h)
  intro a b c hb hc
  rcases key hb with rfl | hb'
  · exact ⟨c, hc, .rfl⟩
  have ⟨_, hab⟩ := NormalEqF.defeq hΓ hb'
  rcases key hc with rfl | hc'
  · exact ⟨b, .rfl, .tail .rfl ⟨⟨_, hab.hasType.1⟩, hb'⟩⟩
  · exact ⟨c, .tail .rfl ⟨⟨_, hab.hasType.2⟩, (hb'.symm hΓ).trans hΓ hc'⟩, .rfl⟩

theorem ParRed.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : ParRed Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' b := sorry



theorem DeltaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, DeltaPar Γ b b₁ ∧ ReflTransGen (Below Γ 2) b₁ d) ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) := sorry

theorem DeltaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 2) b d ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) := sorry

theorem EtaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : EtaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, EtaPar Γ b b₁ ∧ ReflTransGen (Below Γ 3) b₁ d) ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

theorem EtaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

theorem EtaPar.deltaPar_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

/-! ### Assembly -/

theorem levelled_mac (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.Mac (LevelRel Γ) n b d :=
  ⟨b, b₁, .rfl, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_optLo (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.OptLo (LevelRel Γ) n b d :=
  ⟨b₁, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_peak₁ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → LevelRel Γ n a c →
      ∃ d, Levelled.Mac (LevelRel Γ) n b d ∧ Levelled.Mac (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨_, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  match n, H1, H2 with
  | 1, H1, H2 =>
    obtain ⟨b₁, c₁, h1, h2, h3⟩ := ParRed.church_rosser (η := false) hΓ ha H1 H2
    exact ⟨b₁, levelled_mac hΓ hb (n := 1) h1 .rfl,
      levelled_mac hΓ hc (n := 1) h2 (Below.single (k := 0) (by decide) (h3.symm hΓ))⟩
  | 2, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := DeltaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_mac hΓ hb (n := 2) h1 h2, levelled_mac hΓ hc (n := 2) h3 h4⟩
  | 3, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := EtaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_mac hΓ hb (n := 3) h1 h2, levelled_mac hΓ hc (n := 3) h3 h4⟩
  | n + 4, H1, _ => exact H1.elim

theorem levelled_peak₂ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → Levelled.Lo (LevelRel Γ) n a c →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨k, hk, _, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  have mirror : ∀ {c'}, LevelStep Γ n c c' → NormalEq₀ Γ c' b →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d :=
    fun h1 h2 => ⟨b, .rfl, levelled_optLo hΓ hc h1 (Below.single (k := 0) hn h2)⟩
  match n, k, hk, H1, H2 with
  | 1, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 3, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := DeltaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 2) h2 h3⟩
  | 3, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | 3, 2, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.deltaPar_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | n + 4, _, _, H1, _ => exact H1.elim

theorem levelled_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (Levelled.Lo (LevelRel Γ) 4) :=
  Levelled.joinable (levelZero_joinable hΓ) (levelled_peak₁ hΓ) (levelled_peak₂ hΓ) 3

end Levels

section Strip

/-- Union of the three reducing level relations. -/
def UpStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  ParRed Γ a b ∨ DeltaPar Γ a b ∨ EtaPar Γ a b

theorem UpStep.below (H : ReflTransGen (UpStep Γ) a b) : ReflTransGen (Below Γ 4) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih =>
    refine .tail ih ?_
    rcases h with h | h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩

theorem UpStep.congr {f : VExpr → VExpr} {g : List VExpr → List VExpr}
    (hf : ∀ {a b}, UpStep (g Γ) a b → UpStep Γ (f a) (f b))
    (H : ReflTransGen (UpStep (g Γ)) a b) : ReflTransGen (UpStep Γ) (f a) (f b) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (hf h)

theorem FullStep.upStep (H : FullStep Γ e e') : ReflTransGen (UpStep Γ) e e' := by
  induction H with
  | core h => exact .tail .rfl (.inl h)
  | delta h => exact .tail .rfl (.inr (.inl (.delta rfl (fun _ _ _ => .rfl) h)))
  | quotDelta h => exact .tail .rfl (.inr (.inl (.quotDelta rfl (fun _ _ _ => .rfl) h)))
  | projIota hl hs hi ht =>
    exact .tail .rfl (.inr (.inl (.projIota rfl (fun _ _ _ => .rfl) hl hs hi ht)))
  | structEta hl hp hi hs ht =>
    exact .tail .rfl (.inr (.inr (.structEta .rfl rfl (fun _ _ _ => .rfl) hl hp hi hs ht)))
  | funEta ht => exact .tail .rfl (.inr (.inr (.funEta .rfl .rfl ht)))
  | @app _ f f' a a' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := id) (f := (VExpr.app · a)) ?_ ih1).trans
      (UpStep.congr (g := id) (f := VExpr.app f') ?_ ih2)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app h .rfl)
        | exact .inr (.inl (.app h .rfl))
        | exact .inr (.inr (.app h .rfl))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app .rfl h)
        | exact .inr (.inl (.app .rfl h))
        | exact .inr (.inr (.app .rfl h))
  | proj _ ih =>
    refine UpStep.congr (g := id) ?_ ih
    rintro _ _ (h | h | h) <;> first
      | exact .inl (.proj h)
      | exact .inr (.inl (.proj h))
      | exact .inr (.inr (.proj h))
  | @lam _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.lam d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.lam · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam .rfl h)
        | exact .inr (.inl (.lam .rfl h))
        | exact .inr (.inr (.lam .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam h .rfl)
        | exact .inr (.inl (.lam h .rfl))
        | exact .inr (.inr (.lam h .rfl))
  | @forallE _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.forallE d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.forallE · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE .rfl h)
        | exact .inr (.inl (.forallE .rfl h))
        | exact .inr (.inr (.forallE .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE h .rfl)
        | exact .inr (.inl (.forallE h .rfl))
        | exact .inr (.inr (.forallE h .rfl))

theorem FullReduction.below (H : FullReduction Γ e e') : ReflTransGen (Below Γ 4) e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.trans (UpStep.below h.upStep)

/-- The required global strip property: one full step commutes with an entire
finite development, up to normal equality. -/
theorem FullStep.strip (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (step : FullStep Γ source left) (development : FullReduction Γ source right) :
    ∃ left' right', FullReduction Γ left left' ∧ FullReduction Γ right right' ∧
      NormalEq Γ left' right' := by
  have hl := UpStep.below step.upStep
  have hr := development.below
  obtain ⟨d, h1, h2⟩ := levelled_joinable hΓ source left right
    (Below.loStar hΓ hl ht) (Below.loStar hΓ hr ht)
  obtain ⟨l', a1, a2⟩ := Below.full hΓ (Below.ofLoStar h1) (step.hasType hΓ ht)
  obtain ⟨r', b1, b2⟩ := Below.full hΓ (Below.ofLoStar h2) (development.hasType hΓ ht)
  exact ⟨l', r', a1, b1, a2.trans hΓ (b2.symm hΓ)⟩

/-- Full confluence follows from the global strip property and transport
through normal equality. -/
theorem FullReduction.church_rosser (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (left : FullReduction Γ source l) (right : FullReduction Γ source r) :
    ∃ l' r', FullReduction Γ l l' ∧ FullReduction Γ r r' ∧ NormalEq Γ l' r' := by
  induction left with
  | rfl => exact ⟨_, _, right, .rfl, .refl (right.hasType hΓ ht)⟩
  | tail before step ih =>
    obtain ⟨l', r', hl, hr, heq⟩ := ih
    obtain ⟨l'', r'', hl'', hr'', heq'⟩ := step.strip hΓ (FullReduction.hasType hΓ before ht) hl
    obtain ⟨out, hout, heqOut⟩ := (heq.symm hΓ).fullReduction hΓ hr''
    exact ⟨l'', out, hl'', hr.trans hout, heq'.trans hΓ (heqOut.symm hΓ)⟩

end Strip

end Lean4Lean.VEnv
