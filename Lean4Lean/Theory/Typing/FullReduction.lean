import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.NativePrefixWeakening
import Lean4Lean.Theory.Typing.NativePrefixLevelTyping
import Lean4Lean.Theory.Typing.NativePrefixSubstitution
import Lean4Lean.Theory.Typing.QuotPrefixNormalCongruence
import Lean4Lean.Theory.Typing.QuotPrefixRenaming
import Lean4Lean.Theory.Typing.NativePrefixSpecialization
import Lean4Lean.Theory.Typing.ProjectionIndexBound
import Lean4Lean.Theory.Typing.ProjectionProofResult

/-! The native/schema parallel calculus is the core of this presentation.
Checked singleton and quotient prefixes extend it with declaration-generated
computation. Typed function and structure eta expansions allow computation
beneath extensional equalities. Different prefix lengths can require multiple
beta steps to join; the confluence obligation uses a global strip property.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

/-- Concrete reduction, closed under syntax. The delta branch contains only
the deterministic finite program and its actual declaration replay checks. -/
inductive FullStep : List VExpr → VExpr → VExpr → Prop where
  | core : ParRed Γ source target → FullStep Γ source target
  | delta : NativeDeltaRule env univs recursorData Γ name levels arguments rhs →
      FullStep Γ (VExpr.mkApps (.const name levels) arguments) rhs
  | quotDelta : QuotDeltaRule env univs Γ levels arguments rhs →
      FullStep Γ (VExpr.mkApps (.const ``Quot.lift levels) arguments) rhs
  | projIota : env.projections family info →
      HasType env univs Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) fieldType →
      args[info.nparams + index]? = some field → HasType env univs Γ field fieldType →
      FullStep Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) field
  | structEta : env.projections family info → params.length = info.nparams → info.nindices = 0 →
      HasType env univs Γ e (VExpr.mkApps (.const family levels) params) →
      HasType env univs Γ
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
        (VExpr.mkApps (.const family levels) params) →
      FullStep Γ e
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
  /-- Function eta expansion is an actual reduction in the full presentation.
  This lets structure and prefix computation proceed beneath eta binders. -/
  | funEta : HasType env univs Γ e (.forallE domain body) →
      FullStep Γ e (.lam domain (.app e.lift (.bvar 0)))
  | app : FullStep Γ fn fn' → FullStep Γ arg arg' →
      FullStep Γ (.app fn arg) (.app fn' arg')
  | proj : FullStep Γ major major' →
      FullStep Γ (.proj family index major) (.proj family index major')
  | lam : FullStep Γ domain domain' → FullStep (domain :: Γ) body body' →
      FullStep Γ (.lam domain body) (.lam domain' body')
  | forallE : FullStep Γ domain domain' → FullStep (domain :: Γ) body body' →
      FullStep Γ (.forallE domain body) (.forallE domain' body')

protected theorem FullStep.rfl : FullStep Γ e e := .core .rfl

theorem FullStep.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullStep Γ e e') (he : HasType env univs Γ e A) :
    IsDefEq env univs Γ e e' A := by
  induction H generalizing A with
  | core h => exact h.defeq hΓ he
  | delta h => exact (h.defeq henv hΓ).of_l henv hΓ he
  | quotDelta h => exact (h.defeq henv hΓ).of_l henv hΓ he
  | projIota hl hs hi ht => exact .trans_l henv hΓ he (.projIota hl hs hi ht)
  | structEta hl hp hi hs ht => exact .trans_l henv hΓ he (IsDefEq.structEta hl hp hi hs ht).symm
  | funEta ht => exact .trans_l henv hΓ he (IsDefEq.eta ht).symm
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he (.appDF (ih1 hΓ h1) (ih2 hΓ h2))
  | proj _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
    have majorEq := ihMajor hΓ hmajor.hasType.2
    have projected := IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hmajor (hmajor.trans majorEq) hclosed hguard
    have ⟨_, typeToA⟩ := projected.hasType.1.uniq henv hΓ he
    exact .defeqDF typeToA projected
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact .trans_l henv hΓ he (.lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2))
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he (.forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2))

theorem FullStep.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullStep Γ e e') (he : HasType env univs Γ e A) :
    HasType env univs Γ e' A := (H.defeq hΓ he).hasType.2

theorem FullStep.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : FullStep Γ₁ e e') (he : HasType env univs Γ₁ e A) : FullStep Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | core h => exact .core (h.defeqDFC hΓ W he)
  | delta h => exact .delta (h.defeqDFC henv hΓ W)
  | quotDelta h => exact .quotDelta (h.defeqDFC henv hΓ W)
  | projIota hl hs hi ht => exact .projIota hl (hs.defeqDFC henv W) hi (ht.defeqDFC henv W)
  | structEta hl hp hi hs ht => exact .structEta hl hp hi (hs.defeqDFC henv W) (ht.defeqDFC henv W)
  | funEta ht => exact .funEta (ht.defeqDFC henv W)
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

theorem FullStep.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullStep Γ e e') :
    FullStep Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | core h => exact .core (h.weakN W)
  | delta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .delta (h.weakN henv W)
  | quotDelta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .quotDelta (h.weakN henv W)
  | projIota h1 hs h3 ht =>
    have hs' := hs.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at hs' ⊢
    exact .projIota h1 hs' (by simp [h3]) (ht.weakN henv W)
  | structEta h1 h2 h3 hs ht =>
    have hs' := hs.weakN henv W
    have ht' := ht.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta h1 (by simpa using h2) h3 hs' ht'
  | funEta ht =>
    simpa only [VExpr.liftN, ← VExpr.lift_liftN', liftVar_zero] using
      (FullStep.funEta (ht.weakN henv W))
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

def FullReduction (Γ : List VExpr) : VExpr → VExpr → Prop :=
  ReflTransGen (FullStep Γ)

theorem ParRedS.full (H : ParRedS Γ e e') : FullReduction Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.core h)

theorem FullReduction.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullReduction Γ e e') (he : HasType env univs Γ e A) :
    HasType env univs Γ e' A := by
  induction H with
  | rfl => exact he
  | tail _ h ih => exact h.hasType hΓ ih

theorem FullReduction.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullReduction Γ e e') (he : HasType env univs Γ e A) :
    IsDefEq env univs Γ e e' A := by
  induction H with
  | rfl => exact he
  | tail _ h ih => exact ih.trans (h.defeq hΓ ih.hasType.2)

theorem FullReduction.app (hf : FullReduction Γ f f') (ha : FullReduction Γ a a') :
    FullReduction Γ (.app f a) (.app f' a') := by
  have right : FullReduction Γ (.app f a) (.app f a') := by
    induction ha with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.app .rfl h)
  refine right.trans ?_
  induction hf with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.app h .rfl)

theorem FullReduction.mkApps (head : FullReduction Γ fn fn')
    (args : List.Forall₂ (FullReduction Γ) arguments arguments') :
    FullReduction Γ (mkApps fn arguments) (mkApps fn' arguments') := by
  induction args generalizing fn fn' with
  | nil => exact head
  | cons ha _ ih => exact ih (head.app ha)

theorem FullReduction.lam (hd : FullReduction Γ d d')
    (hb : FullReduction (d :: Γ) b b') : FullReduction Γ (.lam d b) (.lam d' b') := by
  have body : FullReduction Γ (.lam d b) (.lam d b') := by
    induction hb with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.lam .rfl h)
  refine body.trans ?_
  induction hd with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.lam h .rfl)

theorem FullReduction.proj (H : FullReduction Γ e e') :
    FullReduction Γ (.proj family index e) (.proj family index e') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.proj h)

theorem FullReduction.forallE (hd : FullReduction Γ d d')
    (hb : FullReduction (d :: Γ) b b') : FullReduction Γ (.forallE d b) (.forallE d' b') := by
  have body : FullReduction Γ (.forallE d b) (.forallE d b') := by
    induction hb with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.forallE .rfl h)
  refine body.trans ?_
  induction hd with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.forallE h .rfl)

theorem FullReduction.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : FullReduction Γ₁ e e') (he : HasType env univs Γ₁ e A) : FullReduction Γ₂ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail before h ih => exact .tail ih (h.defeqDFC hΓ W (FullReduction.hasType (W.isType' hΓ) before he))

theorem FullReduction.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullReduction Γ e e') :
    FullReduction Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (h.weakN W)

theorem FullStep.instN (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env univs Γ₀ arg A) (H : FullStep Γ₁ e e') :
    FullStep Γ (e.inst arg k) (e'.inst arg k) := by
  induction H generalizing Γ k with
  | core h => exact .core (ParRed.instN (H₀ := .rfl) (H₀' := harg) W h)
  | delta h =>
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .delta (h.instN henv W harg)
  | quotDelta h =>
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .quotDelta (h.instN henv W harg)
  | projIota h1 hs h3 ht =>
    have hs' := hs.instN henv W harg
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota h1 hs' (by simp [h3]) (ht.instN henv W harg)
  | structEta h1 h2 h3 hs ht =>
    have hs' := hs.instN henv W harg
    have ht' := ht.instN henv W harg
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta h1 (by simpa using h2) h3 hs' ht'
  | funEta ht =>
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, instVar, if_pos (Nat.zero_lt_succ k)] using
      (FullStep.funEta (ht.instN henv W harg))
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

theorem FullReduction.instN (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env univs Γ₀ arg A) (H : FullReduction Γ₁ e e') :
    FullReduction Γ (e.inst arg k) (e'.inst arg k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (h.instN W harg)


/-- A reduction of the substituted argument is replayed at every occurrence,
including under dependent binders. The finite structural closure handles
any number of copies of that argument. -/
theorem FullReduction.instN_r (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (H : FullReduction Γ₀ arg arg') (e : VExpr) :
    FullReduction Γ (e.inst arg k) (e.inst arg' k) := by
  induction e generalizing Γ₁ Γ k with
  | bvar i =>
    dsimp only [VExpr.inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H
      | succ i => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ i => exact (ih i).weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ _ _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

/-- Simultaneous development of a term and its typed substituend. -/
theorem FullReduction.instN_both (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env univs Γ₀ arg A)
    (H : FullReduction Γ₁ e e') (Harg : FullReduction Γ₀ arg arg') :
    FullReduction Γ (e.inst arg k) (e'.inst arg' k) :=
  (H.instN W harg).trans (Harg.instN_r W e')


/-- The beta contractum and a developed lambda application meet after
substituting the developed argument in the developed body. -/
theorem FullReduction.beta_development
    (harg : HasType env univs Γ arg domain)
    (hbody : FullReduction (domain :: Γ) body body')
    (hargument : FullReduction Γ arg arg') :
    FullReduction Γ (body.inst arg) (body'.inst arg') ∧
      FullReduction Γ (.app (.lam domain' body') arg') (body'.inst arg') :=
  ⟨hbody.instN_both .zero harg hargument, .tail .rfl (.core (.beta .rfl .rfl))⟩

/-- Adjacent aligned prefixes have the expected beta overlap. The earlier
unfolding, supplied with the next argument, computes to the later unfolding's
exact generated right-hand side. -/
theorem FullReduction.delta_prefix_overlap
    (early : NativeDeltaRule env univs recursorData Γ name levels args earlyRhs)
    (late : NativeDeltaRule env univs recursorData Γ name levels (args ++ [arg]) lateRhs) :
    FullReduction Γ (.app earlyRhs arg) lateRhs := by
  cases early with
  | intro hl _ _ _ _ _ hg replay =>
    cases late with
    | intro hl' _ _ _ _ _ hg' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      obtain ⟨domain, body, hearly, hlate⟩ :=
        InductiveSignature.NativeRecursorData.prefixProgram_supply_one hg hg'
          (replay.templateScope henv).2.1
      rw [hearly, ← hlate]
      exact .tail .rfl (.core (.beta .rfl .rfl))

/-- Projection computation commutes with an arbitrary finite development
of its constructor argument spine. The selected field follows its own
finite development, and the developed constructor projects to that field. -/
theorem FullReduction.projIota_spine (hΓ : OnCtx Γ (env.IsType univs))
    (hinfo : env.projections family info)
    (hproj : HasType env univs Γ
      (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) fieldType)
    (hfield : args[info.nparams + index]? = some field)
    (ht : HasType env univs Γ field fieldType)
    (hargs : List.Forall₂ (FullReduction Γ) args args') :
    ∃ field', args'[info.nparams + index]? = some field' ∧
      FullReduction Γ field field' ∧ FullReduction Γ
        (.proj family index (VExpr.mkApps (.const info.ctorName levels) args')) field' := by
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hfield
  have hi' : info.nparams + index < args'.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargs]
    exact hi
  have hred := Lean4Lean.List.Forall₂.getElem_of hargs (info.nparams + index) hi hi'
  rw [heq] at hred
  have hprojRed := (FullReduction.mkApps (fn := .const info.ctorName levels) .rfl hargs).proj (family := family) (index := index)
  have hget : args'[info.nparams + index]? = some args'[info.nparams + index] := by simp [hi']
  exact ⟨_, hget, hred, .tail .rfl
    (.projIota hinfo (hprojRed.hasType hΓ hproj) hget (hred.hasType hΓ ht))⟩

/-- Projecting an eta-expanded structure computes back to the original
projection, giving the concrete projection/structure-eta overlap. -/
theorem FullReduction.proj_structEta_cancel (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hindex : index < info.numFields)
    (hs : HasType env univs Γ major (VExpr.mkApps (.const family levels) params))
    (hc : HasType env univs Γ
      (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun i => .proj family i major))
      (VExpr.mkApps (.const family levels) params))
    (ht : HasType env univs Γ (.proj family index major) fieldType) :
    FullReduction Γ
      (.proj family index (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun i => .proj family i major)))
      (.proj family index major) := by
  have hred : FullStep Γ (.proj family index major)
      (.proj family index (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun i => .proj family i major))) :=
    .proj (.structEta hl hp hi hs hc)
  have hget : (params ++ (List.range info.numFields).map fun i => VExpr.proj family i major)[info.nparams + index]? = some (.proj family index major) := by
    rw [List.getElem?_append_right (by omega)]
    simp [hp, hindex]
  exact .tail .rfl (.projIota hl (hred.hasType hΓ ht) hget ht)

private theorem eta_arguments_wf (hΓ : OnCtx Γ (env.IsType univs))
    (H : VExpr.WF env univs Γ (mkApps fn args)) :
    ∀ arg ∈ args, VExpr.WF env univs Γ arg := by
  induction args generalizing fn with
  | nil => simp
  | cons a args ih =>
    have hf := VExpr.WF.of_mkApps (f := fn.app a) (args := args) henv.ordered hΓ H
    obtain ⟨_, _, _, ha⟩ := hf.app_inv henv.ordered hΓ
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact ih H arg hm

/-- Structure expansion respects normal equality of the major. All field
projections are taken at the same concrete registry entry and parameter spine. -/
theorem NormalEq.fullStep_structEta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right)
    (hl : env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0)
    (hs : HasType env univs Γ right (mkApps (.const family levels) params))
    (ht : HasType env univs Γ
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj family index right))
      (mkApps (.const family levels) params)) :
    ∃ output, FullReduction Γ left output ∧
      NormalEq Γ output
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index right)) := by
  have hsleft := ((H.defeq hΓ).of_r henv hΓ hs).hasType.1
  have hargs := eta_arguments_wf hΓ ⟨_, ht⟩
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  have hparams : List.Forall₂ (NormalEq Γ) params params := by
    apply List.forall₂_of_getElem rfl
    intro i hi hi'
    obtain ⟨_, h⟩ := hargs _ (List.mem_append_left _ (List.getElem_mem hi))
    exact .refl h
  have hfields : List.Forall₂ (NormalEq Γ)
      ((List.range info.numFields).map fun index => .proj family index right)
      ((List.range info.numFields).map fun index => .proj family index left) := by
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    have himem : i ∈ List.range info.numFields := by simpa using hi
    obtain ⟨_, h⟩ := hargs _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, himem, rfl⟩))
    simpa only [List.getElem_map, List.getElem_range] using
      (NormalEq.projDF h (H.symm hΓ))
  have hctorEq := NormalEq.mkApps_spine hΓ (.refl hhead) (case_forall₂_append hparams hfields) ht
  have htleft := ((hctorEq.defeq hΓ).of_l henv hΓ ht).hasType.2
  exact ⟨_, .tail .rfl (.structEta hl hp hi hsleft htleft), hctorEq.symm hΓ⟩


/-- A proof-valued computation is compatible with every normal equality,
regardless of how the right-hand proof exposes its computational head. -/
theorem NormalEq.fullStep_proof (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (R : FullStep Γ right result)
    (ht : HasType env univs Γ right proposition)
    (hp : HasType env univs Γ proposition (.sort .zero)) :
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result := by
  have hl := ht.defeqU_l henv hΓ (H.defeq hΓ).symm
  exact ⟨_, .rfl, .proofIrrel hp hl (R.hasType hΓ ht)⟩

/-- The added function expansion is already one of the structural normal
eta equalities, so it is compatible with every normal-equality derivation. -/
theorem NormalEq.fullStep_funEta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (ht : HasType env univs Γ right (.forallE domain body)) :
    ∃ output, FullReduction Γ left output ∧
      NormalEq Γ output (.lam domain (.app right.lift (.bvar 0))) := by
  exact ⟨_, .rfl, H.trans hΓ (.etaR ht (.refl (.app (ht.weak henv) (.bvar .zero))))⟩

/-- Once normal equality has exposed the constructor argument spines,
projection computation selects the same pair of normally equal fields. -/
theorem NormalEq.fullStep_projIota_spine (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info)
    (hproj : HasType env univs Γ
      (.proj family index (mkApps (.const info.ctorName levels) args)) fieldType)
    (hargs : List.Forall₂ (NormalEq Γ) args args')
    (hfield : args'[info.nparams + index]? = some field')
    (ht : HasType env univs Γ field' fieldType) :
    ∃ field, FullReduction Γ
      (.proj family index (mkApps (.const info.ctorName levels) args)) field ∧
      NormalEq Γ field field' := by
  obtain ⟨hi', heq⟩ := List.getElem?_eq_some_iff.mp hfield
  have hi : info.nparams + index < args.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hargs]
    exact hi'
  have hnormal := Lean4Lean.List.Forall₂.getElem_of hargs (info.nparams + index) hi hi'
  rw [heq] at hnormal
  have hget : args[info.nparams + index]? = some args[info.nparams + index] := by simp [hi]
  have hleft := ht.defeqU_l henv hΓ (hnormal.defeq hΓ).symm
  exact ⟨_, .tail .rfl (.projIota hl hproj hget hleft), hnormal⟩

omit [Params] in
private theorem mkApps_ne_proj {fn : VExpr}
    (hf : ∀ n i e, fn ≠ .proj n i e) (args : List VExpr) :
    mkApps fn args ≠ .proj family index major := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

omit [Params] in
private theorem mkApps_ne_elim {fn : VExpr}
    (hf : ∀ n i levels, fn ≠ .elim n i levels) (args : List VExpr) :
    mkApps fn args ≠ .elim block owner levels := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

omit [Params] in
private theorem const_eq_mkApps (h : VExpr.const c ls = VExpr.mkApps (.const name levels) args) :
    c = name ∧ ls = levels ∧ args = [] := by
  have hh := congrArg VExpr.getAppFnArgs h
  rw [InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
  change (VExpr.const c ls, ([] : List VExpr)) = (VExpr.const name levels, args) at hh
  cases hh
  exact ⟨rfl, rfl, rfl⟩

theorem NormalEq.fullStep_delta_levels (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeDeltaRule env univs recursorData Γ name levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF univs)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels univs) args args') :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const name levels') args') rhs' ∧ NormalEq Γ rhs' rhs := by
  obtain ⟨rhs', hh, hr⟩ := H.congr_levels henv hΓ hw' he ha
  obtain ⟨type, hd⟩ := H.defeq henv hΓ
  exact ⟨_, .tail .rfl (.delta hh), (NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hr) hd.hasType.2).symm hΓ⟩

theorem NormalEq.fullStep_quotDelta_levels (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotDeltaRule env univs Γ levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF univs)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels univs) args args') :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const ``Quot.lift levels') args') rhs' ∧ NormalEq Γ rhs' rhs := by
  obtain ⟨rhs', hh, hr⟩ := H.congr_levels henv hΓ hw' he ha
  obtain ⟨type, hd⟩ := H.defeq henv hΓ
  exact ⟨_, .tail .rfl (.quotDelta hh), (NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hr) hd.hasType.2).symm hΓ⟩

/-- Once the application heads agree, actual native replay transports every
normally related supplied argument, including dependent indices and captures. -/
theorem NormalEq.fullStep_delta_args (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeDeltaRule env univs recursorData Γ name levels args rhs)
    (ha : List.Forall₂ (NormalEq Γ) args' args) :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const name levels) args') rhs' ∧ NormalEq Γ rhs' rhs := by
  have hback := Lean4Lean.List.Forall₂.imp (fun _ _ (h : NormalEq Γ _ _) => h.symm hΓ)
    (Lean4Lean.List.Forall₂.flip ha)
  obtain ⟨rhs', hr, hn⟩ := H.congr_normal hΓ hback
  exact ⟨rhs', .tail .rfl (.delta hr), hn.symm hΓ⟩

theorem NormalEq.fullStep_quotDelta_args (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotDeltaRule env univs Γ levels args rhs)
    (ha : List.Forall₂ (NormalEq Γ) args' args) :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const ``Quot.lift levels) args') rhs' ∧ NormalEq Γ rhs' rhs := by
  have hback := Lean4Lean.List.Forall₂.imp (fun _ _ (h : NormalEq Γ _ _) => h.symm hΓ)
    (Lean4Lean.List.Forall₂.flip ha)
  obtain ⟨rhs', hr, hn⟩ := H.congr_normal hΓ hback
  exact ⟨rhs', .tail .rfl (.quotDelta hr), hn.symm hΓ⟩

section NormalParallel

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

omit [Params] in
private theorem mkApps_concat (f : VExpr) (l : List VExpr) (b : VExpr) :
    VExpr.mkApps f (l ++ [b]) = .app (VExpr.mkApps f l) b := by
  simp [VExpr.mkApps, List.foldl_append]

omit [Params] in
private theorem eq_nil_or_snoc (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simpa using h⟩

omit [Params] in
private theorem mkApps_app_isApp (g c : VExpr) (bs : List VExpr) :
    ∃ f a, VExpr.mkApps (.app g c) bs = .app f a := by
  rcases eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, mkApps_concat ..⟩

omit [Params] in
private theorem lift_beta_spine (A e a : VExpr) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (.app (.lam A e) a) bs).lift (.bvar 0) =
      VExpr.mkApps (.app (.lam A.lift (e.liftN 1 1)) a.lift)
        (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [mkApps_concat]; simp [VExpr.liftN]

omit [Params] in
private theorem lift_beta_spine_result (e a : VExpr) (bs : List VExpr) :
    VExpr.mkApps ((e.liftN 1 1).inst a.lift) (bs.map VExpr.lift ++ [.bvar 0]) =
      VExpr.app (VExpr.mkApps (e.inst a) bs).lift (.bvar 0) := by
  rw [mkApps_concat, ← lift_inst_hi]; simp

private theorem FullReduction.beta_spine (A e a : VExpr) (bs : List VExpr) :
    FullReduction Γ (VExpr.mkApps (.app (.lam A e) a) bs) (VExpr.mkApps (e.inst a) bs) := by
  refine FullReduction.mkApps (.tail .rfl (.core (.beta .rfl .rfl))) ?_
  induction bs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .rfl ih

/-- Beta computation through normal equality, by strong induction on the
comparison bound. The first component handles a left side normally equal to
an applied redex spine (eta and extensionality steps add a fresh variable to
the spine); the second handles a function normally equal to a lambda. Eta
expansion of the left side is a `FullStep.funEta` step. -/
private theorem NormalEqN.beta_aux (n : Nat) :
    (∀ {Γ A e a bs x T}, OnCtx Γ (env.IsType univs) →
      NormalEqN n Γ x (VExpr.mkApps (.app (.lam A e) a) bs) → Γ ⊢ x : T →
      ∃ X, FullReduction Γ x X ∧ NormalEq Γ X (VExpr.mkApps (e.inst a) bs)) ∧
    (∀ {Γ A e f c T}, OnCtx Γ (env.IsType univs) →
      NormalEqN n Γ f (.lam A e) → Γ ⊢ .app f c : T →
      ∃ X, FullReduction Γ (.app f c) X ∧ NormalEq Γ X (e.inst c)) := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  refine ⟨fun {Γ A e a bs x T} hΓ H hx => ?_, fun {Γ A e f c T} hΓ H hfc => ?_⟩
  · have hRt := hx.defeqU_l henv hΓ (H.defeq hΓ)
    have hred := FullReduction.beta_spine (Γ := Γ) A e a bs
    have hrt := hred.hasType hΓ hRt
    generalize hR : VExpr.mkApps (.app (.lam A e) a) bs = R at H hRt hred
    have ⟨_, _, happ⟩ := mkApps_app_isApp (.lam A e) a bs
    cases H with
    | refl _ => exact ⟨_, hred, .refl hrt⟩
    | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (hred.hasType hΓ l3)⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR =>
      rw [happ] at hR; cases hR
    | appDF l1 l2 l3 l4 l5 l6 =>
      rcases eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
      · cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).2 hΓ l5 hx)
        have ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
        have hx2 := u1.symm.defeq l3
        exact ⟨X, hX, hn.trans hΓ (.instN_r (by exact ⟨hΓ, _, d1⟩) hx2 ⟨_, l6⟩ .zero d2)⟩
      · rw [mkApps_concat] at hR; cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).1 hΓ l5 l1)
        have hX' := hX.hasType hΓ l1
        rw [mkApps_concat]
        exact ⟨_, hX.app .rfl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
          hn ⟨_, l6⟩⟩
    | etaL l1 l2 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      have ⟨_, _, hg⟩ := hx.lam_inv henv hΓ
      rw [lift_beta_spine] at l2
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l2 hg
      rw [lift_beta_spine_result] at hn
      exact ⟨_, .lam .rfl hY, .etaL (hred.hasType hΓ l1) hn⟩
    | etaBoth l1 l2 l3 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      rw [lift_beta_spine] at l3
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l3 ((l1.weakN henv .one).app (.bvar .zero))
      rw [lift_beta_spine_result] at hn
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hY),
        .etaL (hred.hasType hΓ l2) hn⟩
  · have ⟨_, _, hf, hc⟩ := hfc.app_inv henv hΓ
    have hbeta {A₁ g} : FullStep Γ (.app (.lam A₁ g) c) (g.inst c) := .core (.beta .rfl .rfl)
    generalize hL : VExpr.lam A e = L at H
    cases H with
    | refl _ =>
      subst hL
      exact ⟨_, .tail .rfl hbeta, .refl (hbeta.hasType hΓ hfc)⟩
    | sortDF | constDF | elimDF | projDF | forallEDF | appDF => cases hL
    | lamDF a1 a2 a3 =>
      cases hL
      have ⟨⟨_, H3⟩, _, H4⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((H3.lam H4).uniqU henv hΓ hf).forallE_inv henv hΓ
      exact ⟨_, .tail .rfl hbeta,
        .instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) hc) .zero ⟨_, a3⟩⟩
    | etaL a1 a2 =>
      subst hL
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have := a2.instN (u1.symm.defeq hc) .zero
      simp [VExpr.inst, inst_lift] at this
      obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 (bs := []) hΓ this (hbeta.hasType hΓ hfc)
      exact ⟨X, (ReflTransGen.tail .rfl hbeta).trans hX, hn⟩
    | etaR a1 a2 =>
      cases hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a2.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact ⟨_, .rfl, ⟨_, this⟩⟩
    | etaBoth a1 a2 a3 =>
      subst hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a3.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact (ih _ (by omega)).1 (bs := []) hΓ this hfc
    | proofIrrel a1 a2 a3 =>
      subst hL
      have hf' := a2.uniqU henv hΓ hf; have := a1.defeqU_l henv hΓ hf'
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf' |>.forallE_inv henv hΓ
      exact ⟨_, .rfl, .proofIrrel (b2.instN henv .zero hc) (hf.app hc)
        ((u2.defeq c2).instN henv .zero (u1.symm.defeq hc))⟩

/-- A function normally equal to a lambda computes, when applied, to the
instantiated lambda body up to normal equality. -/
theorem NormalEq.lam_beta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ f (.lam A e)) (ht : Γ ⊢ .app f c : T) :
    ∃ X, FullReduction Γ (.app f c) X ∧ NormalEq Γ X (e.inst c) :=
  let ⟨n, H⟩ := H; (NormalEqN.beta_aux n).2 hΓ H ht

end NormalParallel

section NormalParallel2

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/- Outstanding head-computation compatibility: expose native or registered
schema computation through normal equality, including eta expansion and proof
irrelevance, and transport the parallel developments of captured arguments.
This is a proof obligation for the concrete reduction relation, not an added
assumption on its callers. -/
theorem NormalEq.headParallel (hΓ : OnCtx Γ (env.IsType univs)) (H : NormalEq Γ e₁ e₂)
    (Hhead : HeadParallelReduction Γ e₂ e₂') :
    ∃ e₁', FullReduction Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂' := by
  sorry

/-- Normal equality respects one parallel step. Eta expansion of the left
side, needed for the eta and extensionality comparisons, is the full
presentation's `FullStep.funEta`. -/
theorem NormalEq.parRed (hΓ : OnCtx Γ (env.IsType univs)) (H1 : NormalEq Γ e₁ e₂)
    (H2 : ParRed Γ e₂ e₂') :
    ∃ e₁', FullReduction Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂' := by
  obtain ⟨_, H1⟩ := H1
  induction H1 generalizing e₂' with
  | refl l1 => exact ⟨_, .tail .rfl (.core H2), .refl (H2.hasType hΓ l1)⟩
  | sortDF l1 l2 l3 =>
    cases H2 with
    | sort => exact ⟨_, .rfl, .sortDF l1 l2 l3⟩
    | extra r1 r2 => cases r2
  | elimDF h heq =>
    cases H2 with
    | elim => exact ⟨_, .rfl, .elimDF h heq⟩
    | extra hp hm => exact False.elim (Params.pat_not_elim hp hm)
  | constDF l1 l2 l3 l4 l5 =>
    cases H2 with
    | const => exact ⟨_, .rfl, .constDF l1 l2 l3 l4 l5⟩
    | extra r1 r2 r3 r4 =>
      obtain ⟨_, h1, h2⟩ := NormalEq.const_native_parallel hΓ l1 l2 l3 l4 l5 r1 r2 r3 r4
      exact ⟨_, h1.full, h2⟩
  | appDF l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    cases H2 with
    | app r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 hΓ r1
      let ⟨_, b1, b2⟩ := ih2 hΓ r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2) (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩
    | beta r1 r2 =>
      let ⟨f', a1, a2⟩ := ih1 hΓ (.lam .rfl r1)
      let ⟨a', b1, b2⟩ := ih2 hΓ r2
      let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
      let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
      refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.hasType hΓ' (u2.defeq d2); ?_
      replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
      let ⟨_, h1, h2⟩ := NormalEq.lam_beta hΓ a2
        (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
      exact ⟨_, .trans (a1.app b1) h1, h2.trans hΓ (.instN_r hΓ' l3 b2 .zero d2)⟩
    | extra r1 r2 r3 r4 =>
      exact NormalEq.headParallel hΓ ⟨_, .appDF l1 l2 l3 l4 l5 l6⟩ (.native r1 r2 r3 r4)
    | schema hm hl hr =>
      exact NormalEq.headParallel hΓ ⟨_, .appDF l1 l2 l3 l4 l5 l6⟩ (.schema hm hl hr)
  | projDF lproj lMajor ihMajor =>
    cases H2 with
    | proj rMajor =>
      let ⟨_, majorRed, majorNormal⟩ := ihMajor hΓ rMajor
      have reducedAtLeft := majorRed.proj.hasType hΓ lproj
      exact ⟨_, majorRed.proj, .projDF reducedAtLeft majorNormal⟩
    | extra _ hmatch => cases hmatch
  | lamDF l1 l2 l3 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩); have ⟨_, h1⟩ := l3.defeq hΓ'; ?_
      have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
      replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
      let ⟨_, b1, b2⟩ := ih1 hΓ' r2
      exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
        .lamDF l1 (.trans l2 (r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
    | extra _ r2 => cases r2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with
    | forallE r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 hΓ r1
      refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩)
        have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ'); ?_
      have W := l1.transU_l henv hΓ (l2.defeq hΓ)
      replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
      let ⟨_, b1, b2⟩ := ih2 hΓ' r2
      have := r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
      exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
        .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2 (b1.hasType hΓ' l3) b2⟩
    | extra _ r2 => cases r2
  | etaL l1 l2 ih1 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    refine have hΓ' := by exact ⟨hΓ, _, hA⟩
      let ⟨_, a1, a2⟩ := ih1 hΓ' (.app (.weakN .one H2) .bvar); ?_
    exact ⟨_, .lam .rfl a1, .etaL (H2.hasType hΓ l1) a2⟩
  | etaR l1 l2 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      have ⟨⟨_, hA⟩, _, _⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      obtain ⟨out, hr, hn⟩ := ih1 (by exact ⟨hΓ, _, hA⟩) r2
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hr),
        .lamDF hA (r1.defeq hΓ hA) hn⟩
    | extra _ r2 => cases r2
  | etaBoth l1 l2 l3 ih1 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    obtain ⟨_, a1, a2⟩ := ih1 (by exact ⟨hΓ, _, hA⟩) (.app (.weakN .one H2) .bvar)
    exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl a1),
      .etaL (H2.hasType hΓ l2) a2⟩
  | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (H2.hasType hΓ l3)⟩

theorem NormalEq.parRedS (hΓ : OnCtx Γ (env.IsType univs)) (H1 : NormalEq Γ e₁ e₂)
    (H2 : ParRedS Γ e₂ e₂') :
    ∃ e₁', FullReduction Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂' := by
  induction H2 with
  | rfl => exact ⟨_, .rfl, H1⟩
  | tail _ h2 ih =>
    let ⟨_, a1, a2⟩ := ih
    let ⟨_, b1, b2⟩ := a2.parRed hΓ h2
    exact ⟨_, a1.trans b1, b2⟩

end NormalParallel2

/-- Normal equality respects full reduction. The remaining proof obligations
are application-head and primitive projection exposure; constant unfolding
and the explicit function and structure eta cases are proved. -/
theorem NormalEq.fullStep (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (R : FullStep Γ right result) :
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result := by
  classical
  obtain ⟨_, H⟩ := H
  induction H generalizing result with
  | refl h => exact ⟨_, .tail .rfl R, .refl (R.hasType hΓ h)⟩
  | proofIrrel hp hl hr => exact ⟨_, .rfl, .proofIrrel hp hl (R.hasType hΓ hr)⟩
  | @sortDF l₁ l₂ Γ hl hr he =>
    generalize hs : VExpr.sort l₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.fullStep_funEta hΓ hfun
    | delta h => exact False.elim (VExpr.mkApps_ne_sort (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_sort (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @lamDF Γ A A₁ u A₂ _ body₁ body₂ l1 l2 l3 ih1 =>
    generalize hs : VExpr.lam A₂ body₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.fullStep_funEta hΓ hfun
    | lam r1 r2 =>
      cases hs
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, l1.hasType.1⟩
      obtain ⟨_, h1⟩ := l3.defeq hΓ'
      have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
      replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
      obtain ⟨_, b1, b2⟩ := ih1 hΓ' r2
      exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
        .lamDF l1 (.trans l2 (r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | forallE => cases hs
  | @forallEDF Γ A A₁ u _ A₂ B₁ v _ B₂ l1 l2 l3 l4 ih1 ih2 =>
    generalize hs : VExpr.forallE A₂ B₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.fullStep_funEta hΓ hfun
    | forallE r1 r2 =>
      cases hs
      obtain ⟨_, a1, a2⟩ := ih1 hΓ r1
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, l1.hasType.1⟩
      have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ')
      have W := l1.transU_l henv hΓ (l2.defeq hΓ)
      replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
      obtain ⟨_, b1, b2⟩ := ih2 hΓ' r2
      have := r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
      exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
        .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2 (b1.hasType hΓ' l3) b2⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
  | @appDF Γ f A B f₂ a b _ _ l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    generalize hs : VExpr.app f₂ b = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_funEta hΓ hfun
    | app r1 r2 =>
      cases hs
      obtain ⟨_, a1, a2⟩ := ih1 hΓ r1
      obtain ⟨_, b1, b2⟩ := ih2 hΓ r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2)
          (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩
    | delta h =>
      have rr := FullStep.delta h
      rw [← hs] at rr
      by_cases hp : ∃ proposition, HasType env univs Γ (VExpr.app f₂ b) proposition ∧
          HasType env univs Γ proposition (.sort .zero)
      · obtain ⟨proposition, ht, hp⟩ := hp
        exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_proof hΓ rr ht hp
      · sorry
    | quotDelta h =>
      have rr := FullStep.quotDelta h
      rw [← hs] at rr
      by_cases hp : ∃ proposition, HasType env univs Γ (VExpr.app f₂ b) proposition ∧
          HasType env univs Γ proposition (.sort .zero)
      · obtain ⟨proposition, ht, hp⟩ := hp
        exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_proof hΓ rr ht hp
      · sorry
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @projDF Γ family index major resultType _ major' lproj lMajor ihMajor =>
    generalize hs : VExpr.proj family index major' = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.fullStep_funEta hΓ hfun
    | proj rMajor =>
      cases hs
      obtain ⟨_, majorRed, majorNormal⟩ := ihMajor hΓ rMajor
      have reducedAtLeft := majorRed.proj.hasType hΓ lproj
      exact ⟨_, majorRed.proj, .projDF reducedAtLeft majorNormal⟩
    | delta h => exact False.elim (mkApps_ne_proj (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (mkApps_ne_proj (by intros; intro h; cases h) _ hs.symm)
    | projIota hl hproj hget hfield =>
      cases lMajor with
      | proofIrrel hp hm hm' =>
        cases hs
        have hprop := lproj.proj_result_prop_of_major_proof henv hΓ hp hm
        have hnormal := NormalEq.projDF lproj (.proofIrrel hp hm hm')
        have hright := ((hnormal.defeq hΓ).of_l henv hΓ lproj).hasType.2
        have hout := (FullStep.projIota hl hproj hget hfield).hasType hΓ hright
        exact ⟨_, .rfl, .proofIrrel hprop lproj hout⟩
      | _ => sorry
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @elimDF Γ block owner levels levels' A h heq =>
    generalize hs : VExpr.elim block owner levels' = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.fullStep_funEta hΓ hfun
    | delta h => exact False.elim (mkApps_ne_elim (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (mkApps_ne_elim (by intros; intro h; cases h) _ hs.symm)
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @constDF c ci ls ls' Γ hc hl hr hlen heq =>
    generalize hs : VExpr.const c ls' = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.fullStep_funEta hΓ hfun
    | delta h =>
      obtain ⟨rfl, rfl, rfl⟩ := const_eq_mkApps hs
      exact NormalEq.fullStep_delta_levels hΓ h hl
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip heq)) .nil
    | quotDelta h =>
      obtain ⟨rfl, rfl, rfl⟩ := const_eq_mkApps hs
      exact NormalEq.fullStep_quotDelta_levels hΓ h hl
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip heq)) .nil
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | etaL ht he ih =>
    have ⟨⟨_, hA⟩, _, _⟩ := (ht.isType henv hΓ).choose_spec.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨_, hr, hn⟩ := ih hΓ' (.app (R.weakN .one) .rfl)
    exact ⟨_, .lam .rfl hr, .etaL (R.hasType hΓ ht) hn⟩
  | etaBoth hl hr' _ ih =>
    have ⟨⟨_, hA⟩, _, _⟩ := (hl.isType henv hΓ).choose_spec.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨_, hr, hn⟩ := ih hΓ' (.app (R.weakN .one) .rfl)
    exact ⟨_, (ReflTransGen.tail .rfl (.funEta hl)).trans (FullReduction.lam .rfl hr),
      .etaL (R.hasType hΓ hr') hn⟩
  | @etaR Γ e A B _ body ht he ih =>
    generalize hs : VExpr.lam A body = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.fullStep_funEta hΓ hfun
    | lam rd rb =>
      cases hs
      obtain ⟨⟨_, hA⟩, _, _⟩ := (ht.isType henv hΓ).choose_spec.forallE_inv henv
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      obtain ⟨out, hr, hn⟩ := ih hΓ' rb
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta ht)).trans (FullReduction.lam .rfl hr),
        .lamDF hA (rd.defeq hΓ hA) hn⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | forallE => cases hs

theorem NormalEq.fullReduction (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (R : FullReduction Γ right result) :
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result := by
  induction R with
  | rfl => exact ⟨_, .rfl, H⟩
  | tail _ step ih =>
    obtain ⟨mid, hmid, heq⟩ := ih
    obtain ⟨out, hout, heq'⟩ := heq.fullStep hΓ step
    exact ⟨out, hmid.trans hout, heq'⟩

/-- Structure expansion commutes with an entire full development by
developing the repeated occurrences below its generated projections. The
other endpoint expands to exactly the same constructor application. -/
theorem FullReduction.structEta_strip (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0)
    (hs : HasType env univs Γ source (VExpr.mkApps (.const family levels) params))
    (hc : HasType env univs Γ
      (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj family index source))
      (VExpr.mkApps (.const family levels) params))
    (development : FullReduction Γ source target) :
    ∃ left' right',
      FullReduction Γ
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index source)) left' ∧
      FullReduction Γ target right' ∧ NormalEq Γ left' right' := by
  have hparams : List.Forall₂ (FullReduction Γ) params params := by
    clear hp hs hc
    induction params with | nil => exact .nil | cons _ _ ih => exact .cons .rfl ih
  have hfields (indices : List Nat) : List.Forall₂ (FullReduction Γ)
      (indices.map fun index => .proj family index source)
      (indices.map fun index => .proj family index target) := by
    induction indices with
    | nil => exact .nil
    | cons _ _ ih => exact .cons development.proj ih
  have expanded := FullReduction.mkApps (fn := .const info.ctorName levels) .rfl
    (case_forall₂_append hparams (hfields (List.range info.numFields)))
  have hc' := expanded.hasType hΓ hc
  have right := FullStep.structEta hl hp hi (development.hasType hΓ hs) hc'
  exact ⟨_, _, expanded, .tail .rfl right, .refl hc'⟩

/-- Function eta expansion commutes with a whole development by moving
that development under its fresh binder and expanding the other endpoint. -/
theorem FullReduction.funEta_strip (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source (.forallE domain body))
    (development : FullReduction Γ source target) :
    ∃ left' right',
      FullReduction Γ (.lam domain (.app source.lift (.bvar 0))) left' ∧
      FullReduction Γ target right' ∧ NormalEq Γ left' right' := by
  have lifted := development.weakN (Γ' := domain :: Γ) .one
  have hright := development.hasType hΓ ht
  exact ⟨_, _, .lam .rfl (.app lifted .rfl), .tail .rfl (.funEta hright),
    .refl (IsDefEq.eta hright).hasType.1⟩

/-- The required global strip property. One arbitrary full step must commute
with an entire finite development. Local sequence joinability would not be
sufficient to derive this statement in a calculus without termination. -/
theorem FullStep.strip (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (step : FullStep Γ source left) (development : FullReduction Γ source right) :
    ∃ left' right', FullReduction Γ left left' ∧ FullReduction Γ right right' ∧
      NormalEq Γ left' right' := by
  classical
  by_cases hprop : HasType env univs Γ type (.sort .zero)
  · exact ⟨_, _, .rfl, .rfl,
      .proofIrrel hprop (step.hasType hΓ ht) (development.hasType hΓ ht)⟩
  cases step with
  | funEta hfun => exact FullReduction.funEta_strip hΓ hfun development
  | structEta hl hp hi hs hc =>
    exact FullReduction.structEta_strip hΓ hl hp hi hs hc development
  | @proj Γ major major' family index hmajor =>
    cases hmajor with
    | @structEta other info _ _ levels params hl hp hi hs hc =>
      by_cases hfamily : family = other
      · subst other
        have hcancel := FullReduction.proj_structEta_cancel hΓ hl hp hi
          (ht.proj_index_lt henv hΓ hl) hs hc ht
        exact ⟨_, _, hcancel.trans development, .rfl,
          .refl (development.hasType hΓ ht)⟩
      · sorry
    | _ => sorry
  | _ => sorry

/-- Full confluence follows from the global strip property and transport
through normal equality; no termination or local-confluence inference is
used. -/
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

/-- Every installed equation joins in the full presentation at each scoped
universe packing. The terminal comparison permits proof irrelevance: quotient
reconstruction can return a generated proof selector that is normally equal
to the original field without a primitive computation rule for that selector. -/
class FullEquationCoverage : Prop where
  equations : OnCtx Γ (env.IsType univs) → env.defeqs equation →
    (∀ level ∈ levels, level.WF univs) → levels.length = equation.uvars →
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right

end Lean4Lean.VEnv
