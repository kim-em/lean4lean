import Lean4Lean.Theory.Typing.Strengthening.Exposure

/-! # The eta-normal relation

Direction B3 (`docs/inductives/STRENGTHENING_B3_LOG.md`). `EtaNE Γ s X` ("`X` is an eta-normal
expansion of `s`") is the relation between a source and the reducts that eta expansions and
annotation changes produce above a lift. It is a structural congruence (up to universe levels,
proof irrelevance and convertible binder annotations, as `NormalEq₀`) extended by

* `funEta`: a non-lambda source expands to a lambda whose body is related to the source applied
  to the new variable;
* `structEta`: a source of structure type expands to a constructor application whose arguments
  are related to the parameters and the projections of the source;
* `betaVarR`: the right side may carry the administrative redex left by a collapsed junk
  expansion of a lambda, a lambda applied to a variable spine, when the source is related to its
  contractum;
* `betaL`, `projIotaL`: the left side may carry a beta or projection redex when its contractum is
  related to the right side (these are dissolved by reduction below in the replay).

`EtaNE` contains every eta chain of a typed term (`EtaNE.etaPar_r`, `EtaNE.of_etaChain`) and a
type related to a `Π` reduces to a `Π` by administrative steps (`EtaNE.forallE_inv`). -/

namespace Lean4Lean.VEnv.StrengtheningEtaNormal
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-- The arguments of the structure eta expansion of `e`: the parameters and the projections. -/
def structArgs (family : Name) (info : VProjectionInfo) (params : List VExpr) (e : VExpr) :
    List VExpr :=
  params ++ (List.range info.numFields).map fun i => VExpr.proj family i e

omit [Params] in
theorem structExpand_eq (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (params : List VExpr) (e : VExpr) :
    structExpand family info levels params e =
      mkApps (.const info.ctorName levels) (structArgs family info params e) := rfl

/-- The eta-normal relation (see the module docstring). -/
inductive EtaNE : List VExpr → VExpr → VExpr → Prop where
  | refl {Γ : List VExpr} {e A : VExpr} : Γ ⊢ e : A → EtaNE Γ e e
  | sortDF {Γ : List VExpr} {l₁ l₂ : VLevel} : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → EtaNE Γ (.sort l₁) (.sort l₂)
  | constDF {Γ : List VExpr} {c : Name} {ci : VConstant} {ls ls' : List VLevel} :
      Params.env.constants c = some ci → (∀ l ∈ ls, l.WF univs) →
      (∀ l ∈ ls', l.WF univs) → ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      EtaNE Γ (.const c ls) (.const c ls')
  | elimDF {Γ : List VExpr} {block : Name} {owner : Nat} {levels levels' : List VLevel}
      {A : VExpr} : Γ ⊢ .elim block owner levels ≡ .elim block owner levels' : A →
      List.Forall₂ (· ≈ ·) levels levels' →
      EtaNE Γ (.elim block owner levels) (.elim block owner levels')
  | app {Γ : List VExpr} {f f' a a' : VExpr} :
      EtaNE Γ f f' → EtaNE Γ a a' → EtaNE Γ (.app f a) (.app f' a')
  | proj {Γ : List VExpr} {m m' : VExpr} {S : Name} {i : Nat} :
      EtaNE Γ m m' → EtaNE Γ (.proj S i m) (.proj S i m')
  | lam {Γ : List VExpr} {A A' b b' : VExpr} {u : VLevel} :
      Γ ⊢ A ≡ A' : .sort u → EtaNE (A :: Γ) b b' → EtaNE Γ (.lam A b) (.lam A' b')
  | forallE {Γ : List VExpr} {A A' B B' : VExpr} {u : VLevel} :
      Γ ⊢ A ≡ A' : .sort u → EtaNE (A :: Γ) B B' → EtaNE Γ (.forallE A B) (.forallE A' B')
  | proofIrrel {Γ : List VExpr} {p h h' : VExpr} : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → EtaNE Γ h h'
  | funEta {Γ : List VExpr} {e A B A' body : VExpr} {u : VLevel} : (∀ D t, e ≠ .lam D t) → Γ ⊢ e : .forallE A B → Γ ⊢ A ≡ A' : .sort u →
      EtaNE (A' :: Γ) (.app e.lift (.bvar 0)) body → EtaNE Γ e (.lam A' body)
  | structEta {Γ : List VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params args : List VExpr} {e : VExpr} : Params.env.projections family info → params.length = info.nparams →
      info.nindices = 0 → Γ ⊢ e : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params e : mkApps (.const family levels) params →
      (hlen : (structArgs family info params e).length = args.length) →
      (∀ i (hi : i < (structArgs family info params e).length) (hi' : i < args.length),
        EtaNE Γ (structArgs family info params e)[i] args[i]) →
      EtaNE Γ e (mkApps (.const info.ctorName levels) args)
  | betaR {Γ : List VExpr} {A b a s T : VExpr} {args : List VExpr} :
      Γ ⊢ mkApps (.app (.lam A b) a) args : T →
      EtaNE Γ s (mkApps (b.inst a) args) → EtaNE Γ s (mkApps (.app (.lam A b) a) args)
  | betaL {Γ : List VExpr} {A b a T X : VExpr} : Γ ⊢ .app (.lam A b) a : T → EtaNE Γ (b.inst a) X → EtaNE Γ (.app (.lam A b) a) X
  | projIotaL {Γ : List VExpr} {S : Name} {info : VProjectionInfo} {i : Nat} {ls : List VLevel}
      {args : List VExpr} {T field X : VExpr} : Params.env.projections S info →
      Γ ⊢ .proj S i (mkApps (.const info.ctorName ls) args) : T →
      args[info.nparams + i]? = some field → Γ ⊢ field : T →
      EtaNE Γ field X → EtaNE Γ (.proj S i (mkApps (.const info.ctorName ls) args)) X

/-- A typed beta redex is convertible to its contractum. -/
theorem beta_defeqU {Γ : List VExpr} {A b a T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : Γ ⊢ .app (.lam A b) a : T) : Γ ⊢ .app (.lam A b) a ≡ b.inst a := by
  obtain ⟨A₁, B₁, hlam, ha⟩ := H.app_inv henv hΓ
  obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
  obtain ⟨⟨u, hA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
  exact ⟨_, .beta hb (hA.defeq' ha)⟩

/-- Soundness: a source and its expansion are convertible. -/
theorem EtaNE.defeq {Γ : List VExpr} {e e' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaNE Γ e e') (he : Γ ⊢ e : T) : Γ ⊢ e ≡ e' := by
  induction H generalizing T with
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | elimDF h _ => exact ⟨_, h⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    exact ⟨_, .appDF ((ih1 hΓ hf).of_l henv hΓ hf) ((ih2 hΓ ha).of_l henv hΓ ha)⟩
  | proj _ ih =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
    have majorEq := (ih hΓ hmajor.hasType.2).of_l henv hΓ hmajor.hasType.2
    exact ⟨_, .projDF hinfo hlevels huvars hparams hindices hfield
      hfieldTyping hmajor (hmajor.trans majorEq) hclosed hguard⟩
  | lam hA _ ih =>
    obtain ⟨⟨_, hA₀⟩, _, hb⟩ := he.lam_inv henv hΓ
    have ⟨_, hB⟩ := ih ⟨hΓ, _, hA₀⟩ hb
    exact ⟨_, .lamDF hA hB⟩
  | @forallE Γ₀ A A' B B' u hA _ ih =>
    obtain ⟨⟨_, hA₀⟩, _, hb⟩ := he.forallE_inv henv
    have hΓ' : OnCtx (A :: Γ₀) (Params.env.IsType univs) := ⟨hΓ, _, hA₀⟩
    have hB := (ih hΓ' hb).of_l henv hΓ' hb
    exact ⟨_, .forallEDF hA hB⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, .proofIrrel h1 h2 h3⟩
  | @funEta Γ₀ e A B A' body u _ hPi hA _ ih =>
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨_, hA₀⟩, _, hB⟩ := hPiT.forallE_inv henv
    have hΓ' : OnCtx (A' :: Γ₀) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
    have hbody : A' :: Γ₀ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ₀ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv
      have h0 : A' :: Γ₀ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    have ih' := (ih hΓ' hbody).of_l henv hΓ' hbody
    have hPiEq : Γ₀ ⊢ .forallE A' B ≡ .forallE A B : .sort (.imax u _) :=
      .forallEDF hA.symm (hB.defeqDFC henv.ordered (.succ .zero hA))
    have heta : Γ₀ ⊢ .lam A' (.app e.lift (.bvar 0)) ≡ .lam A (.app e.lift (.bvar 0)) :
        .forallE A B :=
      .defeqDF hPiEq (.lamDF hA.symm hbody)
    exact ⟨_, IsDefEq.trans (IsDefEq.trans heta (.eta hPi)).symm
      (.defeqDF hPiEq (.lamDF hA.hasType.2 ih'))⟩
  | structEta hl hp hi hs ht hlen _ ih =>
    have hexp : _ ⊢ _ ≡ structExpand _ _ _ _ _ := ⟨_, (IsDefEq.structEta hl hp hi hs ht).symm⟩
    refine hexp.trans henv hΓ ?_
    rw [structExpand_eq] at ht ⊢
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
    refine IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ (List.forall₂_of_getElem hlen fun i hi hi' => ?_) ht
    obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ ht (List.getElem_mem hi)
    exact ih i hi hi' hΓ hx
  | @betaR Γ₀ A b a s T args hT _ ih =>
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
    have hhead' : Γ₀ ⊢ .app (.lam A b) a : _ := hhead
    have hred : Γ₀ ⊢ mkApps (.app (.lam A b) a) args ≡ mkApps (b.inst a) args := by
      refine IsDefEqU.mkApps_args hΓ (beta_defeqU hΓ hhead')
        (List.forall₂_of_getElem rfl fun i hi hi' => ?_) hT
      obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
      exact ⟨_, hx⟩
    exact (ih hΓ he).trans henv hΓ hred.symm
  | betaL hT _ ih =>
    have hred := beta_defeqU hΓ hT
    exact hred.trans henv hΓ (ih hΓ (hT.defeqU_l henv hΓ hred))
  | projIotaL hl hT hi hf _ ih =>
    have h1 : _ ⊢ _ ≡ _ := ⟨_, IsDefEq.projIota hl hT hi hf⟩
    exact h1.trans henv hΓ (ih hΓ hf)

theorem EtaNE.hasType {Γ : List VExpr} {e e' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaNE Γ e e') (he : Γ ⊢ e : T) : Γ ⊢ e' : T :=
  he.defeqU_l henv hΓ (H.defeq hΓ he)

omit [Params] in
theorem lift_lift'_cons (e : VExpr) (l : Lift) : (lift e).lift' (.cons l) = lift (e.lift' l) := by
  show (liftN 1 e 0).lift' (.cons l) = liftN 1 (e.lift' l) 0
  rw [← lift'_consN_skipN, ← lift'_consN_skipN, ← lift'_comp, ← lift'_comp]
  simp

omit [Params] in
theorem lift'_mkApps (f : VExpr) (args : List VExpr) (l : Lift) :
    (mkApps f args).lift' l = mkApps (f.lift' l) (args.map (·.lift' l)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

omit [Params] in
theorem lift'_ne_lam {e : VExpr} {l : Lift} (h : ∀ D t, e ≠ .lam D t) :
    ∀ D t, e.lift' l ≠ .lam D t := by
  intro D t he
  cases e <;> simp [lift'] at he
  exact h _ _ rfl

omit [Params] in
theorem structArgs_lift' (family : Name) (info : VProjectionInfo) (params : List VExpr)
    (e : VExpr) (l : Lift) :
    structArgs family info (params.map (·.lift' l)) (e.lift' l) =
      (structArgs family info params e).map (·.lift' l) := by
  simp [structArgs, List.map_append, List.map_map, Function.comp_def]

/-- Weakening along any lift. -/
theorem EtaNE.weak' {Γ Γ' : List VExpr} {l : Lift} {e e' : VExpr} (W : Ctx.Lift' l Γ Γ')
    (H : EtaNE Γ e e') : EtaNE Γ' (e.lift' l) (e'.lift' l) := by
  induction H generalizing l Γ' with
  | refl h => exact .refl (h.weak' henv.ordered W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | elimDF h heq => exact .elimDF (h.weak' henv.ordered W) heq
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam hA _ ih => exact .lam (hA.weak' henv.ordered W) (ih W.cons)
  | forallE hA _ ih => exact .forallE (hA.weak' henv.ordered W) (ih W.cons)
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weak' henv.ordered W) (h2.weak' henv.ordered W) (h3.weak' henv.ordered W)
  | funEta hne hPi hA _ ih =>
    refine .funEta (lift'_ne_lam hne) (hPi.weak' henv.ordered W) (hA.weak' henv.ordered W) ?_
    have := ih W.cons
    simpa [lift_lift'_cons] using this
  | @structEta Γ₀ family info levels params args e hl hp hi hs ht hlen hargs ih =>
    have hs' := hs.weak' henv.ordered W
    have ht' := ht.weak' henv.ordered W
    simp only [structExpand_eq, lift'_mkApps, lift', ← structArgs_lift'] at hs' ht' ⊢
    refine .structEta hl (by simpa using hp) hi hs' ht' ?_ ?_
    · rw [structArgs_lift']; simp [hlen]
    · intro i hi hi'
      simp only [structArgs_lift', List.getElem_map]
      exact ih i (by simpa [structArgs_lift'] using hi) (by simpa using hi') W
  | betaR hT _ ih =>
    have hT' := hT.weak' henv.ordered W
    have := ih W
    rw [lift'_mkApps, lift'_inst_hi] at this
    simp only [lift'_mkApps, lift'] at hT' ⊢
    exact .betaR hT' this
  | betaL hT _ ih =>
    have := ih W
    rw [lift'_inst_hi] at this
    exact .betaL (hT.weak' henv.ordered W) this
  | projIotaL hl hT hi hf _ ih =>
    have hT' := hT.weak' henv.ordered W
    simp only [lift', lift'_mkApps] at hT' ⊢
    refine .projIotaL hl hT' ?_ (hf.weak' henv.ordered W) (ih W)
    simp [hi]

theorem EtaNE.weakN {Γ Γ' : List VExpr} {n k : Nat} {e e' : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (H : EtaNE Γ e e') : EtaNE Γ' (e.liftN n k) (e'.liftN n k) := by
  rw [← lift'_consN_skipN, ← lift'_consN_skipN]
  exact H.weak' (Ctx.liftN_iff_lift'.mp W)

theorem EtaNE.weak {Γ : List VExpr} {e e' B : VExpr} (H : EtaNE Γ e e') :
    EtaNE (B :: Γ) e.lift e'.lift := H.weakN .one

/-- Context conversion. -/
theorem EtaNE.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {e e' T : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (he : Γ₁ ⊢ e : T) (H : EtaNE Γ₁ e e') : EtaNE Γ₂ e e' := by
  induction H generalizing Γ₂ T with
  | refl h => exact .refl (h.defeqDFC henv.ordered W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | elimDF h heq => exact .elimDF (h.defeqDFC henv.ordered W) heq
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam hA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (hA.defeqDFC henv.ordered W) (ih (.succ W hd) hb)
  | forallE hA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    exact .forallE (hA.defeqDFC henv.ordered W) (ih (.succ W hd) hb)
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.defeqDFC henv.ordered W) (h2.defeqDFC henv.ordered W)
      (h3.defeqDFC henv.ordered W)
  | @funEta Γ₁ e A B A' body u hne hPi hA _ ih =>
    have hΓ₁ := W.isType' hΓ
    have hΓ' : OnCtx (A' :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, _, hA.hasType.2⟩
    have hbody : A' :: Γ₁ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ₁ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A' :: Γ₁ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    exact .funEta hne (hPi.defeqDFC henv.ordered W) (hA.defeqDFC henv.ordered W)
      (ih (.succ W hA.hasType.2) hbody)
  | structEta hl hp hi hs ht hlen _ ih =>
    refine .structEta hl hp hi (hs.defeqDFC henv.ordered W) (ht.defeqDFC henv.ordered W) hlen
      fun i hi hi' => ?_
    rw [structExpand_eq] at ht
    obtain ⟨_, hx⟩ := schema_mkApps_arg_type (W.isType' hΓ) ht (List.getElem_mem hi)
    exact ih i hi hi' W hx
  | betaR hT _ ih => exact .betaR (hT.defeqDFC henv.ordered W) (ih W he)
  | betaL hT _ ih =>
    have hred := beta_defeqU (W.isType' hΓ) hT
    exact .betaL (hT.defeqDFC henv.ordered W) (ih W (hT.defeqU_l henv (W.isType' hΓ) hred))
  | projIotaL hl hT hi hf _ ih =>
    exact .projIotaL hl (hT.defeqDFC henv.ordered W) hi (hf.defeqDFC henv.ordered W) (ih W hf)

/-- The body of a lambda typed at a proposition is a proof. -/
theorem lam_prop_body {Γ : List VExpr} {D t p : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : Γ ⊢ p : .sort .zero) (hl : Γ ⊢ .lam D t : p) :
    ∃ B, D :: Γ ⊢ t : B ∧ D :: Γ ⊢ B : .sort .zero ∧ Γ ⊢ .forallE D B ≡ p := by
  obtain ⟨B, hPi, ht⟩ := hl.lam_inv_forallE henv hΓ
  obtain ⟨⟨u, hD⟩, hb⟩ := hl.lam_inv henv hΓ
  have hΓ' : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD⟩
  obtain ⟨v, hB⟩ := ht.isType henv hΓ'
  have hsort : Γ ⊢ .forallE D B : .sort (.imax u v) := .forallE hD hB
  have h1 := (hPi.of_l henv hΓ hsort).hasType.2
  have h2 : Γ ⊢ .sort (.imax u v) ≡ .sort .zero := h1.uniqU henv hΓ hp
  have h3 : v ≈ .zero := VLevel.imax_eq_zero.mp (IsDefEqU.sort_inv henv hΓ h2)
  refine ⟨B, ht, ?_, hPi⟩
  exact (IsDefEq.sortDF (l' := .zero) (hB.sort_r henv.ordered hΓ')
    (show VLevel.WF univs .zero from trivial) h3).defeq hB

/-- Inversion of a relation between two lambdas. -/
theorem EtaNE.lam_inv {Γ : List VExpr} {D D' t t' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hl : Γ ⊢ .lam D t : T)
    (H : EtaNE Γ (.lam D t) (.lam D' t')) : EtaNE (D :: Γ) t t' := by
  generalize hs : VExpr.lam D t = s at H hl
  generalize hr : VExpr.lam D' t' = r at H
  cases H with
  | refl h =>
    cases hs; cases hr
    obtain ⟨_, _, hb⟩ := h.lam_inv henv hΓ
    exact .refl hb
  | lam _ hb => cases hs; cases hr; exact hb
  | proofIrrel hp h1 h2 =>
    cases hs; cases hr
    obtain ⟨B, ht, hB, hPi⟩ := lam_prop_body hΓ hp h1
    obtain ⟨B', ht', hB', hPi'⟩ := lam_prop_body hΓ hp h2
    obtain ⟨⟨_, hDD⟩, _, hBB⟩ := IsDefEqU.forallE_inv henv hΓ (hPi.trans henv hΓ hPi'.symm)
    have ht'' : D :: Γ ⊢ t' : B := by
      have := ht'.defeqDFC henv.ordered (.succ .zero hDD.symm)
      exact this.defeqU_r henv ⟨hΓ, _, hDD.hasType.1⟩ ⟨_, hBB.symm⟩
    exact .proofIrrel hB ht ht''
  | funEta hne => cases hs; exact (hne _ _ rfl).elim
  | structEta hl' _ _ hs' =>
    cases hs
    obtain ⟨B, hPi, -⟩ := hl.lam_inv_forallE henv hΓ
    exact (pi_not_struct hΓ hl' (hl.defeqU_r henv hΓ hPi.symm) hs').elim
  | betaR =>
    exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hr.symm).elim
  | sortDF | constDF | elimDF | app | proj | forallE | betaL | projIotaL => cases hs

/-- A parallel eta step from a typed term is an eta-normal expansion; for a lambda source, the
body is related to the expansion applied to the new variable. -/
theorem EtaNE.of_etaPar_aux {Γ : List VExpr} {e e' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : EtaPar Γ e e') (he : Γ ⊢ e : T) :
    EtaNE Γ e e' ∧ ∀ D t, e = .lam D t → EtaNE (D :: Γ) t (.app e'.lift (.bvar 0)) := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact ⟨.refl he, fun _ _ h => by cases h⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    exact ⟨.app (ih1 hΓ hf).1 (ih2 hΓ ha).1, fun _ _ h => by cases h⟩
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    exact ⟨.proj (ih hΓ hm.hasType.2).1, fun _ _ h => by cases h⟩
  | @lam Γ D D' t t' hD ht ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓ' : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hbody := (ih2 hΓ' hb).1
    refine ⟨.lam ((EtaPar.full hΓ hD hd).defeq hΓ hd) hbody, fun D₀ t₀ h => ?_⟩
    cases h
    obtain ⟨B, hPi, -⟩ := he.lam_inv_forallE henv hΓ
    have he' : Γ ⊢ .lam D' t' : .forallE D B :=
      ((EtaPar.full hΓ (.lam hD ht) he).hasType hΓ he).defeqU_r henv hΓ hPi.symm
    have hT : D :: Γ ⊢ .app (VExpr.lam D' t').lift (.bvar 0) : _ :=
      HasType.app (he'.weak henv.ordered) (.bvar .zero)
    refine .betaR (args := []) (by simpa [mkApps, lift, liftN] using hT) ?_
    simpa [mkApps, lift, liftN, inst, instVar, VExpr.inst_liftN_bvar] using hbody
  | forallE hA _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    exact ⟨.forallE ((EtaPar.full hΓ hA hd).defeq hΓ hd) (ih2 ⟨hΓ, _, hd⟩ hb).1,
      fun _ _ h => by cases h⟩
  | @funEta Γ e e' A A' B H₀ HA hPi ih _ =>
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA₀⟩, _, hB⟩ := hPiT.forallE_inv henv.ordered
    have hAA : Γ ⊢ A ≡ A' : .sort u := (EtaPar.full hΓ HA hA₀).defeq hΓ hA₀
    obtain ⟨hee', hlamBody⟩ := ih hΓ hPi
    have he' : Γ ⊢ e' : .forallE A B := hee'.hasType hΓ hPi
    have hbody : A' :: Γ ⊢ .app e'.lift (.bvar 0) : B := by
      have h1 : A' :: Γ ⊢ e'.lift : .forallE A.lift (B.liftN 1 1) := he'.weak henv.ordered
      have h0 : A' :: Γ ⊢ .bvar 0 : A.lift :=
        (hAA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    have hX : Γ ⊢ .lam A' (.app e'.lift (.bvar 0)) : .forallE A B :=
      (EtaPar.full hΓ (.funEta H₀ HA hPi) hPi).hasType hΓ hPi
    refine ⟨?_, fun D t h => ?_⟩
    · by_cases hlam : ∃ D t, e = .lam D t
      · obtain ⟨D, t, rfl⟩ := hlam
        obtain ⟨B₀, hPi₀, ht⟩ := hPi.lam_inv_forallE henv hΓ
        obtain ⟨⟨u₀, hD⟩, -⟩ := hPi.lam_inv henv hΓ
        obtain ⟨⟨w, hDA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi₀
        have hwu : Γ ⊢ .sort w ≡ .sort u := hDA.hasType.2.uniqU henv hΓ hA₀
        have hDA' : Γ ⊢ D ≡ A' : .sort u :=
          .trans (.defeqDF (hwu.of_l henv hΓ (HasType.sort (hDA.sort_r henv.ordered hΓ))) hDA) hAA
        exact .lam hDA' (hlamBody D t rfl)
      · have hne : ∀ D t, e ≠ .lam D t := fun D t h => hlam ⟨D, t, h⟩
        exact .funEta hne hPi hAA (.app hee'.weak (.refl (.bvar .zero)))
    · subst h
      have hinner := hlamBody _ _ rfl
      obtain ⟨B₀, hPi₀, -⟩ := hPi.lam_inv_forallE henv hΓ
      obtain ⟨⟨w, hDA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi₀
      have h0 : D :: Γ ⊢ .bvar 0 : A.lift := (hDA.weak henv.ordered (B := D)).defeq (.bvar .zero)
      have hT : D :: Γ ⊢ .app (VExpr.lam A' (.app e'.lift (.bvar 0))).lift (.bvar 0) : _ :=
        HasType.app (hX.weak henv.ordered) h0
      refine .betaR (args := []) (by simpa [mkApps, lift, liftN] using hT) ?_
      simpa [mkApps, lift, liftN, inst, instVar, VExpr.inst_liftN_bvar] using hinner
  | @structEta Γ e e' family info levels params params' H₀ hlen hps hl hp hi hs hexp ih ihp =>
    have hee' := (ih hΓ hs).1
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    have hF : List.Forall₂ (EtaNE Γ) (structArgs family info params e)
        (structArgs family info params' e') := by
      refine List.Forall₂.append' (List.forall₂_of_getElem hlen fun i hi hi' => ?_)
        (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
      · obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
        exact (ihp i hi hi' hΓ hpT).1
      · simp only [List.getElem_map, List.getElem_range]
        exact .proj hee'
    obtain ⟨hlen', hargs'⟩ := getElem_of_forall₂ hF
    refine ⟨.structEta hl hp hi hs hexp hlen' hargs', fun D t h => ?_⟩
    subst h
    obtain ⟨B, hPi, -⟩ := hs.lam_inv_forallE henv hΓ
    exact (pi_not_struct hΓ hl (hs.defeqU_r henv hΓ hPi.symm) hs).elim

theorem EtaNE.of_etaPar {Γ : List VExpr} {e e' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : EtaPar Γ e e') (he : Γ ⊢ e : T) :
    EtaNE Γ e e' := (EtaNE.of_etaPar_aux hΓ H he).1

/-- The structure expansion of a term convertible to `X` is typed like the expansion of `X`. -/
theorem structExpand_typed_of_defeqU {Γ : List VExpr} {s X T : VExpr} {family : Name}
    {info : VProjectionInfo} {levels : List VLevel} {params : List VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (h : Γ ⊢ X ≡ s)
    (ht : Γ ⊢ structExpand family info levels params X : T) :
    Γ ⊢ structExpand family info levels params s : T := by
  rw [structExpand_eq] at ht ⊢
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  refine ht.defeqU_l henv hΓ (IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ ?_ ht)
  refine List.Forall₂.append' (List.forall₂_of_getElem rfl fun i hi hi' => ?_)
    (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
  · obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ ht (List.mem_append_left _ (List.getElem_mem hi))
    exact ⟨_, hx⟩
  · have hjmem : j ∈ List.range info.numFields := by simpa using hj
    obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ ht
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
    simp only [List.getElem_map, List.getElem_range]
    exact ⟨_, IsDefEq.proj_congr hΓ hpj h⟩

/-- The eta body of a function. -/
theorem eta_body_typed {Γ : List VExpr} {X A B : VExpr} (hX : Γ ⊢ X : .forallE A B) :
    A :: Γ ⊢ .app X.lift (.bvar 0) : B := by
  have := HasType.app (hX.weak henv.ordered (B := A)) (.bvar .zero)
  simpa [VExpr.inst_liftN_bvar] using this

/-- A lambda source is related to the body of any expansion applied to the new variable. -/
theorem EtaNE.lam_body {Γ : List VExpr} {D t X B : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hl : Γ ⊢ .lam D t : .forallE D B) (H : EtaNE Γ (.lam D t) X) :
    EtaNE (D :: Γ) t (.app X.lift (.bvar 0)) := by
  obtain ⟨B₀, hPi, ht⟩ := hl.lam_inv_forallE henv hΓ
  obtain ⟨⟨u, hD⟩, -⟩ := hl.lam_inv henv hΓ
  have hΓ' : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD⟩
  obtain ⟨-, _, hBB⟩ := IsDefEqU.forallE_inv henv hΓ hPi
  replace ht : D :: Γ ⊢ t : B := ht.defeqU_r henv hΓ' ⟨_, hBB⟩
  clear hBB hPi B₀
  generalize hs : VExpr.lam D t = s at H hl
  induction H generalizing D t with
  | refl h =>
    subst hs
    exact .betaR (args := []) (by simpa [mkApps, lift, liftN] using eta_body_typed hl)
      (by simpa [mkApps, lift, liftN, inst, instVar, VExpr.inst_liftN_bvar] using EtaNE.refl ht)
  | lam hA hb =>
    cases hs
    have hX := (EtaNE.lam hA hb).hasType hΓ hl
    exact .betaR (args := []) (by simpa [mkApps, lift, liftN] using eta_body_typed hX)
      (by simpa [mkApps, lift, liftN, inst, instVar, VExpr.inst_liftN_bvar] using hb)
  | proofIrrel hp h1 h2 =>
    subst hs
    obtain ⟨B', ht', hB', hPi'⟩ := lam_prop_body hΓ hp h1
    have h3 : _ ⊢ .forallE D B ≡ _ := hl.uniqU henv hΓ h1
    obtain ⟨-, _, hBB⟩ := IsDefEqU.forallE_inv henv hΓ (h3.trans henv hΓ hPi'.symm)
    have hBB' : _ ⊢ B ≡ B' := ⟨_, hBB⟩
    have hX := (EtaNE.proofIrrel hp h1 h2).hasType hΓ hl
    exact .proofIrrel hB' (ht.defeqU_r henv hΓ' hBB') ((eta_body_typed hX).defeqU_r henv hΓ' hBB')
  | @betaR Γ A b a s T' args hT hrel ih =>
    subst hs
    have hX := (EtaNE.betaR hT hrel).hasType hΓ hl
    have hbody := eta_body_typed hX
    have := ih hΓ hD hΓ' ht rfl hl
    simp only [lift, liftN_mkApps, liftN] at this hbody ⊢
    rw [← VExpr.mkApps_snoc] at this hbody ⊢
    refine .betaR hbody ?_
    have h := lift_inst_hi b a
    simp only [lift] at h
    rwa [h] at this
  | funEta hne => cases hs; exact (hne _ _ rfl).elim
  | structEta hl' _ _ hs' =>
    subst hs
    exact (pi_not_struct hΓ hl' hl hs').elim
  | sortDF | constDF | elimDF | app | proj | forallE | betaL | projIotaL => cases hs

/-- A root function eta expansion of the right side. -/
theorem EtaNE.root_funEta {Γ : List VExpr} {s X A A' B T : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (hX : Γ ⊢ X : .forallE A B) (hA : Γ ⊢ A ≡ A' : .sort u) :
    EtaNE Γ s (.lam A' (.app X.lift (.bvar 0))) := by
  have hsPi : Γ ⊢ s : .forallE A B := hX.defeqU_l henv hΓ (H.defeq hΓ hs).symm
  by_cases hlam : ∃ D t, s = .lam D t
  · obtain ⟨D, t, rfl⟩ := hlam
    obtain ⟨B₀, hPi₀, ht⟩ := hsPi.lam_inv_forallE henv hΓ
    obtain ⟨⟨u₀, hD⟩, -⟩ := hsPi.lam_inv henv hΓ
    obtain ⟨⟨w, hDA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi₀
    have hwu : Γ ⊢ .sort w ≡ .sort u := hDA.hasType.2.uniqU henv hΓ hA.hasType.1
    have hDA' : Γ ⊢ D ≡ A' : .sort u :=
      .trans (.defeqDF (hwu.of_l henv hΓ (HasType.sort (hDA.sort_r henv.ordered hΓ))) hDA) hA
    exact .lam hDA' (EtaNE.lam_body hΓ (HasType.lam hD ht) H)
  · have hne : ∀ D t, s ≠ .lam D t := fun D t h => hlam ⟨D, t, h⟩
    exact .funEta hne hsPi hA (.app H.weak (.refl (.bvar .zero)))

/-- A root structure eta expansion of the right side. -/
theorem EtaNE.root_structEta {Γ : List VExpr} {s X T : VExpr} {family : Name}
    {info : VProjectionInfo} {levels : List VLevel} {params params' : List VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (hl : Params.env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hX : Γ ⊢ X : mkApps (.const family levels) params)
    (hexp : Γ ⊢ structExpand family info levels params X : mkApps (.const family levels) params)
    (hlen : params.length = params'.length)
    (hps : ∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) :
    EtaNE Γ s (structExpand family info levels params' X) := by
  have hsX := (H.defeq hΓ hs).symm
  have hsS : Γ ⊢ s : mkApps (.const family levels) params := hX.defeqU_l henv hΓ hsX
  have hexp' := structExpand_typed_of_defeqU hΓ hsX hexp
  have hF : List.Forall₂ (EtaNE Γ) (structArgs family info params s)
      (structArgs family info params' X) := by
    refine List.Forall₂.append' (List.forall₂_of_getElem hlen hps)
      (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
    simp only [List.getElem_map, List.getElem_range]
    exact .proj H
  obtain ⟨hlen', hargs'⟩ := getElem_of_forall₂ hF
  exact .structEta hl hp hi hsS hexp' hlen' hargs'

/-- Eta wrappers around a spine: expansions of partial applications, which the following
applications turn into beta redexes. -/
inductive Wrap (Γ : List VExpr) : VExpr → VExpr → Prop where
  | rfl {Y : VExpr} : Wrap Γ Y Y
  | eta {Y Y' A A' B : VExpr} {u : VLevel} : Wrap Γ Y Y' → Γ ⊢ Y' : .forallE A B →
      Γ ⊢ A ≡ A' : .sort u → Wrap Γ Y (.lam A' (.app Y'.lift (.bvar 0)))
  | struct {Y Y' : VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params params' : List VExpr} : Wrap Γ Y Y' → Params.env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ Y' : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params Y' : mkApps (.const family levels) params →
      params.length = params'.length →
      (∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) →
      Wrap Γ Y (structExpand family info levels params' Y')
  | app {F F' a : VExpr} : Wrap Γ F F' → Wrap Γ (.app F a) (.app F' a)

theorem Wrap.defeq {Γ : List VExpr} {Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (W : Wrap Γ Y Y') (hY : Γ ⊢ Y : T) : Γ ⊢ Y ≡ Y' := by
  induction W generalizing T with
  | rfl => exact ⟨_, hY⟩
  | @eta Y Y' A A' B u _ hY' hA ih =>
    have h1 := ih hY
    have hbody : A' :: Γ ⊢ .app Y'.lift (.bvar 0) : B := by
      have h0 : A' :: Γ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app (hY'.weak henv.ordered) h0
    have hlam : Γ ⊢ .lam A' (.app Y'.lift (.bvar 0)) ≡ .lam A (.app Y'.lift (.bvar 0)) :
        .forallE A' B := .lamDF hA.symm hbody
    have h2 : Γ ⊢ Y' ≡ .lam A (.app Y'.lift (.bvar 0)) := ⟨_, (IsDefEq.eta hY').symm⟩
    have h3 : Γ ⊢ .lam A (.app Y'.lift (.bvar 0)) ≡ .lam A' (.app Y'.lift (.bvar 0)) :=
      ⟨_, hlam.symm⟩
    exact h1.trans henv hΓ (h2.trans henv hΓ h3)
  | struct _ hl hp hi hY' hexp hlen hps ih =>
    have h1 := ih hY
    have h2 : _ ⊢ _ ≡ structExpand _ _ _ _ _ := ⟨_, (IsDefEq.structEta hl hp hi hY' hexp).symm⟩
    refine (h1.trans henv hΓ h2).trans henv hΓ ?_
    simp only [structExpand_eq] at hexp ⊢
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hexp⟩
    refine IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ ?_ hexp
    refine List.Forall₂.append' (List.forall₂_of_getElem hlen fun i hi hi' => ?_)
      (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
    · obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hexp
        (List.mem_append_left _ (List.getElem_mem hi))
      exact (hps i hi hi').defeq hΓ hpT
    · obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hexp
        (List.mem_append_right _ (List.mem_map.mpr ⟨j, by simpa using hj, Eq.refl _⟩))
      simp only [List.getElem_map, List.getElem_range]
      exact ⟨_, hpj⟩
  | app _ ih =>
    obtain ⟨_, _, hF, ha⟩ := hY.app_inv henv hΓ
    exact ⟨_, .appDF ((ih hF).of_l henv hΓ hF) ha⟩

omit [Params] in
theorem mkApps_eq_cases' {H Z : VExpr} {args : List VExpr} (he : mkApps H args = Z) :
    (args = [] ∧ Z = H) ∨ ∃ args₀ x, args = args₀ ++ [x] ∧ Z = .app (mkApps H args₀) x := by
  rcases eq_nil_or_snoc' args with rfl | ⟨args₀, x, rfl⟩
  · exact .inl ⟨rfl, he.symm⟩
  · exact .inr ⟨args₀, x, rfl, by rw [← he, VExpr.mkApps_snoc]⟩

/-- A parallel eta step on a spine reduces the head and the arguments and wraps partial
applications. -/
theorem EtaPar.spine_inv {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {Z X' T : VExpr} {H : VExpr} {args : List VExpr}, EtaPar Γ Z X' → mkApps H args = Z →
      Γ ⊢ Z : T →
      ∃ H' args', EtaPar Γ H H' ∧ List.Forall₂ (EtaPar Γ) args args' ∧
        Wrap Γ (mkApps H' args') X' := by
  intro Z X' T H args HX
  induction HX generalizing H args T with
  | app hf ha ihf _ =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .app hf ha, .nil, .rfl⟩
    · cases he'
      obtain ⟨_, _, hF, -⟩ := hZ.app_inv henv hΓ
      obtain ⟨H', args₀', hH, hargs, hW⟩ := ihf hΓ rfl hF
      refine ⟨H', args₀' ++ [_], hH, List.Forall₂.append' hargs (.cons ha .nil), ?_⟩
      rw [VExpr.mkApps_snoc]
      exact .app hW
  | funEta H₀ HA hPi ih _ =>
    intro he hZ
    obtain ⟨H', args', hH, hargs, hW⟩ := ih hΓ he hZ
    subst he
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA⟩, -⟩ := hPiT.forallE_inv henv.ordered
    exact ⟨H', args', hH, hargs, .eta hW ((EtaPar.full hΓ H₀ hPi).hasType hΓ hPi)
      ((EtaPar.full hΓ HA hA).defeq hΓ hA)⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih _ =>
    intro he hZ
    obtain ⟨H', args', hH, hargs, hW⟩ := ih hΓ he hZ
    subst he
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    refine ⟨H', args', hH, hargs, .struct hW hl hp hi ((EtaPar.full hΓ H₀ hs).hasType hΓ hs)
      ((FullReduction.structExpand (EtaPar.full hΓ H₀ hs)).hasType hΓ hexp) hlen
      fun i hi hi' => ?_⟩
    obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
    exact EtaNE.of_etaPar hΓ (hps i hi hi') hpT
  | bvar | sort | const | elim =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .rfl, .nil, .rfl⟩
    · cases he'
  | proj h =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .proj h, .nil, .rfl⟩
    · cases he'
  | lam h1 h2 =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .lam h1 h2, .nil, .rfl⟩
    · cases he'
  | forallE h1 h2 =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .forallE h1 h2, .nil, .rfl⟩
    · cases he'

/-- Eta wrappers on the right are absorbed. -/
theorem EtaNE.wrap_r {Γ : List VExpr} {s Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hs : Γ ⊢ s : T) (W : Wrap Γ Y Y') :
    ∀ {as : List VExpr}, EtaNE Γ s (mkApps Y as) → EtaNE Γ s (mkApps Y' as) := by
  induction W with
  | rfl => intro _ H; exact H
  | @eta Y Y' A A' B u W hY' hA ih =>
    intro as H
    have H' := ih H
    have hY'as : Γ ⊢ mkApps Y' as : T := H'.hasType hΓ hs
    cases as with
    | nil => exact EtaNE.root_funEta hΓ hs H' hY' hA
    | cons a rest =>
      have hT : Γ ⊢ mkApps (.app (.lam A' (.app Y'.lift (.bvar 0))) a) rest : T := by
        have h2 : Γ ⊢ Y' ≡ .lam A' (.app Y'.lift (.bvar 0)) :=
          (Wrap.eta (Y := Y') .rfl hY' hA).defeq hΓ hY'
        have h3 : Γ ⊢ mkApps Y' (a :: rest) ≡ mkApps (.lam A' (.app Y'.lift (.bvar 0))) (a :: rest) :=
          IsDefEqU.mkApps_args hΓ h2 (List.forall₂_of_getElem rfl fun i hi hi' =>
            let ⟨_, hx⟩ := schema_mkApps_arg_type hΓ hY'as (List.getElem_mem hi); ⟨_, hx⟩) hY'as
        exact hY'as.defeqU_l henv hΓ h3
      refine .betaR hT ?_
      have hr : mkApps Y' (a :: rest) = mkApps (.app Y' a) rest := rfl
      rw [hr] at H'
      simpa [inst, instVar, inst_lift] using H'
  | struct W hl hp hi hY' hexp hlen hps ih =>
    intro as H
    have H' := ih H
    cases as with
    | nil => exact EtaNE.root_structEta hΓ hs H' hl hp hi hY' hexp hlen hps
    | cons a rest =>
      exfalso
      have hY'as : Γ ⊢ mkApps _ (a :: rest) : T := H'.hasType hΓ hs
      have hY'a : Γ ⊢ mkApps (.app _ a) rest : T := hY'as
      obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hY'a⟩
      have hhead' : Γ ⊢ .app _ a : _ := hhead
      obtain ⟨_, _, hPi, -⟩ := hhead'.app_inv henv hΓ
      exact pi_not_struct hΓ hl hPi hY'
  | app W ih =>
    intro as H
    exact ih (as := _ :: as) H

/-- The congruence part of a parallel eta step: no expansion at the root. -/
inductive EtaParC (Γ : List VExpr) : VExpr → VExpr → Prop where
  | bvar {i : Nat} : EtaParC Γ (.bvar i) (.bvar i)
  | sort {u : VLevel} : EtaParC Γ (.sort u) (.sort u)
  | const {c : Name} {ls : List VLevel} : EtaParC Γ (.const c ls) (.const c ls)
  | elim {block : Name} {owner : Nat} {ls : List VLevel} :
      EtaParC Γ (.elim block owner ls) (.elim block owner ls)
  | app {f f' a a' : VExpr} : EtaPar Γ f f' → EtaPar Γ a a' → EtaParC Γ (.app f a) (.app f' a')
  | proj {m m' : VExpr} {S : Name} {i : Nat} : EtaPar Γ m m' → EtaParC Γ (.proj S i m) (.proj S i m')
  | lam {A A' b b' : VExpr} : EtaPar Γ A A' → EtaPar (A :: Γ) b b' →
      EtaParC Γ (.lam A b) (.lam A' b')
  | forallE {A A' B B' : VExpr} : EtaPar Γ A A' → EtaPar (A :: Γ) B B' →
      EtaParC Γ (.forallE A B) (.forallE A' B')

theorem EtaParC.toEtaPar {Γ : List VExpr} {X X' : VExpr} (H : EtaParC Γ X X') : EtaPar Γ X X' := by
  cases H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app h1 h2 => exact .app h1 h2
  | proj h => exact .proj h
  | lam h1 h2 => exact .lam h1 h2
  | forallE h1 h2 => exact .forallE h1 h2

/-- A root eta expansion: function or structure eta of the whole term. -/
inductive RootStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | funEta {Y A A' B : VExpr} {u : VLevel} : Γ ⊢ Y : .forallE A B → Γ ⊢ A ≡ A' : .sort u →
      RootStep Γ Y (.lam A' (.app Y.lift (.bvar 0)))
  | structEta {Y : VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params params' : List VExpr} : Params.env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ Y : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params Y : mkApps (.const family levels) params →
      params.length = params'.length →
      (∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) →
      RootStep Γ Y (structExpand family info levels params' Y)

abbrev RootChain (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (RootStep Γ)

/-- A parallel eta step is a congruence step followed by root expansions. -/
theorem EtaPar.root_decomp {Γ : List VExpr} {X X' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (HX : EtaPar Γ X X') (hX : Γ ⊢ X : T) :
    ∃ X₀, EtaParC Γ X X₀ ∧ RootChain Γ X₀ X' := by
  induction HX generalizing T with
  | bvar => exact ⟨_, .bvar, .rfl⟩
  | sort => exact ⟨_, .sort, .rfl⟩
  | const => exact ⟨_, .const, .rfl⟩
  | elim => exact ⟨_, .elim, .rfl⟩
  | app h1 h2 => exact ⟨_, .app h1 h2, .rfl⟩
  | proj h => exact ⟨_, .proj h, .rfl⟩
  | lam h1 h2 => exact ⟨_, .lam h1 h2, .rfl⟩
  | forallE h1 h2 => exact ⟨_, .forallE h1 h2, .rfl⟩
  | funEta H₀ HA hPi ih _ =>
    obtain ⟨X₀, hc, hchain⟩ := ih hΓ hPi
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA⟩, -⟩ := hPiT.forallE_inv henv.ordered
    exact ⟨X₀, hc, hchain.tail (.funEta ((EtaPar.full hΓ H₀ hPi).hasType hΓ hPi)
      ((EtaPar.full hΓ HA hA).defeq hΓ hA))⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih _ =>
    obtain ⟨X₀, hc, hchain⟩ := ih hΓ hs
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    refine ⟨X₀, hc, hchain.tail (.structEta hl hp hi ((EtaPar.full hΓ H₀ hs).hasType hΓ hs)
      ((FullReduction.structExpand (EtaPar.full hΓ H₀ hs)).hasType hΓ hexp) hlen
      fun i hi hi' => ?_)⟩
    obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
    exact EtaNE.of_etaPar hΓ (hps i hi hi') hpT

theorem RootStep.defeq {Γ : List VExpr} {Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (R : RootStep Γ Y Y') (hY : Γ ⊢ Y : T) : Γ ⊢ Y ≡ Y' := by
  cases R with
  | funEta hY' hA => exact (Wrap.eta .rfl hY' hA).defeq hΓ hY
  | structEta hl hp hi hY' hexp hlen hps => exact (Wrap.struct .rfl hl hp hi hY' hexp hlen hps).defeq hΓ hY

/-- Root expansions of the head of a spine on the right are absorbed. -/
theorem EtaNE.rootChain_spine_r {Γ : List VExpr} {s Y Y' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (hchain : RootChain Γ Y Y') :
    ∀ {as : List VExpr}, EtaNE Γ s (mkApps Y as) → EtaNE Γ s (mkApps Y' as) := by
  induction hchain with
  | rfl => intro _ H; exact H
  | tail _ step ih =>
    intro as H
    have H' := ih H
    cases step with
    | funEta hY₁ hA => exact EtaNE.wrap_r hΓ hs (.eta .rfl hY₁ hA) H'
    | structEta hl hp hi hY₁ hexp hlen hps =>
      exact EtaNE.wrap_r hΓ hs (.struct .rfl hl hp hi hY₁ hexp hlen hps) H'

/-- A step inside a lambda body is transported to the source's binder context. -/
theorem EtaPar.body_transport {Γ : List VExpr} {A A' b b' T : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hA : Γ ⊢ A ≡ A' : .sort u)
    (hb : A' :: Γ ⊢ b : T) (H : EtaPar (A' :: Γ) b b') : EtaPar (A :: Γ) b b' :=
  H.defeqDFC hΓ (.succ .zero hA.symm) hb

/-- Closure of the eta-normal relation under a parallel eta step on the right. -/
theorem EtaNE.etaPar_r {Γ : List VExpr} {s X X' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (HX : EtaPar Γ X X') : EtaNE Γ s X' := by
  induction H generalizing X' T with
  | refl h => exact EtaNE.of_etaPar hΓ HX hs
  | sortDF h1 h2 h3 =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX ((EtaNE.sortDF h1 h2 h3).hasType hΓ hs)
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) (EtaNE.sortDF h1 h2 h3)
  | constDF h1 h2 h3 h4 h5 =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX ((EtaNE.constDF h1 h2 h3 h4 h5).hasType hΓ hs)
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) (EtaNE.constDF h1 h2 h3 h4 h5)
  | elimDF h1 h2 =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX ((EtaNE.elimDF h1 h2).hasType hΓ hs)
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) (EtaNE.elimDF h1 h2)
  | app H1 H2 ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ
    have hX := (EtaNE.app H1 H2).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | app h1 h2 => exact .app (ih1 hΓ hf h1) (ih2 hΓ ha h2)
  | proj H1 ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ
    have hX := (EtaNE.proj H1).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | proj h => exact .proj (ih hΓ hm.hasType.2 h)
  | @lam Γ A A' b b' u hA Hb ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.lam hA Hb).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | lam h1 h2 =>
      obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
      have hAA : Γ ⊢ A ≡ _ : .sort u :=
        hA.trans ((EtaPar.full hΓ h1 hA.hasType.2).defeq hΓ hA.hasType.2)
      exact .lam hAA (ih hΓ' hb (EtaPar.body_transport hΓ hA hb' h2))
  | @forallE Γ A A' B B' u hA HB ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.forallE hA HB).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | forallE h1 h2 =>
      obtain ⟨-, _, hb'⟩ := hX.forallE_inv henv.ordered
      have hAA : Γ ⊢ A ≡ _ : .sort u :=
        hA.trans ((EtaPar.full hΓ h1 hA.hasType.2).defeq hΓ hA.hasType.2)
      exact .forallE hAA (ih hΓ' hb (EtaPar.body_transport hΓ hA hb' h2))
  | proofIrrel hp h1 h2 =>
    exact .proofIrrel hp h1 ((EtaPar.full hΓ HX h2).hasType hΓ h2)
  | @funEta Γ e A B A' body u hne hPi hA Hb ih =>
    have hX := (EtaNE.funEta hne hPi hA Hb).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | lam h1 h2 =>
      obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
      obtain ⟨-, _, hB⟩ := hPiT.forallE_inv henv.ordered
      have hΓ' : OnCtx (A' :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
      have hPi' : Γ ⊢ e : .forallE A' B := (IsDefEq.forallEDF hA hB).defeq hPi
      have hbody := eta_body_typed hPi'
      have hA'A'' : Γ ⊢ A' ≡ _ : .sort u := (EtaPar.full hΓ h1 hA.hasType.2).defeq hΓ hA.hasType.2
      have inner := ih hΓ' hbody h2
      exact .funEta hne hPi (hA.trans hA'A'') (inner.defeqDFC hΓ (.succ .zero hA'A'') hbody)
  | @structEta Γ family info levels params args e hl hp hi hs' hexp hlen hargs ih =>
    have hX := (EtaNE.structEta hl hp hi hs' hexp hlen hargs).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    have hargsT : ∀ i (hi : i < (structArgs family info params e).length),
        ∃ T, Γ ⊢ (structArgs family info params e)[i] : T := fun i hi => by
      rw [structExpand_eq] at hexp
      exact schema_mkApps_arg_type hΓ hexp (List.getElem_mem hi)
    -- the step on the constructor spine
    obtain ⟨H', args', hH, hF, hW⟩ :=
      EtaPar.spine_inv hΓ (args := args) hc.toEtaPar rfl hX
    have hlen' : (structArgs family info params e).length = args'.length :=
      hlen.trans (Lean4Lean.List.Forall₂.length_eq hF)
    have h1 : EtaNE Γ e (mkApps (.const info.ctorName levels) args') := by
      refine .structEta hl hp hi hs' hexp hlen' fun i hi hi' => ?_
      obtain ⟨_, hT⟩ := hargsT i hi
      exact ih i hi (by omega) hΓ hT (case_forall₂_get hF (by omega) hi')
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hX⟩
    obtain ⟨H₀, hc', hchain'⟩ := EtaPar.root_decomp hΓ hH hhead
    cases hc'
    exact EtaNE.wrap_r hΓ hs hW (as := []) (EtaNE.rootChain_spine_r hΓ hs hchain' h1)
  | @betaR Γ A b a s' T' args hT Hc ih =>
    have hX := (EtaNE.betaR hT Hc).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    obtain ⟨H', as', hH, hF, hW⟩ :=
      EtaPar.spine_inv hΓ (H := .lam A b) (args := a :: args) hc.toEtaPar rfl hX
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
    have hhead' : Γ ⊢ .app (.lam A b) a : _ := hhead
    obtain ⟨A₁, B₁, hlam, ha⟩ := hhead'.app_inv henv hΓ
    obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
    obtain ⟨⟨u, hAA₁⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have ha' : Γ ⊢ a : A := hAA₁.defeq' ha
    obtain ⟨⟨_, hA⟩, -⟩ := hlam.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨L₀, hc', hchain'⟩ := EtaPar.root_decomp hΓ hH hlam
    cases hF with
    | cons ha₁ hargs =>
      cases hc' with
      | lam h1 h2 =>
        have hstep := EtaPar.congrRel.mkApps (EtaPar.instN .zero hΓ' ha₁ ha' h2 hb) hargs
        have h1' := ih hΓ hs hstep
        have hred : EtaPar Γ (mkApps (.app (.lam A b) a) args) (mkApps (.app (.lam _ _) _) _) :=
          EtaPar.congrRel.mkApps (.app (.lam h1 h2) ha₁) hargs
        have h2' := EtaNE.betaR ((EtaPar.full hΓ hred hT).hasType hΓ hT) h1'
        exact EtaNE.wrap_r hΓ hs hW (as := [])
          (EtaNE.rootChain_spine_r hΓ hs hchain' (as := _ :: _) h2')
  | betaL hT Hc ih => exact .betaL hT (ih hΓ (hT.defeqU_l henv hΓ (beta_defeqU hΓ hT)) HX)
  | projIotaL hl hT hi hf Hc ih => exact .projIotaL hl hT hi hf (ih hΓ hf HX)

/-- Every eta chain from a typed term is an eta-normal expansion. -/
theorem EtaNE.of_etaChain {Γ : List VExpr} {e X T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : EtaChain Γ e X) (he : Γ ⊢ e : T) :
    EtaNE Γ e X := by
  induction H with
  | rfl => exact .refl he
  | tail _ step ih => exact ih.etaPar_r hΓ he step

/-- A lift of a type related to a `Π` reduces below to a `Π`: the only non-syntactic cases are
the administrative redexes on the left, which are redexes of the term below. -/
theorem EtaNE.forallE_inv_lift (hTF : TypedFrontN Params.env) {k : Nat} {Γ Γ' : List VExpr}
    {F A B : VExpr} {u : VLevel} (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (hF : Γ ⊢ F : .sort u)
    (H : EtaNE Γ' (F.liftN 1 k) (.forallE A B)) : ∃ A₀ B₀, FullReduction Γ F (.forallE A₀ B₀) := by
  generalize hs : F.liftN 1 k = s at H
  generalize hr : VExpr.forallE A B = r at H
  induction H generalizing F A B with
  | refl _ =>
    subst hr
    obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hs
    exact ⟨A₀, B₀, .rfl⟩
  | forallE =>
    cases hr
    obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hs
    exact ⟨A₀, B₀, .rfl⟩
  | proofIrrel hp h1 h2 =>
    subst hr hs
    have hF' := hF.weakN henv.ordered W
    have h3 := (hF'.uniqU henv hΓ' h1).of_r henv hΓ' hp
    have h4 := IsDefEq.uniqU henv hΓ' (HasType.sort (hF'.sort_r henv.ordered hΓ')) h3.hasType.1
    have h5 := congrFun (h4.sort_inv henv hΓ') []
    simp [VLevel.eval] at h5
  | funEta _ hPi =>
    subst hs
    exact (type_not_function hΓ' (hF.weakN henv.ordered W) hPi).elim
  | structEta hl _ _ hs' =>
    subst hs
    exact (type_not_structure hΓ' (hF.weakN henv.ordered W) hl hs').elim
  | betaR hT =>
    exact (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hr.symm).elim
  | @betaL Γ' A₁ b a T X hT _ ih =>
    subst hr
    obtain ⟨f₀, a₀, rfl, hf, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hf.symm
    have hstep : FullStep Γ (.app (.lam A₀ b₀) a₀) (b₀.inst a₀) := .core (.beta .rfl .rfl)
    have hF' := hstep.hasType hΓ hF
    obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' hF' (by rw [VExpr.liftN_inst_hi]) rfl
    exact ⟨A₂, B₂, (ReflTransGen.tail .rfl hstep).trans hred⟩
  | @projIotaL Γ' S info i ls args T field X hl hT hi hf _ ih =>
    subst hr
    obtain ⟨m₀, rfl, hm⟩ := liftN_eq_proj_inv hs
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hm.symm
    obtain ⟨field₀, hget, rfl⟩ : ∃ field₀, args₀[info.nparams + i]? = some field₀ ∧
        field = field₀.liftN 1 k := by
      rw [List.getElem?_map] at hi
      obtain ⟨f₀, hf₀, rfl⟩ := Option.map_eq_some_iff.mp hi
      exact ⟨f₀, hf₀, rfl⟩
    -- the field is typed below at the projection's type
    have hF' := hF.weakN henv.ordered W
    simp only [liftN, VExpr.liftN_mkApps] at hF'
    have hTu : _ ⊢ T ≡ .sort u := hT.uniqU henv hΓ' hF'
    have hfu : _ ⊢ field₀.liftN 1 k : .sort u := hf.defeqU_r henv hΓ' hTu
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := hF.proj_inv henv hΓ
    obtain ⟨_, hfield₀⟩ := HasType.mkApps_args_typed hΓ hmajor.hasType.2 field₀
      (List.mem_of_getElem? hget)
    have hf₀ : Γ ⊢ field₀ : .sort u :=
      hTF.retype henv W hΓ hΓ' hfield₀ (HasType.sort (hF.sort_r henv.ordered hΓ)) hfu
    have hstep : FullStep Γ (.proj S i (mkApps (.const info.ctorName ls) args₀)) field₀ :=
      .projIota hl hF hget hf₀
    obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' hf₀ rfl rfl
    exact ⟨A₂, B₂, (ReflTransGen.tail .rfl hstep).trans hred⟩
  | sortDF | constDF | elimDF | app | proj | lam => cases hr

end

end Lean4Lean.VEnv.StrengtheningEtaNormal
