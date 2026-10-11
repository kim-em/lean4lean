import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Inversion of joinable typings

A joinable typing of an application spine relates the spine's type to the declared telescope of
its head by a join (`HasTypeJ.mkApps_wrapForalls`): every conversion on the way is a join, and
joins of Π-types are injective (`FullCRDefEq.forallE_inv`) and stable under substitution
(`FullCRDefEq.instN`). -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

theorem FullCRDefEq.refl_type (hΓ : OnCtx Γ (env.IsType univs)) (h : Γ ⊢ e : T) :
    Γ ⊢ T ≫≪ T :=
  let ⟨_, hT⟩ := h.isType henv.ordered hΓ; .refl hΓ hT

theorem HasTypeJ.app_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeJ Γ (.app f a) T) :
    ∃ A B, HasTypeJ Γ f (.forallE A B) ∧ HasTypeJ Γ a A ∧ Γ ⊢ B.inst a ≫≪ T := by
  generalize he : VExpr.app f a = e at H
  induction H with
  | const => cases he
  | app hf ha h => cases he; exact ⟨_, _, hf, ha, .refl_type hΓ h⟩
  | other hne => exact (hne _ _ he.symm).elim
  | defeq hAB _ _ ih =>
    obtain ⟨A, B, hf, ha, hj⟩ := ih hΓ he
    exact ⟨A, B, hf, ha, hj.trans hΓ hAB⟩

theorem HasTypeJ.const_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeJ Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ Γ ⊢ ci.type.instL ls ≫≪ T := by
  generalize he : VExpr.const c ls = e at H
  induction H with
  | const hc h => cases he; exact ⟨_, hc, .refl_type hΓ h⟩
  | app => cases he
  | other _ hne => exact (hne _ _ he.symm).elim
  | defeq hAB _ _ ih =>
    obtain ⟨ci, hc, hj⟩ := ih hΓ he
    exact ⟨ci, hc, hj.trans hΓ hAB⟩

theorem HasTypeJ.mkApps_head (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f T}, HasTypeJ Γ (VExpr.mkApps f args) T → ∃ T', HasTypeJ Γ f T'
  | [], _, _, H => ⟨_, H⟩
  | a :: as, f, _, H =>
    let ⟨_, H'⟩ := HasTypeJ.mkApps_head hΓ (f := .app f a) (args := as) H
    let ⟨_, _, hf, _⟩ := H'.app_inv hΓ
    ⟨_, hf⟩

/-- One step of a telescope: a join of Π-types instantiated at a typed argument. -/
theorem FullCRDefEq.forallE_inst (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .forallE X Y ≫≪ .forallE A B) (ha : Γ ⊢ a : A) :
    Γ ⊢ a : X ∧ Γ ⊢ Y.inst a ≫≪ B.inst a := by
  obtain ⟨hX, hY⟩ := H.forallE_inv hΓ
  have ha' : Γ ⊢ a : X := ha.defeqU_r henv hΓ (hX.defeq hΓ).symm
  exact ⟨ha', hY.inst0 ha'⟩

/-- **Joinable typing along a telescope.** If every joinable type of `f` joins the telescope
`∀ doms, body`, then every joinable type of `f args` joins `body` instantiated at `args`. -/
theorem HasTypeJ.mkApps_wrapForalls (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms body}, args.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body →
      (∀ T', HasTypeJ Γ f T' → Γ ⊢ VExpr.wrapForalls doms body ≫≪ T') →
      ∀ T', HasTypeJ Γ (VExpr.mkApps f args) T' → Γ ⊢ body.instOuter args ≫≪ T' := by
  intro args
  induction args with
  | nil =>
    intro f doms body hlen _ hcond T' hJ
    cases doms with
    | nil => exact hcond T' hJ
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms body hlen hf hcond T' hJ
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨_, hJa⟩ := HasTypeJ.mkApps_head hΓ (f := .app f a) (args := as) hJ
      obtain ⟨A, B, hJf, hJa', -⟩ := hJa.app_inv hΓ
      obtain ⟨had, -⟩ := (hcond _ hJf).forallE_inst hΓ hJa'.hasType
      have hfa : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      rw [VExpr.wrapForalls_inst] at hfa
      have := ih (f := .app f a) (by simpa using hlen) hfa ?_ T' hJ
      · simpa [hlen] using this
      · intro T'' hJ''
        obtain ⟨A', B', hJf', hJa'', hB⟩ := hJ''.app_inv hΓ
        have ⟨_, hY⟩ := (hcond _ hJf').forallE_inst hΓ hJa''.hasType
        rw [← VExpr.wrapForalls_inst]
        exact hY.trans hΓ hB

/-- Two joinable telescopes of the same length have joinable bodies at arguments that a function
typed by the first telescope accepts. -/
theorem FullCRDefEq.wrapForalls_instOuter (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms doms' body body'}, args.length = doms.length → doms'.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body → VExpr.WF env univs Γ (VExpr.mkApps f args) →
      Γ ⊢ VExpr.wrapForalls doms body ≫≪ VExpr.wrapForalls doms' body' →
      Γ ⊢ body.instOuter args ≫≪ body'.instOuter args := by
  intro args
  induction args with
  | nil =>
    intro f doms doms' body body' hlen hlen' _ _ H
    cases doms with
    | nil => cases doms' with
      | nil => exact H
      | cons => simp at hlen'
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms doms' body body' hlen hlen' hf hwf H
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
    cases doms' with
    | nil => simp at hlen'
    | cons d' ds' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hlen'
      have hfa : VExpr.WF env univs Γ (.app f a) :=
        VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app f a) (by simpa [VExpr.mkApps] using hwf)
      obtain ⟨A, B, hf', ha'⟩ := hfa.app_inv henv.orderedStrong hΓ
      have ⟨⟨_, hdA⟩, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
      have had : Γ ⊢ a : d := ha'.defeqU_r henv hΓ ⟨_, hdA.symm⟩
      obtain ⟨hdd, -⟩ := H.forallE_inv hΓ
      have had' : Γ ⊢ a : d' := had.defeqU_r henv hΓ (hdd.defeq hΓ)
      obtain ⟨-, hY⟩ := H.forallE_inst hΓ had'
      have hfa' : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      have hY' : Γ ⊢ (VExpr.wrapForalls ds body).inst a ≫≪ (VExpr.wrapForalls ds' body').inst a := hY
      rw [VExpr.wrapForalls_inst] at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.wrapForalls_inst] at hY'
      have := ih (f := .app f a) (by simpa using hlen) (by simpa [hlen] using hlen') hfa'
        (by simpa [VExpr.mkApps] using hwf) hY'
      simpa [hlen, hlen'] using this

end Lean4Lean.VEnv
