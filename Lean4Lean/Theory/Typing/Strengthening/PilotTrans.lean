import Lean4Lean.Theory.Typing.Strengthening.ProofAware

/-! # Towards transitivity of pilot conversion

The diagram lemmas for `Cert.trans` (`Cert .conv Γ a b → Cert .conv Γ b c → Cert .conv Γ a c`),
written as Lean statements. This file holds the parts that are proved; the attempt itself and
the recursive-call analysis are recorded in `docs/inductives/STRENGTHENING_A_LOG.md`.

* `PStep`: the eta-free, equation-free parallel step (beta and congruences), context-free. It
  embeds into certified steps (`PStep.toCert`), is closed under lifting and substitution
  (`PStep.liftN`, `PStep.inst`) and has the diamond property (`PStep.diamond`); its reflexive
  transitive closure `PRed` is confluent (`PRed.confluent`) and embeds into certified
  reduction (`PRed.toCert`).
* Shape lemmas for certified reduction: reducts of a sort are the sort (`CRed.sort_inv`),
  reducts of a `Π` are `Π`s with reduced domain (`CRed.forallE_inv`), reducts of a `λ` are
  `λ`s (`CRed.lam_inv`); `CRed.trans`.
* `Cert.norm_refl_of_ty`, `Cert.conv_refl_of_ty`: a certified-typed term is normally equal
  and convertible to itself.
* `CComplete`: completeness of the pilot for typing and conversion; `Cancel.of_cComplete`:
  completeness gives `Cancel` (the theorem announced in `Pilot.lean`), by `IsDefEqU.lam_body`,
  completeness in the extended context, `Cert.descend` and `Cert.sound`.
* The strip lemma `CConv.trans_of`: transitivity follows from three stated obligations,
  confluence of certified reduction modulo normal equality (`RedConfluent`), transport of
  normal equality along certified reduction (`NormTransport`) and transitivity of normal
  equality (`NormTrans`), all for declaratively typed endpoints. -/

namespace Lean4Lean
namespace VEnv
open VExpr

variable {env : VEnv} {U : Nat}

/-! ## Pilot syntax -/

/-- The pilot syntax: no projections, no case eliminators. -/
def _root_.Lean4Lean.VExpr.IsPilot : VExpr → Prop
  | .bvar _ | .sort _ | .const _ _ => True
  | .elim .. | .proj .. => False
  | .app f a => f.IsPilot ∧ a.IsPilot
  | .lam A b | .forallE A b => A.IsPilot ∧ b.IsPilot

/-! ## The eta-free, equation-free parallel step -/

/-- Parallel beta reduction on pilot syntax, without eta and without stored equations. It
does not depend on the context. -/
inductive PStep : VExpr → VExpr → Prop
  | bvar : PStep (.bvar i) (.bvar i)
  | sort : PStep (.sort l) (.sort l)
  | const : PStep (.const c ls) (.const c ls)
  | app : PStep f f' → PStep a a' → PStep (.app f a) (.app f' a')
  | lam : PStep A A' → PStep b b' → PStep (.lam A b) (.lam A' b')
  | forallE : PStep A A' → PStep B B' → PStep (.forallE A B) (.forallE A' B')
  | beta : PStep b b' → PStep a a' → PStep (.app (.lam A b) a) (b'.inst a')

/-- Every eta-free parallel step is a certified step, in every context. -/
theorem PStep.toCert (h : PStep a b) : CStep env U Γ a b := by
  induction h generalizing Γ with
  | bvar => exact .step_bvar
  | sort => exact .step_sort
  | const => exact .step_const
  | app _ _ ihf iha => exact .step_app ihf iha
  | lam _ _ ihA ihb => exact .step_lam ihA ihb
  | forallE _ _ ihA ihB => exact .step_forallE ihA ihB
  | beta _ _ ihb iha => exact .step_beta ihb iha

theorem _root_.Lean4Lean.VExpr.IsPilot.pstep_rfl : ∀ {e : VExpr}, e.IsPilot → PStep e e
  | .bvar _, _ => .bvar
  | .sort _, _ => .sort
  | .const _ _, _ => .const
  | .app _ _, ⟨h1, h2⟩ => .app h1.pstep_rfl h2.pstep_rfl
  | .lam _ _, ⟨h1, h2⟩ => .lam h1.pstep_rfl h2.pstep_rfl
  | .forallE _ _, ⟨h1, h2⟩ => .forallE h1.pstep_rfl h2.pstep_rfl

theorem PStep.liftN (h : PStep a b) : PStep (a.liftN n k) (b.liftN n k) := by
  induction h generalizing k with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | beta _ _ ihb iha =>
    simp only [VExpr.liftN, liftN_inst_hi]
    exact .beta ihb iha

/-- Substitution for the eta-free step: both the body and the substituted term may step. -/
theorem PStep.inst (h : PStep e e') (ha : PStep a a') : PStep (e.inst a k) (e'.inst a' k) := by
  induction h generalizing k with
  | @bvar i =>
    simp only [VExpr.inst, instVar]
    split
    · exact .bvar
    split
    · exact ha.liftN
    · exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | beta _ _ ihb iha =>
    simp only [VExpr.inst, inst0_inst_hi]
    exact .beta ihb iha

theorem PStep.lam_inv (h : PStep (.lam A b) x) :
    ∃ A' b', x = .lam A' b' ∧ PStep A A' ∧ PStep b b' := by
  cases h with
  | lam hA hb => exact ⟨_, _, rfl, hA, hb⟩

/-- **Diamond property** of the eta-free parallel step. -/
theorem PStep.diamond (h1 : PStep a b) (h2 : PStep a c) : ∃ d, PStep b d ∧ PStep c d := by
  induction h1 generalizing c with
  | bvar => cases h2; exact ⟨_, .bvar, .bvar⟩
  | sort => cases h2; exact ⟨_, .sort, .sort⟩
  | const => cases h2; exact ⟨_, .const, .const⟩
  | app hf ha ihf iha =>
    cases h2 with
    | app hf₂ ha₂ =>
      obtain ⟨f₃, h1, h2⟩ := ihf hf₂
      obtain ⟨a₃, h3, h4⟩ := iha ha₂
      exact ⟨_, .app h1 h3, .app h2 h4⟩
    | beta hb₂ ha₂ =>
      obtain ⟨A', b', rfl, hA, hb⟩ := hf.lam_inv
      obtain ⟨d, h1, h2⟩ := ihf (.lam hA hb₂)
      obtain ⟨A'', b₃, rfl, -, h1⟩ := h1.lam_inv
      obtain ⟨a₃, h3, h4⟩ := iha ha₂
      cases h2 with
      | lam _ h2 => exact ⟨_, .beta h1 h3, h2.inst h4⟩
  | lam _ _ ihA ihb =>
    cases h2 with
    | lam hA₂ hb₂ =>
      obtain ⟨_, h1, h2⟩ := ihA hA₂
      obtain ⟨_, h3, h4⟩ := ihb hb₂
      exact ⟨_, .lam h1 h3, .lam h2 h4⟩
  | forallE _ _ ihA ihB =>
    cases h2 with
    | forallE hA₂ hB₂ =>
      obtain ⟨_, h1, h2⟩ := ihA hA₂
      obtain ⟨_, h3, h4⟩ := ihB hB₂
      exact ⟨_, .forallE h1 h3, .forallE h2 h4⟩
  | beta _ _ ihb iha =>
    cases h2 with
    | app hf₂ ha₂ =>
      obtain ⟨A₂, b₂, rfl, hA₂, hb₂⟩ := hf₂.lam_inv
      obtain ⟨_, h1, h2⟩ := ihb hb₂
      obtain ⟨_, h3, h4⟩ := iha ha₂
      exact ⟨_, h1.inst h3, .beta h2 h4⟩
    | beta hb₂ ha₂ =>
      obtain ⟨_, h1, h2⟩ := ihb hb₂
      obtain ⟨_, h3, h4⟩ := iha ha₂
      exact ⟨_, h1.inst h3, h2.inst h4⟩

/-- Eta-free parallel reduction. -/
def PRed : VExpr → VExpr → Prop := ReflTransGen PStep

theorem PRed.strip (h1 : PStep a b) (h2 : PRed a c) : ∃ d, PRed b d ∧ PStep c d := by
  induction h2 with
  | rfl => exact ⟨_, .rfl, h1⟩
  | tail _ h ih =>
    obtain ⟨d, hd, hc⟩ := ih
    obtain ⟨e, h3, h4⟩ := hc.diamond h
    exact ⟨_, hd.tail h3, h4⟩

/-- **Confluence** of eta-free parallel reduction. -/
theorem PRed.confluent (h1 : PRed a b) (h2 : PRed a c) : ∃ d, PRed b d ∧ PRed c d := by
  induction h1 with
  | rfl => exact ⟨_, h2, .rfl⟩
  | tail _ h ih =>
    obtain ⟨d, hd, hc⟩ := ih
    obtain ⟨e, h3, h4⟩ := PRed.strip h hd
    exact ⟨_, h3, hc.tail h4⟩

/-! ## Certified reduction: composition and shapes -/

/-- The composition statement for reductions. -/
def Cert.TransShape (env : VEnv) (U : Nat) : CKind → List VExpr → VExpr → VExpr → Prop
  | .red, Γ, a, b => ∀ c, CRed env U Γ b c → CRed env U Γ a c
  | _, _, _, _ => True

theorem Cert.transShape (H : Cert env U k Γ a b) : Cert.TransShape env U k Γ a b := by
  induction H with
  | red_refl => exact fun _ h => h
  | red_step h _ _ ih => exact fun c hc => .red_step h (ih c hc)
  | _ => trivial

theorem CRed.trans (h1 : CRed env U Γ a b) (h2 : CRed env U Γ b c) : CRed env U Γ a c :=
  h1.transShape _ h2

/-- Every stored equation has a constant-headed left side (definitional unfoldings, recursor
and quotient rules). Needed only to know that no stored equation rewrites a sort, a `Π` or a
`λ`. -/
def ConstHeadedEquations (env : VEnv) : Prop :=
  ∀ df, env.defeqs df → ∃ c ls args, df.lhs = VExpr.mkApps (.const c ls) args

theorem ConstHeadedEquations.lhs_ne_sort (hex : ConstHeadedEquations env) (h : env.defeqs df) :
    df.lhs.instL ls ≠ .sort l := by
  obtain ⟨c, ls', args, hl⟩ := hex df h
  rw [hl, instL_mkApps]
  exact mkApps_ne_sort (fun _ h => by cases h) _

theorem ConstHeadedEquations.lhs_ne_forallE (hex : ConstHeadedEquations env)
    (h : env.defeqs df) : df.lhs.instL ls ≠ .forallE A B := by
  obtain ⟨c, ls', args, hl⟩ := hex df h
  rw [hl, instL_mkApps]
  exact mkApps_ne_forallE (fun _ _ h => by cases h) _

theorem ConstHeadedEquations.lhs_ne_lam (hex : ConstHeadedEquations env) (h : env.defeqs df) :
    df.lhs.instL ls ≠ .lam A e := by
  obtain ⟨c, ls', args, hl⟩ := hex df h
  rw [hl, instL_mkApps]
  exact mkApps_ne_lam (fun _ _ h => by cases h) _

theorem PRed.toCert (h : PRed a b) : CRed env U Γ a b := by
  induction h with
  | rfl => exact .red_refl
  | tail _ h ih => exact ih.trans (.red_step h.toCert .red_refl)

/-- The shape statement for sorts: a step or reduction from a sort stays at the sort. -/
def Cert.SortShape : CKind → List VExpr → VExpr → VExpr → Prop
  | .step, _, a, b | .red, _, a, b => ∀ l, a = .sort l → b = .sort l
  | _, _, _, _ => True

theorem Cert.sortShape (hex : ConstHeadedEquations env) (H : Cert env U k Γ a b) :
    Cert.SortShape k Γ a b := by
  induction H with
  | step_sort => exact fun _ h => h
  | step_eta h1 _ _ ih2 =>
    intro l hl
    subst hl
    cases h1
    cases ih2 _ rfl
  | red_refl => exact fun _ h => h
  | red_step _ _ ih1 ih2 => exact fun l hl => ih2 l (ih1 l hl)
  | step_extra h => exact fun l hl => absurd hl (hex.lhs_ne_sort h)
  | step_bvar | step_const | step_app | step_lam | step_forallE | step_beta =>
    intro l hl; cases hl
  | _ => trivial

/-- A certified reduct of a sort is the sort. -/
theorem CRed.sort_inv (hex : ConstHeadedEquations env) (H : CRed env U Γ (.sort l) b) :
    b = .sort l := H.sortShape hex _ rfl

/-- A certified step from a sort is trivial. -/
theorem CStep.sort_inv (hex : ConstHeadedEquations env) (H : CStep env U Γ (.sort l) b) :
    b = .sort l := H.sortShape hex _ rfl

/-- The shape statement for `Π` and `λ`: reducts of a `Π` are `Π`s with a reduced domain,
reducts of a `λ` are `λ`s. -/
def Cert.BinderShape (env : VEnv) (U : Nat) : CKind → List VExpr → VExpr → VExpr → Prop
  | .step, Γ, a, b | .red, Γ, a, b =>
    (∀ A B, a = .forallE A B → ∃ A' B', b = .forallE A' B' ∧ CRed env U Γ A A') ∧
    (∀ A e, a = .lam A e → ∃ A' e', b = .lam A' e')
  | _, _, _, _ => True

theorem Cert.binderShape (hex : ConstHeadedEquations env) (H : Cert env U k Γ a b) :
    Cert.BinderShape env U k Γ a b := by
  induction H with
  | step_forallE hA _ =>
    refine ⟨fun A B h => ?_, fun A e h => ?_⟩
    · cases h; exact ⟨_, _, rfl, .red_step hA .red_refl⟩
    · cases h
  | step_lam =>
    refine ⟨fun A B h => ?_, fun A e h => ?_⟩
    · cases h
    · cases h; exact ⟨_, _, rfl⟩
  | step_eta h1 h2 =>
    refine ⟨fun A B h => ?_, fun A e h => ⟨_, _, rfl⟩⟩
    subst h
    cases h1
    cases CRed.sort_inv hex h2
  | red_refl =>
    exact ⟨fun A B h => ⟨_, _, h, .red_refl⟩, fun A e h => ⟨_, _, h⟩⟩
  | red_step _ _ ih1 ih2 =>
    refine ⟨fun A B h => ?_, fun A e h => ?_⟩
    · obtain ⟨A', B', rfl, hA⟩ := ih1.1 A B h
      obtain ⟨A'', B'', rfl, hA'⟩ := ih2.1 A' B' rfl
      exact ⟨_, _, rfl, hA.trans hA'⟩
    · obtain ⟨A', e', rfl⟩ := ih1.2 A e h
      exact ih2.2 A' e' rfl
  | step_extra h =>
    exact ⟨fun A B hl => absurd hl (hex.lhs_ne_forallE h),
      fun A e hl => absurd hl (hex.lhs_ne_lam h)⟩
  | step_bvar | step_sort | step_const | step_app | step_beta =>
    refine ⟨fun A B h => ?_, fun A e h => ?_⟩ <;> cases h
  | _ => trivial

/-- A certified reduct of a `Π` is a `Π` whose domain is a certified reduct of the domain. -/
theorem CRed.forallE_inv (hex : ConstHeadedEquations env) (H : CRed env U Γ (.forallE A B) b) :
    ∃ A' B', b = .forallE A' B' ∧ CRed env U Γ A A' := (H.binderShape hex).1 _ _ rfl

/-- A certified reduct of a `λ` is a `λ`. -/
theorem CRed.lam_inv (hex : ConstHeadedEquations env) (H : CRed env U Γ (.lam A e) b) :
    ∃ A' e', b = .lam A' e' := (H.binderShape hex).2 _ _ rfl

/-! ## Reflexivity -/

/-- Reflexivity of normal equality and conversion for certified-typed terms. -/
def Cert.ReflShape (env : VEnv) (U : Nat) : CKind → List VExpr → VExpr → VExpr → Prop
  | .ty, Γ, e, _ => CNorm env U Γ e e ∧ CConv env U Γ e e
  | _, _, _, _ => True

theorem Cert.reflShape (H : Cert env U k Γ a b) : Cert.ReflShape env U k Γ a b := by
  induction H with
  | ty_bvar => exact ⟨.norm_bvar, .conv_mk .red_refl .red_refl .norm_bvar⟩
  | ty_sort h =>
    exact ⟨.norm_sort h h rfl, .conv_mk .red_refl .red_refl (.norm_sort h h rfl)⟩
  | ty_const h1 h2 h3 =>
    exact ⟨.norm_const h1 h2 h2 h3 (VLevel.forall₂_equiv_refl _),
      .conv_mk .red_refl .red_refl (.norm_const h1 h2 h2 h3 (VLevel.forall₂_equiv_refl _))⟩
  | ty_app _ _ _ _ ihf _ iha =>
    have := Cert.norm_app ihf.1 iha.1
    exact ⟨this, .conv_mk .red_refl .red_refl this⟩
  | ty_lam _ _ _ ihA _ ihb =>
    have := Cert.norm_lam ihA.2 ihb.1
    exact ⟨this, .conv_mk .red_refl .red_refl this⟩
  | ty_forallE _ _ _ _ ihA _ ihB _ =>
    have := Cert.norm_forallE ihA.2 ihB.1
    exact ⟨this, .conv_mk .red_refl .red_refl this⟩
  | _ => trivial

theorem Cert.norm_refl_of_ty (H : CTy env U Γ e T) : CNorm env U Γ e e := H.reflShape.1
theorem Cert.conv_refl_of_ty (H : CTy env U Γ e T) : CConv env U Γ e e := H.reflShape.2

/-! ## Completeness and `Cancel` -/

/-- **Completeness of the pilot** at universe count `U`: every typing has a certified synthesis
and every definitional equality a certified conversion. This is the exact hypothesis under
which the pilot gives `Cancel` (`Cancel.of_cComplete`); it fails in environments whose
definitional equality uses projections, eliminators or the singleton and quotient unfoldings,
so it is the statement "the definitional equality of `env` is generated by pilot rules only". -/
def CComplete (env : VEnv) (U : Nat) : Prop :=
  (∀ {Γ e A}, OnCtx Γ (env.IsType U) → env.HasType U Γ e A → ∃ T, CTy env U Γ e T) ∧
  (∀ {Γ a b A}, OnCtx Γ (env.IsType U) → env.IsDefEq U Γ a b A → CConv env U Γ a b)

/-- Completeness gives cancellation: the body equation is certified in the extended context,
descended by `Cert.descend` (together with the synthesised types of both bodies), and read
back by `Cert.sound`. No inhabitant of the binder is used. -/
theorem Cancel.of_cComplete (henv : env.WF) (hc : ∀ U, CComplete env U) : Cancel env := by
  intro U Γ Q a b hΓ H
  obtain ⟨T₀, H₀⟩ := H
  obtain ⟨u, hQ⟩ := (H₀.hasType.1.lam_inv henv hΓ).1
  have hΓ' : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, u, hQ⟩
  obtain ⟨T, hT⟩ := IsDefEqU.lam_body henv hΓ ⟨T₀, H₀⟩
  have hcv := (hc U).2 hΓ' hT
  obtain ⟨Ta, hTa⟩ := (hc U).1 hΓ' hT.hasType.1
  obtain ⟨Tb, hTb⟩ := (hc U).1 hΓ' hT.hasType.2
  have W : Ctx.LiftN 1 0 Γ (Q :: Γ) := .one
  have hcv' := CConv.descend henv W hcv
  obtain ⟨_, _, hTa'⟩ := CTy.descend henv W hTa
  obtain ⟨_, _, hTb'⟩ := CTy.descend henv W hTb
  exact hcv'.defeq henv hΓ (hTa'.hasType henv hΓ) (hTb'.hasType henv hΓ)

/-! ## The strip lemma from its three obligations -/

/-- Obligation: confluence of certified reduction modulo normal equality, for typed sources. -/
def RedConfluent (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ a b c A}, OnCtx Γ (env.IsType U) → env.HasType U Γ a A →
    CRed env U Γ a b → CRed env U Γ a c →
    ∃ d d', CRed env U Γ b d ∧ CRed env U Γ c d' ∧ CNorm env U Γ d d'

/-- Obligation: transport of normal equality along a certified reduction of its right side, for
typed endpoints. -/
def NormTransport (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ a b b' A B}, OnCtx Γ (env.IsType U) → env.HasType U Γ a A → env.HasType U Γ b B →
    CNorm env U Γ a b → CRed env U Γ b b' →
    ∃ a', CRed env U Γ a a' ∧ CNorm env U Γ a' b'

/-- Obligation: transport along a certified reduction of the left side. -/
def NormTransportL (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ a b a' A B}, OnCtx Γ (env.IsType U) → env.HasType U Γ a A → env.HasType U Γ b B →
    CNorm env U Γ a b → CRed env U Γ a a' →
    ∃ b', CRed env U Γ b b' ∧ CNorm env U Γ a' b'

/-- Obligation: transitivity of normal equality for typed endpoints. -/
def NormTrans (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ a b c A B C}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ a A → env.HasType U Γ b B → env.HasType U Γ c C →
    CNorm env U Γ a b → CNorm env U Γ b c → CNorm env U Γ a c

/-- Transitivity of certified conversion for typed endpoints. -/
def CConv.Trans (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ a b c A B C}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ a A → env.HasType U Γ b B → env.HasType U Γ c C →
    CConv env U Γ a b → CConv env U Γ b c → CConv env U Γ a c

/-- **The strip lemma.** Transitivity of certified conversion follows from confluence of
certified reduction modulo normal equality, transport of normal equality along certified
reduction on either side, and transitivity of normal equality: join the two reductions of the
middle term, transport both normal equalities to the common reducts, compose. -/
theorem CConv.trans_of (henv : env.WF) (hconf : RedConfluent env U)
    (htr : NormTransport env U) (htl : NormTransportL env U) (hnt : NormTrans env U) :
    CConv.Trans env U := by
  intro Γ a b c A B C hΓ ha hb hc h1 h2
  cases h1 with | conv_mk ra rb₁ n1 =>
  cases h2 with | conv_mk rb₂ rc n2 =>
  obtain ⟨d, d', hd, hd', nd⟩ := hconf hΓ hb rb₁ rb₂
  have ha' := (CRed.defeq henv hΓ ra ha).hasType.2
  have hb₁ := (CRed.defeq henv hΓ rb₁ hb).hasType.2
  have hb₂ := (CRed.defeq henv hΓ rb₂ hb).hasType.2
  have hc' := (CRed.defeq henv hΓ rc hc).hasType.2
  obtain ⟨a'', ha'', n1'⟩ := htr hΓ ha' hb₁ n1 hd
  obtain ⟨c'', hc'', n2'⟩ := htl hΓ hb₂ hc' n2 hd'
  have hA'' := (CRed.defeq henv hΓ ha'' ha').hasType.2
  have hD := (CRed.defeq henv hΓ hd hb₁).hasType.2
  have hD' := (CRed.defeq henv hΓ hd' hb₂).hasType.2
  have hC'' := (CRed.defeq henv hΓ hc'' hc').hasType.2
  exact .conv_mk (CRed.trans ra ha'') (CRed.trans rc hc'')
    (hnt hΓ hA'' hD' hC'' (hnt hΓ hA'' hD hD' n1' nd) n2')

end VEnv
end Lean4Lean
