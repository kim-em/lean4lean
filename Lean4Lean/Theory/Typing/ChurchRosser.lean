import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.NativeOrigin
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.QuotPrefixReduction

namespace Lean4Lean
open Lean4Lean

namespace VEnv

open VExpr

/-- A finite structural derivation realizing an installed equation in the
chosen native/schema reduction presentation. The full presentation adds
checked singleton and quotient prefix replay for zero-source occurrences. -/
inductive NativeReductionTrace (env : VEnv) (U : Nat)
    (Pat : (p : Pattern) → p.RHS × p.Check → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | refl : NativeReductionTrace env U Pat Γ e e
  | trans : NativeReductionTrace env U Pat Γ e e' →
      NativeReductionTrace env U Pat Γ e' e'' → NativeReductionTrace env U Pat Γ e e''
  | native : Pat p r → p.Matches e levels values →
      r.2.OK (IsDefEqU env U Γ) levels values →
      NativeReductionTrace env U Pat Γ e (r.1.apply levels values)
  | schema : AppliedSchemaReduction env U Γ e e' → NativeReductionTrace env U Pat Γ e e'
  | beta : NativeReductionTrace env U Pat Γ (.app (.lam domain body) arg) (body.inst arg)
  | app : NativeReductionTrace env U Pat Γ fn fn' → NativeReductionTrace env U Pat Γ arg arg' →
      NativeReductionTrace env U Pat Γ (.app fn arg) (.app fn' arg')
  | lam : NativeReductionTrace env U Pat (domain :: Γ) body body' →
      NativeReductionTrace env U Pat Γ (.lam domain body) (.lam domain body')

class Params where
  env : VEnv
  henv : env.WF
  univs : Nat
  recursorData : Name → Option InductiveSignature.NativeRecursorData
  recursorData_registered : recursorData name = some data →
    NativeRecursorRegistered env data ∧ data.name = name
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  pat_origin : Pat p r → NativePatternOrigin env p
  /-- Inductive iota heads retain finite compilation and their case registry.
  Primitive quotient iota retains its exact installed declarations instead.
  Both large-elimination paths exclude zero-source computation here. -/
  pat_recursor : Pat (SimplePattern.iota recursor major ctor fields).toPattern r →
    (∃ data, NativeRecursorRegistered env data ∧ data.name = recursor ∧ data.majorOffset = major ∧ recursorData recursor = some data ∧
      (data.largeTarget = true → ∃ rest,
        r.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest)) ∨
    (QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, r.2 = .nonzero (.param 0) rest)
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  pat_wf : OnCtx Γ (env.IsType univs) → Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
variable [Params]
open Params

theorem Params.pat_not_var : ¬Pat (.var p) r := (nomatch pat_simple ·)

theorem Params.pat_not_elim (H : Pat p r)
    (hm : p.Matches (.elim block owner levels) m1 m2) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple H
  cases sp <;> cases hm

/-- Every fixed node of a native pattern has a native constant head. -/
def NativeHeads : Pattern → Prop
  | .const _ => True
  | .elim _ _ => False
  | .app fn arg => NativeHeads fn ∧ NativeHeads arg
  | .var fn => NativeHeads fn

omit [Params] in
theorem NativeHeads.varN (h : NativeHeads p) : NativeHeads (p.varN n) := by
  induction n with
  | zero => exact h
  | succ _ ih => exact ih

theorem Params.nativeHeads (h : Pat p r) : NativeHeads p := by
  obtain ⟨sp, rfl⟩ := pat_simple h
  cases sp with
  | defn => trivial
  | iota => exact ⟨NativeHeads.varN trivial, NativeHeads.varN trivial⟩

omit [Params] in
private theorem native_spine_go_head (e : VExpr) (args : List VExpr) :
    (VExpr.getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app fn arg ih _ => exact (ih (arg :: args)).trans (ih [arg]).symm
  | _ => rfl

omit [Params] in
theorem NativeHeads.matches_head (hp : NativeHeads p) (hm : p.Matches e levels values) :
    ∃ name, e.getAppFnArgs.1 = .const name levels := by
  induction hm with
  | const => exact ⟨_, rfl⟩
  | elim => cases hp
  | app hf ha ih _ =>
    obtain ⟨name, h⟩ := ih hp.1
    exact ⟨name, (native_spine_go_head _ [_]).trans h⟩
  | var hf ih =>
    obtain ⟨name, h⟩ := ih hp
    exact ⟨name, (native_spine_go_head _ [_]).trans h⟩

omit [Params] in
theorem NativeHeads.subpattern (H : NativeHeads parent) (hs : Subpattern child parent) : NativeHeads child := by
  induction hs with
  | refl => exact H
  | appL _ ih => exact ih H.1
  | appR _ ih => exact ih H.2
  | varL _ ih => exact ih H

omit [Params] in
theorem matches_nativeHead {p : Pattern} {e : VExpr} {levels : List VLevel} {values : p.Path → VExpr} (hm : p.Matches e levels values)
    (hh : e.getAppFnArgs.1 = .const name us) : p.nativeHead = some name := by
  induction hm with
  | const => cases hh; rfl
  | elim => cases hh
  | app _ _ ih _ => exact ih ((native_spine_go_head _ [_]).symm.trans hh)
  | var _ ih => exact ih ((native_spine_go_head _ [_]).symm.trans hh)

theorem Params.not_rigid_match (h : env.NativeHeadRigid name) (hp : Pat p r)
    (hm : p.Matches e levels values) (hh : e.getAppFnArgs.1 = .const name us) : False := by
  obtain ⟨equation, originalName, originalLevels, hd, hn, he⟩ := pat_origin hp
  have hname := matches_nativeHead hm hh
  have heq : originalName = name := Option.some.inj (hn.symm.trans hname)
  subst originalName
  exact h equation hd originalLevels he

/-- A finite trace leaving a native constant must start with its native
delta pattern. Structural/beta/schema steps cannot change a bare constant. -/
theorem NativeReductionTrace.const_pattern
    (H : NativeReductionTrace env univs Pat Γ source output)
    (hsource : source = .const name levels) :
    output = .const name levels ∨ ∃ r, Pat (.const name) r := by
  induction H with
  | refl => exact .inl hsource
  | trans _ _ ih1 ih2 =>
    rcases ih1 hsource with h | h
    · exact ih2 h
    · exact .inr h
  | native hp hm hc =>
    rw [hsource] at hm
    cases hm
    exact .inr ⟨_, hp⟩
  | schema hs =>
    have hh := hs.head
    rw [hsource] at hh
    obtain ⟨block, owner, packed, hh⟩ := hh
    cases hh
  | beta | app | lam => cases hsource

/-- Orthogonality gives priority to a native delta presentation: an iota
pattern at the same recursor cannot coexist with its constant pattern. -/
theorem Params.no_iota_of_const
    (hp : Pat (SimplePattern.iota recursor major ctor fields).toPattern r)
    (hc : Pat (.const recursor) r') : False := by
  have hsub : Subpattern (.const recursor) ((Pattern.const recursor).varN major) := by
    clear hp r
    induction major with
    | zero => exact .refl
    | succ n ih => exact .varL ih
  have h := pat_uniq hp hc (.appL hsub) (p₄ := .const recursor) (by simp [Pattern.inter])
  cases h.1

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- The concrete union of legacy native head computation and declaration-
generated abstract case computation. Only the native branch uses `Params.Pat`;
case equations are obtained from the installed schema registry. -/
inductive HeadComputation (Γ : List VExpr) : VExpr → VExpr → Prop where
  | native : Pat p r → p.Matches e m1 m2 →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    HeadComputation Γ e (r.1.apply m1 m2)
  | schema : AppliedSchemaReduction env univs Γ e e' → HeadComputation Γ e e'

theorem HeadComputation.defeq (H : HeadComputation Γ e e')
    (hΓ : OnCtx Γ (env.IsType univs)) (he : Γ ⊢ e : A) : Γ ⊢ e ≡ e' := by
  cases H with
  | native hp hm hc => exact pat_wf hΓ hp hm he hc
  | schema h => exact h.defeq henv hΓ

/-- Cross-branch overlap at a head is impossible, including when an abstract
case restores to a constructor also mentioned by a native rule. -/
theorem HeadComputation.native_schema_disjoint
    (hp : Pat p r) (hm : p.Matches e m1 m2)
    (hs : AppliedSchemaReduction env univs Γ e e') : False := by
  obtain ⟨pattern, rfl⟩ := pat_simple hp
  exact hs.not_native_match hm

theorem _root_.Lean4Lean.Pattern.Check.OK.weakN (W : Ctx.LiftN n k Γ Γ') {p : Pattern}
    (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ') m1 fun x => (m2 x).liftN n k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.liftN_apply]
  exact h.weakN henv W

theorem _root_.Lean4Lean.Pattern.Check.OK.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H₀ : Γ₀ ⊢ e₀ : A₀)
    {p : Pattern} (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ₁) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 fun x => (m2 x).inst e₀ k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.instN_apply]
  exact h.instN henv W H₀

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem IsDefEq.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) : Γ ⊢ apply m1 m2 r ≡ apply m1 m2' r : A := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact he.trans_l henv hΓ <| .appDF (ih1 h1) (ih2 h2)
  | var path => exact (ih path _ he).of_l henv hΓ he

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem _root_.Lean4Lean.Pattern.Matches.hasType {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (H2 : Γ ⊢ e : V) (a) : ∃ A, Γ ⊢ m2 a : A := by
  induction H generalizing V with
  | const | elim => cases a
  | var _ ih =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec ⟨_, ha⟩ (ih hf)
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec (ih1 hf) (ih2 ha)

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ .sort l₂
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ .const c ls'
  /-- Universe congruence at a disjoint abstract eliminator head. The typing
  witness certifies the selected schema; this rule introduces no computation. -/
  | elimDF :
    Γ ⊢ .elim block owner levels ≡ .elim block owner levels' : A →
    List.Forall₂ (· ≈ ·) levels levels' →
    Γ ⊢ .elim block owner levels ≡ₚ .elim block owner levels'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | projDF :
    Γ ⊢ .proj typeName index major : resultType →
    Γ ⊢ major ≡ₚ major' →
    Γ ⊢ .proj typeName index major ≡ₚ .proj typeName index major'
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    A::Γ ⊢ body₁ ≡ₚ body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e →
    Γ ⊢ e' ≡ₚ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ h'

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e1 ≡ e2 := by
  induction H with
  | elimDF h _ => exact ⟨_, h⟩
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 =>
    exact ⟨_, .appDF ((ih1 hΓ).of_l henv hΓ hf₁) ((ih2 hΓ).of_l henv hΓ ha₁)⟩
  | projDF hproj _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := hproj.proj_inv henv hΓ
    have majorEq := (ihMajor hΓ).of_l henv hΓ hmajor.hasType.2
    exact ⟨_, .projDF hinfo hlevels huvars hparams hindices hfield
      hfieldTyping hmajor (hmajor.trans majorEq) hclosed hguard⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | lamDF hA₁ hA₂ _ ihB =>
    have ⟨_, hB⟩ := ihB ⟨hΓ, _, hA₁.hasType.1⟩
    exact ⟨_, .trans (.symm <| .lamDF hA₁ hB.symm) (.lamDF hA₂ hB.hasType.2)⟩
  | forallEDF hA₁ hA hB₁ _ ihA ihB =>
    exact have hΓ' := ⟨hΓ, _, hA₁.hasType.1⟩
      ⟨_, .trans (.symm <| .forallEDF hA₁ hB₁)
        (.forallEDF (hA₁.transU_l henv hΓ (ihA hΓ)) ((ihB hΓ').of_l henv hΓ' hB₁))⟩
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_r henv hΓ ⟨_, .lamDF hA he⟩ (.eta h1)⟩
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_l henv hΓ (.symm (.eta h1)) ⟨_, .lamDF hA he⟩⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, .proofIrrel h1 h2 h3⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e2 ≡ₚ e1 := by
  induction H with
  | elimDF h heq => exact .elimDF h.symm (heq.flip.imp fun _ _ h => h.symm)
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | projDF hproj hMajor ihMajor =>
    have ⟨_, whole⟩ := (NormalEq.projDF hproj hMajor).defeq hΓ
    exact .projDF whole.hasType.2 (ihMajor hΓ)
  | lamDF h1 h2 h3 ih1 => exact .lamDF h2 h1 (ih1 ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := ⟨hΓ, _, h1.hasType.1⟩
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaR h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaL h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

theorem NormalEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2) :
    Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k := by
  induction H generalizing k Γ' with
  | elimDF h heq => exact .elimDF (h.weakN henv W) heq
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W)
      (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (hproj.weakN henv W) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
     exact .lamDF (h1.weakN henv W) (h2.weakN henv W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN henv W) (ih1 W) (h3.weakN henv W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)

variable! (h₀ : Γ₀ ⊢ e₀ : A₀) in
theorem NormalEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e1 ≡ₚ e2) :
    Γ ⊢ e1.inst e₀ k ≡ₚ e2.inst e₀ k := by
  induction H generalizing Γ k with
  | elimDF h heq => exact .elimDF (h.instN henv h₀ W) heq
  | refl h => exact .refl (h.instN henv W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀) (h4.instN henv W h₀) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (hproj.instN henv W h₀) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (h1.instN henv h₀ W) (h2.instN henv h₀ W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.instN henv h₀ W) (ih1 W) (h3.instN henv W.succ h₀) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaR h1 _ ih =>
    refine .etaR (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀)

variable! (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : Γ₀ ⊢ e₀ ≡ₚ e₀') in
theorem NormalEq.instN_r (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e : A) :
    Γ ⊢ e.inst e₀ k ≡ₚ e.inst e₀' k := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := H.bvar_inv henv hΓ₁; clear H hΓ₁
    induction W generalizing i ty with
    | zero =>
      cases h with simp
      | zero => exact H'
      | succ h => exact .refl (.bvar h)
    | succ _ ih =>
      cases h with simp
      | zero => exact .refl (.bvar .zero)
      | succ h => exact (ih _ _ h).weakN .one
  | sort => exact .refl (.sort (H.sort_inv henv))
  | const =>
    let ⟨_, h1, h2, h3⟩ := H.const_inv henv hΓ₁
    exact .refl (.const h1 h2 h3)
  | elim => exact .refl (H.instN henv W h₀)
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := H.app_inv henv hΓ₁
    specialize ih1 hΓ₁ W h1; have hf := h1.instN henv W h₀
    specialize ih2 hΓ₁ W h2; have ha := h2.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .appDF hf (.defeqU_l henv hΓ (ih1.defeq hΓ) hf) ha
      (.defeqU_l henv hΓ (ih2.defeq hΓ) ha) ih1 ih2
  | proj typeName index major ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := H.proj_inv henv hΓ₁
    have majorNormal := ihMajor hΓ₁ W hmajor.hasType.2
    have natural : Γ₁ ⊢ .proj typeName index major : fieldType :=
      .projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
        hmajor hmajor hclosed hguard
    exact .projDF (natural.instN henv W h₀) majorNormal
  | lam A body ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ₁
    have hA := h1.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .lamDF hA (((ih1 hΓ₁ W h1).defeq hΓ).of_l henv hΓ hA)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    have hA := h1.instN henv W h₀
    exact .forallEDF hA (ih1 hΓ₁ W h1) (h2.instN henv W.succ h₀)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)

variable! (H₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEq.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2) : Γ₂ ⊢ e1 ≡ₚ e2 := by
  induction H generalizing Γ₂ with
  | elimDF h heq => exact .elimDF (h.defeqDFC henv W) heq
  | refl h => refine .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (.defeqDFC henv W h1) (.defeqDFC henv W h2)
      (.defeqDFC henv W h3) (.defeqDFC henv W h4) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (.defeqDFC henv W hproj) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (.defeqDFC henv W h1) (.defeqDFC henv W h2) (ih1 (W.succ h1.hasType.1))
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (.defeqDFC henv W h1) (ih1 W)
      (.defeqDFC henv (W.succ h1.hasType.1) h3) (ih2 (W.succ h1.hasType.1))
  | etaL h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaL (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaR h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaR (.defeqDFC henv W h1) (ih (W.succ h2))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (.defeqDFC henv W h1)
      (.defeqDFC henv W h2) (.defeqDFC henv W h3)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.defeq_l (W : Γ ⊢ A ≡ A' : sort u) (H : A::Γ ⊢ e1 ≡ₚ e2) :
    A'::Γ ⊢ e1 ≡ₚ e2 := defeqDFC hΓ (.succ .zero W) H

private theorem HasType.proj_weakN_iff
    (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ'
        (.proj typeName index (major.liftN n k))
        (resultType.liftN n k) ↔
      env.HasType U Γ (.proj typeName index major) resultType := by
  simpa only [VExpr.liftN] using
    (HasType.weakN_iff
      (e := .proj typeName index major) (A := resultType) henv hΓ' W)

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEq.weakN_inv_DFC (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1.liftN n k ≡ₚ e2.liftN n k) : Γ ⊢ e1 ≡ₚ e2 := by
  generalize eq1 : e1.liftN n k = e1' at H
  generalize eq2 : e2.liftN n k = e2' at H
  induction H generalizing Γ Γ₂ e1 e2 k with
  | elimDF h heq =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h'⟩ := (IsDefEqU.weakN_iff (e1 := .elim _ _ _) (e2 := .elim _ _ _) henv hΓ₂ W).1
      ⟨_, h.defeqDFC henv W₂⟩
    exact .elimDF h' heq
  | refl h =>
    cases eq2; cases liftN_inj.1 eq1
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h'⟩ := (IsDefEqU.weakN_iff henv hΓ₂ W).1 ⟨_, h.defeqDFC henv W₂⟩
    exact .refl h'
  | sortDF h1 h2 h3 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h1 := h1.defeqDFC henv W₂
    replace h2 := h2.defeqDFC henv W₂
    replace h3 := h3.defeqDFC henv W₂
    replace h4 := h4.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have hΓ := hΓ₂.weakN_inv henv W
    have ⟨_, _, l1, l2⟩ :=
      let ⟨_, h⟩ := (VExpr.WF.weakN_iff henv hΓ₂ W (e := .app ..)).1 ⟨_, h1.app h3⟩
      HasType.app_inv henv hΓ h
    have ⟨_, _, r1, r2⟩ :=
      let ⟨_, h⟩ := (VExpr.WF.weakN_iff henv hΓ₂ W (e := .app ..)).1 ⟨_, h2.app h4⟩
      HasType.app_inv henv hΓ h
    have := (IsDefEqU.weakN_iff henv hΓ₂ W).1
      (.trans henv hΓ₂ ((l1.weakN henv W).uniqU henv hΓ₂ h1) (h2.uniqU henv hΓ₂ (r1.weakN henv W)))
    have ⟨⟨_, h5⟩, _⟩ := this.forallE_inv henv hΓ
    exact .appDF (l1.defeqU_r henv hΓ this) r1
      (l2.defeqU_r henv hΓ ⟨_, h5⟩) r2 (ih1 W W₂ rfl rfl) (ih2 W W₂ rfl rfl)
  | projDF hproj _ ihMajor =>
    cases e1 with
    | bvar | sort | const | elim | app | lam | forallE => cases eq1
    | proj sourceName sourceIndex sourceMajor =>
      cases eq1
      cases e2 <;> cases eq2
      have hΓ₂ := (W₂.symm henv).isType' hΓ₀
      have hproj' := hproj.defeqDFC henv W₂
      have ⟨_, hnatural⟩ :=
        (VExpr.WF.weakN_iff (e := .proj _ _ _) henv hΓ₂ W).1 ⟨_, hproj'⟩
      exact .projDF hnatural (ihMajor W W₂ rfl rfl)
  | lamDF h1 h2 _ ih1 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have := (IsDefEq.weakN_iff (A := .sort ..) henv hΓ₂ W).1 <|
      .defeqDFC henv W₂ (h2.symm.trans h1)
    exact .lamDF this this.hasType.1 (ih1 W.succ (W₂.succ h2) rfl rfl)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂' := ((W₂.succ h1).symm henv).isType' hΓ₀
    have h3' := h3.defeqDFC henv (W₂.succ h1)
    replace h4 := (IsDefEq.weakN_iff (A := .sort ..) henv hΓ₂' W.succ).1 h3'
    have := (HasType.weakN_iff (A := .sort ..) henv hΓ₂'.1 W).1 <|
      .defeqDFC henv W₂ h1.hasType.2
    exact .forallEDF this (ih1 W W₂ rfl rfl) h4 (ih2 W.succ (W₂.succ h1) rfl rfl)
  | etaL h1 _ ih =>
    cases e1 <;> cases eq1
    subst eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have hB' := hB.defeqDFC henv (W₂.succ hA)
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := (IsDefEqU.weakN_iff henv hΓ₂' W.succ).1 ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := (IsDefEq.weakN_iff (A := .forallE ..) henv hΓ₂'.1 W).1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaL this (ih W.succ (W₂.succ hA) rfl (by simp [liftN, lift_liftN']))
  | etaR h1 _ ih =>
    subst eq1
    cases e2 <;> cases eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have hB' := hB.defeqDFC henv (W₂.succ hA)
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := (IsDefEqU.weakN_iff henv hΓ₂' W.succ).1 ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := (IsDefEq.weakN_iff (A := .forallE ..) henv hΓ₂'.1 W).1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaR this (ih W.succ (W₂.succ hA) (by simp [liftN, lift_liftN']) rfl)
  | proofIrrel h1 h2 h3 =>
    subst eq1; subst eq2
    have h1' := h1.defeqDFC henv W₂
    have h2' := h2.defeqDFC henv W₂
    have h3' := h3.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h⟩ := (IsDefEqU.weakN_iff henv hΓ₂ W).1 ⟨_, h2'⟩
    have ⟨_, hw⟩ := h2'.uniq henv hΓ₂ (h.weakN henv W)
    exact .proofIrrel
      ((HasType.weakN_iff henv hΓ₂ (A := .sort ..) W).1 (h1'.defeqU_l henv hΓ₂ ⟨_, hw⟩))
      ((HasType.weakN_iff henv hΓ₂ W).1 (hw.defeq h2'))
      ((HasType.weakN_iff henv hΓ₂ W).1 (hw.defeq h3'))

variable! (hΓ' : OnCtx Γ' (IsType env univs)) in
theorem NormalEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k ↔ Γ ⊢ e1 ≡ₚ e2 :=
  ⟨fun H => H.weakN_inv_DFC hΓ' W .zero, fun H => H.weakN W⟩

private def meas : VExpr → Nat
  | .app f a
  | .forallE f a => meas f + meas a + 1
  | .proj _ _ e => meas e + 1
  | .bvar _ | .const .. | .elim .. | .sort _ => 0
  | .lam A e => meas A + meas e + 3

omit [Params] in private theorem meas_liftN : meas (e.liftN n k) = meas e := by
  induction e generalizing k <;> simp [*, meas, liftN]
omit [Params] in private theorem meas_lift : meas e.lift = meas e := meas_liftN

attribute [local simp] meas meas_lift in
theorem NormalEq.trans (hΓ : OnCtx Γ (IsType env univs)) :
    Γ ⊢ e1 ≡ₚ e2 → Γ ⊢ e2 ≡ₚ e3 → Γ ⊢ e1 ≡ₚ e3
  | .elimDF l1 l2, .elimDF r1 r2 =>
    .elimDF (l1.trans_l henv hΓ r1) (l2.trans (fun _ _ _ h1 => h1.trans) r2)
  | .sortDF l1 _ l3, .sortDF r1 r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4) (l5.trans hΓ r5) (l6.trans hΓ r6)
  | .projDF l1 l2, .projDF _ r2 =>
    .projDF l1 (l2.trans hΓ r2)
  | .lamDF l1 l2 l3, .lamDF r1 r2 r3 =>
    have aa := r1.trans_r henv hΓ l2.symm
    .lamDF l1 (aa.symm.trans_l henv hΓ r2) (l3.trans ⟨hΓ, _, l1.hasType.1⟩ (r3.defeq_l hΓ aa))
  | .forallEDF l1 l2 l3 l4, .forallEDF r1 r2 r3 r4 =>
    have r4' := r4.defeq_l hΓ (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
    .forallEDF l1 (l2.trans hΓ r2) l3 (l4.trans ⟨hΓ, _, l1.hasType.1⟩ r4')
  | .etaR l1 ih, .lamDF r1 r2 r3 =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have eq := r1.symm.trans r2
    .etaR (IsDefEq.defeq (.forallEDF eq hB) l1) <|
      (ih.defeq_l hΓ eq).trans ⟨hΓ, _, r2.hasType.2⟩ (r3.defeq_l hΓ r2)
  | .lamDF l1 l2 l3, .etaL r1 ih =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have eq := l2.symm.trans l1
    .etaL (IsDefEq.defeq (.forallEDF eq hB) r1) <|
      (l3.defeq_l hΓ l1).trans ⟨hΓ, _, l1.hasType.2⟩ (ih.defeq_l hΓ eq)
  | H1@(.etaR l1 ihl), .etaL r1 ihr => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have := ihl.trans (by exact ⟨hΓ, _, hA⟩) ihr
    generalize eq : e1.lift = e1' at this
    cases this with first | cases eq | cases liftN_inj.1 eq
    | refl h => exact .refl r1
    | proofIrrel h1 h2 h3 =>
      refine .proofIrrel (IsDefEqU.defeqDF henv hΓ ?_ (HasType.forallE hA h1))
        (.defeqU_l henv hΓ ⟨_, .eta l1⟩ (.lam hA h2))
        (.defeqU_l henv hΓ ⟨_, .eta r1⟩ (.lam hA h3))
      have hw := let ⟨_, h⟩ := hA.isType henv hΓ; h.sort_inv henv
      exact ⟨_, .sortDF ⟨hw, ⟨⟩⟩ ⟨⟩ rfl⟩
    | appDF _ _ _ _ ih => exact (NormalEq.weakN_iff (by exact ⟨hΓ, _, hA⟩) .one).1 ih
  | .refl h, H2 => H2
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)
  | .etaL l1 ih, H2 => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    refine .etaL (.defeqU_l henv hΓ (H2.defeq hΓ) l1) (ih.trans ⟨hΓ, _, hA⟩ ?_)
    exact .appDF (l1.weakN henv .one)
      ((l1.defeqU_l henv hΓ (H2.defeq hΓ)).weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H2) (.refl (.bvar .zero))
  | H1, .refl _ => H1
  | H1, .etaR r1 ih => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    refine .etaR (.defeqU_l henv hΓ (H1.defeq hΓ).symm r1) (.trans ⟨hΓ, _, hA⟩ ?_ ih)
    refine .appDF ((r1.defeqU_l henv hΓ (H1.defeq hΓ).symm).weakN henv .one)
      (r1.weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H1) (.refl (.bvar .zero))
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3
termination_by meas e1 + meas e2 + meas e3

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ₚ m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) :
    Γ ⊢ apply m1 m2 r ≡ₚ apply m1 m2' r := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact .refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact ih path _ he

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⋙ " e2:36 => CParRed Γ e1 e2

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    MatchedCaseStep env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ≫ arguments[i]'(by omega)) →
    Γ ⊢ actual.expr ≫ rule.rhs actual.levels arguments
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | elim : Γ ⊢ .elim block owner ls ≫ .elim block owner ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | proj : Γ ⊢ major ≫ major' →
      Γ ⊢ .proj typeName index major ≫ .proj typeName index major'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

/-- The concrete native and registered-schema head developments, including
parallel reduction of their captured arguments. -/
inductive HeadParallelReduction (Γ : List VExpr) : VExpr → VExpr → Prop where
  | native : Pat p r → p.Matches e m1 m2 →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) →
    HeadParallelReduction Γ e (r.1.apply m1 m2')
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    MatchedCaseStep env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ≫ arguments[i]'(by omega)) →
    HeadParallelReduction Γ actual.expr (rule.rhs actual.levels arguments)

theorem HeadParallelReduction.parRed (H : HeadParallelReduction Γ e e') :
    Γ ⊢ e ≫ e' := by
  cases H with
  | native hp hm hc hr => exact .extra hp hm hc hr
  | schema hm hl hr => exact .schema hm hl hr

/-- A beta-redex cannot simultaneously have an abstract case head. -/
theorem ParRed.app_lam_cases (H : Γ ⊢ .app (.lam A body) arg ≫ out) :
    (∃ fn' arg', Γ ⊢ .lam A body ≫ fn' ∧ Γ ⊢ arg ≫ arg' ∧ out = .app fn' arg') ∨
    (∃ body' arg', A :: Γ ⊢ body ≫ body' ∧ Γ ⊢ arg ≫ arg' ∧ out = body'.inst arg') := by
  generalize he : VExpr.app (.lam A body) arg = source at H
  cases H with
  | schema hm hl hr =>
    have hfn := VExpr.app.inj he |>.1
    exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
  | app hf ha => cases he; exact .inl ⟨_, _, hf, ha, rfl⟩
  | beta hb ha => cases he; exact .inr ⟨_, _, hb, ha, rfl⟩
  | extra hp hm =>
    obtain ⟨sp, rfl⟩ := pat_simple hp
    obtain ⟨name, hhead⟩ := InductiveSignature.CaseSchema.native_pattern_head hm
    rw [← he] at hhead
    cases hhead
  | _ => cases he

/-- A free variable in the major position cannot match a generated case or a
native constructor pattern. -/
theorem ParRed.app_bvar_cases (H : Γ ⊢ .app fn (.bvar i) ≫ out) :
    (∃ fn', Γ ⊢ fn ≫ fn' ∧ out = .app fn' (.bvar i)) ∨
    (∃ A body body', fn = .lam A body ∧ A :: Γ ⊢ body ≫ body' ∧ out = body'.inst (.bvar i)) := by
  generalize he : VExpr.app fn (.bvar i) = source at H
  cases H with
  | schema hm hl hr =>
    have hmajor := VExpr.app.inj he |>.2
    have hne : ∀ (head : VExpr) args, (∀ i, head ≠ .bvar i) →
        VExpr.mkApps head args ≠ .bvar i := by
      intro head args
      induction args generalizing head with
      | nil => exact fun h => h i
      | cons arg args ih => intro _; exact ih _ (by intros; intro h; cases h)
    exact False.elim (hne _ _ (by intros; intro h; cases h) hmajor.symm)
  | app hf ha =>
    cases he
    cases ha with
    | bvar => exact .inl ⟨_, hf, rfl⟩
    | extra _ hm => cases hm
  | beta hb ha =>
    cases he
    cases ha with
    | bvar => exact .inr ⟨_, _, _, rfl, hb, rfl⟩
    | extra _ hm => cases hm
  | extra hp hm =>
    rw [← he] at hm
    obtain ⟨sp, rfl⟩ := pat_simple hp
    cases sp with
    | defn => cases hm
    | iota rec major ctor args =>
      cases hm with
      | app _ hmajor => cases args <;> cases hmajor
  | _ => cases he

def NonNeutral (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  ((∃ p r m1 m2, Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2) ∨
    ∃ rule actual, MatchedCaseStep env univs Γ rule actual ∧ e = actual.expr)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    MatchedCaseStep env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ⋙ arguments[i]'(by omega)) →
    Γ ⊢ actual.expr ⋙ rule.rhs actual.levels arguments
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : ¬NonNeutral Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | elim : ¬NonNeutral Γ (.elim block owner ls) → Γ ⊢ .elim block owner ls ⋙ .elim block owner ls
  | app : ¬NonNeutral Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | proj : ¬NonNeutral Γ (.proj typeName index major) →
      Γ ⊢ major ⋙ major' →
      Γ ⊢ .proj typeName index major ⋙ .proj typeName index major'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ⋙ m2' a) → Γ ⊢ e ⋙ r.1.apply m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .proj .. => .proj ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl

omit [Params] in
private theorem reverse_induction {P : List α → Prop} (hnil : P [])
    (happend : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have h : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => exact hnil
    | cons y ys ih => simpa only [List.reverse_cons] using happend ys.reverse y ih
  simpa only [List.reverse_reverse] using h xs.reverse


theorem schema_mkApps_head_type (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ mkApps fn args : type) : ∃ headType, Γ ⊢ fn : headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, ht⟩
  | cons arg args ih =>
    obtain ⟨_, happ⟩ := ih ht
    obtain ⟨_, _, hfn, _⟩ := happ.app_inv henv hΓ
    exact ⟨_, hfn⟩


theorem schema_mkApps_arg_type (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ mkApps fn args : type) (hmem : arg ∈ args) : ∃ argType, Γ ⊢ arg : argType := by
  induction args generalizing fn with
  | nil => cases hmem
  | cons first args ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · obtain ⟨_, hhead⟩ := schema_mkApps_head_type hΓ (fn := .app fn _) ht
      obtain ⟨_, _, _, ha⟩ := hhead.app_inv henv hΓ
      exact ⟨_, ha⟩
    · exact ih ht hmem

theorem ParRed.elim_prefix
    (Hfixed : CaseStep env univs Γ rule levels captured)
    (hlen : args.length ≤ rule.application.arguments.length)
    (H : Γ ⊢ VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args ≫ out) :
    ∃ args', out = VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args' ∧
      List.Forall₂ (ParRed Γ) args args' := by
  induction args using reverse_induction generalizing out with
  | hnil =>
    cases H with
    | elim => exact ⟨[], rfl, .nil⟩
    | extra hp hm => exact False.elim (Params.pat_not_elim hp hm)
  | happend args arg ih =>
    generalize he : VExpr.mkApps (.elim rule.application.block rule.application.owner packed) (args ++ [arg]) = source at H
    have hshape : source = .app (VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args) arg := by
      rw [← he]
      simp [VExpr.mkApps, List.foldl_append]
    cases H with
    | schema hm => exact False.elim (hm.not_elim_prefix henv Hfixed he.symm hlen)
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih (by simp only [List.length_append, List.length_singleton] at hlen; omega) hf
      refine ⟨args' ++ [arg'], ?_, ?_⟩
      · simp [VExpr.mkApps, List.foldl_append]
      · exact case_forall₂_append hargs (.cons ha .nil)
    | beta =>
      have hfn := VExpr.app.inj hshape |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
    | extra hp hm =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      obtain ⟨name, hh⟩ := InductiveSignature.CaseSchema.native_pattern_head hm
      rw [← he, InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
      cases hh
    | _ => cases hshape

theorem ParRed.rigid_const_spine (hrigid : env.NativeHeadRigid name)
    (H : Γ ⊢ VExpr.mkApps (.const name levels) args ≫ out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧
      List.Forall₂ (ParRed Γ) args args' := by
  induction args using reverse_induction generalizing out with
  | hnil =>
    cases H with
    | const => exact ⟨[], rfl, .nil⟩
    | extra hp hm => exact False.elim (Params.not_rigid_match hrigid hp hm rfl)
  | happend args arg ih =>
    generalize he : VExpr.mkApps (.const name levels) (args ++ [arg]) = source at H
    have hshape : source = .app (VExpr.mkApps (.const name levels) args) arg := by
      rw [← he]
      simp [VExpr.mkApps, List.foldl_append]
    have hhead : source.getAppFnArgs.1 = .const name levels := by
      rw [← he, InductiveSignature.spine_mkApps_exact _ _ rfl]
    cases H with
    | schema hm =>
      rw [InductiveSignature.CaseSchema.Application.head] at hhead
      cases hhead
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih hf
      refine ⟨args' ++ [arg'], ?_, case_forall₂_append hargs (.cons ha .nil)⟩
      simp [VExpr.mkApps, List.foldl_append]
    | beta =>
      have hfn := VExpr.app.inj hshape |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
    | extra hp hm => exact False.elim (Params.not_rigid_match hrigid hp hm hhead)
    | _ => cases hshape

theorem ParRed.instantiate_variables (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      Γ ⊢ arguments[i] ≫ arguments'[i]) :
    Γ ⊢ InductiveSignature.instantiateParams body arguments ≫
      InductiveSignature.instantiateParams body arguments' := by
  induction H with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha => exact .app (ihf hc.1) (iha hc.2)

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.instantiate_variables (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      Γ ⊢ arguments[i] ≡ₚ arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    Γ ⊢ InductiveSignature.instantiateParams body arguments ≡ₚ
      InductiveSignature.instantiateParams body arguments' := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    have hnf := ihf hc.1 hfn
    have hna := iha hc.2 harg
    exact .appDF hfn ((hnf.defeq hΓ).of_l henv hΓ hfn).hasType.2
      harg ((hna.defeq hΓ).of_l henv hΓ harg).hasType.2 hnf hna


theorem ParRed.of_schema (H : AppliedSchemaReduction env univs Γ e e') : Γ ⊢ e ≫ e' := by
  cases H with
  | iota hm => exact .schema hm rfl fun _ _ => .rfl

theorem ParRed.wrapLams (H : domains.reverse ++ Γ ⊢ body ≫ body') :
    Γ ⊢ VExpr.wrapLams domains body ≫ VExpr.wrapLams domains body' := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons domain domains ih =>
    apply ParRed.lam .rfl
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H

theorem ParRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≫ e2) :
    Γ' ⊢ e1.liftN n k ≫ e2.liftN n k := by
  induction H generalizing k Γ' with
  | @schema Γ args rule actual hm hl _ ih =>
    have hc : (rule.body.rhs.instL actual.levels).ClosedN args.length := by
      simpa [hl] using hm.source.closed.2.1.instL
    have hnew : Γ' ⊢ (CaseApplicationMap actual fun e => e.liftN n k).expr ≫
        rule.rhs actual.levels (args.map fun e => e.liftN n k) := by
      refine .schema (hm.weakN henv W) (by simpa only [List.length_map, case_capture_map] using hl) ?_
      intro i hi
      have hi' : i < (rule.capture actual).length := by simpa only [case_capture_map, List.length_map] using hi
      simpa only [case_capture_map, List.getElem_map] using ih i hi' W
    simpa only [case_application_liftN, InductiveSignature.CaseSchema.AppliedRule.rhs,
      instantiateParams_liftN hc] using hnew
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ihMajor => exact .proj (ihMajor W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    refine .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)

variable! (H₀ : Γ₀ ⊢ a1 ≫ a2) (H₀' : Γ₀ ⊢ a1 : A₀) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≫ e2) : Γ ⊢ e1.inst a1 k ≫ e2.inst a2 k := by
  induction H generalizing Γ k with
  | @schema sourceCtx args rule actual hm hl _ ih =>
    have hc : (rule.body.rhs.instL actual.levels).ClosedN args.length := by
      simpa [hl] using hm.source.closed.2.1.instL
    have hnew : Γ ⊢ (CaseApplicationMap actual fun e => e.inst a1 k).expr ≫
        rule.rhs actual.levels (args.map fun e => e.inst a2 k) := by
      refine .schema (hm.instN henv H₀' W) (by simpa only [List.length_map, case_capture_map] using hl) ?_
      intro i hi
      have hi' : i < (rule.capture actual).length := by simpa only [case_capture_map, List.length_map] using hi
      simpa only [case_capture_map, List.getElem_map] using ih i hi' W
    simpa only [case_application_instN, InductiveSignature.CaseSchema.AppliedRule.rhs,
      instantiateParams_instN hc] using hnew
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact ih.weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ihMajor => exact .proj (ihMajor W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀') (fun a => ih _ W)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.defeq (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H generalizing A with
  | schema hm hl _ ih =>
    have hbase := (AppliedSchemaReduction.iota hm).defeq henv hΓ
    have hargs := hm.source.rhs_congr henv hΓ hl fun i hi _ =>
      let ⟨_, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      ⟨_, ih i hi hΓ ht⟩
    exact (hbase.trans henv hΓ hargs).of_l henv hΓ he

  | bvar | sort | const | elim => exact he
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he <| .appDF (ih1 hΓ h1) (ih2 hΓ h2)
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
    exact .trans_l henv hΓ he <| .lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he <| .forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have hf' := hA.lam hb
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hf')
    replace ha := ha.defeqU_r henv hΓ ⟨_, u1⟩
    exact .trans_l henv hΓ he <| .trans
      (.symm <| .appDF (.symm <| .lamDF hA (ih1 ⟨hΓ, _, hA⟩ hb)) (.symm <| ih2 hΓ ha))
      (.beta (ih1 ⟨hΓ, _, hA⟩ hb).hasType.2 (ih2 hΓ ha).hasType.2)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .trans_l henv hΓ he <| .transU_r henv hΓ (pat_wf hΓ h1 h2 he h3) <|
     .apply_pat hΓ (fun _ _ h => ⟨_, ih _ hΓ h⟩) (.defeqU_l henv hΓ (pat_wf hΓ h1 h2 he h3) he)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.hasType (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e' : A :=
  (H.defeq hΓ he).hasType.2

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫ e2) : Γ₂ ⊢ e1 ≫ e2 := by
  induction H generalizing Γ₂ A with
  | schema hm hl _ ih =>
    exact .schema (hm.defeqDFC henv W) hl fun i hi =>
      let ⟨_, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      ih i hi W ht
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      h.proj_inv henv (W.isType' hΓ₀)
    exact .proj (ihMajor W hmajor.hasType.2)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv (W.isType' hΓ₀)
    exact .lam (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (W.succ hA) hB)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv (W.isType' hΓ₀)
    exact .beta (ih1 (W.succ hA) hb) (ih2 W ha)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => h.defeqDFC henv W) fun a =>
      let ⟨_, h⟩ := h2.hasType (W.isType' hΓ₀) h a; ih a W h

theorem ParRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, Γ ⊢ m2 a ≫ m3 a) : Γ ⊢ r.apply m1 m2 ≫ r.apply m1 m3 := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_lift' {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).lift' ρ = r.apply m1 (fun a => (m2 a).lift' ρ) := by
  induction r with simp! [*]
  | fixed _ h => exact instL_lift'.symm.trans ((h.lift'_eq trivial).symm ▸ rfl)

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_liftN {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).liftN k n = r.apply m1 (fun a => (m2 a).liftN k n) := by
  simp [← lift'_consN_skipN, Pattern.RHS.apply_lift']

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem HasType.matches_inv {p : Pattern} {m1 m2} (H : Γ ⊢ e : A)
    (H2 : p.Matches e m1 m2) : ∀ a, ∃ A, Γ ⊢ m2 a : A := by
  induction H2 generalizing A with
  | const | elim => nofun
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (h|h) <;> [exact ih1 hf h; exact ih2 ha h]
  | var _ ih1 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (_|h) <;> [exact ⟨_, ha⟩; exact ih1 hf h]

variable! (hΓ : OnCtx Γ' (IsType env univs)) in
theorem ParRed.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (h : Γ' ⊢ e1.liftN n k : A) (H : Γ' ⊢ e1.liftN n k ≫ e2') :
    ∃ e2, Γ ⊢ e1 ≫ e2 ∧ e2' = e2.liftN n k := by
  generalize eq : e1.liftN n k = e1' at H
  induction H generalizing e1 Γ k A with
  | bvar => cases e1 <;> cases eq; exact ⟨_, .bvar, rfl⟩
  | sort => cases e1 <;> cases eq; exact ⟨_, .sort, rfl⟩
  | const => cases e1 <;> cases eq; exact ⟨_, .const, rfl⟩
  | elim => cases e1 <;> cases eq; exact ⟨_, .elim, rfl⟩
  | app h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hf rfl
    obtain ⟨_, b1, rfl⟩ := ih2 hΓ W ha rfl
    exact ⟨_, .app a1 b1, rfl⟩
  | proj hMajor ihMajor =>
    cases e1 <;> cases eq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      h.proj_inv henv hΓ
    obtain ⟨_, majorRed, rfl⟩ := ihMajor hΓ W hmajor.hasType.2 rfl
    exact ⟨_, .proj majorRed, rfl⟩
  | lam h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hA rfl
    obtain ⟨_, b1, rfl⟩ := ih2 (by exact ⟨hΓ, _, hA⟩) W.succ he rfl
    exact ⟨_, .lam a1 b1, rfl⟩
  | forallE h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hA rfl
    obtain ⟨_, b1, rfl⟩ := ih2 (by exact ⟨hΓ, _, hA⟩) W.succ hB rfl
    exact ⟨_, .forallE a1 b1, rfl⟩
  | beta h1 h2 ih1 ih2 =>
    cases e1 <;> injection eq
    rename_i f a eq eq2; cases eq2
    cases f <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 (by exact ⟨hΓ, _, hA⟩) W.succ hb rfl
    obtain ⟨_, b1, rfl⟩ := ih2 hΓ W ha rfl
    exact ⟨_, .beta a1 b1, (liftN_inst_hi ..).symm⟩
  | @schema Γ' args rule actual hm hl hred ih =>
    obtain ⟨original, rfl, rfl⟩ := case_application_liftN_inv eq.symm
    have hm' := hm.weakN_inv henv hΓ W
    have hlen : args.length = (rule.capture original).length := by
      simpa only [case_capture_map, List.length_map] using hl
    have recargs : ∀ i : Fin (rule.capture original).length,
        ∃ out, Γ ⊢ (rule.capture original)[i.val] ≫ out ∧
          args[i]'(by omega) = out.liftN n k := by
      intro i
      have hi : i.val < (rule.capture (CaseApplicationMap original fun e => e.liftN n k)).length := by
        simpa only [case_capture_map, List.length_map] using i.isLt
      obtain ⟨ty, hty⟩ := hm.capture_typed (List.getElem_mem hi)
      have hty' : Γ' ⊢ ((rule.capture original)[i.val]).liftN n k : ty := by
        simpa only [case_capture_map, List.getElem_map] using hty
      exact ih i hi hΓ W hty' (by simp only [case_capture_map, List.getElem_map])
    classical
    let outputs := List.ofFn fun i => (recargs i).choose
    refine ⟨rule.rhs original.levels outputs, .schema hm' (by simp [outputs]) ?_, ?_⟩
    · intro i hi
      simpa [outputs] using (recargs ⟨i, hi⟩).choose_spec.1
    · have hargs : args = outputs.map fun e => e.liftN n k := by
        apply List.ext_getElem
        · simpa [outputs] using hlen
        · intro i hi hi'
          have hi'' : i < (rule.capture original).length := by simpa [outputs] using hi'
          simpa [outputs] using (recargs ⟨i, hi''⟩).choose_spec.2
      have hc : rule.body.rhs.ClosedN outputs.length := by
        simpa [outputs] using hm'.source.closed.2.1
      simp only [case_application_map_levels, hargs, InductiveSignature.CaseSchema.AppliedRule.rhs,
        instantiateParams_liftN hc.instL]
  | @extra p r e m1 m2 Γ' m2' h1 h2 h3 h4 ih =>
    suffices ∃ m3 m3' : _ → _, p.Matches e1 m1 m3 ∧
        (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧
        (∀ a, m2 a = (m3 a).liftN n k) ∧
        (∀ a, m2' a = (m3' a).liftN n k) by
      let ⟨m3, m3', a1, a2, a3, a4⟩ := this
      refine ⟨_, .extra h1 a1 (h3.map fun _ _ h => ?_) a2,
        .trans (by congr; funext; apply a4) r.1.apply_liftN.symm⟩
      rw [(funext a3 : m2 = _), ← Pattern.RHS.apply_liftN, ← Pattern.RHS.apply_liftN] at h
      exact (IsDefEqU.weakN_iff henv hΓ W).1 h
    clear h1 h3 r
    induction h2 generalizing e1 A with
    | const => cases e1 <;> cases eq; exact ⟨_, nofun, .const, nofun, nofun, nofun⟩
    | elim => cases e1 <;> cases eq; exact ⟨_, nofun, .elim, nofun, nofun, nofun⟩
    | var h1 ih1 =>
      cases e1 <;> cases eq
      have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| some ·) (ih <| some ·) hf rfl
      have ⟨_, b2, b4⟩ := ih none hΓ W ha rfl
      exact ⟨_, Option.rec _ _, .var a1, Option.rec b2 a2, Option.rec rfl a3, Option.rec b4 a4⟩
    | app h1 h2 ih1 ih2 =>
      cases e1 <;> cases eq
      have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| .inl ·) (ih <| .inl ·) hf rfl
      have ⟨_, _, b1, b2, b3, b4⟩ := ih2 (h4 <| .inr ·) (ih <| .inr ·) ha rfl
      exact ⟨_, Sum.rec _ _, .app a1 b1, Sum.rec a2 b2, Sum.rec a3 b3, Sum.rec a4 b4⟩

theorem CParRed.toParRed (H : Γ ⊢ e ⋙ e') : Γ ⊢ e ≫ e' := by
  induction H with
  | schema hm hl _ ih => exact .schema hm hl ih
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ _ ihMajor => exact .proj ihMajor
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih3 => exact .extra h1 h2 h3 ih3

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CParRed.exists (H : Γ ⊢ e : A) : ∃ e', Γ ⊢ e ⋙ e' := by
  induction e using VExpr.brecOn generalizing Γ A with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  have neut {e} (H' : Γ ⊢ e : A) (e_ih : e.below (motive := motive)) :
      NonNeutral Γ e → ∃ e', Γ ⊢ e ⋙ e' := by
    rintro (⟨A, e, a, rfl⟩ | ⟨p, r, m1, m2, h1, hp2, hp3⟩ | ⟨rule, actual, hmatch, rfl⟩)
    · have ⟨_, _, hf, ha⟩ := H'.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, he⟩ := hf.lam_inv henv hΓ
      have ⟨_, he⟩ := e_ih.1.2.2.1 (by exact ⟨hΓ, _, hA⟩) he
      have ⟨_, ha⟩ := e_ih.2.1 hΓ ha
      exact ⟨_, .beta he ha⟩
    · suffices ∃ m3 : p.Path → VExpr, ∀ a, Γ ⊢ m2 a ⋙ m3 a from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H r h1 hp3
      induction p generalizing e m1 A with
      | const | elim => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih1 H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 hΓ H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
    · have recargs : ∀ i : Fin (rule.capture actual).length,
          ∃ out, Γ ⊢ (rule.capture actual)[i] ⋙ out := by
        intro i
        have hm := List.getElem_mem i.isLt
        obtain ⟨ty, ht⟩ := hmatch.capture_typed hm
        exact below_case_capture e_ih _ hm hΓ ht
      classical
      let args := List.ofFn fun i => (recargs i).choose
      refine ⟨_, .schema (arguments := args) hmatch (by simp [args]) ?_⟩
      intro i hi
      simpa [args] using (recargs ⟨i, hi⟩).choose_spec

  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const n ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .const hn⟩
  | elim block owner ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .elim hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hf
    have ⟨_, h2⟩ := e_ih.2.1 hΓ ha
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .app hn h1 h2⟩
  | proj ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      H.proj_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1 hΓ hmajor.hasType.2
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .proj hn h1⟩
  | lam ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := H.lam_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := H.forallE_inv henv
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) hB
    exact ⟨_, .forallE h1 h2⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.instantiate_variables_parRed (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ arguments[i] ≫ out ∧ Γ ⊢ out ≡ₚ arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    ∃ out, Γ ⊢ InductiveSignature.instantiateParams body arguments ≫ out ∧
      Γ ⊢ out ≡ₚ InductiveSignature.instantiateParams body arguments' := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    obtain ⟨fn', hfnRed, hfnNormal⟩ := ihf hc.1 hfn
    obtain ⟨arg', hargRed, hargNormal⟩ := iha hc.2 harg
    have hfn' := hfnRed.hasType hΓ hfn
    have harg' := hargRed.hasType hΓ harg
    exact ⟨_, .app hfnRed hargRed, .appDF hfn'
      ((hfnNormal.defeq hΓ).of_l henv hΓ hfn').hasType.2
      harg' ((hargNormal.defeq hΓ).of_l henv hΓ harg').hasType.2 hfnNormal hargNormal⟩


variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CaseApplicationRelated.parRed_defeq
    (H : CaseApplicationRelated (ParRed Γ) actual actual')
    (ht : Γ ⊢ actual.expr : type) : CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' := by
  obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
  refine { H with arguments := ?_, ctorArguments := ?_ }
  · exact H.arguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ hf h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩
  · exact H.ctorArguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ ha h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩

/-- A structural parallel step keeps a registered case application's fixed
heads and moves only its two argument spines. -/
theorem ParRed.case_spines (hm : MatchedCaseStep env univs Γ rule actual)
    (hrigid : env.NativeHeadRigid actual.ctorName)
    (hf : Γ ⊢ mkApps (.elim actual.block actual.owner actual.levels) actual.arguments ≫ fn')
    (ha : Γ ⊢ mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments ≫ major') :
    ∃ actual', actual'.expr = .app fn' major' ∧ CaseApplicationRelated (ParRed Γ) actual actual' := by
  have hf' := hf
  rw [hm.block_eq, hm.owner_eq] at hf'
  obtain ⟨args', hefn, hargs⟩ := ParRed.elim_prefix hm.source (Nat.le_of_eq hm.arguments_length) hf'
  obtain ⟨fields', hemajor, hfields⟩ := ha.rigid_const_spine hrigid
  refine ⟨{ actual with arguments := args', ctorArguments := fields' }, ?_,
    ⟨rfl, rfl, rfl, rfl, rfl, hargs, hfields⟩⟩
  simp only [InductiveSignature.CaseSchema.Application.expr, hefn, hemajor, hm.block_eq, hm.owner_eq]

theorem MatchedCaseStep.ctor_rigid (H : MatchedCaseStep env univs Γ rule actual) :
    env.NativeHeadRigid actual.ctorName := by
  obtain ⟨schema, block, owner, hl, hg⟩ := H.source.generates
  rw [H.ctor_eq]
  exact henv.case_constructor_rigid hl hg

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.schema_app_triangle
    (hm : MatchedCaseStep env univs Γ rule actual)
    (hrigid : env.NativeHeadRigid actual.ctorName)
    (hlen : args.length = (rule.capture actual).length)
    (hcomplete : ∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ⋙ args[i]'(by omega))
    (ht : Γ ⊢ actual.expr : type)
    (hf : Γ ⊢ mkApps (.elim actual.block actual.owner actual.levels) actual.arguments ≫ fn')
    (ha : Γ ⊢ mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments ≫ major')
    (hrec : ∀ i (hi : i < (rule.capture actual).length) {a b},
      (Γ ⊢ (rule.capture actual)[i] ≫ a) → (Γ ⊢ (rule.capture actual)[i] ⋙ b) →
      ∃ out, Γ ⊢ a ≫ out ∧ Γ ⊢ out ≡ₚ b) :
    ∃ out, Γ ⊢ .app fn' major' ≫ out ∧ Γ ⊢ out ≡ₚ rule.rhs actual.levels args := by
  obtain ⟨actual', he, hspines⟩ := ParRed.case_spines hm hrigid hf ha
  have hstruct : Γ ⊢ actual.expr ≫ actual'.expr := by rw [he]; exact .app hf ha
  have hm' := hm.congr henv hΓ (hspines.parRed_defeq hΓ ht) ⟨_, hstruct.defeq hΓ ht⟩
  have hcapture := hspines.capture (rule := rule)
  have hcaplen := hcapture.length_eq
  have recargs : ∀ i : Fin (rule.capture actual).length,
      ∃ out, Γ ⊢ (rule.capture actual')[i.val]'(by omega) ≫ out ∧
        Γ ⊢ out ≡ₚ args[i.val]'(by omega) := by
    intro i
    exact hrec i.val i.isLt (case_forall₂_get hcapture i.isLt (by omega)) (hcomplete i.val i.isLt)
  classical
  let outputs := List.ofFn fun i => (recargs i).choose
  have hschema : Γ ⊢ actual'.expr ≫ rule.rhs actual'.levels outputs := by
    refine .schema hm' (by simp [outputs]; omega) ?_
    intro i hi
    have hi' : i < (rule.capture actual).length := by omega
    simpa [outputs] using (recargs ⟨i, hi'⟩).choose_spec.1
  refine ⟨_, he ▸ hschema, ?_⟩
  have hvars := hm.source.rhs_variables
  have htyped := hschema.hasType hΓ (hstruct.hasType hΓ ht)
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at htyped ⊢
  apply NormalEq.instantiate_variables hΓ hvars
    (by simpa [outputs] using hm.source.closed.2.1) (by simpa [outputs] using hlen) ?_ htyped
  intro i hi hi'
  have hi'' : i < (rule.capture actual).length := by simpa [outputs] using hi
  simpa [outputs] using (recargs ⟨i, hi''⟩).choose_spec.2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.triangle (H1 : Γ ⊢ e : A) (H : Γ ⊢ e ≫ e') (H2 : Γ ⊢ e ⋙ o) :
    ∃ o', Γ ⊢ e' ≫ o' ∧ Γ ⊢ o' ≡ₚ o := by
  induction e using VExpr.brecOn generalizing Γ A e' o with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  induction H2 generalizing A e' with
  | @schema Γ args rule actual hm hl hargs ih =>
    generalize he : actual.expr = source at H
    cases H with
    | @schema _ args' rule' actual' hm' hl' hargs' =>
      cases case_application_injective he
      cases hm.rule_unique henv hm'
      have hvars := hm.source.rhs_variables
      have hc : rule.body.rhs.ClosedN args'.length := by simpa only [hl'] using hm.source.closed.2.1
      have hlen : args.length = args'.length := hl.trans hl'.symm
      have hargJoin : ∀ i (hi : i < args'.length) (hi' : i < args.length),
          ∃ out, Γ ⊢ args'[i] ≫ out ∧ Γ ⊢ out ≡ₚ args[i] := by
        intro i hi hi'
        have hiC : i < (rule.capture actual).length := by omega
        obtain ⟨ty, ht⟩ := hm.capture_typed (List.getElem_mem hiC)
        exact below_case_capture e_ih _ (List.getElem_mem hiC) hΓ ht (hargs' i hiC) (hargs i hiC)
      have htyped := (ParRed.schema hm' hl' hargs').hasType hΓ H1
      simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at htyped ⊢
      exact NormalEq.instantiate_variables_parRed hΓ hvars hc hlen hargJoin htyped
    | app hf ha =>
      cases he
      apply ParRed.schema_app_triangle hΓ hm hm.ctor_rigid hl hargs H1 hf ha
      intro i hi a b hr hc
      obtain ⟨type, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      exact below_case_capture e_ih _ (List.getElem_mem hi) hΓ ht hr hc
    | beta =>
      have hfn := VExpr.app.inj he |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn)
    | extra hp hmatch =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      obtain ⟨name, hh⟩ := InductiveSignature.CaseSchema.native_pattern_head hmatch
      rw [← he, InductiveSignature.CaseSchema.Application.head] at hh
      cases hh
    | bvar | sort | const | elim | proj | lam | forallE => cases he
  | bvar =>
    cases H with
    | bvar => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | sort =>
    cases H with
    | sort => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | const hn =>
    cases H with
    | const => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | elim hn =>
    cases H with
    | elim => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := H1.app_inv henv hΓ
    cases H with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 hΓ l2 r2 e_ih.2.2
      have o1 := p1.hasType hΓ (r1.hasType hΓ l1); have o2 := p2.hasType hΓ (r2.hasType hΓ l2)
      exact ⟨_, .app p1 p2, .appDF o1 (.defeqU_l henv hΓ (n1.defeq hΓ) o1)
        o2 (.defeqU_l henv hΓ (n2.defeq hΓ) o2) n1 n2⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
    | schema hm => cases hn (.inr (.inr ⟨_, _, hm, rfl⟩))
    | beta => cases hn (.inl ⟨_, _, _, rfl⟩)
  | proj hn _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, _, _⟩ := H1.proj_inv henv hΓ
    cases H with
    | proj rMajor =>
      let ⟨_, pMajor, nMajor⟩ := ihMajor hΓ hmajor.hasType.2 rMajor e_ih.2
      have targetNatural := (ParRed.proj pMajor).hasType hΓ
        ((ParRed.proj rMajor).hasType hΓ H1)
      exact ⟨_, .proj pMajor, .projDF targetNatural nMajor⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.lam_inv henv hΓ
    cases H with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      have := (r1.defeq hΓ l1).trans (p1.defeq hΓ (r1.hasType hΓ l1)) |>.symm
      refine ⟨_, .lam p1 ?_, .lamDF this.symm (this.symm.transU_l henv hΓ (n1.defeq hΓ)) n2⟩
      exact p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType (by exact ⟨hΓ, _, l1⟩) l2)
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.forallE_inv henv
    cases H with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      exact ⟨_, .forallE p1 (p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType hΓ' l2)),
        .forallEDF (.trans (r1.defeq hΓ l1) (p1.defeq hΓ (r1.hasType hΓ l1)))
          n1 (p2.hasType hΓ' (r2.hasType hΓ' l2)) n2⟩
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := H1.app_inv henv hΓ
    have ⟨⟨_, lA⟩, _, le⟩ := lf.lam_inv henv hΓ
    have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lA le)).forallE_inv henv hΓ
    have la' := hw.defeq la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
      ⟨ha, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    rcases H.app_lam_cases with ⟨_, _, rf, ra, rfl⟩ | ⟨_, _, re, ra, rfl⟩
    ·
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      cases rf with
      | lam rA re =>
        refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
        refine ⟨_, .beta (p2.defeqDFC hΓ (.succ .zero (rA.defeq hΓ lA)) (re.hasType hΓ' le)) p3, ?_⟩
        refine .trans hΓ
          (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
            (p2.hasType hΓ' (re.hasType hΓ' le)))
          (.instN (l2.toParRed.hasType hΓ la') .zero n2)
      | extra h1 h2 => cases h2
    ·
      refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      refine ⟨_, .instN p3 (ra.hasType hΓ la') .zero p2, ?_⟩
      refine .trans hΓ
        (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
          (p2.hasType hΓ' (re.hasType hΓ' le)))
        (.instN (l2.toParRed.hasType hΓ la') .zero n2)
  | @extra p r e m1 m2 Γ m2' l1 l2 l3 l4 ih =>
    have :
      (∃ m3 m3' : p.Path → VExpr, p.Matches e' m1 m3 ∧
        (∀ a, Γ ⊢ m2 a ≫ m3 a) ∧ (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ m2' a)) ∨
      (∃ p₁ e₁' e₁ m1₁ m2₁, Subpattern p₁ p ∧ (p₁ = p → e₁ = e ∧ e₁' = e' ∧ m1₁ ≍ m1 ∧ m2₁ ≍ m2) ∧
        p₁.Matches e₁ m1₁ m2₁ ∧ ∃ p' r m1 m2 m2',
        Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ (∀ a, Γ ⊢ m2 a ≫ m2' a) ∧ e₁' = r.1.apply m1 m2') := by
      have hnative := Params.nativeHeads l1
      clear l1 l3 l4 r
      induction H generalizing p m1 A with
      | schema hm =>
        obtain ⟨name, hn⟩ := hnative.matches_head l2
        rw [InductiveSignature.CaseSchema.Application.head] at hn
        cases hn
      | const | elim =>
        cases id l2; exact .inl ⟨_, _, l2, nofun, fun _ => .rfl, nofun⟩
      | @app Γ f f' a a' hf ha ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        cases l2 with
        | var lf =>
          match ih1 lf (ih <| some ·) hΓ Hf e_ih.1.2 hnative with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.varL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.varL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            have ⟨_, a3, a4⟩ := ih none hΓ Ha ha e_ih.2.2
            exact .inl ⟨_, (·.elim _ _), .var f1,
              (·.casesOn ha f2), (·.casesOn a3 f3), (·.casesOn a4 f4)⟩
        | app lf la =>
          match ih1 lf (ih <| .inl ·) hΓ Hf e_ih.1.2 hnative.1 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.appL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.appL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            match ih2 la (ih <| .inr ·) hΓ Ha e_ih.2.2 hnative.2 with
            | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
              refine .inr ⟨_, _, _, _, _, h1.appR, ?_, h3⟩
              rintro rfl; cases h1.antisymm (.appR .refl)
            | .inl ⟨_, _, a1, a2, a3, a4⟩ =>
              exact .inl ⟨_, Sum.elim _ _, .app f1 a1,
                (·.casesOn f2 a2), (·.casesOn f3 a3), (·.casesOn f4 a4)⟩
      | beta _ _ => cases l2 with | var h | app h => cases h
      | @extra _ _ _ _ _ _ _ r1 r2 _ r4 =>
        exact .inr ⟨_, _, _, _, _, .refl, fun _ => ⟨rfl, rfl, .rfl, .rfl⟩,
          l2, _, _, _, _, _, r1, r2, r4, rfl⟩
      | _ => cases l2
    match this with
    | .inl ⟨m3, m3', h1, h2, h3, h4⟩ =>
      refine
        have h := .extra l1 h1 (l3.map fun _ _ ⟨_, h1⟩ => ?_) h3
        ⟨_, h, .apply_pat hΓ (fun a _ _ => h4 a) (h.hasType hΓ (H.hasType hΓ H1))⟩
      refine ⟨_, .trans
        (.symm <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.1)
        (.trans h1 <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.2)⟩
    | .inr ⟨_, _, _, _, _, h1, h2, l2', _, _, _, _, m3, r1, r2, r4, e⟩ =>
      obtain ⟨_, -, -, hr, -⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2'⟩⟩
      obtain ⟨rfl, rfl, ⟨⟩⟩ := pat_uniq l1 r1 h1 hr
      obtain ⟨rfl, rfl, ⟨⟩, ⟨⟩⟩ := h2 rfl; subst e
      obtain ⟨rfl, rfl⟩ := l2'.uniq r2
      suffices ∃ m3' : p.Path → VExpr, (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ m2' a) by
        let ⟨m3', h3, h4⟩ := this
        refine ⟨_, ?h3, .apply_pat hΓ (fun a _ _ => h4 a) ((?h3).hasType hΓ (H.hasType hΓ H1))⟩
        exact .apply_pat _ h3
      clear H r l1 l2 l3 l4 this h1 h2 r1 r2 hr
      induction l2' generalizing A with
      | const | elim => exact ⟨nofun, nofun, nofun⟩
      | app _ _ ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| .inl ·) _ Hf e_ih1 (r4 <| .inl ·)
        have ⟨g2, r1, r2⟩ := ih2 (ih <| .inr ·) _ Ha e_ih2 (r4 <| .inr ·)
        exact ⟨Sum.elim g1 g2, (·.casesOn l1 r1), (·.casesOn l2 r2)⟩
      | var _ ih1 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| some ·) _ Hf e_ih1 (r4 <| some ·)
        have ⟨g2, r1, r2⟩ := ih none hΓ Ha (r4 none) e_ih2
        exact ⟨(·.elim g2 g1), (·.casesOn r1 l1), (·.casesOn r2 l2)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.church_rosser (H : Γ ⊢ e : A)
    (H1 : Γ ⊢ e ≫ e₁) (H2 : Γ ⊢ e ≫ e₂) :
      ∃ e₁' e₂', Γ ⊢ e₁ ≫ e₁' ∧ Γ ⊢ e₂ ≫ e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  let ⟨e', h'⟩ := CParRed.exists hΓ H
  let ⟨_, l1, l2⟩ := H1.triangle hΓ H h'
  let ⟨_, r1, r2⟩ := H2.triangle hΓ H h'
  exact ⟨_, _, l1, r1, l2.trans hΓ (r2.symm hΓ)⟩

def ParRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed Γ)
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.hasType (H : Γ ⊢ e ≫* e') : Γ ⊢ e : A → Γ ⊢ e' : A := by
  induction H with
  | rfl => exact id
  | tail h1 h2 ih => exact h2.hasType hΓ ∘ ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.defeq (H : Γ ⊢ e ≫* e') (h : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H with
  | rfl => exact h
  | tail h1 h2 ih => exact ih.trans (h2.defeq hΓ (hasType hΓ h1 h))

variable! (hΓ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRedS.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫* e2) : Γ₂ ⊢ e1 ≫* e2 := by
  induction H with
  | rfl => exact .rfl
  | tail h1 h2 ih => refine .tail ih (h2.defeqDFC hΓ W (hasType (W.isType' hΓ) h1 h))

theorem ParRedS.app (hf : Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') :
    Γ ⊢ f.app a ≫* f'.app a' := by
  have : Γ ⊢ f.app a ≫* f.app a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.app .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.app f2 .rfl)

theorem ParRedS.proj (hmajor : Γ ⊢ major ≫* major') :
    Γ ⊢ VExpr.proj typeName index major ≫*
      VExpr.proj typeName index major' := by
  induction hmajor with
  | rfl => exact .rfl
  | tail h1 h2 ih => exact .tail ih (.proj h2)

theorem ParRedS.lam (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.lam body ≫* A'.lam body' := by
  have : Γ ⊢ A.lam body ≫* A.lam body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.lam .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.lam f2 .rfl)

theorem ParRedS.forallE (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.forallE body ≫* A'.forallE body' := by
  have : Γ ⊢ A.forallE body ≫* A.forallE body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.forallE .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.forallE f2 .rfl)

theorem NativeReductionTrace.parRedS
    (H : NativeReductionTrace env univs Pat Γ e e') : Γ ⊢ e ≫* e' := by
  induction H with
  | refl => exact .rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | native hp hm hc => exact .tail .rfl (.extra hp hm hc fun _ => .rfl)
  | schema hs => exact .tail .rfl (ParRed.of_schema hs)
  | beta => exact .tail .rfl (.beta .rfl .rfl)
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ ih => exact .lam .rfl ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.inst (Ha : Γ ⊢ a : A)
    (hf : A :: Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') : Γ ⊢ f.inst a ≫* f'.inst a' := by
  have : Γ ⊢ f.inst a ≫* f.inst a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.instN a2 (ParRedS.hasType hΓ a1 Ha) .zero .rfl)
  replace Ha := ha.hasType hΓ Ha
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail _ h ihf => exact .tail ihf (.instN .rfl Ha .zero h)

theorem ParRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e ≫* e') :
    Γ' ⊢ e.liftN n k ≫* e'.liftN n k := by
  induction H with
  | rfl =>  exact .rfl
  | tail _ h ih => exact .tail ih (.weakN W h)

inductive ParRedExt : Type where
  | base : ParRedExt
  | lift : ParRedExt → ParRedExt
  | app : ParRedExt → ParRedExt

def ParRedExt.depth : ParRedExt → Nat
  | .base => 0
  | .lift l
  | .app l => l.depth + 1

def ParRedExt.apply : ParRedExt → VExpr → VExpr
  | .base, e => e
  | .lift l, e => (l.apply e).lift
  | .app l, e => (l.apply e).lift.app (.bvar 0)

def ParRedExt.meas : ParRedExt → Nat
  | .base => 0
  | .lift l => l.meas + 1
  | .app l => l.meas + 2

def IsApp := fun | VExpr.app .. => True | _ => False

omit [Params] in
theorem ParRedExt.isApp {l : ParRedExt} (H : l.apply (.app f a) = e') : IsApp e' := by
  induction l generalizing e' with simp [apply] at H
  | lift l ih =>
    specialize ih rfl; unfold IsApp at ih; split at ih <;> cases ih <;>
    · rename_i h1; cases h1 ▸ H; trivial
  | _ => subst H; trivial

variable! (hΓ : OnCtx (A::Γ) (IsType env univs)) in
theorem hasType_app_bvar0
    (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B' := by
  have ⟨_, _, c1, c2⟩ := H.app_inv henv hΓ
  replace c1 :=
    have ⟨_, d1⟩ := c1.isType henv hΓ
    have ⟨_, _, d3⟩ := d1.forallE_inv henv
    have ⟨_, d4⟩ := c2.uniq henv hΓ (.bvar .zero)
    HasType.defeqU_r henv hΓ ⟨_, d4.forallEDF d3⟩ c1
  have := c1.eta
  rw [show A.lift.lam (e.lift.lift.app (bvar 0)) = (A.lam (e.lift.app (bvar 0))).lift by
    simp [VExpr.liftN, liftN'_liftN_lo, liftN_liftN]] at this
  have ⟨_, f1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, this⟩
  have ⟨⟨_, f2⟩, _, f3⟩ := f1.hasType.1.lam_inv henv hΓ.1
  exact ⟨_, (HasType.lam f2 f3).defeqU_l henv hΓ.1 ⟨_, f1⟩⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedExt.parRed_beta :
    Γ ⊢ f ≡ₚ lam A e' → ∀ {a B}, Γ ⊢ f.app a : B → ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a := by
  refine (?_ : _ ∧ ∀ (l : ParRedExt), l.depth ≤ Γ.length →
    Γ ⊢ f ≡ₚ l.apply ((lam A e').lift.app (bvar 0)) → ∃ e, Γ ⊢ f ≫* e ∧ Γ ⊢ e ≡ₚ l.apply e').1
  induction f using VExpr.brecOn generalizing Γ A e' with | _ f f_ih => ?_
  revert f_ih; change let motive := ?_; ∀ _: f.below (motive := motive), _; intro motive f_ih
  refine ⟨fun h1 a B h2 => ?_, fun l W h1 => ?_⟩
  · cases h1 with
    | @refl _ _ B H =>
      clear f_ih motive
      exact have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, .refl (h.hasType hΓ h2)⟩
    | lamDF a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, H3⟩, _, H4⟩ := H1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((H3.lam H4).uniqU henv hΓ H1).forallE_inv henv hΓ
      exact ⟨_, .tail .rfl <| .beta .rfl .rfl,
        .instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) H2) .zero a3⟩
    | @etaL _ _ A' _ _ a1 a2 =>
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
      have ⟨⟨_, c1⟩, _, c2⟩ := a1.lam_inv henv hΓ
      have ⟨_, d1, d2⟩ := (f_ih.2.1 <| by exact ⟨hΓ, _, hA⟩).2 .base (Nat.zero_le _) a2
      have ⟨_, _, c3, c4⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, c1⟩, _, c2⟩ := c3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((c1.lam c2).uniqU henv hΓ c3).forallE_inv henv hΓ
      exact ⟨_, .tail (ParRedS.app (.lam .rfl d1) .rfl) <| .beta .rfl .rfl,
        .instN (.defeq u1.symm c4) .zero d2⟩
    | etaR a1 a2 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := (H1.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a2.instN (.defeq u1 H2) .zero
      simp [inst, inst_lift] at this
      exact ⟨_, .rfl, this⟩
    | proofIrrel a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have hf := a2.uniqU henv hΓ H1; have := a1.defeqU_l henv hΓ hf
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf |>.forallE_inv henv hΓ
      exact ⟨_, .rfl, .proofIrrel (b2.instN henv .zero H2) (H1.app H2)
        ((u2.defeq c2).instN henv .zero (u1.symm.defeq H2))⟩
  generalize eq : l.apply .. = s at h1
  cases h1 with
  | @refl _ _ B H =>
    subst eq; clear f_ih motive
    generalize ls : l.meas = n
    induction n using Nat.strongRecOn generalizing l Γ B with | _ _ ih; subst ls
    cases l with
    | base =>
      refine have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, ?_⟩
      simp [instN_bvar0] at h ⊢; exact .refl (h.hasType hΓ H)
    | lift l =>
      let A::Γ := Γ
      have ⟨_, a1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, H⟩
      have ⟨_, a2, a3⟩ := ih _ (by simp [meas]) hΓ.1 l (by simpa [depth] using W) a1 rfl
      exact ⟨_, .weakN .one a2, .weakN .one a3⟩
    | app l =>
      let A::Γ := Γ
      have ⟨_, _, H1, H2⟩ := H.app_inv henv hΓ
      have ⟨_, a1, a2⟩ := ih _ (by simp [meas]) hΓ (lift l) W H1 rfl
      have := a1.hasType hΓ H1
      exact ⟨_, .app a1 .rfl, .appDF this (this.defeqU_l henv hΓ (a2.defeq hΓ)) H2 H2 a2 (.refl H2)⟩
  | @appDF _ _ A' B' f' _ a' a1 a2 a3 a4 a5 a6 =>
    obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ : ∃ n, a' = bvar n ∧
        (f' = (A.lam e').liftN (n+1) ∧ l.apply e' = liftN n e' ∨
        ∃ l', l'.depth ≤ l.depth ∧
          f' = apply l' ((A.lam e').lift.app (bvar 0)) ∧
          l.apply e' = (l'.apply e').app (bvar n)) := by
      clear W a2 a4 a5 a6
      induction l generalizing f' a' with
      | base => cases eq; exact ⟨_, rfl, .inl ⟨rfl, by simp [apply]⟩⟩
      | lift l ih =>
        simp [apply] at eq
        generalize eq' : apply .. = s at eq; cases s <;> cases eq
        obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ := ih eq'
        · refine ⟨_, rfl, .inl ⟨by simp [liftN_liftN], ?_⟩⟩
          have := congrArg VExpr.lift h
          simpa [lift_inst_hi, liftN'_liftN']
        · exact ⟨_, rfl, .inr ⟨lift _, Nat.succ_le_succ W', rfl, congrArg VExpr.lift h⟩⟩
      | app l ih => cases eq; exact ⟨_, rfl, .inr ⟨lift _, Nat.le_refl _, rfl, rfl⟩⟩
    · have ⟨⟨_, c1⟩, _, c2⟩ := (a1.defeqU_l henv hΓ (a5.defeq hΓ)).lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := a1.defeqU_l henv hΓ (a5.defeq hΓ)
        |>.uniqU henv hΓ (c1.lam c2) |>.forallE_inv henv hΓ
      have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).1 a5 (.app a1 a3)
      replace b2 := b2.trans hΓ <|
        .instN_r (by exact ⟨hΓ, _, c1⟩) (.defeqU_r henv hΓ ⟨_, u1⟩ a3) a6 .zero c2
      have := congrArg (liftN n) (instN_bvar0 e' 0)
      simp [liftN_inst_hi, liftN'_liftN', liftN] at this
      rw [Nat.add_comm, this, ← h] at b2
      exact ⟨_, b1, b2⟩
    · have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).2 l' (Nat.le_trans W' W) a5
      rw [h]; have := b1.hasType hΓ a1
      exact ⟨_, .app b1 .rfl, .appDF this (.defeqU_l henv hΓ (b2.defeq hΓ) this) a3 a4 b2 a6⟩
  | @etaL _ _ A' _ _ a1 a2 =>
    subst eq
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA⟩
      have ⟨_, b1, b2⟩ := (f_ih.2.1 hΓ').2 (app l) (by exact Nat.succ_le_succ W) a2; ?_
    have ⟨_, c1⟩ := b2.defeq hΓ'
    let ⟨_, b3⟩ := hasType_app_bvar0 hΓ' c1.hasType.2
    exact ⟨_, .lam .rfl b1, .etaL b3 b2⟩
  | @proofIrrel _ p _ _ a1 a2 a3 =>
    subst eq; refine ⟨_, .rfl, .proofIrrel a1 a2 ?_⟩
    clear a2; induction l generalizing Γ p with
    | base =>
      have ⟨_, _, b1, b2⟩ := a3.app_inv henv hΓ
      have ⟨⟨_, b3⟩, _, b4⟩ := b1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((b3.lam b4).uniqU henv hΓ b1).forallE_inv henv hΓ
      have := b4.beta (u1.symm.defeq b2)
      simp [instN_bvar0] at this
      exact .defeqU_l henv hΓ ⟨_, this⟩ a3
    | lift l ih =>
      let A::Γ := Γ
      have ⟨_, b1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, a3⟩
      have u1 := a3.uniqU henv hΓ (b1.weak henv)
      have := (HasType.weakN_iff henv hΓ (A := sort _) .one).1 (a1.defeqU_l henv hΓ u1)
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      exact .defeqU_r henv hΓ u1.symm (this.weak henv)
    | app l ih =>
      let A::Γ := Γ
      let ⟨_, b1⟩ := hasType_app_bvar0 hΓ a3
      have H := a3.uniqU henv hΓ (HasType.app (b1.weak henv) (.bvar .zero))
      simp [instN_bvar0] at H
      have ⟨⟨_, b2⟩, _, b3⟩ := have ⟨_, b2⟩ := b1.isType henv hΓ.1; b2.forallE_inv henv
      have wf := let ⟨_, h⟩ := b2.isType henv hΓ.1; h.sort_inv henv
      have := b2.forallE (.defeqU_l henv hΓ H a1)
      have := IsDefEq.defeq (.sortDF (by exact ⟨wf, ⟨⟩⟩) (by trivial) VLevel.imax_zero) this
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      have := HasType.app (this.weak henv) (.bvar .zero)
      simp [instN_bvar0] at this
      exact .defeqU_r henv hΓ H.symm this
  | _ => cases l.isApp eq


variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.instantiate_variables_parRedS (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ arguments[i] ≫* out ∧ Γ ⊢ out ≡ₚ arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    ∃ out, Γ ⊢ InductiveSignature.instantiateParams body arguments ≫* out ∧
      Γ ⊢ out ≡ₚ InductiveSignature.instantiateParams body arguments' := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    obtain ⟨fn', hfnRed, hfnNormal⟩ := ihf hc.1 hfn
    obtain ⟨arg', hargRed, hargNormal⟩ := iha hc.2 harg
    have hfn' := hfnRed.hasType hΓ hfn
    have harg' := hargRed.hasType hΓ harg
    exact ⟨_, .app hfnRed hargRed, .appDF hfn'
      ((hfnNormal.defeq hΓ).of_l henv hΓ hfn').hasType.2
      harg' ((hargNormal.defeq hΓ).of_l henv hΓ harg').hasType.2 hfnNormal hargNormal⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseStep.rhs_normalEq_parRedS
    (H : CaseStep env univs Γ rule levels arguments)
    (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ arguments[i] ≫* out ∧ Γ ⊢ out ≡ₚ arguments'[i]) :
    ∃ out, Γ ⊢ rule.rhs levels arguments ≫* out ∧
      Γ ⊢ out ≡ₚ rule.rhs levels' arguments' := by
  have hvars := H.rhs_variables
  obtain ⟨type, ht⟩ := H.defeq henv hΓ
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at ht ⊢
  exact NormalEq.instantiate_variables_parRedS hΓ hvars H.closed.2.1 hlen hargs ht.hasType.2

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem MatchedCaseStep.normalEq_parRedS
    (H : MatchedCaseStep env univs Γ rule actual)
    (hlen : arguments'.length = (rule.capture actual).length)
    (hargs : ∀ i (hi : i < (rule.capture actual).length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ (rule.capture actual)[i] ≫* out ∧ Γ ⊢ out ≡ₚ arguments'[i]) :
    ∃ out, Γ ⊢ actual.expr ≫* out ∧ Γ ⊢ out ≡ₚ rule.rhs levels' arguments' := by
  obtain ⟨out, hr, hn⟩ := H.source.rhs_normalEq_parRedS hΓ hlen hargs
  exact ⟨out, .trans (.tail .rfl (.schema H rfl fun _ _ => .rfl)) hr, hn⟩


variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.mkApps_spine
    (hfn : Γ ⊢ fn ≡ₚ fn') (hargs : List.Forall₂ (NormalEq Γ) args args')
    (ht : Γ ⊢ mkApps fn args : type) : Γ ⊢ mkApps fn args ≡ₚ mkApps fn' args' := by
  induction hargs generalizing fn fn' with
  | nil => exact hfn
  | cons harg hargs ih =>
    obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app fn _) ht
    obtain ⟨_, _, hfnType, hargType⟩ := happ.app_inv henv hΓ
    apply ih _ ht
    exact .appDF hfnType ((hfn.defeq hΓ).of_l henv hΓ hfnType).hasType.2
      hargType ((harg.defeq hΓ).of_l henv hΓ hargType).hasType.2 hfn harg

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq
    (H : CaseApplicationRelated (NormalEq Γ) actual actual')
    (ht : Γ ⊢ actual.expr : type) : Γ ⊢ actual.expr ≡ₚ actual'.expr := by
  obtain ⟨_, _, hfn, hmajor⟩ := ht.app_inv henv hΓ
  obtain ⟨_, hhead⟩ := schema_mkApps_head_type hΓ hfn
  obtain ⟨_, hctor⟩ := schema_mkApps_head_type hΓ hmajor
  have hnfn := NormalEq.mkApps_spine hΓ (.refl hhead) H.arguments hfn
  have hnmajor := NormalEq.mkApps_spine hΓ (.refl hctor) H.ctorArguments hmajor
  change NormalEq Γ (.app _ _) (.app _ _)
  rw [← H.block_eq, ← H.owner_eq, ← H.levels_eq, ← H.ctor_eq, ← H.ctorLevels_eq]
  apply NormalEq.appDF hfn ?_ hmajor ?_ hnfn hnmajor
  · exact ((hnfn.defeq hΓ).of_l henv hΓ hfn).hasType.2
  · exact ((hnmajor.defeq hΓ).of_l henv hΓ hmajor).hasType.2

private theorem normalEq_forall2_symm (hΓ : OnCtx Γ (env.IsType univs)) (H : List.Forall₂ (NormalEq Γ) args args') :
    List.Forall₂ (NormalEq Γ) args' args := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.symm hΓ) ih

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq_symm
    (H : CaseApplicationRelated (NormalEq Γ) actual actual') :
    CaseApplicationRelated (NormalEq Γ) actual' actual where
  block_eq := H.block_eq.symm
  owner_eq := H.owner_eq.symm
  levels_eq := H.levels_eq.symm
  ctor_eq := H.ctor_eq.symm
  ctorLevels_eq := H.ctorLevels_eq.symm
  arguments := normalEq_forall2_symm hΓ H.arguments
  ctorArguments := normalEq_forall2_symm hΓ H.ctorArguments

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq_defeq
    (H : CaseApplicationRelated (NormalEq Γ) actual actual') :
    CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' where
  block_eq := H.block_eq
  owner_eq := H.owner_eq
  levels_eq := H.levels_eq
  ctor_eq := H.ctor_eq
  ctorLevels_eq := H.ctorLevels_eq
  arguments := H.arguments.imp fun _ _ h => h.defeq hΓ
  ctorArguments := H.ctorArguments.imp fun _ _ h => h.defeq hΓ

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem MatchedCaseStep.of_normalEq_spine
    (H : MatchedCaseStep env univs Γ rule actual')
    (hspine : CaseApplicationRelated (NormalEq Γ) actual actual') :
    MatchedCaseStep env univs Γ rule actual := by
  obtain ⟨_, hactual⟩ := H.guard
  have hs := hspine.normalEq_symm hΓ
  exact H.congr henv hΓ (hs.normalEq_defeq hΓ)
    ((hs.normalEq hΓ hactual.hasType.1).defeq hΓ)

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.schema_of_spine
    (H : MatchedCaseStep env univs Γ rule actual')
    (hspine : CaseApplicationRelated (NormalEq Γ) actual actual')
    (hlen : arguments'.length = (rule.capture actual).length)
    (hargs : ∀ i (hi : i < (rule.capture actual).length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ (rule.capture actual)[i] ≫* out ∧ Γ ⊢ out ≡ₚ arguments'[i]) :
    ∃ out, Γ ⊢ actual.expr ≫* out ∧ Γ ⊢ out ≡ₚ rule.rhs levels' arguments' :=
  (H.of_normalEq_spine hΓ hspine).normalEq_parRedS hΓ hlen hargs



variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.of_levelEquiv (L : VExpr.LEquiv univs e e') (ht : Γ ⊢ e : type) :
    Γ ⊢ e ≡ₚ e' := by
  induction L generalizing Γ type with
  | refl => exact .refl ht
  | sort he hw => exact .sortDF (ht.sort_inv henv.ordered) hw he
  | const he hw =>
    obtain ⟨ci, hc, hu, hn⟩ := ht.const_inv henv.ordered hΓ
    exact .constDF hc hu hw hn he
  | elim he hw =>
    exact .elimDF ((VExpr.LEquiv.defeq henv hΓ (.elim he hw) ⟨_, ht⟩).of_l henv hΓ ht) he
  | app hf ha ihf iha =>
    obtain ⟨_, _, hft, hat⟩ := ht.app_inv henv.ordered hΓ
    have hnf := ihf hΓ hft
    have hna := iha hΓ hat
    exact .appDF hft ((hnf.defeq hΓ).of_l henv hΓ hft).hasType.2
      hat ((hna.defeq hΓ).of_l henv hΓ hat).hasType.2 hnf hna
  | proj hm ihm =>
    obtain ⟨info, ls, params, indices, major, field, level, hi, hlu, hun, hp, hix, hf,
      hfield, hmajor, hclosed, hguard⟩ := ht.proj_inv henv.ordered hΓ
    exact .projDF ht (ihm hΓ hmajor.hasType.2)
  | lam hd hb ihd ihb =>
    obtain ⟨⟨_, hdomain⟩, _, hbody⟩ := ht.lam_inv henv.ordered hΓ
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hdomain⟩
    exact .lamDF hdomain ((ihd hΓ hdomain).defeq hΓ |>.of_l henv hΓ hdomain)
      (ihb hctx hbody)
  | forallE hd hb ihd ihb =>
    obtain ⟨⟨_, hdomain⟩, _, hbody⟩ := ht.forallE_inv henv.ordered
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hdomain⟩
    exact .forallEDF hdomain (ihd hΓ hdomain) hbody (ihb hctx hbody)

private theorem _root_.Lean4Lean.Pattern.RHS.const_levelEquiv
    (r : (Pattern.const name).RHS) (hls : ∀ l ∈ ls, l.WF univs)
    (hls' : ∀ l ∈ ls', l.WF univs) (he : List.Forall₂ (· ≈ ·) ls ls') :
    VExpr.LEquiv univs (r.apply ls values) (r.apply ls' values') := by
  induction r with
  | fixed c hc => exact .instL_expr c hls hls' he
  | app _ _ ihf iha => exact .app ihf iha
  | var i => cases i

private theorem _root_.Lean4Lean.Pattern.Check.const_levels
    (hΓ : OnCtx Γ (env.IsType univs))
    {check : (Pattern.const name).Check}
    (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : check.OK (IsDefEqU env univs Γ) ls values) :
    check.OK (IsDefEqU env univs Γ) ls' values' := by
  induction check with
  | true => trivial
  | nonzero level rest ih =>
    refine ⟨fun hz => H.1 ((VLevel.inst_congr rfl he).trans hz), ih H.2⟩
  | defeq left right rest ih =>
    obtain ⟨ht, hr⟩ := H
    obtain ⟨type, ht⟩ := ht
    have hl := NormalEq.of_levelEquiv hΓ (left.const_levelEquiv (values' := values') hls hls' he) ht.hasType.1
    have hh := NormalEq.of_levelEquiv hΓ (right.const_levelEquiv (values' := values') hls hls' he) ht.hasType.2
    exact ⟨(hl.defeq hΓ).symm.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, ht⟩ (hh.defeq hΓ)), ih hr⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.const_native_parallel
    (hc : env.constants name = some ci)
    (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (hlen : ls.length = ci.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    {p : Pattern} {r : p.RHS × p.Check} {levels : List VLevel}
    {values : p.Path → VExpr}
    (hp : Pat p r) (hm : p.Matches (.const name ls') levels values)
    (hcheck : r.2.OK (IsDefEqU env univs Γ) levels values)
    {values' : p.Path → VExpr} (hargs : ∀ a, Γ ⊢ values a ≫ values' a) :
    ∃ out, Γ ⊢ .const name ls ≫* out ∧ Γ ⊢ out ≡ₚ r.1.apply levels values' := by
  cases hm
  let zeroArgs : (Pattern.const name).Path → VExpr := nofun
  have hcheckLeft := Pattern.Check.const_levels hΓ hls' hls
    (he.flip.imp fun _ _ h => h.symm) hcheck (values' := zeroArgs)
  have hrLeft : Γ ⊢ .const name ls ≫ r.1.apply ls zeroArgs :=
    .extra hp .const hcheckLeft (fun a => nomatch a)
  have ht : Γ ⊢ .const name ls : ci.type.instL ls := .const hc hls hlen
  exact ⟨_, .tail .rfl hrLeft,
    NormalEq.of_levelEquiv hΓ (r.1.const_levelEquiv hls hls' he) (hrLeft.hasType hΓ ht)⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.schema_parallel_of_major_proof
    (H : Γ ⊢ left ≡ₚ actual.expr)
    (hmatch : MatchedCaseStep env univs Γ rule actual)
    (hlen : arguments'.length = (rule.capture actual).length)
    (hargs : ∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ≫ arguments'[i]'(by omega))
    (hprop : Γ ⊢ proposition : .sort .zero)
    (hproof : Γ ⊢ VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
      actual.ctorArguments : proposition) :
    ∃ out, Γ ⊢ left ≫* out ∧ Γ ⊢ out ≡ₚ rule.rhs actual.levels arguments' := by
  obtain ⟨resultType, hresultProp, hresult⟩ :=
    hmatch.result_prop_of_major_proof henv hΓ hprop hproof
  have hleft := hresult.defeqU_l henv hΓ (H.defeq hΓ).symm
  have hred : Γ ⊢ actual.expr ≫ rule.rhs actual.levels arguments' :=
    .schema hmatch hlen hargs
  exact ⟨left, .rfl, .proofIrrel hresultProp hleft (hred.hasType hΓ hresult)⟩

/- Outstanding head-computation compatibility: expose native or registered
schema computation through normal equality, including eta expansion and proof
irrelevance, and transport the parallel developments of captured arguments.
This is a proof obligation for the concrete reduction relation, not an added
assumption on its callers. -/
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.headParallel (H : Γ ⊢ e₁ ≡ₚ e₂)
    (Hhead : HeadParallelReduction Γ e₂ e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  sorry

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.parRed (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : Γ ⊢ e₂ ≫ e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  induction H1 generalizing e₂' with
  | refl l1 => exact ⟨_, .tail .rfl H2, .refl (H2.hasType hΓ l1)⟩
  | sortDF l1 l2 l3 =>
    cases H2 with
    | sort => exact ⟨_, .tail .rfl .sort, .sortDF l1 l2 l3⟩
    | extra r1 r2 => cases r2
  | elimDF h heq =>
    cases H2 with
    | elim => exact ⟨_, .rfl, .elimDF h heq⟩
    | extra hp hm => exact False.elim (Params.pat_not_elim hp hm)
  | constDF l1 l2 l3 l4 l5 =>
    cases H2 with
    | const => exact ⟨_, .tail .rfl .const, .constDF l1 l2 l3 l4 l5⟩
    | extra r1 r2 r3 r4 =>
      exact NormalEq.const_native_parallel hΓ l1 l2 l3 l4 l5 r1 r2 r3 r4
  | @appDF Γ f A B f₂ a b l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    cases H2 with
    | app r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 hΓ r1
      let ⟨_, b1, b2⟩ := ih2 hΓ r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2) (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩
    | @beta A _ e e' _ b' r1 r2 =>
      let ⟨f', a1, a2⟩ := ih1 hΓ (.lam .rfl r1)
      let ⟨a', b1, b2⟩ := ih2 hΓ r2
      let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
      let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
      refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.hasType hΓ' (u2.defeq d2); ?_
      replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
      let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta hΓ a2
        (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
      exact ⟨_, .trans (a1.app b1) h1, h2.trans hΓ (.instN_r hΓ' l3 b2 .zero d2)⟩
    | extra r1 r2 r3 r4 =>
      exact (NormalEq.appDF l1 l2 l3 l4 l5 l6).headParallel hΓ (.native r1 r2 r3 r4)
    | schema hm hl hr =>
      exact (NormalEq.appDF l1 l2 l3 l4 l5 l6).headParallel hΓ (.schema hm hl hr)
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
  | @etaR Γ e A _ _ l1 l2 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      refine have hΓ' := (by exact ⟨hΓ, _, hA⟩); let ⟨t, a1, a2⟩ := ih1 hΓ' r2; ?_
      suffices
          (∃ A', Γ ⊢ e ≫* A'.lam t ∧ Γ ⊢ A' ≡ A) ∨
          (∃ e', Γ ⊢ e ≫* e' ∧ t = .app (.lift e') (.bvar 0)) by
        obtain ⟨_, h1, h2⟩ | ⟨_, h, rfl⟩ := this
        · exact ⟨_, h1, .lamDF (h2.of_r henv hΓ hA).symm (r1.defeq hΓ hA) a2⟩
        · have := a2.etaR (h.hasType hΓ l1)
          have ⟨_, a3⟩ := a2.defeq hΓ'
          exact ⟨_, h, this.trans hΓ (.lamDF hA (r1.defeq hΓ hA) (.refl a3.hasType.2))⟩
      generalize eq : e.lift.app (.bvar 0) = e' at a1
      clear l2 ih1 a2
      induction a1 generalizing e with subst eq
      | rfl => exact .inr ⟨_, .rfl, rfl⟩ | tail _ a1 ih
      obtain ⟨_, h1, h2⟩ | ⟨e', h, rfl⟩ := ih l1 rfl
      · have h2' := h2.of_r henv hΓ hA
        have ⟨⟨_, d1⟩, _, d2⟩ := (h1.hasType hΓ l1).lam_inv henv hΓ
        exact .inl ⟨_, h1.tail <| .lam .rfl (a1.defeqDFC hΓ (.succ .zero h2'.symm)
          (.defeqDFC henv (.succ .zero h2') d2)), h2⟩
      generalize eq : e'.lift = e1 at a1
      rcases a1.app_bvar_cases with ⟨_, b1, rfl⟩ | ⟨_, _, _, he, b1, rfl⟩
      ·
        cases eq; obtain ⟨_, b1', rfl⟩ := b1.weakN_inv hΓ' .one ((h.hasType hΓ l1).weak henv)
        exact .inr ⟨_, .tail h b1', rfl⟩
      · rw [he] at eq
        cases e' <;> cases eq
        have ⟨⟨_, c1⟩, _, c2⟩ := (h.hasType hΓ l1).lam_inv henv hΓ
        obtain ⟨_, b1', rfl⟩ := b1.weakN_inv
          (by exact ⟨hΓ', _, c1.weak henv⟩) (.succ .one) (c2.weakN henv (.succ .one))
        rw [instN_bvar0]
        have l1' := h.hasType hΓ l1
        have ⟨⟨_, d1⟩, _, d2⟩ := l1'.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l1').forallE_inv henv hΓ
        exact .inl ⟨_, .tail h <| .lam .rfl b1', _, u1⟩
    | extra _ r2 => cases r2
  | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (H2.hasType hΓ l3)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.parRedS (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : Γ ⊢ e₂ ≫* e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  induction H2 with
  | rfl => exact ⟨_, .rfl, H1⟩
  | tail h1 h2 ih =>
    let ⟨_, a1, a2⟩ := ih
    let ⟨_, b1, b2⟩ := a2.parRed hΓ h2
    exact ⟨_, .trans a1 b1, b2⟩

local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => CRDefEq Γ e1 e2

def CRDefEq (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  (∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂'

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.church_rosser  (H : Γ ⊢ e : A)
    (H1 : Γ ⊢ e ≫* e₁) (H2 : Γ ⊢ e ≫* e₂) : Γ ⊢ e₁ ≫≪ e₂ := by
  refine ⟨⟨_, H1.hasType hΓ H⟩, ⟨_, H2.hasType hΓ H⟩, ?_⟩
  induction H2 with
  | rfl => exact ⟨_, _, .rfl, H1, .refl (H1.hasType hΓ H)⟩
  | @tail b c h1 H2 ih =>
    replace H := ParRedS.hasType hΓ h1 H
    have ⟨_, A2, a1, a2, a3⟩ := ih
    have ⟨_, _, b1, b2, b3⟩ :
        ∃ e₁' e₂', Γ ⊢ A2 ≫ e₁' ∧ Γ ⊢ c ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
      clear a3; induction a2 with
      | rfl => exact ⟨_, _, H2, .rfl, .refl (H2.hasType hΓ H)⟩
      | tail h1 h2 ih =>
        have ⟨_, _, a1, a2, a3⟩ := ih
        have ⟨_, _, b1, b2, b3⟩ := a1.church_rosser hΓ (ParRedS.hasType hΓ h1 H) h2
        have ⟨_, c1, c2⟩ := (a3.symm hΓ).parRed hΓ b1
        exact ⟨_, _, b2, .trans a2 c1, (c2.trans hΓ b3).symm hΓ⟩
    have ⟨_, c1, c2⟩ := a3.parRed hΓ b1
    exact ⟨_, _, .trans a1 c1, b2, c2.trans hΓ b3⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂) : Γ ⊢ e₁ ≫≪ e₂ :=
  let ⟨_, h⟩ := H.defeq hΓ; ⟨⟨_, h.hasType.1⟩, ⟨_, h.hasType.2⟩, _, _, .rfl, .rfl, H⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e := .normalEq hΓ (.refl H)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₁ ≡ e₂
  | ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, h3, h4, h5⟩ =>
    ⟨_, .trans_l henv hΓ (h3.defeq hΓ h1) <| .transU_r henv hΓ (h5.defeq hΓ) (h4.defeq hΓ h2).symm⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₁
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h2, h1, _, _, h4, h3, h5.symm hΓ⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₃ → Γ ⊢ e₁ ≫≪ e₃
  | ⟨l1, ⟨_, l2⟩, _, _, l3, l4, l5⟩, ⟨_, r2, _, _, r3, r4, r5⟩ => by
    let ⟨_, _, _, _, m1, m2, m3⟩ := l4.church_rosser hΓ l2 r3
    let ⟨_, a1, a2⟩ := l5.parRedS hΓ m1
    let ⟨_, b1, b2⟩ := (r5.symm hΓ).parRedS hΓ m2
    exact ⟨l1, r2, _, _, .trans l3 a1, .trans r4 b1, a2.trans hΓ <| m3.trans hΓ (b2.symm hΓ)⟩
