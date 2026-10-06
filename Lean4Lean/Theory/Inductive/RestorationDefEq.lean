import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Restoration of auxiliary heads preserves definitional equality.

An auxiliary family header `aux : ∀ params, Sort l` is an opaque constant of the
lowered environment. Replacing each such constant by a closed lambda telescope
`λ params, target levels arguments` is a total, purely syntactic substitution
`VExpr.replaceConsts`; it commutes with lifting, instantiation and universe
instantiation, and therefore transports every derivation of the lowered
environment to the source environment (`ConstReplacement.isDefEq`).

Restoration proper (`Restoration.expr`) instead substitutes the parameters
directly into fully applied heads. It agrees with the lambda replacement up to
the beta steps of the inserted telescopes (`RestorationSubstitution.restore`).
Contracting a beta redex whose typing passes through a conversion of its Pi type
is subject reduction for beta, which requires injectivity of Pi types; this is
taken as the explicit hypothesis `VEnv.BetaSubjectReduction` rather than from
the (unproved) injectivity theorems.
-/

namespace Lean4Lean

namespace VExpr

/-- Replace constants by closed universe-polymorphic terms. -/
def replaceConsts (ρ : Name → Option VExpr) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls =>
    match ρ c with
    | some t => t.instL ls
    | none => .const c ls
  | .elim block owner ls => .elim block owner ls
  | .app f a => .app (f.replaceConsts ρ) (a.replaceConsts ρ)
  | .proj n i e => .proj n i (e.replaceConsts ρ)
  | .lam A b => .lam (A.replaceConsts ρ) (b.replaceConsts ρ)
  | .forallE A b => .forallE (A.replaceConsts ρ) (b.replaceConsts ρ)

/-- Every replacement is closed, and no replacement is a Pi type (so that
replacement does not create new telescope binders). -/
def ReplacementsClosed (ρ : Name → Option VExpr) : Prop :=
  ∀ c t, ρ c = some t → t.ClosedN ∧ ∀ A B, t ≠ .forallE A B

theorem instL_ne_forallE (h : ∀ A B, t ≠ VExpr.forallE A B) (ls : List VLevel) :
    ∀ A B, t.instL ls ≠ .forallE A B := by
  cases t <;> simp [instL]
  exact h _ _ rfl

theorem replaceConsts_const_some (h : ρ c = some t) :
    (VExpr.const c ls).replaceConsts ρ = t.instL ls := by
  simp [replaceConsts, h]

theorem replaceConsts_const_none (h : ρ c = none) :
    (VExpr.const c ls).replaceConsts ρ = .const c ls := by
  simp [replaceConsts, h]

@[simp] theorem replaceConsts_mkApps (f : VExpr) (args : List VExpr) :
    (mkApps f args).replaceConsts ρ = mkApps (f.replaceConsts ρ) (args.map (·.replaceConsts ρ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem replaceConsts_liftN (hρ : ReplacementsClosed ρ) (e : VExpr) (n k : Nat) :
    (e.liftN n k).replaceConsts ρ = (e.replaceConsts ρ).liftN n k := by
  induction e generalizing k with
  | bvar | sort | elim => rfl
  | const c ls =>
    simp only [liftN, replaceConsts]
    split
    · next t h => exact ((hρ c t h).1.instL.liftN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [liftN, replaceConsts, ihf, iha]
  | proj _ _ e ih => simp [liftN, replaceConsts, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [liftN, replaceConsts, ihA, ihb]

theorem replaceConsts_lift (hρ : ReplacementsClosed ρ) (e : VExpr) :
    e.lift.replaceConsts ρ = (e.replaceConsts ρ).lift := replaceConsts_liftN hρ e 1 0

theorem replaceConsts_inst (hρ : ReplacementsClosed ρ) (e a : VExpr) (k : Nat) :
    (e.inst a k).replaceConsts ρ = (e.replaceConsts ρ).inst (a.replaceConsts ρ) k := by
  induction e generalizing k with
  | sort | elim => rfl
  | bvar i =>
    simp only [inst, instVar, replaceConsts]
    split
    · rfl
    · split
      · exact replaceConsts_liftN hρ a k 0
      · rfl
  | const c ls =>
    simp only [inst, replaceConsts]
    split
    · next t h => exact ((hρ c t h).1.instL.instN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [inst, replaceConsts, ihf, iha]
  | proj _ _ e ih => simp [inst, replaceConsts, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [inst, replaceConsts, ihA, ihb]

theorem replaceConsts_instL (e : VExpr) (ls : List VLevel) :
    (e.instL ls).replaceConsts ρ = (e.replaceConsts ρ).instL ls := by
  induction e with
  | bvar | sort | elim => rfl
  | const c us =>
    simp only [instL, replaceConsts]
    split
    · exact instL_instL.symm
    · rfl
  | app f a ihf iha => simp [instL, replaceConsts, ihf, iha]
  | proj _ _ e ih => simp [instL, replaceConsts, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [instL, replaceConsts, ihA, ihb]

end VExpr

namespace VProjectionInfo

theorem instantiateProjectionParameters_of_ne_forallE {x : VExpr}
    (h : ∀ A B, x ≠ .forallE A B) : instantiateProjectionParameters x (p :: ps) = none := by
  cases x <;> simp_all [instantiateProjectionParameters]

theorem instantiateProjectionFields_of_ne_forallE {x : VExpr}
    (h : ∀ A B, x ≠ .forallE A B) :
    instantiateProjectionFields typeName major wanted current fuel x = none := by
  cases fuel <;> cases x <;> simp_all [instantiateProjectionFields]

theorem instantiateProjectionParameters_replaceConsts (hρ : VExpr.ReplacementsClosed ρ)
    (type : VExpr) (params : List VExpr) :
    instantiateProjectionParameters (type.replaceConsts ρ) (params.map (·.replaceConsts ρ)) =
      (instantiateProjectionParameters type params).map (·.replaceConsts ρ) := by
  induction params generalizing type with
  | nil => simp [instantiateProjectionParameters]
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters, VExpr.replaceConsts]
    case const c ls =>
      cases h : ρ c with
      | none => simp [instantiateProjectionParameters]
      | some t =>
        exact instantiateProjectionParameters_of_ne_forallE (VExpr.instL_ne_forallE (hρ c t h).2 ls)
    case forallE domain body =>
      rw [← VExpr.replaceConsts_inst hρ]
      exact ih (body.inst param)

theorem instantiateProjectionFields_replaceConsts (hρ : VExpr.ReplacementsClosed ρ)
    (type : VExpr) :
    instantiateProjectionFields typeName (major.replaceConsts ρ) wanted current fuel
        (type.replaceConsts ρ) =
      (instantiateProjectionFields typeName major wanted current fuel type).map
        (·.replaceConsts ρ) := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, VExpr.replaceConsts]
    case const c ls =>
      cases h : ρ c with
      | none => simp [instantiateProjectionFields]
      | some t =>
        exact instantiateProjectionFields_of_ne_forallE (VExpr.instL_ne_forallE (hρ c t h).2 ls)
    case forallE domain body =>
      split
      · simp
      · change instantiateProjectionFields typeName (major.replaceConsts ρ) wanted
            (current + 1) fuel
            ((body.replaceConsts ρ).inst
              ((VExpr.proj typeName current major).replaceConsts ρ)) = _
        rw [← VExpr.replaceConsts_inst hρ]
        exact ih (current := current + 1) (body.inst (.proj typeName current major))

theorem fieldType_replaceConsts (hρ : VExpr.ReplacementsClosed ρ) (info : VProjectionInfo)
    (hctor : info.ctorType.replaceConsts ρ = info.ctorType) :
    info.fieldType typeName levels (params.map (·.replaceConsts ρ)) index
        (major.replaceConsts ρ) =
      (info.fieldType typeName levels params index major).map (·.replaceConsts ρ) := by
  simp only [fieldType, List.length_map]
  split
  · rfl
  · have hfix : (info.ctorType.instL levels).replaceConsts ρ = info.ctorType.instL levels := by
      rw [VExpr.replaceConsts_instL, hctor]
    conv => lhs; rw [← hfix]
    rw [instantiateProjectionParameters_replaceConsts hρ]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_replaceConsts hρ]

end VProjectionInfo

theorem Lookup.replaceConsts (hρ : VExpr.ReplacementsClosed ρ) (H : Lookup Γ i A) :
    Lookup (Γ.map (·.replaceConsts ρ)) i (A.replaceConsts ρ) := by
  induction H with
  | zero => rw [VExpr.replaceConsts_lift hρ]; exact .zero
  | succ _ ih => rw [VExpr.replaceConsts_lift hρ]; exact .succ ih

namespace VEnv

/-- Facts needed to transport derivations of `envL` to `envS` along the constant
replacement `ρ`. `envL` is intended to be `envS` extended by opaque auxiliary
headers (no definitional rules); the replaced constants are those headers, and
every other piece of `envL` is literally present in `envS` and untouched by `ρ`. -/
structure ConstReplacement (envS envL : VEnv) (ρ : Name → Option VExpr) : Prop where
  closed : VExpr.ReplacementsClosed ρ
  ordered : envS.Ordered
  /-- Each replaced header's replacement is a closed term of the header's type. -/
  replaced : ∀ c ci t, envL.constants c = some ci → ρ c = some t →
    envS.HasType ci.uvars [] t (ci.type.replaceConsts ρ)
  /-- Every other constant is present in `envS` with the replaced type. -/
  kept : ∀ c ci, envL.constants c = some ci → ρ c = none →
    ∃ ci', envS.constants c = some ci' ∧ ci'.uvars = ci.uvars ∧
      ci'.type = ci.type.replaceConsts ρ
  defeqs : ∀ df, envL.defeqs df → ∃ df', envS.defeqs df' ∧ df'.uvars = df.uvars ∧
    df'.lhs = df.lhs.replaceConsts ρ ∧ df'.rhs = df.rhs.replaceConsts ρ ∧
    df'.type = df.type.replaceConsts ρ
  eliminators : ∀ block schema, envL.eliminators block schema →
    envS.eliminators block schema ∧
    (∀ owner type, schema.genericType owner = some type → type.replaceConsts ρ = type) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.replaceConsts ρ = df.lhs ∧ df.rhs.replaceConsts ρ = df.rhs ∧
      df.type.replaceConsts ρ = df.type)
  projections : ∀ typeName info, envL.projections typeName info →
    envS.projections typeName info ∧ ρ typeName = none ∧ ρ info.ctorName = none ∧
    info.ctorType.replaceConsts ρ = info.ctorType

/-- Constant replacement transports definitional equality, in every context. -/
theorem ConstReplacement.isDefEq (S : ConstReplacement envS envL ρ)
    (H : envL.IsDefEq U Γ e₁ e₂ A) :
    envS.IsDefEq U (Γ.map (·.replaceConsts ρ)) (e₁.replaceConsts ρ) (e₂.replaceConsts ρ)
      (A.replaceConsts ρ) := by
  have hρ := S.closed
  induction H with
  | bvar h => exact .bvar (h.replaceConsts hρ)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' _ h1 h2 h3 h4 h5 =>
    rw [VExpr.replaceConsts_instL]
    cases hc : ρ c with
    | some t =>
      rw [VExpr.replaceConsts_const_some hc, VExpr.replaceConsts_const_some hc]
      have ht := S.replaced c ci t h1 hc
      have := IsDefEq.instL_r S.ordered (Γ := []) trivial h2 h3 h5 ht
      exact this.weak0 S.ordered
    | none =>
      rw [VExpr.replaceConsts_const_none hc, VExpr.replaceConsts_const_none hc]
      obtain ⟨ci', hci', hu, ht⟩ := S.kept c ci h1 hc
      rw [← ht]
      exact .constDF hci' h2 h3 (h4.trans hu.symm) h5
  | elimDF hlookup htype hclosed hperm hright heq _ ih =>
    obtain ⟨hS, htypes, _⟩ := S.eliminators _ _ hlookup
    have hfix := htypes _ _ htype
    simp only [VExpr.replaceConsts_instL, hfix, VExpr.replaceConsts] at ih ⊢
    exact .elimDF hS htype hclosed hperm hright heq ih
  | elimIota hlookup hgen hmem hclosed hperm _ _ ihLeft ihRight =>
    obtain ⟨hS, _, hrules⟩ := S.eliminators _ _ hlookup
    obtain ⟨hl, hr, ht⟩ := hrules _ _ hgen _ hmem
    simp only [VExpr.replaceConsts_instL, hl, hr, ht] at ihLeft ihRight ⊢
    exact .elimIota hS hgen hmem hclosed hperm ihLeft ihRight
  | appDF _ _ ih1 ih2 =>
    rw [VExpr.replaceConsts_inst hρ]
    exact .appDF ih1 ih2
  | @projDF typeName info levels params index sourceMajor fieldType _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    obtain ⟨hS, htn, _, hctor⟩ := S.projections _ _ hinfo
    have hfield' := VProjectionInfo.fieldType_replaceConsts (typeName := typeName)
      (levels := levels) (params := params) (index := index) (major := sourceMajor)
      hρ info hctor
    rw [hfield] at hfield'
    simp only [VExpr.replaceConsts_mkApps, List.map_append,
      VExpr.replaceConsts_const_none htn] at ihLeft ihRight
    exact .projDF hS hlevels huvars (by simpa using hparams) (by simpa using hindices)
      hfield' ihField ihLeft ihRight hclosed hguard
  | projIota h1 _ h3 _ ih1 ih2 =>
    obtain ⟨hS, _, hctor, _⟩ := S.projections _ _ h1
    simp only [VExpr.replaceConsts, VExpr.replaceConsts_mkApps, hctor] at ih1 ⊢
    exact .projIota hS ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    obtain ⟨hS, htn, hctor, _⟩ := S.projections _ _ h1
    simp only [VExpr.replaceConsts, VExpr.replaceConsts_mkApps, List.map_append,
      List.map_map, Function.comp_def, hctor, htn] at ih1 ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    obtain ⟨hS, htn, _, _⟩ := S.projections _ _ h1
    simp only [VExpr.replaceConsts_mkApps, VExpr.replaceConsts_const_none htn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 h4 ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    simp only [VExpr.replaceConsts, VExpr.replaceConsts_inst hρ]
    exact .beta ih1 ih2
  | eta _ ih =>
    simp only [VExpr.replaceConsts, VExpr.replaceConsts_lift hρ]
    exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    obtain ⟨df', hS, hu, hl, hr, ht⟩ := S.defeqs _ h1
    simp only [VExpr.replaceConsts_instL, ← hl, ← hr, ← ht]
    exact .extra hS h2 (h3.trans hu.symm)

variable {env : VEnv}

/-- `x'` is definitionally equal to `x` at every type of `x`. -/
def SimAt (env : VEnv) (U : Nat) (Γ : List VExpr) (x x' : VExpr) : Prop :=
  ∀ T, env.HasType U Γ x T → env.IsDefEq U Γ x x' T

/-- Subject reduction for a single beta step. This is a consequence of
injectivity of Pi types, which is not established (without `sorry`) here. -/
def BetaSubjectReduction (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ A b a, OnCtx Γ (env.IsType U) → env.SimAt U Γ (.app (.lam A b) a) (b.inst a)

theorem SimAt.refl : env.SimAt U Γ x x := fun _ h => h

theorem SimAt.trans (h1 : env.SimAt U Γ x y) (h2 : env.SimAt U Γ y z) : env.SimAt U Γ x z :=
  fun _ h => let h1 := h1 _ h; h1.trans (h2 _ h1.hasType.2)

theorem SimAt.app (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.SimAt U Γ f f') (ha : env.SimAt U Γ a a') :
    env.SimAt U Γ (.app f a) (.app f' a') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : f.app a = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hf ha rfl eq')
  | base H =>
    subst eq'
    let .app _ _ _ _ _ h1 h2 _ := H
    exact .appDF (hf _ h1.hasType) (ha _ h2.hasType)

theorem SimAt.lam (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hd : env.SimAt U Γ d d')
    (hb : OnCtx (d :: Γ) (env.IsType U) → env.SimAt U (d :: Γ) b b') :
    env.SimAt U Γ (.lam d b) (.lam d' b') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.lam d b = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hd hb rfl eq')
  | base H =>
    subst eq'
    let .lam _ _ h1 _ h2 _ := H
    exact .lamDF (hd _ h1.hasType) (hb ⟨hΓ, _, h1.hasType⟩ _ h2.hasType)

theorem SimAt.forallE (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hd : env.SimAt U Γ d d')
    (hb : OnCtx (d :: Γ) (env.IsType U) → env.SimAt U (d :: Γ) b b') :
    env.SimAt U Γ (.forallE d b) (.forallE d' b') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.forallE d b = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hd hb rfl eq')
  | base H =>
    subst eq'
    let .forallE _ _ h1 h2 := H
    exact .forallEDF (hd _ h1.hasType) (hb ⟨hΓ, _, h1.hasType⟩ _ h2.hasType)

theorem SimAt.proj (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hm : env.SimAt U Γ m m') :
    env.SimAt U Γ (.proj typeName index m) (.proj typeName index m') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.proj typeName index m = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hm rfl eq')
  | base H =>
    subst eq'
    let .proj hinfo hlevels huvars hparams hindices hfield _ hfieldTyping hmajorEq hmajor
      hclosed hguard := H
    exact .projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping.hasType
      hmajorEq.defeq (hmajorEq.defeq.trans (hm _ hmajor.hasType)) hclosed hguard

theorem SimAt.mkApps (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.SimAt U Γ f f') (has : List.Forall₂ (env.SimAt U Γ) as as') :
    env.SimAt U Γ (VExpr.mkApps f as) (VExpr.mkApps f' as') := by
  induction has generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (hf.app henv hΓ ha)

theorem HasType.mkApps_head (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f T : VExpr}, env.HasType U Γ (VExpr.mkApps f as) T →
      ∃ T', env.HasType U Γ f T'
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, _, h =>
    let ⟨_, h⟩ := HasType.mkApps_head henv hΓ (as := as) (f := .app f a) h
    let ⟨_, _, h, _⟩ := HasType.app_inv henv hΓ h
    ⟨_, h⟩

theorem SimAt.forall₂_refl : ∀ (as : List VExpr), List.Forall₂ (env.SimAt U Γ) as as
  | [] => .nil
  | _ :: as => .cons SimAt.refl (SimAt.forall₂_refl as)

/-- Full beta reduction of a lambda telescope applied to at least as many
arguments as it has binders. -/
theorem SimAt.mkApps_wrapLams (henv : Ordered env) (hβ : env.BetaSubjectReduction U)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (doms : List VExpr) (body : VExpr) (args : List VExpr), doms.length ≤ args.length →
      env.SimAt U Γ (VExpr.mkApps (VExpr.wrapLams doms body) args)
        (VExpr.mkApps (body.instOuter (args.take doms.length)) (args.drop doms.length))
  | [], body, args, _ => by simpa [VExpr.wrapLams] using SimAt.refl
  | _ :: _, _, [], h => by simp at h
  | d :: ds, body, a :: rest, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have h1 : env.SimAt U Γ (VExpr.mkApps (VExpr.wrapLams (d :: ds) body) (a :: rest))
        (VExpr.mkApps ((VExpr.wrapLams ds body).inst a) rest) :=
      SimAt.mkApps (f := .app (.lam d (VExpr.wrapLams ds body)) a) (as := rest)
        henv hΓ (hβ Γ d _ a hΓ) (SimAt.forall₂_refl rest)
    rw [VExpr.wrapLams_inst, Nat.zero_add] at h1
    have h2 := SimAt.mkApps_wrapLams henv hβ hΓ (VExpr.instDomains ds a 0)
      (body.inst a ds.length) rest (by simpa using h)
    simp only [VExpr.instDomains_length] at h2
    have hlen : (rest.take ds.length).length = ds.length := by simp; omega
    simpa [List.take_succ_cons, VExpr.instOuter_cons, hlen] using h1.trans h2

end VEnv

namespace InductiveSignature

open VEnv

/-- The hypotheses under which restoration `r` transports derivations of the
lowered environment `envL` (source headers plus opaque auxiliary headers) to
the source-header environment `envS`. The constant replacement `ρ` interprets
each auxiliary header by the closed lambda telescope over its parameters whose
body is the restored head `target levels arguments`. -/
structure RestorationSubstitution (envS envL : VEnv) (r : Restoration)
    (ρ : Name → Option VExpr) : Prop extends VEnv.ConstReplacement envS envL ρ where
  /-- Every replacement is the parameter abstraction of a restoration head. -/
  shape : ∀ c t, ρ c = some t → ∃ h doms,
    r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
    t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments)
  /-- Restoration heads are not source constants. -/
  headsFresh : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h →
    envS.constants c = none
  /-- Renamed recursors are not source constants. -/
  recursorsFresh : ∀ p ∈ r.recursors, envS.constants p.1 = none

/-- The canonical lambda replacement of a restoration table, given a parameter
telescope (outermost first) for each head. -/
def Restoration.lambdaReplacement (r : Restoration)
    (domains : HeadSpecialization → List VExpr) : Name → Option VExpr := fun c =>
  (r.heads.find? (fun h => h.auxiliary == c)).map fun h =>
    VExpr.wrapLams (domains h) (VExpr.mkApps (.const h.target h.levels) h.arguments)

theorem Restoration.lambdaReplacement_shape (r : Restoration)
    {domains : HeadSpecialization → List VExpr}
    (hdomains : ∀ h ∈ r.heads, (domains h).length = h.nparams)
    (hρ : r.lambdaReplacement domains c = some t) : ∃ h doms,
      r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
      t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments) := by
  unfold Restoration.lambdaReplacement at hρ
  cases hfind : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hfind] at hρ
  | some h =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hρ
    exact ⟨h, domains h, rfl, hdomains h (List.mem_of_find?_eq_some hfind), hρ.symm⟩

theorem Restoration.lambdaReplacement_ne_forallE (r : Restoration)
    {domains : HeadSpecialization → List VExpr}
    (hρ : r.lambdaReplacement domains c = some t) : ∀ A B, t ≠ .forallE A B := by
  unfold Restoration.lambdaReplacement at hρ
  cases hfind : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hfind] at hρ
  | some h =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hρ
    subst hρ
    intro A B
    cases hd : domains h with
    | nil =>
      simp only [VExpr.wrapLams, List.foldr]
      exact VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) _
    | cons d ds => intro h; simp [VExpr.wrapLams] at h

theorem Restoration.recursorName_of_constants {r : Restoration} {env : VEnv}
    (hfresh : ∀ p ∈ r.recursors, env.constants p.1 = none)
    (hc : env.constants c = some ci) : r.recursorName c = c := by
  unfold Restoration.recursorName
  split
  · next pair hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [beq_iff_eq] at heq
    have := hfresh _ hmem
    rw [heq, hc] at this
    cases this
  · rfl

private theorem instantiateParams_eq_instOuter' (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Restoration agrees with the lambda replacement up to beta, at every type
of the replaced term. -/
theorem RestorationSubstitution.go_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction U) :
    ∀ (e : VExpr) {Γ : List VExpr} {as as' : List VExpr} {out : VExpr},
      OnCtx Γ (envS.IsType U) → List.Forall₂ (envS.SimAt U Γ) as as' →
      Restoration.expr.go r e as' = some out →
      envS.SimAt U Γ (VExpr.mkApps (e.replaceConsts ρ) as) out := by
  have henv := S.ordered
  intro e
  induction e with
  | bvar i =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | sort u =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | elim block owner ls =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | app fn arg ihfn iharg =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', harg, hfn⟩ := h
    have h1 := iharg (as := []) (as' := []) hΓ .nil harg
    exact ihfn (as := arg.replaceConsts ρ :: as) hΓ (.cons h1 has) hfn
  | lam d b ihd ihb =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact SimAt.mkApps henv hΓ (SimAt.lam henv hΓ (ihd (as := []) hΓ .nil hd)
      fun hΓ' => ihb (as := []) hΓ' .nil hb) has
  | forallE d b ihd ihb =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact SimAt.mkApps henv hΓ (SimAt.forallE henv hΓ (ihd (as := []) hΓ .nil hd)
      fun hΓ' => ihb (as := []) hΓ' .nil hb) has
  | proj n i m ih =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨m', hm, rfl⟩ := h
    exact SimAt.mkApps henv hΓ (SimAt.proj henv hΓ (ih (as := []) hΓ .nil hm)) has
  | const c ls =>
    intro Γ as as' out hΓ has h
    simp only [Restoration.expr.go] at h
    split at h
    · next hd hfind =>
      cases hρ : ρ c with
      | none =>
        rw [VExpr.replaceConsts_const_none hρ]
        intro T hT
        obtain ⟨_, hhead⟩ := HasType.mkApps_head henv hΓ hT
        obtain ⟨ci, hci, _⟩ := HasType.const_inv henv hΓ hhead
        rw [S.headsFresh c hd hfind] at hci
        cases hci
      | some t =>
        rw [VExpr.replaceConsts_const_some hρ]
        obtain ⟨hd', doms, hfind', hdoms, rfl⟩ := S.shape c t hρ
        rw [hfind] at hfind'
        cases hfind'
        have hsim := SimAt.mkApps henv hΓ (SimAt.refl (x := (VExpr.wrapLams doms
          (VExpr.mkApps (.const hd.target hd.levels) hd.arguments)).instL ls)) has
        refine hsim.trans ?_
        unfold HeadSpecialization.apply at h
        split at h
        · cases h
        · next hlen =>
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
            Nat.not_lt] at hlen
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          rw [VExpr.instL_wrapLams]
          have := SimAt.mkApps_wrapLams henv hβ hΓ (doms.map (VExpr.instL ls))
            ((VExpr.mkApps (.const hd.target hd.levels) hd.arguments).instL ls) as'
            (by simp [hdoms]; omega)
          simp only [List.length_map, hdoms] at this
          refine this.trans ?_
          simp only [VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps,
            VExpr.instOuter_const, ← VExpr.mkApps_append, List.map_map,
            Function.comp_def, instantiateParams_eq_instOuter']
          exact SimAt.refl
    · next hfind =>
      have hρ : ρ c = none := by
        cases hρ : ρ c with
        | none => rfl
        | some t =>
          obtain ⟨_, _, hfind', _⟩ := S.shape c t hρ
          rw [hfind] at hfind'
          cases hfind'
      simp only [Option.some.injEq] at h
      subst h
      rw [VExpr.replaceConsts_const_none hρ]
      intro T hT
      obtain ⟨_, hhead⟩ := HasType.mkApps_head henv hΓ hT
      obtain ⟨ci, hci, _⟩ := HasType.const_inv henv hΓ hhead
      rw [Restoration.recursorName_of_constants S.recursorsFresh hci]
      exact SimAt.mkApps henv hΓ SimAt.refl has T hT

theorem RestorationSubstitution.expr_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction U) (hΓ : OnCtx Γ (envS.IsType U))
    (h : r.expr e = some e') : envS.SimAt U Γ (e.replaceConsts ρ) e' :=
  S.go_simAt hβ e (as := []) hΓ .nil h

theorem RestorationSubstitution.onCtx {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ) :
    ∀ {Γ : List VExpr}, OnCtx Γ (envL.IsType U) →
      OnCtx (Γ.map (·.replaceConsts ρ)) (envS.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨hΓ, _, hA⟩ => ⟨S.onCtx hΓ, _, S.isDefEq hA⟩

/-- Restoration of a derivation of the lowered environment, in an arbitrary
well-formed context whose entries are restored pointwise. -/
theorem Restoration.expr_isDefEq {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction U) {Γ Γ' : List VExpr}
    (hΓ : OnCtx Γ (envL.IsType U))
    (H : envL.IsDefEq U Γ e₁ e₂ A) (he₁ : r.expr e₁ = some e₁')
    (he₂ : r.expr e₂ = some e₂') (hA : r.expr A = some A')
    (hΓ' : List.Forall₂ (fun d d' => r.expr d = some d') Γ Γ') :
    envS.IsDefEq U Γ' e₁' e₂' A' := by
  have henv := S.ordered
  have hΓσ := S.onCtx hΓ
  have Hσ := S.isDefEq H
  have h1 := S.expr_simAt hβ hΓσ he₁ _ Hσ.hasType.1
  have h2 := S.expr_simAt hβ hΓσ he₂ _ Hσ.hasType.2
  obtain ⟨u, hAσ⟩ := Hσ.isType henv hΓσ
  have h3 := S.expr_simAt hβ hΓσ hA _ hAσ
  have Heq : envS.IsDefEq U (Γ.map (·.replaceConsts ρ)) e₁' e₂' A' :=
    .defeqDF h3 (h1.symm.trans (Hσ.trans h2))
  have hctx : ∀ {Γ Γ'}, OnCtx Γ (envL.IsType U) →
      List.Forall₂ (fun d d' => r.expr d = some d') Γ Γ' →
      IsDefEqCtx envS U [] (Γ.map (·.replaceConsts ρ)) Γ' := by
    intro Γ Γ' hΓ hΓ'
    induction hΓ' with
    | nil => exact .zero
    | cons hd _ ih =>
      obtain ⟨hΓ, _, hA⟩ := hΓ
      have hAσ := S.isDefEq hA
      exact .succ (ih hΓ) (S.expr_simAt hβ (S.onCtx hΓ) hd _ hAσ)
  exact Heq.defeqDFC henv (hctx hΓ hΓ')

theorem Restoration.expr_hasType {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction U) {Γ Γ' : List VExpr}
    (hΓ : OnCtx Γ (envL.IsType U))
    (H : envL.HasType U Γ e A) (he : r.expr e = some e') (hA : r.expr A = some A')
    (hΓ' : List.Forall₂ (fun d d' => r.expr d = some d') Γ Γ') :
    envS.HasType U Γ' e' A' :=
  Restoration.expr_isDefEq S hβ hΓ H he he hA hΓ'

/-- The closed-context form, which needs no restoration of the type. -/
theorem Restoration.expr_isDefEqU {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction U)
    (H : envL.IsDefEqU U [] e₁ e₂) (he₁ : r.expr e₁ = some e₁')
    (he₂ : r.expr e₂ = some e₂') :
    envS.IsDefEqU U [] e₁' e₂' := by
  obtain ⟨_, H⟩ := H
  have Hσ := S.isDefEq H
  have h1 := S.expr_simAt hβ (Γ := []) trivial he₁ _ Hσ.hasType.1
  have h2 := S.expr_simAt hβ (Γ := []) trivial he₂ _ Hσ.hasType.2
  exact ⟨_, h1.symm.trans (Hσ.trans h2)⟩

/-- The nested constructor correspondence: a normalized constructor type that
is definitionally equal in the lowered environment to the expanded constructor
type restores to the restoration of the expanded type. -/
theorem RestoresType.of_models_constructor {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {uvars : Nat} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction uvars)
    (hdefeq : envL.IsDefEqU uvars [] normalized expandedType)
    (hrestored : r.expr expandedType = some sourceType)
    (hnorm : ∃ restored, r.expr normalized = some restored) :
    RestoresType r envS uvars normalized sourceType := by
  obtain ⟨restored, hn⟩ := hnorm
  exact ⟨restored, hn, Restoration.expr_isDefEqU S hβ hdefeq hn hrestored⟩

/-- Variant in which the source type is only definitionally equal (at every
type of it) to the restoration of the expanded type. -/
theorem RestoresType.of_models_constructor' {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {uvars : Nat} (S : RestorationSubstitution envS envL r ρ)
    (hβ : envS.BetaSubjectReduction uvars)
    (hdefeq : envL.IsDefEqU uvars [] normalized expandedType)
    (hrestored : r.expr expandedType = some restoredExpanded)
    (hsource : envS.SimAt uvars [] restoredExpanded sourceType)
    (hnorm : ∃ restored, r.expr normalized = some restored) :
    RestoresType r envS uvars normalized sourceType := by
  obtain ⟨restored, hn⟩ := hnorm
  obtain ⟨_, h1⟩ := Restoration.expr_isDefEqU S hβ hdefeq hn hrestored
  exact ⟨restored, hn, _, h1.trans (hsource _ h1.hasType.2)⟩

end InductiveSignature
end Lean4Lean
