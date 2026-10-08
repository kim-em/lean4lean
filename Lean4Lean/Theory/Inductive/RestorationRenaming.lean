import Lean4Lean.Theory.Inductive.RestorationInterpretation

/-! Restoration with renaming, transporting derivations of a full lowered
environment.

The restoration interpretation keeping projection owners (`Restoration.constInterpretation`) transports derivations of a lowered *header* environment,
whose only extra constants are opaque auxiliary headers, to the source header
environment. A lowered recursor environment additionally contains

* constants kept under their name whose source type is only definitionally
  equal to the replaced lowered type (the source constructors, whose lowered
  types mention auxiliary families, and the source recursors);
* constants that are renamed (the auxiliary recursors `aux.rec ↦ Main.rec_k`);
* projections of lowered families (including auxiliary families, whose
  projections must be renamed to projections of the container).

`VExpr.replaceRen ρ σ` replaces each constant `c` with `ρ c = some t` by
`t.instL ls`, renames every other constant by `σ`, and renames projection type
names by `σ`. `VEnv.RenamingReplacement` collects the facts that transport
every derivation along `replaceRen` (`RenamingReplacement.isDefEq`); kept
constants only need definitionally equal types, and the projection rules are
transported through the abstract `ProjectionRulesRenamed` clause
(`ProjectionRulesRenamed.of_fixed` discharges it for projections untouched by the
replacement). `RenamingRestorationSubstitution` relates `replaceRen` to
`Restoration.expr` up to beta (`RenamingRestorationAgreement.go_simAt`,
`RenamingRestorationSubstitution.expr_simAt`), for terms whose projection names are
fixed by `σ`; the resulting typing of restored terms is in `RestorationRenamingOnCtx.lean`
(`Restoration.expr_hasType_onCtx`).
-/

namespace Lean4Lean

namespace VExpr

/-- Every replacement is closed, and no replacement is a Pi type (so that
replacement does not create new telescope binders). -/
def ReplacementsClosed (ρ : Name → Option VExpr) : Prop :=
  ∀ c t, ρ c = some t → t.ClosedN ∧ ∀ A B, t ≠ .forallE A B

theorem instL_ne_forallE (h : ∀ A B, t ≠ VExpr.forallE A B) (ls : List VLevel) :
    ∀ A B, t.instL ls ≠ .forallE A B := by
  cases t <;> simp [instL]
  exact h _ _ rfl

/-- Replace constants by closed universe-polymorphic terms, rename the other
constants and all projection type names. -/
def replaceRen (ρ : Name → Option VExpr) (σ : Name → Name) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls =>
    match ρ c with
    | some t => t.instL ls
    | none => .const (σ c) ls
  | .elim block owner ls => .elim block owner ls
  | .app f a => .app (f.replaceRen ρ σ) (a.replaceRen ρ σ)
  | .proj n i e => .proj (σ n) i (e.replaceRen ρ σ)
  | .lam A b => .lam (A.replaceRen ρ σ) (b.replaceRen ρ σ)
  | .forallE A b => .forallE (A.replaceRen ρ σ) (b.replaceRen ρ σ)

theorem replaceRen_const_some (h : ρ c = some t) :
    (VExpr.const c ls).replaceRen ρ σ = t.instL ls := by
  simp [replaceRen, h]

theorem replaceRen_const_none (h : ρ c = none) :
    (VExpr.const c ls).replaceRen ρ σ = .const (σ c) ls := by
  simp [replaceRen, h]

@[simp] theorem replaceRen_mkApps (f : VExpr) (args : List VExpr) :
    (mkApps f args).replaceRen ρ σ =
      mkApps (f.replaceRen ρ σ) (args.map (·.replaceRen ρ σ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem replaceRen_liftN (hρ : ReplacementsClosed ρ) (e : VExpr) (n k : Nat) :
    (e.liftN n k).replaceRen ρ σ = (e.replaceRen ρ σ).liftN n k := by
  induction e generalizing k with
  | bvar | sort | elim => rfl
  | const c ls =>
    simp only [liftN, replaceRen]
    split
    · next t h => exact ((hρ c t h).1.instL.liftN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [liftN, replaceRen, ihf, iha]
  | proj _ _ e ih => simp [liftN, replaceRen, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [liftN, replaceRen, ihA, ihb]

theorem replaceRen_lift (hρ : ReplacementsClosed ρ) (e : VExpr) :
    e.lift.replaceRen ρ σ = (e.replaceRen ρ σ).lift := replaceRen_liftN hρ e 1 0

theorem replaceRen_inst (hρ : ReplacementsClosed ρ) (e a : VExpr) (k : Nat) :
    (e.inst a k).replaceRen ρ σ = (e.replaceRen ρ σ).inst (a.replaceRen ρ σ) k := by
  induction e generalizing k with
  | sort | elim => rfl
  | bvar i =>
    simp only [inst, instVar, replaceRen]
    split
    · rfl
    · split
      · exact replaceRen_liftN hρ a k 0
      · rfl
  | const c ls =>
    simp only [inst, replaceRen]
    split
    · next t h => exact ((hρ c t h).1.instL.instN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [inst, replaceRen, ihf, iha]
  | proj _ _ e ih => simp [inst, replaceRen, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [inst, replaceRen, ihA, ihb]

theorem replaceRen_instL (e : VExpr) (ls : List VLevel) :
    (e.instL ls).replaceRen ρ σ = (e.replaceRen ρ σ).instL ls := by
  induction e with
  | bvar | sort | elim => rfl
  | const c us =>
    simp only [instL, replaceRen]
    split
    · exact instL_instL.symm
    · rfl
  | app f a ihf iha => simp [instL, replaceRen, ihf, iha]
  | proj _ _ e ih => simp [instL, replaceRen, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [instL, replaceRen, ihA, ihb]

/-- `replaceRen` is the identity on terms none of whose constants are replaced
or renamed, and none of whose projection names are renamed. -/
theorem replaceRen_eq_self {names : List Name}
    (hρ : ∀ c, c ∉ names → ρ c = none) (hσ : ∀ c, c ∉ names → σ c = c) :
    ∀ {e : VExpr}, e.containsAnyConst names = false → e.replaceRen ρ σ = e
  | .bvar _, _ | .sort _, _ | .elim .., _ => rfl
  | .const c ls, h => by
    have hc : c ∉ names := by simpa [containsAnyConst] using h
    rw [replaceRen_const_none (hρ c hc), hσ c hc]
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [replaceRen, replaceRen_eq_self hρ hσ h.1, replaceRen_eq_self hρ hσ h.2]
  | .proj n i e, h => by
    simp only [containsAnyConst, Bool.or_eq_false_iff] at h
    have hn : n ∉ names := by simpa using h.1
    simp only [replaceRen, replaceRen_eq_self hρ hσ h.2, hσ n hn]

end VExpr

namespace VProjectionInfo

theorem instantiateProjectionParameters_replaceRen (hρ : VExpr.ReplacementsClosed ρ)
    (type : VExpr) (params : List VExpr) :
    instantiateProjectionParameters (type.replaceRen ρ σ) (params.map (·.replaceRen ρ σ)) =
      (instantiateProjectionParameters type params).map (·.replaceRen ρ σ) := by
  induction params generalizing type with
  | nil => simp [instantiateProjectionParameters]
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters, VExpr.replaceRen]
    case const c ls =>
      cases h : ρ c with
      | none => simp [instantiateProjectionParameters]
      | some t =>
        exact instantiateProjectionParameters_of_ne_forallE
          (VExpr.instL_ne_forallE (hρ c t h).2 ls)
    case forallE domain body =>
      rw [← VExpr.replaceRen_inst hρ]
      exact ih (body.inst param)

theorem instantiateProjectionFields_replaceRen (hρ : VExpr.ReplacementsClosed ρ)
    (hσ : σ typeName = typeName) (type : VExpr) :
    instantiateProjectionFields typeName (major.replaceRen ρ σ) wanted current fuel
        (type.replaceRen ρ σ) =
      (instantiateProjectionFields typeName major wanted current fuel type).map
        (·.replaceRen ρ σ) := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, VExpr.replaceRen]
    case const c ls =>
      cases h : ρ c with
      | none => simp [instantiateProjectionFields]
      | some t =>
        exact instantiateProjectionFields_of_ne_forallE (VExpr.instL_ne_forallE (hρ c t h).2 ls)
    case forallE domain body =>
      split
      · simp
      · change instantiateProjectionFields typeName (major.replaceRen ρ σ) wanted
            (current + 1) fuel
            ((body.replaceRen ρ σ).inst
              (.proj typeName current (major.replaceRen ρ σ))) = _
        have : VExpr.proj typeName current (major.replaceRen ρ σ) =
            (VExpr.proj typeName current major).replaceRen ρ σ := by
          simp [VExpr.replaceRen, hσ]
        rw [this, ← VExpr.replaceRen_inst hρ]
        exact ih (current := current + 1) (body.inst (.proj typeName current major))

theorem fieldType_replaceRen (hρ : VExpr.ReplacementsClosed ρ) (hσ : σ typeName = typeName)
    (info : VProjectionInfo) (hctor : info.ctorType.replaceRen ρ σ = info.ctorType) :
    info.fieldType typeName levels (params.map (·.replaceRen ρ σ)) index
        (major.replaceRen ρ σ) =
      (info.fieldType typeName levels params index major).map (·.replaceRen ρ σ) := by
  simp only [fieldType, List.length_map]
  split
  · rfl
  · have hfix : (info.ctorType.instL levels).replaceRen ρ σ = info.ctorType.instL levels := by
      rw [VExpr.replaceRen_instL, hctor]
    conv => lhs; rw [← hfix]
    rw [instantiateProjectionParameters_replaceRen hρ]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_replaceRen hρ hσ]

end VProjectionInfo

theorem Lookup.replaceRen (hρ : VExpr.ReplacementsClosed ρ) (H : Lookup Γ i A) :
    Lookup (Γ.map (·.replaceRen ρ σ)) i (A.replaceRen ρ σ) := by
  induction H with
  | zero => rw [VExpr.replaceRen_lift hρ]; exact .zero
  | succ _ ih => rw [VExpr.replaceRen_lift hρ]; exact .succ ih

namespace VEnv

/-- Full beta reduction of a lambda telescope applied to at least as many
arguments as it has binders. -/
theorem SimAt.mkApps_wrapLams {env : VEnv} (henv : Ordered env) (hβ : env.BetaSubjectReduction U)
    (hΓ : OnCtx Γ (env.IsType U)) (doms : List VExpr) (body : VExpr) (args : List VExpr)
    (h : doms.length ≤ args.length) :
    env.SimAt U Γ (VExpr.mkApps (VExpr.wrapLams doms body) args)
      (VExpr.mkApps (body.instOuter (args.take doms.length)) (args.drop doms.length)) :=
  (VExpr.BetaRed.mkApps_wrapLams doms body args h).simAt henv hβ hΓ

/-- The four projection rules of `envL` at the projection `(typeName, info)`,
transported along `replaceRen ρ σ` to `envS`: each conclusion holds in `envS`
once the replaced premises do. -/
structure ProjectionRulesRenamed (envS : VEnv) (ρ : Name → Option VExpr) (σ : Name → Name)
    (typeName : Name) (info : VProjectionInfo) : Prop where
  projDF : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {index : Nat} {sourceMajor fieldType : VExpr} {fieldLevel : VLevel}
      {major : VExpr} {indexArgs : List VExpr} {major' : VExpr},
    (∀ l ∈ levels, l.WF U) → levels.length = info.uvars →
    params.length = info.nparams → indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    info.ctorType.Closed →
    ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) →
    envS.HasType U Γ (fieldType.replaceRen ρ σ) (.sort fieldLevel) →
    envS.IsDefEq U Γ (sourceMajor.replaceRen ρ σ) (major.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) (params ++ indexArgs)).replaceRen ρ σ) →
    envS.IsDefEq U Γ (sourceMajor.replaceRen ρ σ) (major'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) (params ++ indexArgs)).replaceRen ρ σ) →
    envS.IsDefEq U Γ ((VExpr.proj typeName index major).replaceRen ρ σ)
      ((VExpr.proj typeName index major').replaceRen ρ σ) (fieldType.replaceRen ρ σ)
  projIota : ∀ {U : Nat} {Γ : List VExpr} {index : Nat} {levels : List VLevel}
      {args : List VExpr} {field fieldType : VExpr},
    envS.HasType U Γ
      ((VExpr.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)).replaceRen
        ρ σ) (fieldType.replaceRen ρ σ) →
    args[info.nparams + index]? = some field →
    envS.HasType U Γ (field.replaceRen ρ σ) (fieldType.replaceRen ρ σ) →
    envS.IsDefEq U Γ
      ((VExpr.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)).replaceRen
        ρ σ) (field.replaceRen ρ σ) (fieldType.replaceRen ρ σ)
  structEta : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e : VExpr},
    params.length = info.nparams → info.nindices = 0 →
    envS.HasType U Γ (e.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.HasType U Γ
      ((VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index =>
          .proj typeName index e)).replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.IsDefEq U Γ
      ((VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index =>
          .proj typeName index e)).replaceRen ρ σ)
      (e.replaceRen ρ σ) ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ)
  unitLike : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e e' : VExpr},
    params.length = info.nparams → info.nindices = 0 → info.numFields = 0 →
    envS.HasType U Γ (e.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.HasType U Γ (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.IsDefEq U Γ (e.replaceRen ρ σ) (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ)

/-- A projection of `envS` untouched by the replacement transports. -/
theorem ProjectionRulesRenamed.of_fixed {envS : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} (hρ : VExpr.ReplacementsClosed ρ)
    (hS : envS.projections typeName info) (htn : ρ typeName = none)
    (hσtn : σ typeName = typeName) (hctorName : ρ info.ctorName = none)
    (hσctor : σ info.ctorName = info.ctorName)
    (hctor : info.ctorType.replaceRen ρ σ = info.ctorType) :
    ProjectionRulesRenamed envS ρ σ typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      hlevels huvars hparams hindices hfield hclosed hguard ihField ihLeft ihRight
    have hfield' := VProjectionInfo.fieldType_replaceRen (typeName := typeName)
      (levels := levels) (params := params) (index := index) (major := sourceMajor)
      hρ hσtn info hctor
    rw [hfield] at hfield'
    simp only [VExpr.replaceRen_mkApps, List.map_append,
      VExpr.replaceRen_const_none htn, hσtn] at ihLeft ihRight
    simp only [VExpr.replaceRen, hσtn]
    exact .projDF hS hlevels huvars (by simpa using hparams) (by simpa using hindices)
      hfield' ihField ihLeft ihRight hclosed hguard
  projIota := by
    intro U Γ index levels args field fieldType ih1 h3 ih2
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, hctorName,
      hσctor, hσtn] at ih1 ⊢
    exact .projIota hS ih1 (by simp [h3]) ih2
  structEta := by
    intro U Γ levels params e h2 h3 ih1 ih2
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, List.map_append,
      List.map_map, Function.comp_def, hctorName, htn, hσctor, hσtn] at ih1 ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  unitLike := by
    intro U Γ levels params e e' h2 h3 h4 ih1 ih2
    simp only [VExpr.replaceRen_mkApps, VExpr.replaceRen_const_none htn, hσtn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 h4 ih1 ih2

/-- Facts needed to transport derivations of `envL` to `envS` along
`replaceRen ρ σ`. Kept constants are renamed by `σ` and need only a
definitionally equal type; projections are transported abstractly. -/
structure RenamingReplacement (envS envL : VEnv) (ρ : Name → Option VExpr)
    (σ : Name → Name) : Prop where
  closed : VExpr.ReplacementsClosed ρ
  ordered : envS.Ordered
  /-- Each replaced constant's replacement is a closed term of its replaced type. -/
  replaced : ∀ c ci t, envL.constants c = some ci → ρ c = some t →
    envS.HasType ci.uvars [] t (ci.type.replaceRen ρ σ)
  /-- Every other constant is present in `envS` under its renamed name, with a
  type definitionally equal to its replaced type. -/
  kept : ∀ c ci, envL.constants c = some ci → ρ c = none →
    ∃ ci', envS.constants (σ c) = some ci' ∧ ci'.uvars = ci.uvars ∧
      ∃ u, envS.IsDefEq ci.uvars [] ci'.type (ci.type.replaceRen ρ σ) (.sort u)
  defeqs : ∀ df, envL.defeqs df → ∃ df', envS.defeqs df' ∧ df'.uvars = df.uvars ∧
    df'.lhs = df.lhs.replaceRen ρ σ ∧ df'.rhs = df.rhs.replaceRen ρ σ ∧
    df'.type = df.type.replaceRen ρ σ
  eliminators : ∀ block schema, envL.eliminators block schema →
    envS.eliminators block schema ∧
    (∀ owner type, schema.genericType owner = some type → type.replaceRen ρ σ = type) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
      df.type.replaceRen ρ σ = df.type)
  projections : ∀ typeName info, envL.projections typeName info →
    ProjectionRulesRenamed envS ρ σ typeName info

variable {envS envL : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}

/-- Renaming replacement transports definitional equality, in every context. -/
theorem RenamingReplacement.isDefEq (S : RenamingReplacement envS envL ρ σ)
    (H : envL.IsDefEq U Γ e₁ e₂ A) :
    envS.IsDefEq U (Γ.map (·.replaceRen ρ σ)) (e₁.replaceRen ρ σ) (e₂.replaceRen ρ σ)
      (A.replaceRen ρ σ) := by
  have hρ := S.closed
  induction H with
  | bvar h => exact .bvar (h.replaceRen hρ)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' Γ₀ h1 h2 h3 h4 h5 =>
    rw [VExpr.replaceRen_instL]
    cases hc : ρ c with
    | some t =>
      rw [VExpr.replaceRen_const_some hc, VExpr.replaceRen_const_some hc]
      have ht := S.replaced c ci t h1 hc
      have := IsDefEq.instL_r S.ordered (Γ := []) trivial h2 h3 h5 ht
      exact this.weak0 S.ordered
    | none =>
      rw [VExpr.replaceRen_const_none hc, VExpr.replaceRen_const_none hc]
      obtain ⟨ci', hci', hu, _, ht⟩ := S.kept c ci h1 hc
      have hconst : envS.IsDefEq U (Γ₀.map (·.replaceRen ρ σ)) (.const (σ c) ls) (.const (σ c) ls') (ci'.type.instL ls) :=
        IsDefEq.constDF hci' h2 h3 (h4.trans hu.symm) h5
      have ht' := (ht.instL h2 (Γ := [])).weak0 S.ordered (Γ := Γ₀.map (·.replaceRen ρ σ))
      exact .defeqDF ht' hconst
  | elimDF hlookup htype hclosed hperm hright heq _ ih =>
    obtain ⟨hS, htypes, _⟩ := S.eliminators _ _ hlookup
    have hfix := htypes _ _ htype
    simp only [VExpr.replaceRen_instL, hfix, VExpr.replaceRen] at ih ⊢
    exact .elimDF hS htype hclosed hperm hright heq ih
  | elimIota hlookup hgen hmem hclosed hperm _ _ ihLeft ihRight =>
    obtain ⟨hS, _, hrules⟩ := S.eliminators _ _ hlookup
    obtain ⟨hl, hr, ht⟩ := hrules _ _ hgen _ hmem
    simp only [VExpr.replaceRen_instL, hl, hr, ht] at ihLeft ihRight ⊢
    exact .elimIota hS hgen hmem hclosed hperm ihLeft ihRight
  | appDF _ _ ih1 ih2 =>
    rw [VExpr.replaceRen_inst hρ]
    exact .appDF ih1 ih2
  | projDF hinfo hlevels huvars hparams hindices hfield _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    exact (S.projections _ _ hinfo).projDF hlevels huvars hparams hindices hfield hclosed
      hguard ihField ihLeft ihRight
  | projIota h1 _ h3 _ ih1 ih2 =>
    exact (S.projections _ _ h1).projIota ih1 h3 ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    exact (S.projections _ _ h1).structEta h2 h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact (S.projections _ _ h1).unitLike h2 h3 h4 ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    simp only [VExpr.replaceRen, VExpr.replaceRen_inst hρ]
    exact .beta ih1 ih2
  | eta _ ih =>
    simp only [VExpr.replaceRen, VExpr.replaceRen_lift hρ]
    exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    obtain ⟨df', hS, hu, hl, hr, ht⟩ := S.defeqs _ h1
    simp only [VExpr.replaceRen_instL, ← hl, ← hr, ← ht]
    exact .extra hS h2 (h3.trans hu.symm)

/-- The clause of `RenamingReplacement` for one constant `c : ci` of the
lowered environment. -/
def RenamingReplacement.ConstClause (envS : VEnv) (ρ : Name → Option VExpr)
    (σ : Name → Name) (c : Name) (ci : VConstant) : Prop :=
  (∀ t, ρ c = some t → envS.HasType ci.uvars [] t (ci.type.replaceRen ρ σ)) ∧
  (ρ c = none → ∃ ci', envS.constants (σ c) = some ci' ∧ ci'.uvars = ci.uvars ∧
    ∃ u, envS.IsDefEq ci.uvars [] ci'.type (ci.type.replaceRen ρ σ) (.sort u))

/-- Extend a renaming replacement by one constant. -/
theorem RenamingReplacement.addConst {env env' : VEnv}
    (S : RenamingReplacement envS env ρ σ) (h : env.addConst n ci = some env')
    (hc : RenamingReplacement.ConstClause envS ρ σ n ci) :
    RenamingReplacement envS env' ρ σ where
  closed := S.closed
  ordered := S.ordered
  replaced c ci' t hc' ht := by
    by_cases hn : n = c
    · subst hn
      rw [VEnv.addConst_self h] at hc'
      cases hc'
      exact hc.1 t ht
    · rw [VEnv.addConst_constants_of_ne h hn] at hc'
      exact S.replaced c ci' t hc' ht
  kept c ci' hc' ht := by
    by_cases hn : n = c
    · subst hn
      rw [VEnv.addConst_self h] at hc'
      cases hc'
      exact hc.2 ht
    · rw [VEnv.addConst_constants_of_ne h hn] at hc'
      exact S.kept c ci' hc' ht
  defeqs df hdf := S.defeqs df (by rwa [VEnv.addConst_defeqs h] at hdf)
  eliminators block schema hs :=
    S.eliminators block schema (by rwa [VEnv.addConst_eliminators h] at hs)
  projections typeName info hp :=
    S.projections typeName info (by rwa [VEnv.addConst_projections h] at hp)

/-- Extend a renaming replacement by a list of constants. -/
theorem RenamingReplacement.addConstVals {env env' : VEnv} :
    ∀ {cs : List VConstVal}, RenamingReplacement envS env ρ σ →
      env.addConstVals cs = some env' →
      (∀ c ∈ cs, RenamingReplacement.ConstClause envS ρ σ c.name c.toVConstant) →
      RenamingReplacement envS env' ρ σ
  | [], S, h, _ => by cases h; exact S
  | c :: cs, S, h, hc => by
    simp only [VEnv.addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h₁, h₂⟩ := h
    exact RenamingReplacement.addConstVals
      (S.addConst h₁ (hc c List.mem_cons_self)) h₂
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

/-- A base environment, contained in `envS`, every piece of which is fixed by
the replacement. -/
theorem RenamingReplacement.of_le {base : VEnv} (hρ : VExpr.ReplacementsClosed ρ)
    (hS : envS.Ordered) (hbase : base.Ordered) (hle : base ≤ envS)
    (hconst : ∀ c ci, base.constants c = some ci →
      ρ c = none ∧ σ c = c ∧ ci.type.replaceRen ρ σ = ci.type)
    (hdefeqs : ∀ df, base.defeqs df →
      df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
      df.type.replaceRen ρ σ = df.type)
    (helim : ∀ block schema, base.eliminators block schema →
      (∀ owner type, schema.genericType owner = some type → type.replaceRen ρ σ = type) ∧
      (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
        df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
        df.type.replaceRen ρ σ = df.type)) :
    RenamingReplacement envS base ρ σ where
  closed := hρ
  ordered := hS
  replaced c ci t hc ht := by
    rw [(hconst c ci hc).1] at ht
    cases ht
  kept c ci hc _ := by
    obtain ⟨-, hσ, hty⟩ := hconst c ci hc
    obtain ⟨u, hu⟩ := hbase.constWF hc
    refine ⟨ci, by rw [hσ]; exact hle.constants hc, rfl, u, ?_⟩
    rw [hty]
    exact hu.mono hle
  defeqs df hdf := by
    obtain ⟨hl, hr, ht⟩ := hdefeqs df hdf
    exact ⟨df, hle.defeqs hdf, rfl, hl.symm, hr.symm, ht.symm⟩
  eliminators block schema hs := ⟨hle.eliminators hs, helim block schema hs⟩
  projections typeName info hp := by
    obtain ⟨ci, htn⟩ := hbase.projectionConstant hp
    have hctor := hbase.projectionConstructor hp
    obtain ⟨h1, h2, _⟩ := hconst _ _ htn
    obtain ⟨h3, h4, h5⟩ := hconst _ _ hctor
    exact ProjectionRulesRenamed.of_fixed hρ (hle.projections hp) h1 h2 h3 h4 h5

end VEnv

namespace InductiveSignature

open VEnv

/-- The agreement of the restoration `r` (heads and recursor renaming) with the
renaming replacement `(ρ, σ)`: every replacement is the parameter abstraction of
a restoration head, every head is replaced, and away from the heads the renaming
is the recursor renaming. These clauses alone relate `replaceRen ρ σ` to
`r.expr` up to beta (`RenamingRestorationAgreement.go_simAt`). -/
structure RenamingRestorationAgreement (r : Restoration) (ρ : Name → Option VExpr)
    (σ : Name → Name) : Prop where
  /-- Every replacement is the parameter abstraction of a restoration head. -/
  shape : ∀ c t, ρ c = some t → ∃ h doms,
    r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
    t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments)
  /-- Every restoration head is replaced. -/
  headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → ρ c ≠ none
  /-- Away from the heads, the renaming is the recursor renaming. -/
  renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none → σ c = r.recursorName c

/-- The hypotheses under which restoration `r` (heads and recursor renaming)
transports derivations of the lowered environment `envL` to `envS`: a
renaming replacement whose replacements are the parameter abstractions of the
restoration heads, which replaces every head, and whose renaming agrees with
the recursor renaming of `r` away from the heads. -/
structure RenamingRestorationSubstitution (envS envL : VEnv) (r : Restoration)
    (ρ : Name → Option VExpr) (σ : Name → Name) : Prop
    extends VEnv.RenamingReplacement envS envL ρ σ where
  /-- Every replacement is the parameter abstraction of a restoration head. -/
  shape : ∀ c t, ρ c = some t → ∃ h doms,
    r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
    t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments)
  /-- Every restoration head is replaced. -/
  headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → ρ c ≠ none
  /-- Away from the heads, the renaming is the recursor renaming. -/
  renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none → σ c = r.recursorName c

private theorem instantiateParams_eq_instOuter'' (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Restoration agrees with the renaming replacement up to beta, at every
type of the replaced term, for terms whose projection names are fixed. Only the
agreement clauses, the ordering of `envS` and beta subject reduction are used. -/
theorem RenamingRestorationAgreement.go_simAt {envS : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationAgreement r ρ σ) (henv : envS.Ordered)
    (hβ : envS.BetaSubjectReduction U) :
    ∀ (e : VExpr) {Γ : List VExpr} {as as' : List VExpr} {out : VExpr},
      e.ProjNamesFixed σ →
      OnCtx Γ (envS.IsType U) → List.Forall₂ (envS.SimAt U Γ) as as' →
      Restoration.expr.go r e as' = some out →
      envS.SimAt U Γ (VExpr.mkApps (e.replaceRen ρ σ) as) out := by
  intro e
  induction e with
  | bvar i =>
    intro Γ as as' out _ hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | sort u =>
    intro Γ as as' out _ hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | elim block owner ls =>
    intro Γ as as' out _ hΓ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact SimAt.mkApps henv hΓ SimAt.refl has
  | app fn arg ihfn iharg =>
    intro Γ as as' out hfix hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', harg, hfn⟩ := h
    have h1 := iharg (as := []) (as' := []) hfix.2 hΓ .nil harg
    exact ihfn (as := arg.replaceRen ρ σ :: as) hfix.1 hΓ (.cons h1 has) hfn
  | lam d b ihd ihb =>
    intro Γ as as' out hfix hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact SimAt.mkApps henv hΓ (SimAt.lam henv hΓ (ihd (as := []) hfix.1 hΓ .nil hd)
      fun hΓ' => ihb (as := []) hfix.2 hΓ' .nil hb) has
  | forallE d b ihd ihb =>
    intro Γ as as' out hfix hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact SimAt.mkApps henv hΓ (SimAt.forallE henv hΓ (ihd (as := []) hfix.1 hΓ .nil hd)
      fun hΓ' => ihb (as := []) hfix.2 hΓ' .nil hb) has
  | proj n i m ih =>
    intro Γ as as' out hfix hΓ has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨m', hm, rfl⟩ := h
    simp only [VExpr.replaceRen, hfix.1]
    exact SimAt.mkApps henv hΓ (SimAt.proj henv hΓ (ih (as := []) hfix.2 hΓ .nil hm)) has
  | const c ls =>
    intro Γ as as' out _ hΓ has h
    simp only [Restoration.expr.go] at h
    split at h
    · next hd hfind =>
      cases hρ : ρ c with
      | none => exact absurd hρ (S.headsReplaced c hd hfind)
      | some t =>
        rw [VExpr.replaceRen_const_some hρ]
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
            Function.comp_def, instantiateParams_eq_instOuter'']
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
      rw [VExpr.replaceRen_const_none hρ, S.renamed c hfind]
      exact SimAt.mkApps henv hΓ SimAt.refl has

theorem RenamingRestorationAgreement.expr_simAt {envS : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationAgreement r ρ σ) (henv : envS.Ordered)
    (hβ : envS.BetaSubjectReduction U) (hΓ : OnCtx Γ (envS.IsType U))
    (hfix : e.ProjNamesFixed σ) (h : r.expr e = some e') :
    envS.SimAt U Γ (e.replaceRen ρ σ) e' :=
  S.go_simAt henv hβ e (as := []) hfix hΓ .nil h


/-- The agreement clauses of a renaming restoration substitution. -/
theorem RenamingRestorationSubstitution.agreement {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationSubstitution envS envL r ρ σ) :
    RenamingRestorationAgreement r ρ σ :=
  ⟨S.shape, S.headsReplaced, S.renamed⟩

theorem RenamingRestorationSubstitution.expr_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationSubstitution envS envL r ρ σ)
    (hβ : envS.BetaSubjectReduction U) (hΓ : OnCtx Γ (envS.IsType U))
    (hfix : e.ProjNamesFixed σ) (h : r.expr e = some e') :
    envS.SimAt U Γ (e.replaceRen ρ σ) e' :=
  S.agreement.expr_simAt S.ordered hβ hΓ hfix h

end InductiveSignature
end Lean4Lean
