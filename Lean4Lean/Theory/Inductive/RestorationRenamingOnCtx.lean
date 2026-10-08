import Lean4Lean.Theory.Inductive.RestorationRenaming
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Theory.Typing.EliminatorRestorationScope
import Lean4Lean.Theory.Inductive.CaseTypeClosed

/-! Context-carrying renaming replacement.

`VEnv.RenamingReplacement` transports derivations of a lowered environment in
every context, so its projection clause `ProjectionRulesRenamed` must transport
the projection rules in arbitrary, possibly ill-formed, image contexts. The
variant `RenamingReplacementOnCtx` asks for the projection rules only in
well-formed image contexts (`ProjectionRulesRenamedOnCtx`); its transport
`RenamingReplacementOnCtx.isDefEq` carries the well-formedness of the image
context through the binders of the derivation. Every derivation starting in a
well-formed image context (in particular the empty context, where the
generated equations are stated) is transported.

Its eliminator clause also admits restoration-free lowered eliminators matched
by a registered restored source schema with the same signature
(`RestoredEliminator`, added by `RenamingReplacementOnCtx.addEliminator`): their
rules are transported through the agreement of restoration with the renaming
replacement up to beta (`RenamingRestorationAgreement.expr_simAt`), which needs
the well-formed image context and so is not available to the context-free
`RenamingReplacement`.

`RenamingRestorationSubstitutionOnCtx` is the corresponding variant of
`RenamingRestorationSubstitution`, and `Restoration.equation_wf_onCtx` the
transport of well-formed closed equations.
-/

namespace Lean4Lean

namespace VEnv

/-- The four projection rules of `envL` at the projection `(typeName, info)`,
transported along `replaceRen ρ σ` to `envS`, in well-formed image contexts
(`ProjectionRulesRenamed` with the well-formedness of the context as an extra
premise). -/
structure ProjectionRulesRenamedOnCtx (envS : VEnv) (ρ : Name → Option VExpr) (σ : Name → Name)
    (typeName : Name) (info : VProjectionInfo) : Prop where
  projDF : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {index : Nat} {sourceMajor fieldType : VExpr} {fieldLevel : VLevel}
      {major : VExpr} {indexArgs : List VExpr} {major' : VExpr},
    OnCtx Γ (envS.IsType U) →
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
    OnCtx Γ (envS.IsType U) →
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
    OnCtx Γ (envS.IsType U) →
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
    OnCtx Γ (envS.IsType U) →
    params.length = info.nparams → info.nindices = 0 → info.numFields = 0 →
    envS.HasType U Γ (e.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.HasType U Γ (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.IsDefEq U Γ (e.replaceRen ρ σ) (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ)

theorem ProjectionRulesRenamed.onCtx {envS : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}
    {typeName : Name} {info : VProjectionInfo}
    (H : ProjectionRulesRenamed envS ρ σ typeName info) :
    ProjectionRulesRenamedOnCtx envS ρ σ typeName info where
  projDF _ := H.projDF
  projIota _ := H.projIota
  structEta _ := H.structEta
  unitLike _ := H.unitLike

/-- A restoration-free eliminator `(block, schema)` of the lowered environment,
matched in `envS` by the registered schema with the same signature, the
original families `families` and the restoration `r`, which agrees with the
renaming replacement `(ρ, σ)` (`CaseSchema.eq_with_of_signature` puts a source
schema with the same signature in this form). Its
elimination rules are transported through the agreement of restoration with
`replaceRen ρ σ` up to beta
(`InductiveSignature.RenamingRestorationAgreement.expr_simAt`), which needs beta
subject reduction in `envS`, the projection names of the generic type and
equations fixed by `σ`, and their restorations to succeed. -/
structure RestoredEliminator (envS : VEnv) (ρ : Name → Option VExpr) (σ : Name → Name)
    (block : Name) (schema : InductiveSignature.CaseSchema) (families : List Name)
    (r : InductiveSignature.Restoration) : Prop where
  /-- The lowered schema carries no restoration. -/
  restorationFree : schema.restoration = {}
  /-- The source schema, with the same signature, the original families
  `families` and the restoration `r`, is registered under the same key. -/
  registered : envS.eliminators block
    { schema with sourceFamilies := families, restoration := r }
  /-- The restoration agrees with the renaming replacement. -/
  agreement : InductiveSignature.RenamingRestorationAgreement r ρ σ
  /-- The restoration table is scoped (the head arguments are closed under the
  head parameters, so restoration preserves closedness). -/
  restorationScoped : r.Scoped
  betaSubjectReduction : ∀ U, envS.BetaSubjectReduction U
  /-- The generic type has its projection names fixed and is restorable. -/
  genericType : ∀ owner type, schema.genericType owner = some type →
    type.ProjNamesFixed σ ∧ (r.expr type).isSome
  /-- The generic equations have their projection names fixed and are restorable. -/
  genericEquations : ∀ owner rules, schema.genericEquations block owner = some rules →
    ∀ df ∈ rules, df.lhs.ProjNamesFixed σ ∧ df.rhs.ProjNamesFixed σ ∧
      df.type.ProjNamesFixed σ ∧ (r.equation df).isSome

/-- A schema with the same signature as `schema` is `schema` with its original
families and restoration replaced. -/
theorem _root_.Lean4Lean.InductiveSignature.CaseSchema.eq_with_of_signature
    {schema schemaS : InductiveSignature.CaseSchema} (h : schemaS.signature = schema.signature) :
    schemaS = { schema with
      sourceFamilies := schemaS.sourceFamilies
      restoration := schemaS.restoration } := by
  cases schemaS
  cases h
  rfl

/-- The generic type of the restored schema is the restoration of the generic
type of the restoration-free schema. -/
theorem _root_.Lean4Lean.InductiveSignature.CaseSchema.genericType_withRestoration
    {schema : InductiveSignature.CaseSchema} (h0 : schema.restoration = {})
    {owner : Fin schema.signature.families.size} {type : VExpr}
    (h : schema.genericType owner = some type) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).genericType owner =
      r.expr type := by
  simp only [InductiveSignature.CaseSchema.genericType, InductiveSignature.CaseSchema.type,
    h0, InductiveSignature.Restoration.expr_empty, Option.some.injEq] at h ⊢
  rw [← h]
  rfl

/-- The generic equations of the restored schema are the restorations of the
generic equations of the restoration-free schema. -/
theorem _root_.Lean4Lean.InductiveSignature.CaseSchema.genericEquations_withRestoration
    {schema : InductiveSignature.CaseSchema} (h0 : schema.restoration = {}) {block : Name}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (h : schema.genericEquations block owner = some rules) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).genericEquations block owner = rules.mapM r.equation := by
  have hempty : (({} : InductiveSignature.Restoration).equation) = fun e => some e := by
    funext e
    exact InductiveSignature.Restoration.equation_empty e
  simp only [InductiveSignature.CaseSchema.genericEquations,
    InductiveSignature.CaseSchema.equations, h0, hempty] at h ⊢
  have hsome : ∀ l : List VDefEq, l.mapM (fun e => some e) = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.mapM_cons, ih]
  rw [hsome] at h
  cases h
  rfl

/-- `Permission` only reads the signature. -/
theorem _root_.Lean4Lean.InductiveSignature.CaseSchema.Permission.withRestoration
    {schema : InductiveSignature.CaseSchema} {owner : Fin schema.signature.families.size}
    {U : Nat} {levels : List VLevel} {target : VLevel}
    (H : schema.Permission U owner levels target) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).Permission U owner levels target :=
  ⟨H.length, H.levels_wf, H.target_wf, H.admissible⟩

private theorem restoredEliminator_closedN {r : InductiveSignature.Restoration}
    (hr : r.Scoped) {e e' : VExpr} (he : e.Closed) (h : r.expr e = some e') : e'.Closed :=
  EnvTables.restore_go_closedN r (fun h hh a ha => (hr.2.2.1 h hh).2 a ha) e [] 0 e' he
    (by simp) h

private theorem restoredEliminator_instL {r : InductiveSignature.Restoration} {e e' : VExpr}
    (h : r.expr e = some e') (ls : List VLevel) :
    r.expr (e.instL ls) = some (e'.instL ls) := by
  rw [← InductiveSignature.Restoration.expr_instL, h]
  rfl

private theorem mapM_equation_of_isSome (r : InductiveSignature.Restoration) :
    ∀ {l : List VDefEq}, (∀ d ∈ l, (r.equation d).isSome) → ∃ l', l.mapM r.equation = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    obtain ⟨l', hl⟩ := mapM_equation_of_isSome r (l := l)
      (fun d hd => h d (List.mem_cons_of_mem _ hd))
    exact ⟨a' :: l', by simp [List.mapM_cons, ha, hl]⟩

/-- The congruence rule of a restoration-free lowered eliminator, transported to
`envS` through the registered restored schema. -/
theorem RestoredEliminator.elimDF {envS : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} {block : Name} {schema : InductiveSignature.CaseSchema}
    {families : List Name} {r : InductiveSignature.Restoration}
    (R : RestoredEliminator envS ρ σ block schema families r)
    (henv : envS.Ordered) {owner : Fin schema.signature.families.size} {type : VExpr}
    {U : Nat} {Γ : List VExpr} {levels levels' : List VLevel} {target target' : VLevel}
    {typeLevel : VLevel}
    (htype : schema.genericType owner = some type) (hclosed : type.Closed)
    (hperm : schema.Permission U owner levels target)
    (hright : ∀ level ∈ target' :: levels', level.WF U)
    (heq : List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels'))
    (hΓ : OnCtx Γ (envS.IsType U))
    (htyped : envS.HasType U Γ ((type.instL (target :: levels)).replaceRen ρ σ)
      (.sort typeLevel)) :
    envS.IsDefEq U Γ (.elim block owner.val (target :: levels))
      (.elim block owner.val (target' :: levels'))
      ((type.instL (target :: levels)).replaceRen ρ σ) := by
  obtain ⟨hfixT, hsome⟩ := R.genericType owner type htype
  obtain ⟨type', htype'⟩ := Option.isSome_iff_exists.mp hsome
  have hgen := InductiveSignature.CaseSchema.genericType_withRestoration
    R.restorationFree htype families r
  rw [htype'] at hgen
  have hdef := R.agreement.expr_simAt henv (R.betaSubjectReduction U) hΓ hfixT.instL
    (restoredEliminator_instL htype' (target :: levels)) _ htyped
  have hS := VEnv.IsDefEq.elimDF
    (schema := { schema with sourceFamilies := families, restoration := r }) (owner := owner)
    R.registered hgen (restoredEliminator_closedN R.restorationScoped hclosed htype')
    (hperm.withRestoration families r) hright heq hdef.hasType.2
  exact .defeqDF hdef.symm hS

/-- The iota rule of a restoration-free lowered eliminator, transported to
`envS` through the restored rule of the registered restored schema. -/
theorem RestoredEliminator.elimIota {envS : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} {block : Name} {schema : InductiveSignature.CaseSchema}
    {families : List Name} {r : InductiveSignature.Restoration}
    (R : RestoredEliminator envS ρ σ block schema families r)
    (henv : envS.Ordered) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} {df : VDefEq}
    {U : Nat} {Γ : List VExpr} {levels : List VLevel} {target : VLevel}
    (hgen : schema.genericEquations block owner = some rules) (hmem : df ∈ rules)
    (hclosed : InductiveSignature.CaseSchema.RuleClosed df)
    (hperm : schema.Permission U owner levels target)
    (hΓ : OnCtx Γ (envS.IsType U))
    (hleft : envS.HasType U Γ ((df.lhs.instL (target :: levels)).replaceRen ρ σ)
      ((df.type.instL (target :: levels)).replaceRen ρ σ))
    (hright : envS.HasType U Γ ((df.rhs.instL (target :: levels)).replaceRen ρ σ)
      ((df.type.instL (target :: levels)).replaceRen ρ σ)) :
    envS.IsDefEq U Γ ((df.lhs.instL (target :: levels)).replaceRen ρ σ)
      ((df.rhs.instL (target :: levels)).replaceRen ρ σ)
      ((df.type.instL (target :: levels)).replaceRen ρ σ) := by
  obtain ⟨hfixL, hfixR, hfixT, hsome⟩ := R.genericEquations owner rules hgen df hmem
  obtain ⟨df', hdf'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨rules', hrules'⟩ := mapM_equation_of_isSome r
    (fun d hd => (R.genericEquations owner rules hgen d hd).2.2.2)
  have hgen' := InductiveSignature.CaseSchema.genericEquations_withRestoration
    R.restorationFree hgen families r
  rw [hrules'] at hgen'
  have hmem' : df' ∈ rules' := by
    obtain ⟨d, hd, hdd⟩ := List.Forall₂.forall_exists_l (List.mapM_eq_some.mp hrules') df hmem
    rw [hdf'] at hdd
    cases hdd
    exact hd
  obtain ⟨hl, hr, ht⟩ := InductiveSignature.Restoration.equation_parts hdf'
  have hclosed' : InductiveSignature.CaseSchema.RuleClosed df' :=
    ⟨restoredEliminator_closedN R.restorationScoped hclosed.1 hl,
      restoredEliminator_closedN R.restorationScoped hclosed.2.1 hr,
      restoredEliminator_closedN R.restorationScoped hclosed.2.2 ht⟩
  have hβ := R.betaSubjectReduction U
  have hL := R.agreement.expr_simAt henv hβ hΓ hfixL.instL
    (restoredEliminator_instL hl (target :: levels)) _ hleft
  have hR := R.agreement.expr_simAt henv hβ hΓ hfixR.instL
    (restoredEliminator_instL hr (target :: levels)) _ hright
  obtain ⟨u, hT⟩ := hleft.isType henv hΓ
  have hTT := R.agreement.expr_simAt henv hβ hΓ hfixT.instL
    (restoredEliminator_instL ht (target :: levels)) _ hT
  have hι := VEnv.IsDefEq.elimIota
    (schema := { schema with sourceFamilies := families, restoration := r })
    (owner := owner) R.registered hgen' hmem' hclosed' (hperm.withRestoration families r)
    (.defeqDF hTT hL.hasType.2) (.defeqDF hTT hR.hasType.2)
  exact hL.trans ((VEnv.IsDefEq.defeqDF hTT.symm hι).trans hR.symm)

/-- `RenamingReplacement` with projection rules transported only in
well-formed image contexts. -/
structure RenamingReplacementOnCtx (envS envL : VEnv) (ρ : Name → Option VExpr)
    (σ : Name → Name) : Prop where
  closed : VExpr.ReplacementsClosed ρ
  ordered : envS.Ordered
  replaced : ∀ c ci t, envL.constants c = some ci → ρ c = some t →
    envS.HasType ci.uvars [] t (ci.type.replaceRen ρ σ)
  kept : ∀ c ci, envL.constants c = some ci → ρ c = none →
    ∃ ci', envS.constants (σ c) = some ci' ∧ ci'.uvars = ci.uvars ∧
      ∃ u, envS.IsDefEq ci.uvars [] ci'.type (ci.type.replaceRen ρ σ) (.sort u)
  defeqs : ∀ df, envL.defeqs df → ∃ df', envS.defeqs df' ∧ df'.uvars = df.uvars ∧
    df'.lhs = df.lhs.replaceRen ρ σ ∧ df'.rhs = df.rhs.replaceRen ρ σ ∧
    df'.type = df.type.replaceRen ρ σ
  /-- Every eliminator of `envL` is either registered in `envS` with the same
  schema, whose generic type and equations are fixed by the replacement, or is
  restoration-free and matched by a registered restored schema of `envS`
  (`RestoredEliminator`). -/
  eliminators : ∀ block schema, envL.eliminators block schema →
    (envS.eliminators block schema ∧
      (∀ owner type, schema.genericType owner = some type → type.replaceRen ρ σ = type) ∧
      (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
        df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
        df.type.replaceRen ρ σ = df.type)) ∨
    ∃ families r, RestoredEliminator envS ρ σ block schema families r
  projections : ∀ typeName info, envL.projections typeName info →
    ProjectionRulesRenamedOnCtx envS ρ σ typeName info

variable {envS envL : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}

theorem RenamingReplacement.toOnCtx (S : RenamingReplacement envS envL ρ σ) :
    RenamingReplacementOnCtx envS envL ρ σ where
  closed := S.closed
  ordered := S.ordered
  replaced := S.replaced
  kept := S.kept
  defeqs := S.defeqs
  eliminators block schema h := .inl (S.eliminators block schema h)
  projections typeName info h := (S.projections typeName info h).onCtx

/-- Renaming replacement transports definitional equality to every
well-formed image context. -/
theorem RenamingReplacementOnCtx.isDefEq (S : RenamingReplacementOnCtx envS envL ρ σ)
    {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : envL.IsDefEq U Γ e₁ e₂ A) :
    OnCtx (Γ.map (·.replaceRen ρ σ)) (envS.IsType U) →
    envS.IsDefEq U (Γ.map (·.replaceRen ρ σ)) (e₁.replaceRen ρ σ) (e₂.replaceRen ρ σ)
      (A.replaceRen ρ σ) := by
  have hρ := S.closed
  induction H with
  | bvar h => intro _; exact .bvar (h.replaceRen hρ)
  | symm _ ih => intro hΓ'; exact .symm (ih hΓ')
  | trans _ _ ih1 ih2 => intro hΓ'; exact .trans (ih1 hΓ') (ih2 hΓ')
  | sortDF h1 h2 h3 => intro _; exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' Γ₀ h1 h2 h3 h4 h5 =>
    intro _
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
      have hconst : envS.IsDefEq U (Γ₀.map (·.replaceRen ρ σ)) (.const (σ c) ls)
          (.const (σ c) ls') (ci'.type.instL ls) :=
        IsDefEq.constDF hci' h2 h3 (h4.trans hu.symm) h5
      have ht' := (ht.instL h2 (Γ := [])).weak0 S.ordered (Γ := Γ₀.map (·.replaceRen ρ σ))
      exact .defeqDF ht' hconst
  | elimDF hlookup htype hclosed hperm hright heq _ ih =>
    intro hΓ'
    have ih := ih hΓ'
    rcases S.eliminators _ _ hlookup with ⟨hS, htypes, _⟩ | ⟨families, r, R⟩
    · have hfix := htypes _ _ htype
      simp only [VExpr.replaceRen_instL, hfix, VExpr.replaceRen] at ih ⊢
      exact .elimDF hS htype hclosed hperm hright heq ih
    · simp only [VExpr.replaceRen] at ih ⊢
      exact R.elimDF S.ordered htype hclosed hperm hright heq hΓ' ih
  | elimIota hlookup hgen hmem hclosed hperm _ _ ihLeft ihRight =>
    intro hΓ'
    have ihLeft := ihLeft hΓ'
    have ihRight := ihRight hΓ'
    rcases S.eliminators _ _ hlookup with ⟨hS, _, hrules⟩ | ⟨families, r, R⟩
    · obtain ⟨hl, hr, ht⟩ := hrules _ _ hgen _ hmem
      simp only [VExpr.replaceRen_instL, hl, hr, ht] at ihLeft ihRight ⊢
      exact .elimIota hS hgen hmem hclosed hperm ihLeft ihRight
    · exact R.elimIota S.ordered hgen hmem hclosed hperm hΓ' ihLeft ihRight
  | appDF _ _ ih1 ih2 =>
    intro hΓ'
    rw [VExpr.replaceRen_inst hρ]
    exact .appDF (ih1 hΓ') (ih2 hΓ')
  | projDF hinfo hlevels huvars hparams hindices hfield _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    intro hΓ'
    exact (S.projections _ _ hinfo).projDF hΓ' hlevels huvars hparams hindices hfield hclosed
      hguard (ihField hΓ') (ihLeft hΓ') (ihRight hΓ')
  | projIota h1 _ h3 _ ih1 ih2 =>
    intro hΓ'
    exact (S.projections _ _ h1).projIota hΓ' (ih1 hΓ') h3 (ih2 hΓ')
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    intro hΓ'
    exact (S.projections _ _ h1).structEta hΓ' h2 h3 (ih1 hΓ') (ih2 hΓ')
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    intro hΓ'
    exact (S.projections _ _ h1).unitLike hΓ' h2 h3 h4 (ih1 hΓ') (ih2 hΓ')
  | lamDF _ _ ih1 ih2 =>
    intro hΓ'
    have ih1 := ih1 hΓ'
    exact .lamDF ih1 (ih2 ⟨hΓ', _, ih1.hasType.1⟩)
  | forallEDF _ _ ih1 ih2 =>
    intro hΓ'
    have ih1 := ih1 hΓ'
    exact .forallEDF ih1 (ih2 ⟨hΓ', _, ih1.hasType.1⟩)
  | defeqDF _ _ ih1 ih2 => intro hΓ'; exact .defeqDF (ih1 hΓ') (ih2 hΓ')
  | beta _ _ ih1 ih2 =>
    intro hΓ'
    have ih2 := ih2 hΓ'
    have ih1 := ih1 ⟨hΓ', ih2.isType S.ordered hΓ'⟩
    simp only [VExpr.replaceRen, VExpr.replaceRen_inst hρ]
    exact .beta ih1 ih2
  | eta _ ih =>
    intro hΓ'
    simp only [VExpr.replaceRen, VExpr.replaceRen_lift hρ]
    exact .eta (ih hΓ')
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro hΓ'; exact .proofIrrel (ih1 hΓ') (ih2 hΓ') (ih3 hΓ')
  | extra h1 h2 h3 =>
    intro _
    obtain ⟨df', hS, hu, hl, hr, ht⟩ := S.defeqs _ h1
    simp only [VExpr.replaceRen_instL, ← hl, ← hr, ← ht]
    exact .extra hS h2 (h3.trans hu.symm)

/-- Extend a context-carrying renaming replacement by one constant. -/
theorem RenamingReplacementOnCtx.addConst {env env' : VEnv} {n : Name} {ci : VConstant}
    (S : RenamingReplacementOnCtx envS env ρ σ) (h : env.addConst n ci = some env')
    (hc : RenamingReplacement.ConstClause envS ρ σ n ci) :
    RenamingReplacementOnCtx envS env' ρ σ where
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

/-- Extend a context-carrying renaming replacement by projections. -/
theorem RenamingReplacementOnCtx.addProjections {env : VEnv}
    (S : RenamingReplacementOnCtx envS env ρ σ) {entries : List VProjectionEntry}
    (hp : ∀ entry ∈ entries, ProjectionRulesRenamedOnCtx envS ρ σ entry.typeName entry.info) :
    RenamingReplacementOnCtx envS (env.addProjections entries) ρ σ where
  closed := S.closed
  ordered := S.ordered
  replaced c ci t hc ht := S.replaced c ci t (by rwa [VEnv.addProjections_constants] at hc) ht
  kept c ci hc ht := S.kept c ci (by rwa [VEnv.addProjections_constants] at hc) ht
  defeqs df hdf := S.defeqs df (by rwa [VEnv.addProjections_defeqs] at hdf)
  eliminators block schema hs :=
    S.eliminators block schema (by rwa [VEnv.addProjections_eliminators] at hs)
  projections typeName info h := by
    rcases VEnv.addProjections_iff.mp h with ⟨entry, hmem, rfl, rfl⟩ | h
    · exact hp entry hmem
    · exact S.projections typeName info h

/-- Extend a context-carrying renaming replacement by restoration-free lowered
eliminators, each matched by a registered restored schema of `envS`. -/
theorem RenamingReplacementOnCtx.addEliminators {env : VEnv}
    (S : RenamingReplacementOnCtx envS env ρ σ)
    {es : List (Name × InductiveSignature.CaseSchema)}
    (hes : ∀ e ∈ es, ∃ families r, RestoredEliminator envS ρ σ e.1 e.2 families r) :
    RenamingReplacementOnCtx envS (env.addEliminators es) ρ σ where
  closed := S.closed
  ordered := S.ordered
  replaced c ci t hc ht := S.replaced c ci t (by rwa [VEnv.addEliminators_constants] at hc) ht
  kept c ci hc ht := S.kept c ci (by rwa [VEnv.addEliminators_constants] at hc) ht
  defeqs df hdf := S.defeqs df (by rwa [VEnv.addEliminators_defeqs] at hdf)
  eliminators block schema hs := by
    rcases VEnv.addEliminators_iff.mp hs with hmem | hs
    · exact .inr (hes _ hmem)
    · exact S.eliminators block schema hs
  projections typeName info hp :=
    S.projections typeName info (by rwa [VEnv.addEliminators_projections] at hp)

/-- A restored eliminator in a well-formed source environment: beta subject
reduction, the scope of the restoration and the restorability of the generic
types follow from well-formedness. -/
theorem RestoredEliminator.of_wf {block : Name} {schema : InductiveSignature.CaseSchema}
    {families : List Name} {r : InductiveSignature.Restoration} (hS : envS.WF)
    (h0 : schema.restoration = {})
    (hreg : envS.eliminators block
      { schema with sourceFamilies := families, restoration := r })
    (A : InductiveSignature.RenamingRestorationAgreement r ρ σ)
    (htype : ∀ owner type, schema.genericType owner = some type → type.ProjNamesFixed σ)
    (heqs : ∀ owner rules, schema.genericEquations block owner = some rules →
      ∀ df ∈ rules, df.lhs.ProjNamesFixed σ ∧ df.rhs.ProjNamesFixed σ ∧
        df.type.ProjNamesFixed σ ∧ (r.equation df).isSome) :
    RestoredEliminator envS ρ σ block schema families r where
  restorationFree := h0
  registered := hreg
  agreement := A
  restorationScoped := VEnv.WF.eliminator_restoration_scoped hS hreg
  betaSubjectReduction _ := hS.betaSubjectReduction
  genericType owner type h := by
    refine ⟨htype owner type h, ?_⟩
    obtain ⟨type', h', -⟩ := EnvTables.VEnv.WF.eliminator_genericType_closed hS hreg owner
    rw [InductiveSignature.CaseSchema.genericType_withRestoration h0 h families r] at h'
    rw [h']
    rfl
  genericEquations := heqs

end VEnv

namespace InductiveSignature

open VEnv

/-- `RenamingRestorationSubstitution` with projection rules transported only
in well-formed image contexts. -/
structure RenamingRestorationSubstitutionOnCtx (envS envL : VEnv) (r : Restoration)
    (ρ : Name → Option VExpr) (σ : Name → Name) : Prop
    extends VEnv.RenamingReplacementOnCtx envS envL ρ σ where
  /-- Every replacement is the parameter abstraction of a restoration head. -/
  shape : ∀ c t, ρ c = some t → ∃ h doms,
    r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
    t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments)
  /-- Every restoration head is replaced. -/
  headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → ρ c ≠ none
  /-- Away from the heads, the renaming is the recursor renaming. -/
  renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none → σ c = r.recursorName c

/-- The agreement clauses of a context-carrying renaming restoration substitution. -/
theorem RenamingRestorationSubstitutionOnCtx.agreement {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ) :
    RenamingRestorationAgreement r ρ σ :=
  ⟨S.shape, S.headsReplaced, S.renamed⟩

/-- Restoration agrees with the renaming replacement up to beta, at every
type of the replaced term, for terms whose projection names are fixed
(`RenamingRestorationAgreement.go_simAt`, which uses only the shape of the
replacement). -/
theorem RenamingRestorationSubstitutionOnCtx.go_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name} {U : Nat}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ)
    (hβ : envS.BetaSubjectReduction U) :
    ∀ (e : VExpr) {Γ : List VExpr} {as as' : List VExpr} {out : VExpr},
      e.ProjNamesFixed σ →
      OnCtx Γ (envS.IsType U) → List.Forall₂ (envS.SimAt U Γ) as as' →
      Restoration.expr.go r e as' = some out →
      envS.SimAt U Γ (VExpr.mkApps (e.replaceRen ρ σ) as) out :=
  S.agreement.go_simAt S.ordered hβ

theorem RenamingRestorationSubstitutionOnCtx.expr_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name} {U : Nat} {Γ : List VExpr} {e e' : VExpr}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ)
    (hβ : envS.BetaSubjectReduction U) (hΓ : OnCtx Γ (envS.IsType U))
    (hfix : e.ProjNamesFixed σ) (h : r.expr e = some e') :
    envS.SimAt U Γ (e.replaceRen ρ σ) e' :=
  S.go_simAt hβ e (as := []) hfix hΓ .nil h

/-- Restoration of a closed typing judgment of the lowered environment. -/
theorem Restoration.expr_hasType_onCtx {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name} {U : Nat} {e A e' A' : VExpr}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ)
    (hβ : envS.BetaSubjectReduction U)
    (H : envL.HasType U [] e A) (he : r.expr e = some e') (hA : r.expr A = some A')
    (hfix : e.ProjNamesFixed σ) (hfixA : A.ProjNamesFixed σ) :
    envS.HasType U [] e' A' := by
  have henv := S.ordered
  have Hσ : envS.HasType U [] (e.replaceRen ρ σ) (A.replaceRen ρ σ) :=
    S.isDefEq H trivial
  have h1 := S.expr_simAt hβ (Γ := []) trivial hfix he _ Hσ
  obtain ⟨u, hAσ⟩ := VEnv.IsDefEq.isType henv (Γ := []) trivial Hσ
  have h3 := S.expr_simAt hβ (Γ := []) trivial hfixA hA _ hAσ
  exact .defeqDF h3 (h1.symm.trans (Hσ.trans h1))

/-- Restoration of a well-formed closed equation of the lowered environment. -/
theorem Restoration.equation_wf_onCtx {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ)
    {df df' : VDefEq} (hβ : envS.BetaSubjectReduction df.uvars)
    (hwf : df.WF envL) (hfixL : df.lhs.ProjNamesFixed σ) (hfixR : df.rhs.ProjNamesFixed σ)
    (hfixT : df.type.ProjNamesFixed σ) (h : r.equation df = some df') :
    df'.WF envS := by
  simp only [Restoration.equation, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨l, hl, rr, hr, t, ht, rfl⟩ := h
  exact ⟨Restoration.expr_hasType_onCtx S hβ hwf.1 hl ht hfixL hfixT,
    Restoration.expr_hasType_onCtx S hβ hwf.2 hr ht hfixR hfixT⟩

end InductiveSignature
end Lean4Lean
