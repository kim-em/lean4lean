import Lean4Lean.Theory.Inductive.RestorationRenaming

/-! Context-carrying renaming replacement.

`VEnv.RenamingReplacement` transports derivations of a lowered environment in
every context, so its projection clause `ProjectionTransport` must transport
the projection rules in arbitrary, possibly ill-formed, image contexts. The
variant `RenamingReplacementOnCtx` asks for the projection rules only in
well-formed image contexts (`ProjectionTransportOnCtx`); its transport
`RenamingReplacementOnCtx.isDefEq` carries the well-formedness of the image
context through the binders of the derivation. Every derivation starting in a
well-formed image context (in particular the empty context, where the
generated equations are stated) is transported.

`RenamingRestorationSubstitutionOnCtx` is the corresponding variant of
`RenamingRestorationSubstitution`, and `Restoration.equation_wf_onCtx` the
transport of well-formed closed equations.
-/

namespace Lean4Lean

namespace VEnv

/-- The four projection rules of `envL` at the projection `(typeName, info)`,
transported along `replaceRen ρ σ` to `envS`, in well-formed image contexts
(`ProjectionTransport` with the well-formedness of the context as an extra
premise). -/
structure ProjectionTransportOnCtx (envS : VEnv) (ρ : Name → Option VExpr) (σ : Name → Name)
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

theorem ProjectionTransport.onCtx {envS : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}
    {typeName : Name} {info : VProjectionInfo}
    (H : ProjectionTransport envS ρ σ typeName info) :
    ProjectionTransportOnCtx envS ρ σ typeName info where
  projDF _ := H.projDF
  projIota _ := H.projIota
  structEta _ := H.structEta
  unitLike _ := H.unitLike

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
  eliminators : ∀ block schema, envL.eliminators block schema →
    envS.eliminators block schema ∧
    (∀ owner type, schema.genericType owner = some type → type.replaceRen ρ σ = type) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
      df.type.replaceRen ρ σ = df.type)
  projections : ∀ typeName info, envL.projections typeName info →
    ProjectionTransportOnCtx envS ρ σ typeName info

variable {envS envL : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}

theorem RenamingReplacement.toOnCtx (S : RenamingReplacement envS envL ρ σ) :
    RenamingReplacementOnCtx envS envL ρ σ where
  closed := S.closed
  ordered := S.ordered
  replaced := S.replaced
  kept := S.kept
  defeqs := S.defeqs
  eliminators := S.eliminators
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
    obtain ⟨hS, htypes, _⟩ := S.eliminators _ _ hlookup
    have hfix := htypes _ _ htype
    have ih := ih hΓ'
    simp only [VExpr.replaceRen_instL, hfix, VExpr.replaceRen] at ih ⊢
    exact .elimDF hS htype hclosed hperm hright heq ih
  | elimIota hlookup hgen hmem hclosed hperm _ _ ihLeft ihRight =>
    intro hΓ'
    obtain ⟨hS, _, hrules⟩ := S.eliminators _ _ hlookup
    obtain ⟨hl, hr, ht⟩ := hrules _ _ hgen _ hmem
    have ihLeft := ihLeft hΓ'
    have ihRight := ihRight hΓ'
    simp only [VExpr.replaceRen_instL, hl, hr, ht] at ihLeft ihRight ⊢
    exact .elimIota hS hgen hmem hclosed hperm ihLeft ihRight
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

/-- The transport of a well-formed context of `envL` is well formed. -/
theorem RenamingReplacementOnCtx.onCtx (S : RenamingReplacementOnCtx envS envL ρ σ)
    {U : Nat} : ∀ {Γ : List VExpr}, OnCtx Γ (envL.IsType U) →
      OnCtx (Γ.map (·.replaceRen ρ σ)) (envS.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨hΓ, _, hA⟩ => ⟨S.onCtx hΓ, _, S.isDefEq hA (S.onCtx hΓ)⟩

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
    (hp : ∀ entry ∈ entries, ProjectionTransportOnCtx envS ρ σ entry.typeName entry.info) :
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

private theorem instantiateParams_eq_instOuter_onCtx (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Restoration agrees with the renaming replacement up to beta, at every
type of the replaced term, for terms whose projection names are fixed
(`RenamingRestorationSubstitution.go_simAt`, which uses only the shape of the
replacement). -/
theorem RenamingRestorationSubstitutionOnCtx.go_simAt {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {σ : Name → Name} {U : Nat}
    (S : RenamingRestorationSubstitutionOnCtx envS envL r ρ σ)
    (hβ : envS.BetaSubjectReduction U) :
    ∀ (e : VExpr) {Γ : List VExpr} {as as' : List VExpr} {out : VExpr},
      e.ProjNamesFixed σ →
      OnCtx Γ (envS.IsType U) → List.Forall₂ (envS.SimAt U Γ) as as' →
      Restoration.expr.go r e as' = some out →
      envS.SimAt U Γ (VExpr.mkApps (e.replaceRen ρ σ) as) out := by
  have henv := S.ordered
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
            Function.comp_def, instantiateParams_eq_instOuter_onCtx]
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
