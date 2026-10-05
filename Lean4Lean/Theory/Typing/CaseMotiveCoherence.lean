import Lean4Lean.Theory.Typing.CaseMotive

/-! Recover the target universe from the motive supplied to a generated case
application. Only motive binders actually used by the application matter. -/

set_option maxHeartbeats 1000000

namespace Lean4Lean.InductiveSignature

private theorem restoration_forall_trace {r : Restoration} {domains : List VExpr}
    (h : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧
      output = VExpr.wrapForalls domains' body' := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, .nil, rfl⟩
  | cons d ds ih =>
    change (do let d' ← r.expr d; let b' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' b')) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, heq⟩ := h
    obtain ⟨ds', body', hds, rfl⟩ := ih hb
    exact ⟨d' :: ds', body', .cons hd hds, Option.some.inj heq.symm⟩

/-- The motive domain of the restored generic telescope ends in its target
universe parameter. -/
theorem CaseSchema.genericType_motive {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {type : VExpr}
    (H : schema.genericType owner = some type) :
    ∃ (domains motiveDomains : List VExpr) (body : VExpr)
      (hp : schema.signature.params.length < domains.length),
      domains.length = VEnv.caseMajorArity schema owner + 1 ∧
      type = VExpr.wrapForalls domains body ∧
      domains[schema.signature.params.length] =
        VExpr.wrapForalls motiveDomains (.sort (.param 0)) := by
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let family := (schema.view owner).families[schema.viewOwner owner]
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let indices := insertBinders (family.indices.map (·.instL g.levels)) extra
  let major := g.familyApp (schema.viewOwner owner)
    (vars (schema.view owner).params.length (extra + indices.length)) (vars indices.length 0)
  let motive := VExpr.bvar
    (indices.length + 1 + (schema.view owner).constructors.size +
      ((schema.view owner).families.size - 1 - (schema.viewOwner owner).val))
  let rawDomains := g.params ++ g.motives ++ g.minors ++ indices ++ [major]
  change schema.restoration.expr (VExpr.wrapForalls rawDomains
    (VExpr.mkApps motive (vars indices.length 1 ++ [.bvar 0]))) = some type at H
  obtain ⟨domains, body, hds, hshape⟩ := restoration_forall_trace H
  have hlen : domains.length = VEnv.caseMajorArity schema owner + 1 := by
    rw [← Lean4Lean.List.Forall₂.length_eq hds]
    simp [rawDomains, g, Instance.params, Instance.motives, Instance.minors,
      indices, insertBinders, family, CaseSchema.viewOwner, CaseSchema.view,
      VEnv.caseMajorArity]
    omega
  have hp : schema.signature.params.length < domains.length := by
    rw [hlen]
    simp only [VEnv.caseMajorArity]
    omega
  have hp' : schema.signature.params.length < rawDomains.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hds]
    exact hp
  have hmotive := VEnv.case_forall₂_get hds hp' hp
  have hsource : rawDomains[schema.signature.params.length] =
      g.motive schema.signature.families[owner] 0 := by
    simp [rawDomains, g, Instance.params, Instance.motives, CaseSchema.view]
  rw [hsource] at hmotive
  obtain ⟨motiveDomains, hmotive⟩ := Restoration.forall_sort_shape hmotive
  exact ⟨domains, motiveDomains, body, hp, hlen, hshape, hmotive⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
variable {env : VEnv} {U : Nat}
open VExpr InductiveSignature InductiveSignature.CaseSchema

private theorem subst_forall_sort (domains : List VExpr) (level : VLevel)
    (σ : VExpr.Subst) :
    ∃ domains', (VExpr.wrapForalls domains (.sort level)).subst σ =
      VExpr.wrapForalls domains' (.sort level) := by
  induction domains generalizing σ with
  | nil => exact ⟨[], rfl⟩
  | cons d ds ih =>
    obtain ⟨ds', hds⟩ := ih σ.lift
    exact ⟨d.subst σ :: ds', congrArg (VExpr.forallE (d.subst σ)) hds⟩

/-- Equal telescope types ending in sorts have the same final universe,
even when their domain lists have not been identified in advance. -/
theorem IsDefEqU.wrapForalls_sort_level (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (wrapForalls ds₁ (.sort u)) (wrapForalls ds₂ (.sort v))) :
    u ≈ v := by
  induction ds₁ generalizing Γ ds₂ with
  | nil =>
    cases ds₂ with
    | nil => exact H.sort_inv henv hΓ
    | cons d ds => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H)
  | cons d ds ih =>
    cases ds₂ with
    | nil => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H.symm)
    | cons d' ds' =>
      obtain ⟨⟨_, hd⟩, _, hb⟩ := H.forallE_inv henv hΓ
      have hctx : OnCtx (d :: Γ) (env.IsType U) := ⟨hΓ, _, hd.hasType.1⟩
      exact ih hctx ⟨_, hb⟩

private theorem motive_head_typed {type : VExpr} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (mkApps fn args) type) :
    ∃ headType, env.HasType U Γ fn headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, H⟩
  | cons a args ih =>
    obtain ⟨_, h⟩ := ih H
    obtain ⟨_, _, hf, _⟩ := h.app_inv henv hΓ
    exact ⟨_, hf⟩

/-- A saturated case occurrence gives its supplied motive a telescope type
ending in the occurrence's target universe. -/
theorem HasType.caseMotive_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {args : List VExpr} {target : VLevel} {levels : List VLevel}
    (hlookup : env.eliminators block schema)
    (hlen : args.length = caseMajorArity schema owner + 1)
    (hp : schema.signature.params.length < args.length)
    (H : VExpr.WF env U Γ (mkApps (.elim block owner.val (target :: levels)) args)) :
    ∃ motiveDomains, env.HasType U Γ args[schema.signature.params.length]
      (wrapForalls motiveDomains (.sort target)) := by
  obtain ⟨_, ht⟩ := H
  obtain ⟨_, hhead⟩ := motive_head_typed henv hΓ ht
  obtain ⟨schema', owner', type, target', levels', typeLevel, hslot, hpacked,
    hlookup', htype, hclosed, hpermission, hsortWF, hsort⟩ :=
    hhead.elim_inv henv.ordered hΓ
  cases henv.eliminators_unique hlookup hlookup'
  have howner : owner = owner' := Fin.ext hslot
  cases howner
  cases List.cons.inj hpacked |>.1
  cases List.cons.inj hpacked |>.2
  have hcanonical : env.HasType U Γ (.elim block owner.val (target :: levels))
      (type.instL (target :: levels)) :=
    .elimDF hlookup htype hclosed hpermission hpermission.packedWF
      (by
        suffices ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls from this _
        intro ls
        induction ls with
        | nil => exact .nil
        | cons l ls ih => exact .cons rfl ih) hsort
  obtain ⟨domains, motiveDomains, body, hp', hdomains, hshape, hmotive⟩ :=
    CaseSchema.genericType_motive htype
  rw [hshape, instL_wrapForalls] at hcanonical
  have hargs := (HasType.mkApps_wrapForalls henv hΓ hcanonical ⟨_, ht⟩
    (by simp only [List.length_map]; omega)).1
  have hm := hargs schema.signature.params.length hp (by simpa using hp')
  simp only [List.getElem_map, hmotive, instL_wrapForalls] at hm
  change env.HasType U Γ args[schema.signature.params.length]
    ((wrapForalls (motiveDomains.map (VExpr.instL (target :: levels))) (.sort target)).instOuter
      (args.take schema.signature.params.length)) at hm
  rw [instOuter_eq_subst] at hm
  obtain ⟨ds, hd⟩ := subst_forall_sort
    (motiveDomains.map (VExpr.instL (target :: levels))) target
    (Subst.ofList (args.take schema.signature.params.length))
  rw [hd] at hm
  exact ⟨ds, hm⟩

/-- Equality of the supplied motives forces equality of the target universes
of two saturated occurrences of the same registered case schema. -/
theorem caseMotive_target_coherence (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {args₁ args₂ : List VExpr} {target₁ target₂ : VLevel}
    {levels₁ levels₂ : List VLevel}
    (hlookup : env.eliminators block schema)
    (hlen₁ : args₁.length = caseMajorArity schema owner + 1)
    (hlen₂ : args₂.length = caseMajorArity schema owner + 1)
    (hp₁ : schema.signature.params.length < args₁.length)
    (hp₂ : schema.signature.params.length < args₂.length)
    (H₁ : VExpr.WF env U Γ (mkApps (.elim block owner.val (target₁ :: levels₁)) args₁))
    (H₂ : VExpr.WF env U Γ (mkApps (.elim block owner.val (target₂ :: levels₂)) args₂))
    (hm : env.IsDefEqU U Γ args₁[schema.signature.params.length]
      args₂[schema.signature.params.length]) : target₁ ≈ target₂ := by
  obtain ⟨ds₁, h₁⟩ := HasType.caseMotive_type henv hΓ hlookup hlen₁ hp₁ H₁
  obtain ⟨ds₂, h₂⟩ := HasType.caseMotive_type henv hΓ hlookup hlen₂ hp₂ H₂
  exact ((hm.of_l henv hΓ h₁).hasType.2.uniqU henv hΓ h₂).wrapForalls_sort_level henv hΓ

end Lean4Lean.VEnv
