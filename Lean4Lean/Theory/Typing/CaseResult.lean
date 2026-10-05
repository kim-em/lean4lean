import Lean4Lean.Theory.Typing.CaseMajorDomain

/-! Exact motive applications produced by typed abstract case calls. -/

namespace Lean4Lean.InductiveSignature

private theorem restoration_forall_prefix {r : Restoration} {domains : List VExpr}
    (h : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', domains'.length = domains.length ∧
      r.expr body = some body' ∧ output = VExpr.wrapForalls domains' body' := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, rfl, h, rfl⟩
  | cons d ds ih =>
    change (do let d' ← r.expr d; let b' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' b')) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, heq⟩ := h
    obtain ⟨ds', body', hlen, hb', rfl⟩ := ih hb
    exact ⟨d' :: ds', body', by simp [hlen], hb', Option.some.inj heq.symm⟩

private theorem restoration_vars (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  unfold vars
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih => simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using ih

namespace CaseSchema

theorem genericType_result {type : VExpr} {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (H : schema.genericType owner = some type) :
    ∃ domains, domains.length = VEnv.caseMajorArity schema owner + 1 ∧
      type = VExpr.wrapForalls domains (VExpr.mkApps
        (.bvar (schema.signature.families[owner].indices.length + 1 +
          (schema.view owner).constructors.size))
        (vars schema.signature.families[owner].indices.length 1 ++ [.bvar 0])) := by
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
  obtain ⟨domains, body, hlen, hbody, htype⟩ := restoration_forall_prefix H
  refine ⟨domains, ?_, ?_⟩
  · rw [hlen]
    simp [rawDomains, g, Instance.params, Instance.motives, Instance.minors,
      indices, insertBinders, family, viewOwner, view, VEnv.caseMajorArity]
    omega
  · have hbodyEq : body = VExpr.mkApps motive (vars indices.length 1 ++ [.bvar 0]) := by
      change Restoration.expr.go schema.restoration (VExpr.mkApps motive _) [] = _ at hbody
      rw [restoration_mkApps] at hbody
      simp only [List.mapM_append, restoration_vars, bind, Option.bind_some,
        List.mapM_cons, List.mapM_nil] at hbody
      simpa [motive, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using hbody.symm
    rw [htype, hbodyEq]
    simp [motive, indices, insertBinders, family, view, viewOwner]

end CaseSchema

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

private theorem caseResult_head_typed {type : VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (VExpr.mkApps fn args) type) :
    ∃ headType, env.HasType U Γ fn headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, H⟩
  | cons a args ih =>
    obtain ⟨_, h⟩ := ih H
    obtain ⟨_, _, hf, _⟩ := h.app_inv henv hΓ
    exact ⟨_, hf⟩

private theorem vars_one_append (count : Nat) :
    vars count 1 ++ [.bvar 0] = vars (count + 1) 0 := by
  have h : vars count 1 ++ vars 1 0 = vars (count + 1) 0 := by
    rw [Nat.add_comm count 1]
    simp [vars, List.range_add, List.map_append, List.map_map]
  exact h

private theorem vars_eq_bvarRange (count below : Nat) :
    vars count below = bvarRange count (count + below) := by
  apply List.ext_getElem
  · simp [vars, bvarRange]
  · intro i hi hi'
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range]
    rw [bvarRange_getElem count (count + below) i (by simpa [vars] using hi)]
    simp only [List.length_range]
    have : i < count := by simpa [vars] using hi
    congr 1
    omega

/-- A fully applied case call returns the supplied motive applied to its
actual indices and major. Its result type is determined by generation even
if the initial typing witness used conversion. -/
theorem HasType.caseResult_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {packed : List VLevel} {args : List VExpr}
    (hlookup : env.eliminators block schema)
    (hlen : args.length = caseMajorArity schema owner + 1)
    (H : VExpr.WF env U Γ (VExpr.mkApps (.elim block owner.val packed) args)) :
    env.HasType U Γ (VExpr.mkApps (.elim block owner.val packed) args)
      (VExpr.mkApps
        (args[schema.signature.params.length]'(by simp only [caseMajorArity] at hlen; omega))
        (args.drop (schema.signature.params.length + 1 + (schema.view owner).constructors.size))) := by
  obtain ⟨_, ht⟩ := H
  obtain ⟨_, hhead⟩ := caseResult_head_typed henv hΓ ht
  obtain ⟨schema', owner', type, target, levels, typeLevel, hslot, hpacked,
    hlookup', htype, hclosed, hpermission, hsortWF, hsort⟩ := hhead.elim_inv henv.ordered hΓ
  cases henv.eliminators_unique hlookup hlookup'
  cases Fin.ext hslot
  cases hpacked
  have hcanonical : env.HasType U Γ (.elim block owner.val (target :: levels))
      (type.instL (target :: levels)) :=
    .elimDF hlookup htype hclosed hpermission hpermission.packedWF
      (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl) hsort
  obtain ⟨domains, hdomains, hshape⟩ := genericType_result htype
  rw [hshape, instL_wrapForalls] at hcanonical
  have hresult := (HasType.mkApps_wrapForalls henv hΓ hcanonical ⟨_, ht⟩
    (by simp only [List.length_map]; omega)).2
  simp only [instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil] at hresult
  have hvars : (vars schema.signature.families[owner].indices.length 1).map
      (VExpr.instL (target :: levels)) = vars schema.signature.families[owner].indices.length 1 := by
    simp [vars, List.map_map, VExpr.instL]
  rw [hvars, vars_one_append, instOuter_mkApps,
    instOuter_bvar args (by simp only [caseMajorArity] at hlen; omega),
    vars_eq_bvarRange, instOuter_bvarRange _ _ _ (by omega) (by simp only [caseMajorArity] at hlen; omega)] at hresult
  have hposition : args.length - 1 -
      (schema.signature.families[owner].indices.length + 1 + (schema.view owner).constructors.size) =
      schema.signature.params.length := by simp only [caseMajorArity] at hlen; omega
  have hdrop : args.length - (schema.signature.families[owner].indices.length + 1 + 0) =
      schema.signature.params.length + 1 + (schema.view owner).constructors.size := by
    simp only [caseMajorArity] at hlen
    omega
  have hget : args[args.length - 1 -
      (schema.signature.families[owner].indices.length + 1 + (schema.view owner).constructors.size)] =
      args[schema.signature.params.length] := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hposition]
  have htake : (args.drop (schema.signature.params.length + 1 +
      (schema.view owner).constructors.size)).length ≤
      schema.signature.families[owner].indices.length + 1 := by
    rw [List.length_drop]
    change args.length = schema.signature.params.length + 1 +
      (schema.view owner).constructors.size + schema.signature.families[owner].indices.length + 1 at hlen
    omega
  rw [hget, hdrop, List.take_of_length_le htake] at hresult
  exact hresult

/-- The case call's explicit argument groups identify the motive and its
arguments without depending on the original typing witness. -/
theorem HasType.caseResult_motive (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {packed : List VLevel} {params minors indices : List VExpr} {motive major : VExpr}
    (hlookup : env.eliminators block schema)
    (hp : params.length = schema.signature.params.length)
    (hm : minors.length = (schema.view owner).constructors.size)
    (hi : indices.length = schema.signature.families[owner].indices.length)
    (H : VExpr.WF env U Γ (VExpr.mkApps (.elim block owner.val packed)
      (params ++ [motive] ++ minors ++ indices ++ [major]))) :
    env.HasType U Γ (VExpr.mkApps (.elim block owner.val packed)
      (params ++ [motive] ++ minors ++ indices ++ [major]))
      (VExpr.mkApps motive (indices ++ [major])) := by
  have h := HasType.caseResult_type henv hΓ hlookup
    (args := params ++ [motive] ++ minors ++ indices ++ [major])
    (by simp only [List.length_append, List.length_singleton, caseMajorArity, hp, hm, hi]) H
  have hget : (params ++ [motive] ++ minors ++ indices ++ [major])[schema.signature.params.length]'(by simp only [List.length_append, List.length_singleton]; omega) = motive := by
    simp only [← hp, List.append_assoc, List.getElem_append_right (Nat.le_refl _),
      Nat.sub_self, List.cons_append, List.getElem_cons_zero]
  have hdrop : (params ++ [motive] ++ minors ++ indices ++ [major]).drop
      (schema.signature.params.length + 1 + (schema.view owner).constructors.size) =
      indices ++ [major] := by
    rw [← hp, ← hm]
    have hlen : (params ++ [motive] ++ minors).length =
        params.length + 1 + minors.length := by simp only [List.length_append, List.length_singleton]
    rw [← hlen, List.append_assoc (params ++ [motive] ++ minors), List.drop_left]
  simpa only [hget, hdrop] using h

/-- A typed lambda telescope has a type using its actual binder annotations. -/
theorem _root_.Lean4Lean.VExpr.WF.wrapLams_type (henv : env.WF) :
    ∀ {domains : List VExpr} {Γ : List VExpr} {body : VExpr},
      OnCtx Γ (env.IsType U) → VExpr.WF env U Γ (wrapLams domains body) →
      ∃ resultType, env.HasType U Γ (wrapLams domains body) (wrapForalls domains resultType) := by
  intro domains
  induction domains with
  | nil => intro Γ body _ h; exact h
  | cons domain domains ih =>
    intro Γ body hΓ h
    obtain ⟨⟨_, hd⟩, hb⟩ := h.lam_inv henv.ordered hΓ
    have hΓ' : OnCtx (domain :: Γ) (env.IsType U) := ⟨hΓ, _, hd⟩
    obtain ⟨resultType, ht⟩ := ih hΓ' hb
    exact ⟨resultType, .lam hd ht⟩

/-- Full beta reduction of a lambda telescope needs only typing of the
actual application, not a separately supplied type annotation. -/
theorem _root_.Lean4Lean.VExpr.WF.beta_wrapLams (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {domains args : List VExpr} {body : VExpr}
    (hlen : args.length = domains.length)
    (H : VExpr.WF env U Γ (mkApps (wrapLams domains body) args)) :
    env.IsDefEqU U Γ (mkApps (wrapLams domains body) args) (body.instOuter args) := by
  obtain ⟨_, ht⟩ := H
  obtain ⟨_, hf⟩ := caseResult_head_typed henv hΓ ht
  obtain ⟨resultType, hf⟩ := VExpr.WF.wrapLams_type henv hΓ ⟨_, hf⟩
  have hargs := (HasType.mkApps_wrapForalls henv hΓ hf ⟨_, ht⟩ hlen).1
  exact ⟨_, IsDefEq.mkApps_wrapLams henv hΓ hf hlen hargs⟩

end Lean4Lean.VEnv
