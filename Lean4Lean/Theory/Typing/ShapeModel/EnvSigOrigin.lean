import Lean4Lean.Theory.Typing.ShapeModel.EnvSigFacts

/-!
# Rule correspondence for the semantic signature of a well-formed environment

Every rule of `envSig env` comes from a stored equation (a definition, the quotient equation, a
native iota equation) or from a generic equation of a registered eliminator schema, and every
such equation has its rule, decomposed exactly as stated by `RuleSyntax` (`RuleOrigin`,
`EnvRule.origin`, `defeq_rule`, `generic_rule`). The field index table is characterized by
`fieldIndexOf_some` / `fieldIndexOf_none` (literal occurrence first, else leftover parameter),
and a leftover parameter comes with the registered structure data of its constructor
(`leftover_struct`).
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

/-! ## The field index table -/

theorem fieldIndexOf_length : (fieldIndexOf pre npre nf lo).length = nf := by
  simp [fieldIndexOf]

/-- A field index is a first literal occurrence of the field variable among the arguments
before the major, or, if the field variable does not occur literally, the leftover-parameter
position `npre + i` (`i < lo`). -/
theorem fieldIndexOf_some (h : i < nf) (hj : (fieldIndexOf pre npre nf lo)[i]? = some (some j)) :
    (∃ hj : j < pre.length, pre[j] = .bvar (nf - 1 - i) ∧
        ∀ j' (hj' : j' < j), pre[j']'(Nat.lt_trans hj' hj) ≠ .bvar (nf - 1 - i)) ∨
      (VExpr.bvar (nf - 1 - i) ∉ pre ∧ i < lo ∧ j = npre + i ∧ npre + i < pre.length) := by
  simp only [fieldIndexOf, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.some.injEq] at hj
  split at hj
  · rename_i j' hf
    cases hj
    obtain ⟨hlt, hp, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    exact .inl ⟨hlt, of_decide_eq_true hp, fun j' hj' he => hmin j' hj' (decide_eq_true he)⟩
  · rename_i hf
    split at hj
    · rename_i hc
      cases hj
      refine .inr ⟨fun hm => ?_, hc.1, rfl, hc.2⟩
      have := List.findIdx?_eq_none_iff.mp hf _ hm
      simp at this
    · cases hj

theorem fieldIndexOf_none (h : i < nf) (hj : (fieldIndexOf pre npre nf lo)[i]? = some none) :
    VExpr.bvar (nf - 1 - i) ∉ pre ∧ ¬(i < lo ∧ npre + i < pre.length) := by
  simp only [fieldIndexOf, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.some.injEq] at hj
  split at hj
  · cases hj
  · rename_i hf
    split at hj
    · cases hj
    · rename_i hc
      refine ⟨fun hm => ?_, hc⟩
      have := List.findIdx?_eq_none_iff.mp hf _ hm
      simp at this

/-- A leftover parameter exists only for the constructor of a registered structure, whose
installed type is the structure's constructor telescope (`StructFacts.ctorType`). -/
theorem leftover_struct (H : env.WF) (h : 0 < structNp env c - p) :
    ∃ s info, env.projections s info ∧ info.ctorName = c ∧ structNp env c = info.nparams ∧
      env.constants c = some ⟨info.uvars, info.ctorType⟩ ∧
      ∃ (Ds idx : List VExpr), Ds.length = info.nparams + info.numFields ∧
        idx.length = info.nindices ∧
        info.ctorType = Ds.foldr .forallE (VExpr.mkApps (.const s (VLevel.params info.uvars))
          ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
            idx)) := by
  rcases structNp_eq H c with h0 | ⟨s, info, hproj, rfl, hnp⟩
  · rw [h0] at h; simp at h
  · exact ⟨s, info, hproj, rfl, hnp, sig_ctorConst H hproj, sig_ctorType H hproj⟩

/-! ## Rule syntax -/

/-- The rule `r` is the decomposition of the equation `df`, whose left body applies `hd`:
`df.lhs = fun Ds => hd (vars npre nf ++ idx) (c lv (ps ++ vars nf 0))`, `df.rhs = fun Ds => R`,
with the rule's binders, arguments, major (fields = the de Bruijn indices of `vars nf 0`),
field index table and right side read off this presentation; `c` is a constructor of the
signature's constructor set (table entry or generic major) with the installed type `k`. -/
def RuleSyntax (env : VEnv) (r : Rule) (df : VDefEq) (hd : VExpr) : Prop :=
  ∃ (Ds idx ps : List VExpr) (npre nf : Nat) (c : Name) (lv : List VLevel) (R : VExpr),
    df.lhs = VExpr.wrapLams Ds (VExpr.mkApps hd
      (vars npre nf ++ idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])) ∧
    df.rhs = VExpr.wrapLams Ds R ∧ Ds.length = npre + nf ∧
    r.nbind = Ds.length ∧ r.vars = (vars npre nf ++ idx).map argVar ∧
    r.major = some ⟨c, lv, (List.range nf).reverse⟩ ∧
    r.fieldIndex = fieldIndexOf (vars npre nf ++ idx) npre nf (structNp env c - ps.length) ∧
    r.rhs = R ∧ (ctorOf env c ≠ none ∨ SchemaMajor env c) ∧ ∃ k, CtorShape env c k

/-- Where a rule of the signature comes from. -/
def RuleOrigin (env : VEnv) (r : Rule) : Prop :=
  (∃ v : VDefVal, env.defeqs v.toDefEq ∧ r = defRule v) ∨
  (∃ df n, env.defeqs df ∧ VDefEq.head df = .const n (VLevel.params df.uvars) ∧
    r.head = .const n ∧ r.uvars = df.uvars ∧ RuleSyntax env r df (.const n (VLevel.params df.uvars))) ∨
  (∃ (key : Name) (schema : CaseSchema), env.eliminators key schema ∧
    ∃ (owner : Fin schema.signature.families.size) (rules : List VDefEq) (df : VDefEq),
      schema.genericEquations key owner = some rules ∧ df ∈ rules ∧
      r.head = .elim key owner.val ∧ r.uvars = schema.genericUvars ∧
      RuleSyntax env r df (.elim key owner.val (.param 0 :: schema.genericLevels)))

theorem ruleSyntax_of_shape {hd : VExpr} (hhd : hd.getAppFnArgs = (hd, []))
    (hlam : ∀ d b, hd ≠ .lam d b) {Ds idx ps : List VExpr} {npre nf : Nat} {c : Name}
    {lv : List VLevel} {R : VExpr}
    (hl : df.lhs = VExpr.wrapLams Ds (VExpr.mkApps hd
      (vars npre nf ++ idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])))
    (hr : df.rhs = VExpr.wrapLams Ds R) (hlen : Ds.length = npre + nf)
    (hc : ctorOf env c ≠ none ∨ SchemaMajor env c) (hk : ∃ k, CtorShape env c k) :
    RuleSyntax env (majorRule (structNp env) h u df nf) df hd := by
  have heq := majorRule_eq (np := structNp env) (h := h) (u := u) hhd hlam hl hr
  rw [heq]
  refine ⟨Ds, idx, ps, npre, nf, c, lv, R, hl, hr, hlen, rfl, rfl, rfl, ?_, rfl, hc, hk⟩
  simp only [hlen, Nat.add_sub_cancel]

theorem native_ruleSyntax (H : env.WF) {data : NativeRecursorData}
    (hd : (envTables env).natives data.name = some data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df) (hdf : env.defeqs df) :
    RuleSyntax env (majorRule (structNp env) (.const data.name) df.uvars df
      data.schema.signature.constructors[index].fields.length) df
      (.const data.name (VLevel.params df.uvars)) := by
  have hreg := ((envTables_inv H).natives hd).2.registered
  obtain ⟨npre, idx, lv, ps, ⟨Ds, R, hl, hr, hlen⟩, _, _⟩ := ruleShape_of_registered hreg howner hgen
  have hm := congrArg VExpr.stripLams hl
  rw [ruleBody_stripLams] at hm
  obtain ⟨k, _, _, hk, _⟩ := defeq_major H hdf hm
  exact ruleSyntax_of_shape rfl (by intros; simp) hl hr hlen (.inl (by rw [hk]; simp))
    ⟨k, ctorOf_shape' H hk⟩

theorem quot_ruleSyntax (H : env.WF) (hq : (envTables env).quot = true) :
    RuleSyntax env (majorRule (structNp env) (.const ``Quot.lift) quotDefEq.uvars quotDefEq 1)
      quotDefEq (.const ``Quot.lift (VLevel.params quotDefEq.uvars)) := by
  obtain ⟨Ds, R, hl, hr, hlen⟩ := quot_ruleShape
  have hk := ((envTables_inv H).quot hq).2.2.1
  exact ruleSyntax_of_shape rfl (by intros; simp) hl hr hlen (.inl (by simp [ctorOf, hk]))
    ⟨quotCtor, ctorOf_shape' H (by simp [ctorOf, hk])⟩

theorem generic_ruleSyntax (H : env.WF) {schema : CaseSchema} (hreg : env.eliminators key schema)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules) :
    RuleSyntax env (majorRule (structNp env) (.elim key owner.val) schema.genericUvars df
      (schemaNf df)) df (.elim key owner.val (.param 0 :: schema.genericLevels)) := by
  obtain ⟨_, _, _, _, _, hcert, _, _⟩ := H.eliminator_origin hreg
  obtain ⟨index, Ds, idx, c, lv, ps, hl, hr, hlen, _⟩ := Certified.generic_shape hcert hgen hdf
  have hnf := schemaNf_eq (by intros; simp) hl hr
  rw [hnf]
  have hm : df.lhs.stripLams = .app (VExpr.mkApps (.elim key owner.val
      (.param 0 :: schema.genericLevels))
      (vars (schema.signature.params.length + (1 + (schema.view owner).constructors.size))
        (schema.view owner).constructors[index].fields.length ++ idx))
      (VExpr.mkApps (.const c lv) (ps ++ vars (schema.view owner).constructors[index].fields.length 0)) := by
    rw [hl, stripLams_wrapLams', mkApps_snoc]; rfl
  have hsm : SchemaMajor env c := ⟨key, schema, hreg, owner, rules, df, _, lv, _, hgen, hdf, hm⟩
  exact ruleSyntax_of_shape rfl (by intros; simp) hl hr hlen (.inr hsm) (hsm.shape H)

theorem RuleSyntax.head (h : RuleSyntax env r df (.const n ls)) :
    VDefEq.head df = .const n ls := by
  obtain ⟨Ds, idx, ps, npre, nf, c, lv, R, hl, _⟩ := h
  exact head_of_ruleBody hl

/-! ## Correspondence -/

/-- Every rule of the signature has an origin. -/
theorem EnvRule.origin (H : env.WF) (hr : EnvRule env r) : RuleOrigin env r := by
  rcases hr with ⟨v, hv, _, rfl⟩ | ⟨hq, hqt, rfl⟩ | ⟨df, hdf, data, hd, index, ho, hg, rfl⟩ |
    ⟨key, schema, hreg, owner, rules, df, hgen, hdf, rfl⟩
  · exact .inl ⟨v, hv, rfl⟩
  · exact .inr (.inl ⟨quotDefEq, ``Quot.lift, hq, quot_head, rfl, rfl, quot_ruleSyntax H hqt⟩)
  · have hs := native_ruleSyntax H hd ho hg hdf
    exact .inr (.inl ⟨df, data.name, hdf, hs.head, rfl, rfl, hs⟩)
  · exact .inr (.inr ⟨key, schema, hreg, owner, rules, df, hgen, hdf, rfl, rfl,
      generic_ruleSyntax H hreg hgen hdf⟩)

/-- Every stored equation has its rule: a definition's, or one decomposed by `RuleSyntax`
with the equation's head. -/
theorem defeq_rule (H : env.WF) (hdf : env.defeqs df) :
    ∃ r, EnvRule env r ∧
      ((∃ v : VDefVal, df = v.toDefEq ∧ r = defRule v) ∨
        ∃ n, VDefEq.head df = .const n (VLevel.params df.uvars) ∧ r.head = .const n ∧
          r.uvars = df.uvars ∧ RuleSyntax env r df (.const n (VLevel.params df.uvars))) := by
  have HT := envTables_inv H
  rcases HT.equations hdf with ⟨v, hv, rfl⟩ | ⟨hq, rfl⟩ | ⟨data, hd, index, ho, hg⟩
  · exact ⟨_, .inl ⟨v, hdf, hv, rfl⟩, .inl ⟨v, rfl, rfl⟩⟩
  · exact ⟨_, .inr (.inl ⟨hdf, hq, rfl⟩),
      .inr ⟨``Quot.lift, quot_head, rfl, rfl, quot_ruleSyntax H hq⟩⟩
  · have hs := native_ruleSyntax H hd ho hg hdf
    exact ⟨_, .inr (.inr (.inl ⟨df, hdf, data, hd, index, ho, hg, rfl⟩)),
      .inr ⟨data.name, hs.head, rfl, rfl, hs⟩⟩

/-- Every generic equation of a registered schema has its rule. -/
theorem generic_rule (H : env.WF) {schema : CaseSchema} (hreg : env.eliminators key schema)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules) :
    ∃ r, EnvRule env r ∧ r.head = .elim key owner.val ∧ r.uvars = schema.genericUvars ∧
      RuleSyntax env r df (.elim key owner.val (.param 0 :: schema.genericLevels)) :=
  ⟨_, .inr (.inr (.inr ⟨key, schema, hreg, owner, rules, df, hgen, hdf, rfl⟩)), rfl, rfl,
    generic_ruleSyntax H hreg hgen hdf⟩

/-! ## Corollaries through the `SchemaStructCompat` stub

These discharge `SchemaStructCompat` by `VEnv.WF.schemaStructCompat`, which currently depends on
the marked `sorry` stub `VEnv.WF'.schemaStructCompat` (to be replaced by the specification fix of
`VEnv.WF'.inductEliminators`). The theorems above take the hypothesis explicitly and are
sorry-free. -/

theorem envSig_coherent_of_wf (H : env.WF) : @SemSig.Coherent (envSig env) :=
  envSig_coherent H H.schemaStructCompat

theorem envSig_envFactsIn_of_wf (H : env.WF) {E : VEnv} (hle : E ≤ env)
    (hsem : ∀ {s info}, E.projections s info → FamTypeSem env s info) :
    letI := envSig env; SemSig.EnvFactsIn E env :=
  envSig_envFactsIn H H.schemaStructCompat hle hsem

end Lean4Lean.ShapeModel
