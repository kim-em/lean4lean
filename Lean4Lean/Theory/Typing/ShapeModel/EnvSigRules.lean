import Lean4Lean.Theory.Typing.ShapeModel.EnvSigCtor

/-!
# Rules of the semantic signature of a well-formed environment: rules with the same head
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

@[simp] theorem majorRule_head : (majorRule np h u df nf).head = h := rfl
@[simp] theorem defRule_head : (defRule v).head = .const v.name := rfl
@[simp] theorem defRule_major : (defRule v).major = none := rfl
@[simp] theorem majorRule_major_isSome : ((majorRule np h u df nf).major).isSome = true := rfl

/-- Two rules with the same head that are not equal: the spine facts used by coherence. -/
def RulePairSpine (env : VEnv) (r₁ r₂ : Rule) : Prop :=
  ∃ (pre₁ pre₂ : List VExpr) (c₁ c₂ : Name) (lv : List VLevel) (f₁ f₂ : List Nat),
    r₁.vars = pre₁.map argVar ∧ r₂.vars = pre₂.map argVar ∧ pre₁.length = pre₂.length ∧
    r₁.major = some ⟨c₁, lv, f₁⟩ ∧ r₂.major = some ⟨c₂, lv, f₂⟩ ∧ c₁ ≠ c₂ ∧
    ctorFamily env c₁ = ctorFamily env c₂ ∧ ctorFamily env c₁ ≠ none

/-- The major constructor of a native equation is the restored name of its constructor. -/
theorem native_major_name (H : env.WF) {data : NativeRecursorData}
    (hd : (envTables env).natives data.name = some data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df) :
    ∃ pre lv args, df.lhs.stripLams = .app
      (VExpr.mkApps (.const data.name (VLevel.params df.uvars)) pre)
      (VExpr.mkApps (.const (data.schema.restoration.headName
        data.schema.signature.constructors[index].name) lv) args) := by
  have hreg := ((envTables_inv H).natives hd).2.registered
  obtain ⟨npre, idx, lv, ps, ⟨Ds, R, hl, _, _⟩, _, _⟩ := ruleShape_of_registered hreg howner hgen
  exact ⟨_, _, _, by rw [hl, ruleBody_stripLams]⟩

theorem native_index_unique (H : env.WF) {data : NativeRecursorData}
    (hd : (envTables env).natives data.name = some data)
    {i j : Fin data.schema.signature.constructors.size}
    (hi : data.schema.signature.constructors[i].owner = data.owner)
    (hj : data.schema.signature.constructors[j].owner = data.owner)
    (hgi : data.equation i = some df) (hgj : data.equation j = some df) : i = j := by
  have hreg := ((envTables_inv H).natives hd).2.registered
  obtain ⟨pre, lv, args, h1⟩ := native_major_name H hd hi hgi
  obtain ⟨pre', lv', args', h2⟩ := native_major_name H hd hj hgj
  rw [h1] at h2
  have := (mkApps_const_inj (VExpr.app.inj h2).2).1
  exact hreg.constructor_index_unique hi hj this

theorem const_pair (H : env.WF) (h₁ : EnvRule env r₁) (h₂ : EnvRule env r₂)
    (hh : r₁.head = r₂.head) (hc : r₁.head = .const n) : r₁ = r₂ ∨ RulePairSpine env r₁ r₂ := by
  have HT := envTables_inv H
  have hq : (envTables env).quot = true → (envTables env).defs ``Quot.lift = none ∧
      (envTables env).natives ``Quot.lift = none := fun hq =>
    ⟨(HT.quot hq).2.2.2.1, (HT.quot hq).2.2.2.2.1⟩
  rcases h₁ with ⟨v₁, _, hv₁, rfl⟩ | ⟨_, hq₁, rfl⟩ | ⟨df₁, hdf₁, d₁, hd₁, i₁, ho₁, hg₁, rfl⟩ |
    ⟨k₁, s₁, _, o₁, _, _, _, _, _, rfl⟩
  · rcases h₂ with ⟨v₂, _, hv₂, rfl⟩ | ⟨_, hq₂, rfl⟩ | ⟨df₂, hdf₂, d₂, hd₂, i₂, ho₂, hg₂, rfl⟩ |
      ⟨k₂, s₂, _, o₂, _, _, _, _, _, rfl⟩
    · simp only [defRule_head, Head.const.injEq] at hh
      rw [hh, hv₂] at hv₁; cases hv₁; exact .inl rfl
    · simp only [defRule_head, majorRule_head, Head.const.injEq] at hh
      rw [hh, (hq hq₂).1] at hv₁; cases hv₁
    · simp only [defRule_head, majorRule_head, Head.const.injEq] at hh
      have := HT.defs_natives (n := d₂.name) (by rw [← hh, hv₁]; simp)
      rw [this] at hd₂; cases hd₂
    · simp at hh
  · rcases h₂ with ⟨v₂, _, hv₂, rfl⟩ | ⟨_, hq₂, rfl⟩ | ⟨df₂, hdf₂, d₂, hd₂, i₂, ho₂, hg₂, rfl⟩ |
      ⟨k₂, s₂, _, o₂, _, _, _, _, _, rfl⟩
    · simp only [defRule_head, majorRule_head, Head.const.injEq] at hh
      rw [← hh, (hq hq₁).1] at hv₂; cases hv₂
    · exact .inl rfl
    · simp only [majorRule_head, Head.const.injEq] at hh
      rw [← hh, (hq hq₁).2] at hd₂; cases hd₂
    · simp at hh
  · rcases h₂ with ⟨v₂, _, hv₂, rfl⟩ | ⟨_, hq₂, rfl⟩ | ⟨df₂, hdf₂, d₂, hd₂, i₂, ho₂, hg₂, rfl⟩ |
      ⟨k₂, s₂, _, o₂, _, _, _, _, _, rfl⟩
    · simp only [defRule_head, majorRule_head, Head.const.injEq] at hh
      have := HT.defs_natives (n := d₁.name) (by rw [hh, hv₂]; simp)
      rw [this] at hd₁; cases hd₁
    · simp only [majorRule_head, Head.const.injEq] at hh
      rw [hh, (hq hq₂).2] at hd₁; cases hd₁
    · simp only [majorRule_head, Head.const.injEq] at hh
      rw [hh, hd₂] at hd₁
      cases hd₁
      by_cases hdf : df₁ = df₂
      · subst hdf
        cases native_index_unique H hd₂ ho₁ ho₂ hg₁ hg₂
        exact .inl rfl
      · right
        obtain ⟨u, pre₁, pre₂, c₁, c₂, lv, args₁, args₂, k₁, k₂, hs₁, hs₂, hlen, hne, hk₁, hk₂, hfam⟩ :=
          same_head_spines H hdf₁ hdf₂ (native_head HT hd₂ ho₁ hg₁) (native_head HT hd₂ ho₂ hg₂) hdf
        obtain ⟨hv₁, hm₁⟩ := majorRule_strip (np := structNp env) (h := .const d₁.name)
          (u := df₁.uvars) (nf := d₁.schema.signature.constructors[i₁].fields.length) rfl hs₁
        obtain ⟨hv₂, hm₂⟩ := majorRule_strip (np := structNp env) (h := .const d₁.name)
          (u := df₂.uvars) (nf := d₁.schema.signature.constructors[i₂].fields.length) rfl hs₂
        refine ⟨pre₁, pre₂, c₁, c₂, lv, _, _, hv₁, hv₂, hlen, hm₁, hm₂, hne, ?_, ?_⟩
        · rw [(ctorOf_shape' H hk₁).family, (ctorOf_shape' H hk₂).family, hfam]
        · rw [(ctorOf_shape' H hk₁).family]; simp
    · simp at hh
  · simp at hc

/-- The field count of a generic equation is that of its constructor in the case view. -/
theorem schemaNf_eq {df : VDefEq} {Ds : List VExpr} {hd : VExpr} {args : List VExpr} {m nf : Nat}
    (hlam : ∀ d b, hd ≠ .lam d b)
    (hl : df.lhs = VExpr.wrapLams Ds (VExpr.mkApps hd args))
    (hr : df.rhs = VExpr.wrapLams Ds (VExpr.mkApps (.bvar m) (vars nf 0))) :
    schemaNf df = nf := by
  unfold schemaNf
  rw [hl, lamDoms_wrapLams (mkApps_ne_lam hlam _), hr, dropLams_wrapLams,
    spine_mkApps_exact _ _ rfl, vars_succ_length]

/-- The left body of a generic equation, after its lambdas. -/
theorem generic_strip {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} (hgen : schema.genericEquations key owner = some rules)
    (hdf : df ∈ rules) :
    ∃ pre c lv margs, df.lhs.stripLams = .app
        (VExpr.mkApps (.elim key owner.val (.param 0 :: schema.genericLevels)) pre)
        (VExpr.mkApps (.const c lv) margs) ∧
      pre.length = schema.signature.params.length + (1 + (schema.view owner).constructors.size) +
        schema.signature.families[owner].indices.length := by
  obtain ⟨_, _, _, _, _, hcert, _, _⟩ := H.eliminator_origin hreg
  obtain ⟨index, Ds, idx, c, lv, ps, hl, _, _, _, hidx, _⟩ := Certified.generic_shape hcert hgen hdf
  refine ⟨vars (schema.signature.params.length + (1 + (schema.view owner).constructors.size))
      (schema.view owner).constructors[index].fields.length ++ idx, c, lv, ps ++ vars (schema.view owner).constructors[index].fields.length 0,
    by rw [hl, stripLams_wrapLams', mkApps_snoc]; rfl, ?_⟩
  rw [List.length_append, vars_succ_length, hidx]

theorem elim_pair (H : env.WF) (h₁ : EnvRule env r₁) (h₂ : EnvRule env r₂)
    (hh : r₁.head = r₂.head) (hc : r₁.head = .elim b o) : r₁ = r₂ ∨ RulePairSpine env r₁ r₂ := by
  rcases h₁ with ⟨v₁, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ |
    ⟨k₁, s₁, hreg₁, o₁, rules₁, df₁, hgen₁, hdf₁, rfl⟩
  · simp at hc
  · simp at hc
  · simp at hc
  rcases h₂ with ⟨v₂, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ |
    ⟨k₂, s₂, hreg₂, o₂, rules₂, df₂, hgen₂, hdf₂, rfl⟩
  · simp at hh
  · simp at hh
  · simp at hh
  simp only [majorRule_head, Head.elim.injEq] at hh
  obtain ⟨rfl, ho⟩ := hh
  cases H.eliminators_unique hreg₁ hreg₂
  have : o₁ = o₂ := Fin.ext ho
  subst this
  rw [hgen₁] at hgen₂
  cases hgen₂
  by_cases hdf : df₁ = df₂
  · subst hdf; exact .inl rfl
  right
  obtain ⟨lvOf, famOf', hclass⟩ := generic_major_class H hreg₁
  obtain ⟨pre₁, c₁, lv₁, m₁, hs₁, hl₁⟩ := generic_strip H hreg₁ hgen₁ hdf₁
  obtain ⟨pre₂, c₂, lv₂, m₂, hs₂, hl₂⟩ := generic_strip H hreg₁ hgen₁ hdf₂
  have hs₁' : df₁.lhs.stripLams = .app _ _ := hs₁
  obtain ⟨hlv₁, hf₁⟩ := hclass hgen₁ hdf₁ hs₁
  obtain ⟨hlv₂, hf₂⟩ := hclass hgen₁ hdf₂ hs₂
  obtain ⟨hv₁, hm₁⟩ := majorRule_strip (np := structNp env) (h := .elim k₁ o₁.val)
    (u := s₁.genericUvars) (nf := schemaNf df₁) rfl hs₁
  obtain ⟨hv₂, hm₂⟩ := majorRule_strip (np := structNp env) (h := .elim k₁ o₁.val)
    (u := s₁.genericUvars) (nf := schemaNf df₂) rfl hs₂
  rw [hlv₁] at hm₁
  rw [hlv₂] at hm₂
  refine ⟨pre₁, pre₂, c₁, c₂, _, _, _, hv₁, hv₂, hl₁.trans hl₂.symm, hm₁, hm₂, ?_,
    hf₁.trans hf₂.symm, by rw [hf₁]; simp⟩
  rintro rfl
  obtain ⟨g₁, hg₁, he₁⟩ := CaseSchema.generates_of_genericEquation hgen₁ hdf₁
  obtain ⟨g₂, hg₂, he₂⟩ := CaseSchema.generates_of_genericEquation hgen₁ hdf₂
  have hn₁ := generates_ctorName hg₁ (he₁ ▸ hs₁)
  have hn₂ := generates_ctorName hg₂ (he₂ ▸ hs₂)
  have := VEnv.WF.case_rule_unique H hreg₁ hg₁ hg₂ (hn₁.trans hn₂.symm)
  subst this
  exact hdf (he₁.symm.trans he₂)

end Lean4Lean.ShapeModel
