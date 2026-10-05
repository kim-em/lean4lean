import Lean4Lean.Theory.Inductive.CaseSchema

/-! Total projection programs built from abstract case analysis.

The selected family may be indexed and its fields may depend on earlier
fields. Each preceding field is replaced by the already generated projection
applied to the same parameters, indices, and major premise. Universe levels
are finite input data; their typing and case admissibility are separate proof
obligations. No projection term or field type is accepted as input.
-/

namespace Lean4Lean

private instance decidableClosedN : ∀ (e : VExpr) (n : Nat), Decidable (e.ClosedN n)
  | .bvar _, _ => Nat.decLt ..
  | .sort .., _ | .const .., _ | .elim .., _ => instDecidableTrue
  | .app f a, n => @instDecidableAnd _ _ (decidableClosedN f n) (decidableClosedN a n)
  | .proj _ _ e, n => decidableClosedN e n
  | .lam t b, n | .forallE t b, n =>
    @instDecidableAnd _ _ (decidableClosedN t n) (decidableClosedN b (n + 1))

namespace InductiveSignature.CaseSchema

/-- Restored syntax in the original common-parameter context. Index domains
are scoped over parameters and preceding indices; field domains over
parameters and preceding fields. `major` is under parameters and all indices,
while `constructor` and `constructorIndices` are under parameters and fields. -/
structure ProjectionData where
  params : List VExpr
  indices : List VExpr
  major : VExpr
  fields : List VExpr
  constructor : VExpr
  constructorIndices : List VExpr

/-- Scope checks reject malformed raw telescopes without inferring types. -/
def telescopeScoped (outer : Nat) (domains : List VExpr) : Bool :=
  domains.zipIdx.all fun (domain, i) => decide (domain.ClosedN (outer + i))

/-- Extract exactly one constructor and restore its original syntax before
building dependent projections. No identity of restored parameter spines is
assumed, so auxiliary families retain their certified specializations. -/
def projectionData (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) : Option ProjectionData := do
  if levels.length != schema.signature.uvars then none else
  let [ctor] := schema.signature.constructors.toList.filter (fun c => c.owner == owner)
    | none
  let family := schema.signature.families[owner]
  if ctor.indices.length != family.indices.length then none else
  let restore := fun e => schema.restoration.expr (e.instL levels)
  let params ← schema.signature.params.mapM restore
  let indices ← family.indices.mapM restore
  let fields ← (schema.signature.fieldTypes ctor).mapM restore
  let constructorIndices ← ctor.indices.mapM restore
  let major ← schema.restoration.expr <|
    schema.signature.familyApp owner levels
      (vars params.length indices.length) (vars indices.length 0)
  let constructor ← schema.restoration.expr <|
    VExpr.mkApps (.const ctor.name levels)
      (vars params.length fields.length ++ vars fields.length 0)
  if !(telescopeScoped 0 params && telescopeScoped params.length indices &&
      telescopeScoped params.length fields &&
      decide (major.ClosedN (params.length + indices.length)) &&
      decide (constructor.ClosedN (params.length + fields.length)) &&
      constructorIndices.all (fun e => decide (e.ClosedN (params.length + fields.length)))) then
    none
  else
    return { params, indices, major, fields, constructor, constructorIndices }

/-- A closed function together with its generated dependent function type.
`targetLevel` is input sort data; this record alone asserts no typing theorem. -/
structure ProjectionFunction where
  targetLevel : VLevel
  value : VExpr
  type : VExpr

/-- Arguments in the complete parameter/index/major context. -/
def ProjectionData.arguments (data : ProjectionData) : List VExpr :=
  vars data.params.length (data.indices.length + 1) ++
    vars data.indices.length 1 ++ [.bvar 0]

/-- The selected field's domain after simultaneous substitution of parameters
and previously generated field projections. The result is scoped under all
parameters, indices, and the major premise. -/
def ProjectionData.fieldTarget (data : ProjectionData) (domain : VExpr)
    (previous : List ProjectionFunction) : VExpr :=
  instantiateParams domain <|
    vars data.params.length (data.indices.length + 1) ++
      previous.map (fun projection => VExpr.mkApps projection.value data.arguments)

/-- Build one case call from its derived field domain. Its motive abstracts
all indices and the major; its sole minor abstracts every original field and
selects the current one. Motive and minor are lifted past the call's indices
and major while their common parameters remain free. -/
def ProjectionData.step (data : ProjectionData) (block : Name) (owner : Nat)
    (levels : List VLevel) (domain : VExpr) (target : VLevel)
    (previous : List ProjectionFunction) : ProjectionFunction :=
  let fieldType := data.fieldTarget domain previous
  let motive := VExpr.wrapLams (data.indices ++ [data.major]) fieldType
  let minor := VExpr.wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length))
  let below := data.indices.length + 1
  let body := VExpr.mkApps (.elim block owner (target :: levels))
    (vars data.params.length below ++ [motive.liftN below, minor.liftN below] ++
      vars data.indices.length 1 ++ [.bvar 0])
  let domains := data.params ++ data.indices ++ [data.major]
  { targetLevel := target
    value := VExpr.wrapLams domains body
    type := VExpr.wrapForalls domains fieldType }

def ProjectionData.prefix (data : ProjectionData) (block : Name) (owner : Nat)
    (levels : List VLevel) : List VExpr → List VLevel → List ProjectionFunction →
      Option (List ProjectionFunction)
  | _, [], previous => some previous
  | [], _ :: _, _ => none
  | domain :: domains, target :: targets, previous =>
    data.prefix block owner levels domains targets
      (previous ++ [data.step block owner levels domain target previous])

/-- Generate a prefix of field projections, in constructor order. A sort
level is required for every field through the desired projection. Invalid
universe arity, multiple constructors, malformed telescopes, failed
restoration, or an overlong requested prefix return `none`.

The generated values use abstract case eliminators only; the generator never
inserts primitive projections or references a native recursor. -/
def projectionPrefix (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (uvars : Nat)
    (levels fieldSorts : List VLevel) : Option (List ProjectionFunction) := do
  if !(levels.all (fun level => decide (level.WF uvars)) &&
      fieldSorts.all (fun level => decide (level.WF uvars))) then none else
  let data ← schema.projectionData owner levels
  data.prefix block owner.val levels data.fields fieldSorts []

end InductiveSignature.CaseSchema
end Lean4Lean

namespace Lean4Lean
namespace VExpr

/-- A scoped simultaneous substitution preserves the indicated scope. -/
theorem ClosedN.subst_closed {e : VExpr} (he : e.ClosedN k)
    (hσ : ∀ i < k, (σ i).ClosedN n) : (e.subst σ).ClosedN n := by
  induction e generalizing k n σ with (simp only [ClosedN, subst] at he ⊢)
  | bvar i => exact hσ i he
  | app _ _ ih1 ih2 => exact ⟨ih1 he.1 hσ, ih2 he.2 hσ⟩
  | proj _ _ _ ih => exact ih he hσ
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    refine ⟨ih1 he.1 hσ, ih2 he.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact (hσ i (by omega)).liftN

theorem ClosedN.mkApps_closed (hf : fn.ClosedN n)
    (ha : ∀ arg ∈ args, arg.ClosedN n) : (VExpr.mkApps fn args).ClosedN n := by
  induction args generalizing fn with
  | nil => exact hf
  | cons a args ih => exact ih ⟨hf, ha _ (.head _)⟩ (fun _ h => ha _ (.tail _ h))

/-- Close a lambda telescope whose domains are scoped in binder order. -/
theorem ClosedN.wrapLams_closed
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapLams domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

theorem ClosedN.wrapForalls_closed
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapForalls domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

end VExpr
namespace InductiveSignature.CaseSchema

theorem telescopeScoped_iff : telescopeScoped n domains = true ↔
    ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i) := by
  simp only [telescopeScoped, List.all_eq_true, Prod.forall, decide_eq_true_eq]
  constructor
  · intro h i hi
    exact h _ i (List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi))
  · intro h e i hi
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hi)
    exact h i hlt

/-- Scope facts enforced by the total extraction function. -/
structure ProjectionData.Scoped (data : ProjectionData) : Prop where
  params : ∀ i (hi : i < data.params.length), data.params[i].ClosedN i
  indices : ∀ i (hi : i < data.indices.length),
    data.indices[i].ClosedN (data.params.length + i)
  fields : ∀ i (hi : i < data.fields.length),
    data.fields[i].ClosedN (data.params.length + i)
  major : data.major.ClosedN (data.params.length + data.indices.length)
  constructor : data.constructor.ClosedN (data.params.length + data.fields.length)
  constructorIndices : ∀ e ∈ data.constructorIndices,
    e.ClosedN (data.params.length + data.fields.length)

theorem projectionData_scoped {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {levels : List VLevel} {data : ProjectionData}
    (h : schema.projectionData owner levels = some data) : data.Scoped := by
  unfold projectionData at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨params, _, indices, _, fields, _, constructorIndices, _, major, _, constructor, _, h⟩ := h
  split at h <;> try contradiction
  cases h
  rename_i valid
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨hp, hi⟩, hf⟩, hm⟩, hc⟩, hci⟩ := valid
  exact ⟨by simpa using telescopeScoped_iff.1 hp, telescopeScoped_iff.1 hi,
    telescopeScoped_iff.1 hf, hm, hc, hci⟩

variable {left right domains : List VExpr} {e domain : VExpr}
  {data : ProjectionData} {previous result : List ProjectionFunction}
  {block : Name} {owner : Nat} {levels targets : List VLevel} {target : VLevel}
  {n : Nat}

private theorem scopes_append
    (hleft : ∀ i (hi : i < left.length), left[i].ClosedN (n + i))
    (hright : ∀ i (hi : i < right.length), right[i].ClosedN (n + left.length + i)) :
    ∀ i (hi : i < (left ++ right).length), (left ++ right)[i].ClosedN (n + i) := by
  intro i hi
  by_cases hl : i < left.length
  · simpa only [List.getElem_append_left hl] using hleft i hl
  · rw [List.getElem_append_right (Nat.le_of_not_gt hl)]
    have hr := hright (i - left.length) (by simp at hi; omega)
    simpa only [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_gt hl)] using hr

private theorem scopes_singleton (h : e.ClosedN n) :
    ∀ i (hi : i < [e].length), ([e][i]).ClosedN (n + i) := by
  intro i hi
  have : i = 0 := by simpa using hi
  subst i
  exact h

private theorem vars_closed (hbound : count + below ≤ n) :
    ∀ e ∈ vars count below, e.ClosedN n := by
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  change below + i < n
  omega

private theorem ProjectionData.arguments_closed (data : ProjectionData) :
    ∀ arg ∈ data.arguments, arg.ClosedN (data.params.length + data.indices.length + 1) := by
  intro arg harg
  simp only [ProjectionData.arguments, List.mem_append, List.mem_singleton] at harg
  rcases harg with (h | h) | rfl
  · exact vars_closed (by omega) _ h
  · exact vars_closed (by omega) _ h
  · exact Nat.zero_lt_succ _

private theorem ProjectionData.fieldTarget_closed (data : ProjectionData)
    (hdomain : domain.ClosedN (data.params.length + previous.length))
    (hprevious : ∀ p ∈ previous, p.value.Closed) :
    (data.fieldTarget domain previous).ClosedN
      (data.params.length + data.indices.length + 1) := by
  unfold ProjectionData.fieldTarget instantiateParams
  apply hdomain.subst_closed
  intro i hi
  split
  · apply List.forall_mem_append.mpr
      ⟨vars_closed (by omega), ?_⟩ _ (List.getElem_mem _)
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact ((hprevious p hp).mono (Nat.zero_le _)).mkApps_closed data.arguments_closed
  · rename_i hbad
    simp only [List.length_append, vars, List.length_map, List.length_reverse,
      List.length_range] at hbad
    omega

private theorem ProjectionData.step_closed (hdata : data.Scoped)
    (hdomain : domain.ClosedN (data.params.length + previous.length))
    (hprevious : ∀ p ∈ previous, p.value.Closed)
    (hindex : previous.length < data.fields.length) :
    (data.step block owner levels domain target previous).value.Closed ∧
      (data.step block owner levels domain target previous).type.Closed := by
  have hindices := scopes_append hdata.indices (scopes_singleton hdata.major)
  have hdomains := scopes_append (n := 0) (left := data.params)
    (right := data.indices ++ [data.major]) (by simpa using hdata.params)
    (by simpa using hindices)
  rw [← List.append_assoc] at hdomains
  have htarget := data.fieldTarget_closed hdomain hprevious
  have hmotive := VExpr.ClosedN.wrapLams_closed hindices (by simpa [Nat.add_assoc] using htarget)
  have hminor : (VExpr.wrapLams data.fields
      (.bvar (data.fields.length - 1 - previous.length))).ClosedN data.params.length :=
    .wrapLams_closed hdata.fields (by change _ < _; omega)
  have hbody : (VExpr.mkApps (.elim block owner (target :: levels))
      (vars data.params.length (data.indices.length + 1) ++
        [VExpr.liftN (data.indices.length + 1)
          (VExpr.wrapLams (data.indices ++ [data.major]) (data.fieldTarget domain previous)) 0,
         VExpr.liftN (data.indices.length + 1)
          (VExpr.wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length))) 0] ++
        vars data.indices.length 1 ++ [.bvar 0])).ClosedN
      (data.params.length + data.indices.length + 1) := by
    apply VExpr.ClosedN.mkApps_closed (by trivial)
    intro arg harg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with ((h | (rfl | rfl)) | h) | rfl
    · exact vars_closed (by omega) _ h
    · simpa [Nat.add_assoc] using hmotive.liftN (n := data.indices.length + 1)
    · simpa [Nat.add_assoc] using hminor.liftN (n := data.indices.length + 1)
    · exact vars_closed (by omega) _ h
    · exact Nat.zero_lt_succ _
  exact ⟨.wrapLams_closed hdomains (by simpa [Nat.add_assoc] using hbody),
    .wrapForalls_closed hdomains (by simpa [Nat.add_assoc] using htarget)⟩

private theorem ProjectionData.prefix_closed (hdata : data.Scoped)
    (hprevious : ∀ p ∈ previous, p.value.Closed ∧ p.type.Closed)
    (hdomains : ∀ i (hi : i < domains.length),
      domains[i].ClosedN (data.params.length + previous.length + i))
    (hlen : previous.length + domains.length = data.fields.length)
    (hout : data.prefix block owner levels domains targets previous = some result) :
    ∀ p ∈ result, p.value.Closed ∧ p.type.Closed := by
  induction targets generalizing domains previous with
  | nil => simp only [ProjectionData.prefix] at hout; cases hout; exact hprevious
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      apply ih (previous := previous ++ [data.step block owner levels domain target previous])
        (domains := domains) ?_ ?_ ?_ hout
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hprevious p hp
        · obtain rfl := List.mem_singleton.mp hp
          exact data.step_closed hdata (hdomains 0 (by simp))
            (fun p hp => (hprevious p hp).1) (by simp at hlen; omega)
      · intro i hi
        have h := hdomains (i + 1) (by simp; omega)
        change domains[i].ClosedN (data.params.length + previous.length + (i + 1)) at h
        simpa [Nat.add_assoc, Nat.add_comm 1] using h
      · simpa [Nat.add_assoc, Nat.add_comm 1] using hlen

/-- Every successfully generated projection and its generated function type
are closed. This is derived from the checked source telescopes and prefix
construction, without checking the final expressions or assuming typing. -/
theorem projectionPrefix_closed {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.projectionPrefix block owner U levels fieldSorts = some result) :
    ∀ p ∈ result, p.value.Closed ∧ p.type.Closed := by
  unfold projectionPrefix at h
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨data, hdata, h⟩ := h
  have hscoped := projectionData_scoped hdata
  exact data.prefix_closed hscoped (by simp) (by simpa using hscoped.fields) (by simp) h

/-- Fixed projection templates reserve the first universe parameters for the
field sorts in prefix order, followed by the source declaration universes.
An occurrence specializes these templates with `fieldSorts ++ sourceLevels`. -/
def genericProjectionPrefix (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (fieldCount : Nat) :
    Option (List ProjectionFunction) :=
  schema.projectionPrefix block owner (schema.signature.uvars + fieldCount)
    ((List.range schema.signature.uvars).map fun i => .param (fieldCount + i))
    (VLevel.params fieldCount)

theorem genericProjectionPrefix_closed {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericProjectionPrefix block owner fieldCount = some result) :
    ∀ p ∈ result, p.value.Closed ∧ p.type.Closed :=
  projectionPrefix_closed h

private theorem ProjectionData.step_outer_lambda (data : ProjectionData) :
    ∃ d b, (data.step block owner levels domain target previous).value = .lam d b := by
  let ds := data.params ++ data.indices ++ [data.major]
  have hnonempty : ds ≠ [] := by simp [ds]
  change ∃ d b, VExpr.wrapLams ds _ = .lam d b
  cases hds : ds with
  | nil => exact (hnonempty hds).elim
  | cons d ds => exact ⟨d, _, rfl⟩

private theorem ProjectionData.prefix_outer_lambdas
    (hprevious : ∀ p ∈ previous, ∃ d b, p.value = .lam d b)
    (hout : data.prefix block owner levels domains targets previous = some result) :
    ∀ p ∈ result, ∃ d b, p.value = .lam d b := by
  induction targets generalizing domains previous with
  | nil => simp only [ProjectionData.prefix] at hout; cases hout; exact hprevious
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      apply ih (previous := previous ++ [data.step block owner levels domain target previous])
        (domains := domains) ?_ hout
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hprevious p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact data.step_outer_lambda

theorem projectionPrefix_outer_lambdas {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.projectionPrefix block owner U levels fieldSorts = some result) :
    ∀ p ∈ result, ∃ d b, p.value = .lam d b := by
  unfold projectionPrefix at h
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨data, _, h⟩ := h
  exact data.prefix_outer_lambdas (by simp) h

theorem genericProjectionPrefix_outer_lambdas {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericProjectionPrefix block owner fieldCount = some result) :
    ∀ p ∈ result, ∃ d b, p.value = .lam d b :=
  projectionPrefix_outer_lambdas h

end InductiveSignature.CaseSchema
end Lean4Lean
