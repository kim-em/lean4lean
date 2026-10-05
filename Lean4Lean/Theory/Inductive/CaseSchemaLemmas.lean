import Lean4Lean.Theory.Inductive.CaseSchema

/-! Pure shape facts about generated and restored abstract case equations. -/

namespace Lean4Lean
namespace VExpr

private theorem spine_head_go (e : VExpr) (args : List VExpr) :
    (getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app f a ih _ => exact (ih (a :: args)).trans (ih [a]).symm
  | _ => rfl

private theorem spine_head_app (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs.1 = fn.getAppFnArgs.1 := spine_head_go fn [arg]

private theorem spine_head_mkApps (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact (ih (.app fn a)).trans (spine_head_app fn a)

private theorem stripLams_of_head_elim {e : VExpr}
    (h : e.getAppFnArgs.1 = .elim block owner levels) : e.stripLams = e := by
  cases e <;> first | rfl | cases h

end VExpr
namespace InductiveSignature

/-- Both endpoints of every generated equation have a nonempty common lambda
telescope, including in abstract head mode. -/
theorem Instance.equation_outer_lambdas {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (mode : HeadMode) :
    ∃ domain lhsBody rhsBody, (g.equation index mode).lhs = .lam domain lhsBody ∧
      (g.equation index mode).rhs = .lam domain rhsBody := by
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size)
  have hlength : g.minors.length = s.constructors.size := by simp [Instance.minors]
  have hnonempty : domains ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    simp only [domains, List.length_append, List.length_nil] at hzero
    have := index.isLt
    omega
  unfold Instance.equation
  change ∃ domain lhsBody rhsBody,
    VExpr.wrapLams domains _ = .lam domain lhsBody ∧
    VExpr.wrapLams domains _ = .lam domain rhsBody
  cases hd : domains with
  | nil => exact (hnonempty hd).elim
  | cons domain domains => exact ⟨domain, _, _, rfl, rfl⟩

theorem Restoration.equation_parts {r : Restoration} {source restored : VDefEq}
    (h : r.equation source = some restored) :
    r.expr source.lhs = some restored.lhs ∧ r.expr source.rhs = some restored.rhs ∧
      r.expr source.type = some restored.type := by
  simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, hl, rhs, hr, type, ht, h⟩ := h
  cases h
  exact ⟨hl, hr, ht⟩

/-- Successful restoration preserves the complete outer lambda constructor. -/
theorem Restoration.expr_lam_parts {r : Restoration} {domain body restored : VExpr}
    (h : r.expr (.lam domain body) = some restored) :
    ∃ domain' body', r.expr domain = some domain' ∧ r.expr body = some body' ∧
      restored = .lam domain' body' := by
  change (do
    let domain' ← r.expr domain
    let body' ← r.expr body
    pure (.lam domain' body')) = some restored at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨domain', hd, body', hb, h⟩ := h
  exact ⟨domain', body', hd, hb, Option.some.inj h.symm⟩

/-- Restoration cannot rename an abstract symbol or confuse it with a native
constant, including when restoring the symbol's argument spine. -/
theorem Restoration.go_head_elim {r : Restoration} {e output : VExpr}
    {args : List VExpr} {block : Name} {owner : Nat} {levels : List VLevel}
    (hhead : e.getAppFnArgs.1 = .elim block owner levels)
    (hgo : Restoration.expr.go r e args = some output) :
    output.getAppFnArgs.1 = .elim block owner levels := by
  induction e generalizing args with
  | app fn arg ihfn _ =>
    have hf : fn.getAppFnArgs.1 = .elim block owner levels :=
      (VExpr.spine_head_app fn arg).symm.trans hhead
    cases ha : Restoration.expr.go r arg [] with
    | none => simp [Restoration.expr.go, ha] at hgo
    | some arg' =>
      simp [Restoration.expr.go, ha] at hgo
      exact ihfn hf hgo
  | elim b o ls =>
    have heq : b = block ∧ o = owner ∧ ls = levels := by simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using hhead
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst output
    exact VExpr.spine_head_mkApps _ _
  | bvar | sort | const | lam | forallE | proj => cases hhead

theorem Restoration.wrapLams_head_elim {r : Restoration} {e output : VExpr}
    {domains : List VExpr} {block : Name} {owner : Nat} {levels : List VLevel}
    (hhead : e.getAppFnArgs.1 = .elim block owner levels)
    (h : r.expr (VExpr.wrapLams domains e) = some output) :
    output.stripLams.getAppFnArgs.1 = .elim block owner levels := by
  induction domains generalizing output with
  | nil =>
    have hh := Restoration.go_head_elim hhead h
    rw [VExpr.stripLams_of_head_elim hh]
    exact hh
  | cons d ds ih =>
    obtain ⟨d', b', _, hb, rfl⟩ := Restoration.expr_lam_parts h
    exact ih (output := b') hb

/-- Exact abstract head ownership survives restoration. -/
theorem Instance.restored_abstract_equation_head {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) {r : Restoration} {equation : VDefEq}
    (h : r.equation (g.equation index (.abstract block firstOwner)) = some equation) :
    equation.lhs.stripLams.getAppFnArgs.1 =
      .elim block (firstOwner + s.constructors[index].owner.val) (g.targetLevel :: g.levels) := by
  have hl := (Restoration.equation_parts h).1
  apply Restoration.wrapLams_head_elim (h := hl)
  exact VExpr.spine_head_mkApps _ _

theorem Instance.restored_equation_outer_lambdas {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (mode : HeadMode) {r : Restoration} {equation : VDefEq}
    (h : r.equation (g.equation index mode) = some equation) :
    (∃ domain body, equation.lhs = .lam domain body) ∧
      (∃ domain body, equation.rhs = .lam domain body) := by
  obtain ⟨domain, lhsBody, rhsBody, hl, hr⟩ := g.equation_outer_lambdas index mode
  have ⟨hleft, hright, _⟩ := Restoration.equation_parts h
  rw [hl] at hleft
  rw [hr] at hright
  obtain ⟨domain', body', _, _, hleft⟩ := Restoration.expr_lam_parts hleft
  obtain ⟨domain'', body'', _, _, hright⟩ := Restoration.expr_lam_parts hright
  exact ⟨⟨_, _, hleft⟩, ⟨_, _, hright⟩⟩

namespace CaseSchema

/-- Every case-view constructor is the selected owner's original constructor,
with the same ordered indices and field domains. -/
theorem view_constructor_origin {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (index : Fin (schema.view owner).constructors.size) :
    ∃ ctor ∈ schema.signature.constructors.toList, ctor.owner = owner ∧
      (schema.view owner).constructors[index] = schema.caseConstructor ctor := by
  have hm : (schema.view owner).constructors[index] ∈ (schema.view owner).constructors.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem (xs := (schema.view owner).constructors) index.isLt)
  change (schema.view owner).constructors[index] ∈
    schema.signature.constructors.toList.filterMap (fun ctor =>
      if ctor.owner == owner then some (schema.caseConstructor ctor) else none) at hm
  obtain ⟨ctor, hctor, he⟩ := List.mem_filterMap.mp hm
  split at he
  · exact ⟨ctor, hctor, by simpa using ‹(ctor.owner == owner) = true›,
      (Option.some.inj he).symm⟩
  · cases he

/-- Each restored case rule comes from a specific constructor in the same
one-family view, with the exact abstract owner offset. -/
theorem equation_origin {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (h : schema.equations block owner U levels target = some rules) (hmem : rule ∈ rules) :
    ∃ index : Fin (schema.view owner).constructors.size,
      schema.restoration.equation
        ((schema.specialize owner U levels target).equation index (.abstract block owner.val)) =
      some rule := by
  have hrel := List.mapM_eq_some.mp h
  have horigin : ∀ {xs ys}, List.Forall₂ (fun x y => schema.restoration.equation x = some y) xs ys →
      ∀ y ∈ ys, ∃ x ∈ xs, schema.restoration.equation x = some y := by
    intro xs ys hxy
    induction hxy with
    | nil => simp
    | cons hhead _ ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, .head _, hhead⟩
      · obtain ⟨x, hx, h⟩ := ih _ hy
        exact ⟨x, .tail _ hx, h⟩
  obtain ⟨generated, hgenerated, hrestore⟩ := horigin hrel _ hmem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hgenerated
  exact ⟨index, hrestore⟩

/-- Generic case rule heads use exactly the registered block and original
expanded owner slot, with target-first source-universe parameters. -/
theorem genericEquation_head {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericEquations block owner = some rules) (hmem : rule ∈ rules) :
    rule.lhs.stripLams.getAppFnArgs.1 =
      .elim block owner.val (.param 0 :: schema.genericLevels) := by
  obtain ⟨index, hrestore⟩ := equation_origin h hmem
  have hhead := Instance.restored_abstract_equation_head _ index hrestore
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  simpa [specialize, hzero] using hhead

theorem genericEquation_outer_lambdas {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericEquations block owner = some rules) (hmem : rule ∈ rules) :
    (∃ domain body, rule.lhs = .lam domain body) ∧
      (∃ domain body, rule.rhs = .lam domain body) := by
  obtain ⟨index, hrestore⟩ := equation_origin h hmem
  exact Instance.restored_equation_outer_lambdas _ index _ hrestore

end CaseSchema
end InductiveSignature
end Lean4Lean
