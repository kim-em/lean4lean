import Lean4Lean.Theory.Typing.ShapeModel.RuleValidAssembly

/-!
# Syntax of restored generated equations and recursor types

The generated equation of a constructor (`Instance.equation`, native or abstract head) and the
generated recursor type (`Instance.recursorType`), after restoration:

* `restored_equation_syntax`: the left side is a lambda telescope `Ds` over the head applied to the
  prefix variables, the restored indices and the restored major; the right side is a lambda
  telescope over the same `Ds`; the type is the Pi telescope over `Ds` of the owner's motive
  applied to the same indices and major; the motive's binder domain is a telescope ending in the
  target sort.
* `restored_recursorType_syntax`: the recursor type is a Pi telescope whose last domain is the
  restored owner family applied to the parameters and the index variables.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

theorem restoration_wrapLams_forall₂ {r : Restoration} :
    ∀ {domains : List VExpr} {body output : VExpr},
      r.expr (VExpr.wrapLams domains body) = some output →
      ∃ domains' body', output = VExpr.wrapLams domains' body' ∧
        List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body'
  | [], _, output, H => ⟨[], output, rfl, .nil, H⟩
  | d :: ds, body, output, H => by
    obtain ⟨d', b', hd, hb, rfl⟩ := Restoration.expr_lam_parts H
    obtain ⟨ds', body', rfl, hrel, hbody⟩ := restoration_wrapLams_forall₂ (domains := ds) hb
    exact ⟨d' :: ds', body', rfl, .cons hd hrel, hbody⟩

theorem restoration_wrapForalls_forall₂ {r : Restoration} :
    ∀ {domains : List VExpr} {body output : VExpr},
      r.expr (VExpr.wrapForalls domains body) = some output →
      ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧
        List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body'
  | [], _, output, H => ⟨[], output, rfl, .nil, H⟩
  | d :: ds, body, output, H => by
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' t')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨d', hd, out, hout, H⟩ := H
    cases H
    obtain ⟨ds', body', rfl, hrel, hb⟩ := restoration_wrapForalls_forall₂ (domains := ds) hout
    exact ⟨d' :: ds', body', rfl, .cons hd hrel, hb⟩

theorem forall₂_functional {f : α → Option β} :
    ∀ {l : List α} {l₁ l₂ : List β}, List.Forall₂ (fun a b => f a = some b) l l₁ →
      List.Forall₂ (fun a b => f a = some b) l l₂ → l₁ = l₂
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [h₁] at h₂; cases h₂; rw [forall₂_functional t₁ t₂]

theorem restoration_sort {r : Restoration} {u : VLevel} {out : VExpr}
    (h : r.expr (.sort u) = some out) : out = .sort u := by
  change Restoration.expr.go r (.sort u) [] = _ at h
  simp [Restoration.expr.go, VExpr.mkApps] at h
  exact h.symm

theorem restoration_bvar_mkApps {r : Restoration} {i : Nat} {args : List VExpr} {out : VExpr}
    (h : r.expr (VExpr.mkApps (.bvar i) args) = some out) :
    ∃ args', args.mapM r.expr = some args' ∧ out = VExpr.mkApps (.bvar i) args' := by
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨args', ha, h⟩ := h
  simp only [List.append_nil, Restoration.expr.go, Option.some.injEq] at h
  exact ⟨args', ha, h.symm⟩

theorem restored_mkApps_head {r : Restoration} {hd hd' : VExpr} {args : List VExpr} {out : VExpr}
    (hhd : ∀ args, Restoration.expr.go r hd args = some (VExpr.mkApps hd' args))
    (h : r.expr (VExpr.mkApps hd args) = some out) :
    ∃ args', args.mapM r.expr = some args' ∧ out = VExpr.mkApps hd' args' := by
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨args', ha, h⟩ := h
  rw [List.append_nil, hhd] at h
  exact ⟨args', ha, (Option.some.inj h).symm⟩

theorem motives_getElem {s : InductiveSignature} (g : Instance s) (o : Fin s.families.size) :
    ∃ h : o.val < g.motives.length, g.motives[o.val] = g.motive s.families[o] o.val := by
  refine ⟨by simp [Instance.motives], ?_⟩
  simp [Instance.motives]

/-- The syntax of a restored generated equation. -/
theorem restored_equation_syntax {s : InductiveSignature} (g : Instance s) (r : Restoration)
    (mode : HeadMode) (index : Fin s.constructors.size) {df : VDefEq}
    (h : r.equation (g.equation index mode) = some df) {hd' : VExpr}
    (hhd : ∀ args, Restoration.expr.go r (g.recursorHead mode s.constructors[index].owner) args =
      some (VExpr.mkApps hd' args)) :
    ∃ (Ds idx : List VExpr) (major R : VExpr) (Es : List VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps hd'
        (vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[index].fields.length ++ idx ++ [major])) ∧
      df.rhs = VExpr.wrapLams Ds R ∧
      df.type = VExpr.wrapForalls Ds (VExpr.mkApps
        (.bvar (s.constructors[index].fields.length + s.constructors.size +
          (s.families.size - 1 - s.constructors[index].owner.val))) (idx ++ [major])) ∧
      Ds.length = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].fields.length ∧
      idx.length = s.constructors[index].indices.length ∧
      r.expr (g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0) =
        some major ∧
      (∃ hm : s.params.length + s.constructors[index].owner.val < Ds.length,
        Ds[s.params.length + s.constructors[index].owner.val] =
          VExpr.wrapForalls Es (.sort g.targetLevel)) ∧
      Es.length = s.families[s.constructors[index].owner].indices.length + 1 ∧
      List.Forall₂ (fun d d' => r.expr d = some d') (g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
          (s.families.size + s.constructors.size)) Ds ∧
      (s.constructors[index].indices.map fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) s.constructors[index].fields.length).mapM r.expr =
        some idx := by
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts h
  obtain ⟨Ds, lB, hlD, hDs, hlB⟩ := restoration_wrapLams_forall₂ hl
  obtain ⟨Ds₂, R, hrD, hDs₂, -⟩ := restoration_wrapLams_forall₂ hr
  obtain ⟨Ds₃, tB, htD, hDs₃, htB⟩ := restoration_wrapForalls_forall₂ ht
  cases forall₂_functional hDs hDs₂
  cases forall₂_functional hDs hDs₃
  obtain ⟨args', hargs', rfl⟩ := restored_mkApps_head hhd hlB
  simp only [List.mapM_append, restoration_vars', bind, Option.bind_eq_some_iff,
    List.mapM_cons, List.mapM_nil, pure, Option.some.injEq] at hargs'
  obtain ⟨_, ⟨_, rfl, idx, hidx, rfl⟩, _, ⟨major, hmajor, _, rfl, rfl⟩, rfl⟩ := hargs'
  obtain ⟨targs, htargs, rfl⟩ := restoration_bvar_mkApps htB
  simp only [List.mapM_append, bind, Option.bind_eq_some_iff, List.mapM_cons, List.mapM_nil, pure,
    Option.some.injEq] at htargs
  obtain ⟨idx', hidx', _, ⟨major', hmajor', _, rfl, rfl⟩, rfl⟩ := htargs
  rw [hidx] at hidx'; cases hidx'
  rw [hmajor] at hmajor'; cases hmajor'
  have hlenD := Lean4Lean.List.Forall₂.length_eq hDs
  have hdl : (g.params ++ g.motives ++ g.minors ++ insertBinders
      ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size)).length =
      s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].fields.length := by
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders, fieldTypes]; omega
  have ho := s.constructors[index].owner.isLt
  have hmpos : s.params.length + s.constructors[index].owner.val <
      (g.params ++ g.motives ++ g.minors ++ insertBinders
        ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size)).length := by rw [hdl]; omega
  have hmd := forall₂_getElem hDs hmpos
  have hdom : (g.params ++ g.motives ++ g.minors ++ insertBinders
      ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size))[s.params.length + s.constructors[index].owner.val] =
      g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val := by
    have hp : g.params.length = s.params.length := by simp [Instance.params]
    have hm : g.motives.length = s.families.size := by simp [Instance.motives]
    rw [List.getElem_append_left (by simp [hp, hm, Instance.minors]; omega),
      List.getElem_append_left (by simp [hp, hm]),
      List.getElem_append_right (by simp [hp]), ]
    simp only [hp, Nat.add_sub_cancel_left]
    obtain ⟨_, hmo⟩ := motives_getElem g s.constructors[index].owner
    exact hmo
  rw [hdom] at hmd
  obtain ⟨Es, body', hEs, hEsrel, hbody'⟩ := restoration_wrapForalls_forall₂ hmd
  cases restoration_sort hbody'
  refine ⟨Ds, idx, major, R, Es, hlD, hrD, htD, ?_, ?_, hmajor, ⟨by rw [← hlenD, hdl]; omega, ?_⟩,
    ?_⟩
  · rw [← hlenD, hdl]
  · have := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hidx)
    simpa using this.symm
  · exact hEs
  · have := Lean4Lean.List.Forall₂.length_eq hEsrel
    refine ⟨?_, hDs, hidx⟩
    rw [← this]; simp [insertBinders]

theorem forall₂_snoc_inv'' {R : α → β → Prop} :
    ∀ {l₀ : List α} {x : α} {l : List β}, List.Forall₂ R (l₀ ++ [x]) l →
    ∃ l₀' x', l = l₀' ++ [x'] ∧ List.Forall₂ R l₀ l₀' ∧ R x x'
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t =>
    let ⟨l₀', x', e, t', h'⟩ := forall₂_snoc_inv'' t
    ⟨_ :: l₀', x', by rw [e]; rfl, .cons h t', h'⟩

/-- The syntax of a restored generated recursor type: a Pi telescope whose last domain is the
restored family application of the owner. -/
theorem restored_recursorType_syntax {s : InductiveSignature} (g : Instance s) (r : Restoration)
    (o : Fin s.families.size) {Th : VExpr} (h : r.expr (g.recursorType o) = some Th) :
    ∃ (doms₀ : List VExpr) (TbH majorDom : VExpr),
      Th = VExpr.wrapForalls (doms₀ ++ [majorDom]) TbH ∧
      doms₀.length = s.params.length + (s.families.size + s.constructors.size) +
        s.families[o].indices.length ∧
      r.expr (g.familyApp o (vars s.params.length
        (s.families.size + s.constructors.size + s.families[o].indices.length))
        (vars s.families[o].indices.length 0)) = some majorDom := by
  obtain ⟨doms, TbH, rfl, hrel, -⟩ := restoration_wrapForalls_forall₂ h
  obtain ⟨doms₀, majorDom, rfl, hpre, hmaj⟩ : ∃ doms₀ majorDom, doms = doms₀ ++ [majorDom] ∧
      List.Forall₂ (fun d d' => r.expr d = some d') (g.params ++ g.motives ++ g.minors ++
        insertBinders (s.families[o].indices.map (·.instL g.levels))
          (s.families.size + s.constructors.size)) doms₀ ∧
      r.expr (g.familyApp o (vars s.params.length
        (s.families.size + s.constructors.size + s.families[o].indices.length))
        (vars s.families[o].indices.length 0)) = some majorDom := by
    obtain ⟨doms₀, majorDom, rfl, h1, h2⟩ := forall₂_snoc_inv'' hrel
    refine ⟨doms₀, majorDom, rfl, h1, ?_⟩
    simpa [insertBinders] using h2
  refine ⟨doms₀, TbH, majorDom, rfl, ?_, ?_⟩
  · have := Lean4Lean.List.Forall₂.length_eq hpre
    rw [← this]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders]; omega
  · exact hmaj

end Lean4Lean.ShapeModel
