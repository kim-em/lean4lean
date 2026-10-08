import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.EnvTables.EnvSigSyntax
import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.EnvTables.EnvSigCtor
import Lean4Lean.Theory.Typing.NativeConstructorRigidity

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

namespace Lean4Lean.EnvTables
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

end Lean4Lean.EnvTables
