import Lean4Lean.Theory.Typing.ProjectionCornerNonempty
import Lean4Lean.Theory.Typing.ProjectionCornerSubst
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness

/-! # The case eliminator of a registered structure, in ordinary form

A registered case schema types `.elim key owner (target :: levels)` at the restoration of the
recursor type of its one-family view. For the family of a structure (one constructor, no
indices), this restored type is the ordinary recursor type of the one-constructor signature
`caseView` whose parameters and field domains are the restored ones. -/

namespace Lean4Lean
namespace InductiveSignature

theorem Restoration.expr_mkApps_const_fixed (r : Restoration) {n : Name} {ls : List VLevel}
    {args : List VExpr}
    (hf : r.heads.find? (fun h => h.auxiliary == n) = none) (hn : r.recursorName n = n)
    (hargs : ∀ e ∈ args, ∃ i, e = .bvar i) :
    r.expr (VExpr.mkApps (.const n ls) args) = some (VExpr.mkApps (.const n ls) args) := by
  rw [r.expr_mkApps, r.mapM_expr_bvars _ hargs]
  simp [Restoration.expr.go, hf, hn]

theorem fieldTypes_external (s : InductiveSignature) {c : Constructor s.families.size}
    {l : List VExpr} (h : c.fields = l.map Field.external) : s.fieldTypes c = l := by
  simp only [fieldTypes, h]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, fieldType]

namespace CaseSchema
variable {schema : CaseSchema} {owner : Fin schema.signature.families.size}

theorem view_fieldTypes_case (c : Constructor schema.signature.families.size) :
    (schema.view owner).fieldTypes (schema.caseConstructor c) = schema.signature.fieldTypes c :=
  fieldTypes_external _ rfl

theorem caseConstructor_recursiveFields (c : Constructor schema.signature.families.size) :
    Instance.recursiveFields (s := schema.view owner) (schema.caseConstructor c) = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  change field ∈ (schema.signature.fieldTypes c).map Field.external at hfield
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hfield
  rfl

end CaseSchema

end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

private theorem insertBinders_len (F : List VExpr) (e : Nat) :
    (insertBinders F e).length = F.length := by simp [insertBinders]

private theorem insertBinders_get (F : List VExpr) (e i : Nat)
    (hi : i < (insertBinders F e).length) :
    (insertBinders F e)[i] = (F[i]'(by simpa [insertBinders_len] using hi)).liftN e i := by
  simp [insertBinders, List.getElem_zipIdx]

private theorem insertBinders_liftN' (F X P : List VExpr) (e : Nat) (hX : X.length = e) :
    ∀ i, i ≤ F.length → Ctx.LiftN e i ((F.take i).reverse ++ P)
      (((insertBinders F e).take i).reverse ++ X ++ P)
  | 0, _ => by simpa using Ctx.LiftN.zero (Γ := P) X hX
  | i + 1, hi => by
    have h1 := insertBinders_liftN' F X P e hX i (by omega)
    have hiF : i < F.length := by omega
    have e1 : (F.take (i + 1)).reverse ++ P = F[i] :: ((F.take i).reverse ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hiF, Option.toList_some,
        List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append]
    have e2 : ((insertBinders F e).take (i + 1)).reverse ++ X ++ P =
        F[i].liftN e i :: (((insertBinders F e).take i).reverse ++ X ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (show i < (insertBinders F e).length by
        rw [insertBinders_len]; omega), insertBinders_get]
      simp
    rw [e1, e2]
    exact .succ h1

/-- Inserting well-typed binders into a well-formed context below a telescope. -/
theorem OnCtx.insert_binders (henv : env.Ordered) {F X Γ : List VExpr}
    (hF : OnCtx (F.reverse ++ Γ) (env.IsType U)) (hX : OnCtx (X ++ Γ) (env.IsType U)) :
    OnCtx ((insertBinders F X.length).reverse ++ X ++ Γ) (env.IsType U) := by
  suffices h : ∀ i, i ≤ F.length →
      OnCtx (((insertBinders F X.length).take i).reverse ++ X ++ Γ) (env.IsType U) by
    have := h F.length (Nat.le_refl _)
    rwa [List.take_of_length_le (by rw [insertBinders_len]; exact Nat.le_refl _)] at this
  intro i
  induction i with
  | zero => intro _; simpa using hX
  | succ i ih =>
    intro hi
    have hiF : i < F.length := by omega
    have e2 : ((insertBinders F X.length).take (i + 1)).reverse ++ X ++ Γ =
        F[i].liftN X.length i :: (((insertBinders F X.length).take i).reverse ++ X ++ Γ) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (show i < (insertBinders F X.length).length by
        rw [insertBinders_len]; omega), insertBinders_get]
      simp
    rw [e2]
    refine ⟨ih (by omega), ?_⟩
    have hdom : env.IsType U ((F.take i).reverse ++ Γ) F[i] := by
      have h := hF
      rw [← List.take_append_drop (i + 1) F, List.reverse_append, List.append_assoc] at h
      have h' := OnCtx.of_append h
      rw [List.take_add_one, List.getElem?_eq_getElem hiF, Option.toList_some,
        List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons_append] at h'
      exact h'.2
    exact hdom.weakN henv (insertBinders_liftN' F X Γ X.length rfl i (by omega))

/-- A telescope over a well-formed context with a typed body is a type. -/
theorem IsType.wrapForalls_of :
    ∀ {doms Γ : List VExpr} {body : VExpr},
      OnCtx (doms.reverse ++ Γ) (env.IsType U) → env.IsType U (doms.reverse ++ Γ) body →
      env.IsType U Γ (VExpr.wrapForalls doms body)
  | [], _, _, _, hb => by simpa [VExpr.wrapForalls] using hb
  | d :: ds, Γ, body, hctx, hb => by
    have hctx' : OnCtx (ds.reverse ++ d :: Γ) (env.IsType U) := by simpa using hctx
    have hb' : env.IsType U (ds.reverse ++ d :: Γ) body := by simpa using hb
    have hd : env.IsType U Γ d := (OnCtx.of_append hctx').2
    exact IsType.forallE hd (IsType.wrapForalls_of hctx' hb')

end VEnv
end Lean4Lean
