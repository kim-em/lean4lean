import Lean4Lean.Theory.Inductive.ProjectionProgramLemmas
import Lean4Lean.Theory.Typing.RestorationLevelCongruence

/-! Equivalent scoped universe packets preserve restored projection data,
including dependent binder scopes and specialized auxiliary heads. -/

namespace Lean4Lean.VEnv
open VExpr

theorem EqUpToLevels.closedN_iff (H : EqUpToLevels U e e') : e.ClosedN n ↔ e'.ClosedN n := by
  induction H generalizing n <;> simp_all [VExpr.ClosedN]

end Lean4Lean.VEnv
namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr VEnv

structure ProjectionData.LevelEquiv (U : Nat) (data data' : ProjectionData) : Prop where
  params : List.Forall₂ (EqUpToLevels U) data.params data'.params
  indices : List.Forall₂ (EqUpToLevels U) data.indices data'.indices
  fields : List.Forall₂ (EqUpToLevels U) data.fields data'.fields
  major : EqUpToLevels U data.major data'.major
  constructor : EqUpToLevels U data.constructor data'.constructor
  constructorIndices : List.Forall₂ (EqUpToLevels U) data.constructorIndices data'.constructorIndices

private theorem telescopeScoped_levels (H : List.Forall₂ (EqUpToLevels U) domains domains') :
    telescopeScoped n domains = telescopeScoped n domains' := by
  unfold telescopeScoped
  suffices ∀ i, (domains.zipIdx i).all (fun (d, j) => decide (d.ClosedN (n+j))) =
      (domains'.zipIdx i).all (fun (d, j) => decide (d.ClosedN (n+j))) from this 0
  intro i
  induction H generalizing i with
  | nil => rfl
  | cons h hs ih => simp [List.zipIdx_cons, h.closedN_iff, ih]

private theorem allScoped_levels (H : List.Forall₂ (EqUpToLevels U) domains domains') :
    domains.all (fun e => decide (e.ClosedN n)) = domains'.all (fun e => decide (e.ClosedN n)) := by
  induction H with
  | nil => rfl
  | cons h hs ih => simp [h.closedN_iff, ih]

private theorem restore_list_levels {r : Restoration} {input output : List VExpr}
    (hl : ∀ l ∈ levels, l.WF U) (hl' : ∀ l ∈ levels', l.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (H : input.mapM (fun e => r.expr (e.instL levels)) = some output) :
    ∃ output', input.mapM (fun e => r.expr (e.instL levels')) = some output' ∧
      List.Forall₂ (EqUpToLevels U) output output' := by
  induction input generalizing output with
  | nil => cases H; exact ⟨[], rfl, .nil⟩
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at H
    obtain ⟨out, ho, outs, hs, h⟩ := H
    cases h
    obtain ⟨out', ho', he'⟩ := r.expr_levels (EqUpToLevels.instL_expr e hl hl' he) ho
    obtain ⟨outs', hs', hes⟩ := ih hs
    exact ⟨out' :: outs', by simp [ho', hs'], .cons he' hes⟩

private theorem forall₂_append {R : α → β → Prop}
    (H : List.Forall₂ R a b) (H' : List.Forall₂ R a' b') :
    List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h hs ih => exact .cons h ih

private theorem vars_levels (n k : Nat) : List.Forall₂ (EqUpToLevels U) (vars n k) (vars n k) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .bvar)

/-- Every successful extraction transports to equivalent occurrence universes. -/
theorem projectionData_levels {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    (hl : ∀ l ∈ levels, l.WF U) (hl' : ∀ l ∈ levels', l.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (H : schema.projectionData owner levels = some data) :
    ∃ data', schema.projectionData owner levels' = some data' ∧ data.LevelEquiv U data' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  unfold projectionData at H ⊢
  simp only [← hlen]
  split at H <;> try contradiction
  rename_i hlevels
  rw [if_neg hlevels]
  split at H <;> try contradiction
  rename_i ctor hctor
  dsimp only at H ⊢
  split at H <;> try contradiction
  rename_i hindices
  rw [if_neg hindices]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨params, hp, indices, hi, fields, hf, cindices, hci,
    major, hm, constructor, hc, H⟩ := H
  split at H <;> try contradiction
  rename_i hscope
  cases H
  obtain ⟨params', hp', hep⟩ := restore_list_levels hl hl' he hp
  obtain ⟨indices', hi', hei⟩ := restore_list_levels hl hl' he hi
  obtain ⟨fields', hf', hef⟩ := restore_list_levels hl hl' he hf
  obtain ⟨cindices', hci', heci⟩ := restore_list_levels hl hl' he hci
  have hpLen := Lean4Lean.List.Forall₂.length_eq hep
  have hiLen := Lean4Lean.List.Forall₂.length_eq hei
  have hfLen := Lean4Lean.List.Forall₂.length_eq hef
  have hvarApp (name : Name) (args : List VExpr)
      (ha : List.Forall₂ (EqUpToLevels U) args args) :
      EqUpToLevels U (mkApps (.const name levels) args) (mkApps (.const name levels') args) :=
    EqUpToLevels.mkApps_args (.const hl hl' he) ha
  have hmEq : EqUpToLevels U
      (schema.signature.familyApp owner levels (vars params.length indices.length) (vars indices.length 0))
      (schema.signature.familyApp owner levels' (vars params.length indices.length) (vars indices.length 0)) := by
    apply hvarApp
    exact forall₂_append (vars_levels _ _) (vars_levels _ _)
  obtain ⟨major', hm', hem⟩ := schema.restoration.expr_levels hmEq hm
  obtain ⟨constructor', hc', hec⟩ := schema.restoration.expr_levels
    (hvarApp ctor.name _ (forall₂_append (vars_levels _ _) (vars_levels _ _))) hc
  simp only [bind, hp', hi', hf', hci', Option.bind_some, ← hpLen, ← hiLen, ← hfLen, hm', hc']
  have hscopeEq : (telescopeScoped 0 params' &&
      telescopeScoped params.length indices' && telescopeScoped params.length fields' &&
      decide (major'.ClosedN (params.length + indices.length)) &&
      decide (constructor'.ClosedN (params.length + fields.length)) &&
      cindices'.all (fun e => decide (e.ClosedN (params.length + fields.length)))) =
      (telescopeScoped 0 params &&
      telescopeScoped params.length indices && telescopeScoped params.length fields &&
      decide (major.ClosedN (params.length + indices.length)) &&
      decide (constructor.ClosedN (params.length + fields.length)) &&
      cindices.all (fun e => decide (e.ClosedN (params.length + fields.length)))) := by
    simp only [← telescopeScoped_levels hep, ← telescopeScoped_levels hei,
      ← telescopeScoped_levels hef, ← hem.closedN_iff, ← hec.closedN_iff,
      ← allScoped_levels heci]
  rw [hscopeEq]
  simp only [hscope]
  exact ⟨_, rfl, ⟨hep, hei, hef, hem, hec, heci⟩⟩

end Lean4Lean.InductiveSignature.CaseSchema
