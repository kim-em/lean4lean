import Lean4Lean.Theory.Inductive.ProjectionUniverseNaturality
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.CaseReduction
import Batteries.Tactic.OpenPrivate

/-! Completeness of the scope checks for original singleton projection data.
Only raw well-scoped normalized types are used here. Constructor-index arity
is a separate structural obligation; no uniqueness-of-typing theorem enters
this parser proof. -/
namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr VEnv
open private vars_closed from Lean4Lean.Theory.Inductive.ProjectionProgram
set_option backward.isDefEq.respectTransparency false

private theorem telescope_scope {domains : List VExpr} {result : VExpr}
    (closed : (wrapForalls domains result).ClosedN count) :
    (∀ i (hi : i < domains.length), domains[i].ClosedN (count + i)) ∧
      result.ClosedN (count + domains.length) := by
  induction domains generalizing count with
  | nil => exact ⟨by intro i hi; simp at hi, closed⟩
  | cons domain domains ih =>
    obtain ⟨scopes, body⟩ := ih closed.2
    refine ⟨?_, by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using body⟩
    intro i hi
    cases i with
    | zero => exact closed.1
    | succ i =>
      simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm 1] using scopes i (by simpa using hi)

theorem projectionData_of_closed
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {ctor : Constructor schema.signature.families.size} {levels : List VLevel}
    (identity : schema.restoration = {})
    (length : levels.length = schema.signature.uvars)
    (unique : schema.signature.constructors.toList.filter (fun c => c.owner == owner) = [ctor])
    (arity : ctor.indices.length = schema.signature.families[owner].indices.length)
    (familyClosed : (wrapForalls (schema.signature.params ++ schema.signature.families[owner].indices)
      (.sort schema.signature.families[owner].resultLevel)).Closed)
    (constructorClosed : (schema.signature.constructorType ctor).Closed) :
    ∃ source, schema.projectionData owner levels = some source := by
  obtain ⟨familyScopes, _⟩ := telescope_scope familyClosed
  obtain ⟨constructorScopes, resultScope⟩ := telescope_scope constructorClosed
  have params : telescopeScoped 0 (schema.signature.params.map (·.instL levels)) = true := by
    apply telescopeScoped_instL
    apply telescopeScoped_iff.mpr
    intro i hi
    have h := familyScopes i (by simp only [List.length_append]; omega)
    rw [List.getElem_append_left hi] at h
    exact h
  have indices : telescopeScoped schema.signature.params.length
      (schema.signature.families[owner].indices.map (·.instL levels)) = true := by
    apply telescopeScoped_instL
    apply telescopeScoped_iff.mpr
    intro i hi
    have h := familyScopes (schema.signature.params.length + i) (by simp only [List.length_append]; omega)
    rw [List.getElem_append_right (by omega)] at h
    simpa only [Nat.zero_add, Nat.add_sub_cancel_left] using h
  have fields : telescopeScoped schema.signature.params.length
      ((schema.signature.fieldTypes ctor).map (·.instL levels)) = true := by
    apply telescopeScoped_instL
    apply telescopeScoped_iff.mpr
    intro i hi
    have h := constructorScopes (schema.signature.params.length + i) (by simp only [List.length_append]; omega)
    rw [List.getElem_append_right (by omega)] at h
    simpa only [Nat.zero_add, Nat.add_sub_cancel_left] using h
  have constructorIndices : ∀ e ∈ ctor.indices.map (·.instL levels),
      e.ClosedN (schema.signature.params.length + (schema.signature.fieldTypes ctor).length) := by
    intro e member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    apply ClosedN.instL
    exact ClosedN.of_mkApps_arg (by simpa only [Nat.zero_add, List.length_append, familyApp] using resultScope)
      original (List.mem_append_right _ originalMember)
  have major : (schema.signature.familyApp owner levels
      (vars schema.signature.params.length schema.signature.families[owner].indices.length)
      (vars schema.signature.families[owner].indices.length 0)).ClosedN
      (schema.signature.params.length + schema.signature.families[owner].indices.length) := by
    exact ClosedN.mkApps_closed trivial
      (List.forall_mem_append.mpr ⟨vars_closed (by omega), vars_closed (by omega)⟩)
  have constructor : (mkApps (.const ctor.name levels)
      (vars schema.signature.params.length (schema.signature.fieldTypes ctor).length ++
        vars (schema.signature.fieldTypes ctor).length 0)).ClosedN
      (schema.signature.params.length + (schema.signature.fieldTypes ctor).length) :=
    ClosedN.mkApps_closed trivial
      (List.forall_mem_append.mpr ⟨vars_closed (by omega), vars_closed (by omega)⟩)
  have mapSome (expressions : List VExpr) :
      expressions.mapM (fun e => some (e.instL levels)) =
        some (expressions.map (·.instL levels)) := by
    induction expressions with
    | nil => rfl
    | cons e rest ih => simp only [List.mapM_cons, ih]; rfl
  unfold projectionData
  simp only [length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, unique, arity,
    identity, Restoration.expr_empty, mapSome, bind, Option.bind_some, List.length_map]
  simp only [params, indices, fields, major, constructor, decide_true,
    List.all_eq_true.mpr (fun e h => decide_eq_true (constructorIndices e h))]
  exact ⟨_, rfl⟩

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature
open VExpr VEnv

/-- Original normalized family and constructor types are closed by raw
typing in their actual base and header environments. This needs ordered
environments only, independently of injectivity or uniqueness of typing. -/
theorem Models.projectionTypes_closed_at
    {s : InductiveSignature} {base : VEnv} {decl : VInductDecl}
    (model : s.Models base decl) (ordered : checkingBase.Ordered)
    (source : decl.SourceWF base) (below : base ≤ checkingBase)
    (added : checkingBase.addConstVals decl.typeConstants = some checkingHeaders)
    (owner : Fin s.families.size)
    (index : Fin s.constructors.size) :
    (wrapForalls (s.params ++ s.families[owner].indices)
      (.sort s.families[owner].resultLevel)).Closed ∧
      (s.constructorType s.constructors[index]).Closed := by
  obtain ⟨_, _, _, _, headers, _, installed, _, headerTypes, _⟩ := source
  have headerOrdered : checkingHeaders.Ordered := ordered.addConstVals (by
    intro constant member
    obtain ⟨family, familyMember, rfl⟩ := List.mem_map.mp member
    exact (headerTypes family familyMember).mono below) added
  obtain ⟨_, _, _, _, _, _, ⟨_, familyEqual⟩, _⟩ := model.family owner
  obtain ⟨_, _, _, _, ⟨_, constructorEqual⟩⟩ := model.constructor index installed
  exact ⟨VExpr.WF.closedN ordered ⟨_, familyEqual.hasType.1.mono below⟩ trivial,
    VExpr.WF.closedN headerOrdered
      ⟨_, constructorEqual.hasType.1.mono (VEnv.addConstVals_mono below installed added)⟩ trivial⟩

/-- Specialization to the original checking base. -/
theorem Models.projectionTypes_closed
    {s : InductiveSignature} {base : VEnv} {decl : VInductDecl}
    (model : s.Models base decl) (ordered : base.Ordered)
    (source : decl.SourceWF base) (owner : Fin s.families.size)
    (index : Fin s.constructors.size) :
    (wrapForalls (s.params ++ s.families[owner].indices)
      (.sort s.families[owner].resultLevel)).Closed ∧
      (s.constructorType s.constructors[index]).Closed := by
  obtain ⟨headers, added, _⟩ := source.originalConstructors
  exact model.projectionTypes_closed_at ordered source .rfl added owner index

/-- A real singleton model passes every projection-data parser check.
The index count is retained from normalization, independently of typing
uniqueness. The original raw typings supply all scope checks. -/
theorem Models.projectionData_exists_at
    {schema : CaseSchema} {base : VEnv} {decl : VInductDecl}
    (model : schema.signature.Models base decl) (ordered : checkingBase.Ordered)
    (source : decl.SourceWF base) (below : base ≤ checkingBase)
    (added : checkingBase.addConstVals decl.typeConstants = some checkingHeaders)
    (identity : schema.restoration = {})
    {owner : Fin schema.signature.families.size}
    (single : schema.signature.constructors.size ≤ 1)
    (index : Fin schema.signature.constructors.size)
    (owner_eq : schema.signature.constructors[index].owner = owner)
    {levels : List VLevel} (length : levels.length = schema.signature.uvars) :
    ∃ data, schema.projectionData owner levels = some data := by
  have count : schema.signature.constructors.toList.length = 1 := by
    have positive := index.isLt
    simp only [Array.length_toList]
    omega
  obtain ⟨ctor, list⟩ := List.length_eq_one_iff.mp count
  have member : schema.signature.constructors[index] ∈ schema.signature.constructors.toList :=
    List.getElem_mem (l := schema.signature.constructors.toList) index.isLt
  have same : schema.signature.constructors[index] = ctor := by
    simpa only [list, List.mem_singleton] using member
  have unique : schema.signature.constructors.toList.filter (fun c => c.owner == owner) =
      [schema.signature.constructors[index]] := by
    rw [list, ← same]
    simp only [owner_eq, beq_self_eq_true, List.filter_cons_of_pos, List.filter_nil]
  have arity := model.constructorArity _ member
  have arity' : schema.signature.constructors[index].indices.length =
      schema.signature.families[owner].indices.length := by
    simpa only [owner_eq] using arity
  obtain ⟨familyClosed, constructorClosed⟩ := model.projectionTypes_closed_at ordered source below added owner index
  exact CaseSchema.projectionData_of_closed identity length unique arity' familyClosed constructorClosed

/-- Original-base specialization; replayed compilations use the actual later
header installation through `projectionData_exists_at`. -/
theorem Models.projectionData_exists
    {schema : CaseSchema} {base : VEnv} {decl : VInductDecl}
    (model : schema.signature.Models base decl) (ordered : base.Ordered)
    (source : decl.SourceWF base)
    (identity : schema.restoration = {})
    {owner : Fin schema.signature.families.size}
    (single : schema.signature.constructors.size ≤ 1)
    (index : Fin schema.signature.constructors.size)
    (owner_eq : schema.signature.constructors[index].owner = owner)
    {levels : List VLevel} (length : levels.length = schema.signature.uvars) :
    ∃ data, schema.projectionData owner levels = some data := by
  obtain ⟨headers, added, _⟩ := source.originalConstructors
  exact model.projectionData_exists_at ordered source .rfl added identity single index owner_eq length

end Lean4Lean.InductiveSignature
