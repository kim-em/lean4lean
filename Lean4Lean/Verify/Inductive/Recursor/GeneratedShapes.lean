import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas
/-! Generated ordinary recursor and iota shapes.

The operational shape contracts follow from the independent generator's
syntax. Constructor index arity is a separate formation consequence.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- An ordinary generated equation is headed by its owner recursor. -/
theorem Instance.equation_head {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    (g.equation index).lhs.stripLams.getAppFnArgs.1 =
      .const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars) := by
  apply Restoration.wrapLams_head_const (r := {})
    (fun _ h => by cases h) ?_ (Restoration.expr_empty (g.equation index).lhs)
  exact VExpr.getAppFnArgs_mkApps_head _ _

theorem vars_eq_bvarRange (n below : Nat) :
    vars n below = VExpr.bvarRange n (n + below) := by
  apply List.ext_getElem
  · simp [vars, VExpr.bvarRange]
  · intro i hi hi'
    simp [vars, VExpr.bvarRange] at hi hi' ⊢
    congr 1
    omega

/-- The generated telescope has exactly the major-family shape consumed by
the recursor reducer, with ordinary uniform constructor parameters. -/
theorem Instance.recursor_shape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) {env : VEnv}
    (hlookup : env.constants (g.recursorName owner) = some (g.recursor owner).toVConstant) :
    Nonempty (VRecursorShape env (g.recursorName owner) g.uvars s.params.length
      s.params.length s.families.size s.constructors.size s.families[owner].indices.length
      s.families[owner].name g.levels) := by
  let extra := s.families.size + s.constructors.size
  let indices := insertBinders (s.families[owner].indices.map (·.instL g.levels)) extra
  let major := g.familyApp owner
    (vars s.params.length (extra + indices.length)) (vars indices.length 0)
  let pre := g.params ++ g.motives ++ g.minors ++ indices
  have hindices : indices.length = s.families[owner].indices.length := by
    simp [indices, insertBinders]
  have hpre : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    simp [pre, Instance.params, Instance.motives, Instance.minors, hindices, Nat.add_assoc]
  refine ⟨{
    ctorParams_length := by simp
    ctorParams_closed := ?_
    type := g.recursorType owner
    const := hlookup
    doms := pre ++ [major]
    result := VExpr.mkApps
      (.bvar (indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars indices.length 1 ++ [.bvar 0])
    type_eq := rfl
    doms_length := by simp [hpre]
    major_eq := ?_ }⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
    simp only [List.mem_range] at hi
    change s.params.length - 1 - i < s.params.length
    omega
  · rw [← hpre]
    simp only [List.getElem?_concat_length]
    congr 1
    simp only [major, Instance.familyApp, InductiveSignature.familyApp,
      vars_eq_bvarRange, Nat.add_zero]
    rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
    congr 2 <;> simp [extra, hindices, Nat.add_assoc]

/-- Generation fixes the complete iota pattern; only family index arity and
installation of that exact equation are supplied separately. -/
theorem Instance.iota_shape {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) {env : VEnv}
    (hdef : env.defeqs (g.equation index))
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length) :
    Nonempty (VIotaRuleShape env (g.recursorName s.constructors[index].owner) g.uvars
      s.params.length s.params.length s.families.size s.constructors.size
      s.families[s.constructors[index].owner].indices.length s.constructors[index].name
      g.levels s.constructors[index].fields.length (g.equation index)) := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  have hdomains : domains.length = s.params.length + s.families.size + s.constructors.size + nf := by
    simp [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, nf, Nat.add_assoc]
  refine ⟨{
    defeq := hdef
    uvars := rfl
    doms := domains
    lhsBody := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
      (vars (s.params.length + extra) nf ++ indices ++ [major])
    rhsBody := VExpr.mkApps (.bvar (nf + s.constructors.size - 1 - index.val))
      (vars nf 0 ++ (recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r)
    typeBody := VExpr.mkApps (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
      (indices ++ [major])
    lhs_eq := rfl
    rhs_eq := rfl
    type_eq := rfl
    doms_length := hdomains
    indexArgs := indices
    indexArgs_length := by simpa [indices, ctor] using hindices
    lhs_pattern := ?_ }⟩
  simp only [hdomains, vars_eq_bvarRange, major, Instance.constructorApp, Nat.add_zero]
  rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
  simp [extra, nf, ctor, Nat.add_assoc]

end InductiveSignature
end Lean4Lean
