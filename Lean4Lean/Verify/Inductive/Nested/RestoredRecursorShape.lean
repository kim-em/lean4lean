import Lean4Lean.Verify.Inductive.Recursor.GeneratedShapes
import Lean4Lean.Verify.Inductive.Recursor.RestoredRealization
import Lean4Lean.Verify.Environment.RecursorAlignment
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.CaseReduction

namespace Lean4Lean
namespace InductiveSignature

theorem Restoration.expr_eq_go (r : Restoration) (e : VExpr) :
    r.expr e = Restoration.expr.go r e [] := rfl

theorem Restoration.go_mkApps (r : Restoration) (f : VExpr) (args acc : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps f args) acc =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f (args' ++ acc) := by
  induction args generalizing f acc with
  | nil => simp [VExpr.mkApps]
  | cons a as ih =>
    have hm : VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as := rfl
    rw [hm, ih]
    simp only [Restoration.expr.go, List.mapM_cons]
    cases ha : Restoration.expr.go r a [] <;>
      cases has : as.mapM r.expr <;> simp [ha, Restoration.expr_eq_go]

theorem Restoration.expr_mkApps (r : Restoration) (f : VExpr) (args : List VExpr) :
    r.expr (VExpr.mkApps f args) =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f args' := by
  simp [Restoration.expr_eq_go, Restoration.go_mkApps]

@[simp] theorem Restoration.expr_bvar (r : Restoration) (i : Nat) :
    r.expr (.bvar i) = some (.bvar i) := rfl

@[simp] theorem Restoration.expr_sort (r : Restoration) (u : VLevel) :
    r.expr (.sort u) = some (.sort u) := rfl

theorem Restoration.mapM_expr_bvars (r : Restoration) (l : List VExpr)
    (hl : ∀ e ∈ l, ∃ i, e = .bvar i) : l.mapM r.expr = some l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rcases hl a (by simp) with ⟨i, rfl⟩
    simp [List.mapM_cons, ih (fun e he => hl e (by simp [he]))]

theorem Restoration.mapM_expr_vars (r : Restoration) (n below : Nat) :
    (vars n below).mapM r.expr = some (vars n below) :=
  r.mapM_expr_bvars _ (by simp [vars])

theorem Restoration.expr_mkApps_bvar (r : Restoration) (i : Nat) (args : List VExpr) :
    r.expr (VExpr.mkApps (.bvar i) args) =
      (args.mapM r.expr).map (VExpr.mkApps (.bvar i)) := by
  rw [r.expr_mkApps]
  cases args.mapM r.expr <;> rfl

/-- Restoration commutes with a `forallE` telescope. -/
theorem Restoration.expr_wrapForalls (r : Restoration) (doms : List VExpr) (body : VExpr) :
    r.expr (VExpr.wrapForalls doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapForalls doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapForalls, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.forallE d (VExpr.wrapForalls ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapForalls]

/-! The generator's recursor type, split into prefix, major and body. -/

/-- Parameters, motives, minors, and indices of the generated recursor telescope. -/
def Instance.recursorPrefix {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)

/-- The generated major domain: the owner family at the parameter and index variables. -/
def Instance.recursorMajor {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  g.familyApp owner
    (vars s.params.length
      (s.families.size + s.constructors.size + s.families[owner].indices.length))
    (vars s.families[owner].indices.length 0)

/-- The generated motive application ending the recursor telescope. -/
def Instance.recursorBody {s : InductiveSignature} (_g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps
    (.bvar (s.families[owner].indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val)))
    (vars s.families[owner].indices.length 1 ++ [.bvar 0])

theorem Instance.recursorType_eq {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    g.recursorType owner =
      VExpr.wrapForalls (g.recursorPrefix owner ++ [g.recursorMajor owner])
        (g.recursorBody owner) := by
  simp [Instance.recursorType, Instance.recursorPrefix, Instance.recursorMajor,
    Instance.recursorBody, insertBinders]

theorem Instance.recursorPrefix_length {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    (g.recursorPrefix owner).length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
  simp [Instance.recursorPrefix, Instance.params, Instance.motives, Instance.minors,
    insertBinders, Nat.add_assoc]

/-- The motive application is restored to itself. -/
theorem Restoration.expr_recursorBody (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) :
    r.expr (g.recursorBody owner) = some (g.recursorBody owner) := by
  rw [Instance.recursorBody, r.expr_mkApps_bvar,
    r.mapM_expr_bvars _ (by
      simp only [vars, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range,
        List.mem_singleton]
      rintro e (⟨a, _, rfl⟩ | rfl) <;> exact ⟨_, rfl⟩)]
  rfl

/-- Restoring the generator's recursor type restores each telescope domain
separately; the motive application is unchanged. -/
theorem Restoration.expr_recursorType (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) :
    r.expr (g.recursorType owner) =
      ((g.recursorPrefix owner).mapM r.expr).bind fun pre =>
        (r.expr (g.recursorMajor owner)).map fun major =>
          VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner) := by
  rw [g.recursorType_eq, r.expr_wrapForalls, r.expr_recursorBody, List.mapM_append]
  cases hp : (g.recursorPrefix owner).mapM r.expr <;>
    cases hm : r.expr (g.recursorMajor owner) <;> simp [hm]

theorem Restoration.expr_recursorType_eq_some (r : Restoration) {s : InductiveSignature}
    {g : Instance s} {owner : Fin s.families.size} {type : VExpr}
    (h : r.expr (g.recursorType owner) = some type) :
    ∃ pre major, (g.recursorPrefix owner).mapM r.expr = some pre ∧
      r.expr (g.recursorMajor owner) = some major ∧
      type = VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner) := by
  rw [r.expr_recursorType] at h
  cases hp : (g.recursorPrefix owner).mapM r.expr <;>
    cases hm : r.expr (g.recursorMajor owner) <;> simp [hp, hm] at h
  exact ⟨_, _, rfl, rfl, by simpa using h.symm⟩

/-! The restored major domain, in the source and auxiliary cases. -/

/-- Instantiating a scoped template at the parameter variables beneath `below`
further binders lifts it past those binders. -/
theorem instantiateParams_vars {e : VExpr} {n : Nat} (he : e.ClosedN n) (below : Nat) :
    instantiateParams e (vars n below) = e.liftN below := by
  change e.subst (VExpr.Subst.ofList (vars n below)) = _
  rw [VExpr.liftN_eq_subst]
  apply VExpr.subst_congr_closedN he
  intro i hi
  simp only [VExpr.Subst.ofList, VExpr.Subst.shift, vars, List.length_map, List.length_reverse,
    List.length_range, hi, dite_true, List.getElem_map, List.getElem_reverse, List.getElem_range]
  congr 1
  omega

theorem Restoration.expr_recursorMajor_source (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size)
    (hfind : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) = none)
    (hname : r.recursorName s.families[owner].name = s.families[owner].name) :
    r.expr (g.recursorMajor owner) = some (g.recursorMajor owner) := by
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
  simp only [Fin.getElem_fin] at hfind hname
  simp [Restoration.expr.go, hfind, hname]

theorem Restoration.expr_recursorMajor_auxiliary (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) {h : HeadSpecialization}
    (hfind : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) = some h)
    (hlevels : g.levels.length = h.uvars) (hnparams : h.nparams = s.params.length)
    (hclosed : ∀ arg ∈ h.arguments, arg.ClosedN h.nparams) :
    r.expr (g.recursorMajor owner) =
      some (VExpr.mkApps (.const h.target (h.levels.map (·.inst g.levels)))
        (h.arguments.map (fun arg => (arg.instL g.levels).liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0)) := by
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
  have hlen : (vars s.params.length
      (s.families.size + s.constructors.size + s.families[owner].indices.length)).length =
      h.nparams := by simp [vars, hnparams]
  simp only [Fin.getElem_fin] at hfind hlen ⊢
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Restoration.expr.go, hfind,
    HeadSpecialization.apply, hlevels, bne_self_eq_false, List.length_append, Bool.false_or]
  rw [if_neg (by simp; omega), List.take_left' hlen, List.drop_left' hlen]
  congr 3
  apply List.map_congr_left
  intro arg harg
  rw [← hnparams]
  exact instantiateParams_vars (hclosed arg harg).instL _

/-! The recursor shape contract for a restored recursor. -/

/-- Exactly the facts about a restored recursor that fix its `VRecursorShape`:
its stored abstract constant is the restored generated type, its counts are the
expanded signature's, it is not K-like, and its major family application is the
restored owner family at the parameter and index variables
(`RestoredRecursorRealization.specialization`). Rules are not involved. -/
structure RestoredRecursorShapeInputs {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (venv : VEnv) (owner : Fin s.families.size)
    (rec : Lean.RecursorVal) : Prop where
  type : ∃ type, r.expr (g.recursorType owner) = some type ∧
    venv.constants rec.name = some ⟨rec.levelParams.length, type⟩
  numParams : rec.numParams = s.params.length
  numIndices : rec.numIndices = s.families[owner].indices.length
  numMotives : rec.numMotives = s.families.size
  numMinors : rec.numMinors = s.constructors.size
  k : rec.k = false
  specialization : ∃ head : RestoredFamilyHead,
    rec.getMajorInduct = head.name ∧
    (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
    r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0))

/-- The abstract constant installed for a restored recursor entry is the
restored generated type at the concrete recursor's name and universe arity. -/
theorem restoredRecursor_constant {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hvalue : r.recursor (g.recursor owner) = some value)
    (hconst : venv.constants value.name = some value.toVConstant)
    (hname : rec.name = r.recursorName (g.recursorName owner))
    (huvars : rec.levelParams.length = g.uvars) :
    ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩ := by
  simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hvalue
  cases ht : r.expr (g.recursor owner).type with
  | none => simp [ht] at hvalue
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at hvalue
    subst hvalue
    refine ⟨type, ht, ?_⟩
    rw [hname, huvars]
    exact hconst

/-- A recursor of a block with more than one family is not K-like. -/
theorem RestoredRecursorRealization.k_eq_false {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {sourceNames : List Name} {venv : VEnv}
    {owner : Fin s.families.size} {rec : Lean.RecursorVal}
    (H : RestoredRecursorRealization g r sourceNames venv owner rec)
    (hfamilies : 1 < s.families.size) : rec.k = false := by
  cases hk : rec.k with
  | false => rfl
  | true => have := (H.k hk).1; omega

/-- The realization of a restored recursor supplies the shape inputs, given its
installed abstract constant and the absence of K. -/
theorem RestoredRecursorRealization.shapeInputs {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {sourceNames : List Name} {venv : VEnv}
    {owner : Fin s.families.size} {rec : Lean.RecursorVal}
    (H : RestoredRecursorRealization g r sourceNames venv owner rec)
    (hconst : ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩)
    (hk : rec.k = false) :
    RestoredRecursorShapeInputs g r venv owner rec where
  type := hconst
  numParams := H.numParams
  numIndices := H.numIndices
  numMotives := H.numMotives
  numMinors := H.numMinors
  k := hk
  specialization := by
    rcases H.specialization with ⟨head, _, hmajor, _, hargs, happ, _⟩
    exact ⟨head, hmajor, hargs, happ⟩

/-- The restored recursor's stored type has the recursor shape, with the
restored family head's arguments as constructor parameters. -/
theorem RestoredRecursorShapeInputs.shape {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShapeInputs g r venv owner rec) :
    ∃ head : RestoredFamilyHead, rec.getMajorInduct = head.name ∧
      Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams
        head.arguments.length rec.numMotives rec.numMinors rec.numIndices
        rec.getMajorInduct head.levels head.arguments) := by
  rcases H.type with ⟨type, htype, hconst⟩
  rcases H.specialization with ⟨head, hmajor, hargs, happ⟩
  rcases r.expr_recursorType_eq_some htype with ⟨pre, major, hpre, hm, rfl⟩
  have hprelen : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hmaj : major = VExpr.mkApps (.const head.name head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
        vars s.families[owner].indices.length 0) := by
    have := hm.symm.trans happ
    exact Option.some.inj this
  refine ⟨head, hmajor, ⟨{
    ctorParams_length := rfl
    ctorParams_closed := by rw [H.numParams]; exact hargs
    type := _
    const := hconst
    doms := pre ++ [major]
    result := g.recursorBody owner
    type_eq := rfl
    doms_length := by
      simp [hprelen, H.numParams, H.numMotives, H.numMinors, H.numIndices]
    major_eq := ?_ }⟩⟩
  rw [H.numParams, H.numMotives, H.numMinors, H.numIndices, ← hprelen,
    List.getElem?_concat_length, hmaj, ← hmajor, vars_eq_bvarRange, Nat.add_zero]

/-- The rule-free copy of a restored recursor is aligned. -/
theorem RestoredRecursorShapeInputs.alignmentCore {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShapeInputs g r venv owner rec) :
    RecursorAlignmentCore venv { rec with rules := [] } := by
  rcases H.shape with ⟨head, _, hshape⟩
  exact ⟨head.arguments.length, head.levels, head.arguments, hshape, by simp⟩

/-- The rule-free copy of a restored recursor is not K-like. -/
theorem RestoredRecursorShapeInputs.kLike {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShapeInputs g r venv owner rec)
    (C : Lean.ConstMap) : KLikeRecursor C venv { rec with rules := [] } := by
  intro hk
  have : rec.k = true := hk
  rw [H.k] at this
  cases this

/-- The recursor-shape and K clauses of `finalValidOfStaged_of_shapes`'s
`Hshapes` for a restored recursor's rule-free copy. -/
theorem RestoredRecursorShapeInputs.strippedShapes {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShapeInputs g r venv owner rec)
    (C : Lean.ConstMap) :
    RecursorAlignmentCore venv { rec with rules := [] } ∧
      KLikeRecursor C venv { rec with rules := [] } :=
  ⟨H.alignmentCore, H.kLike C⟩
