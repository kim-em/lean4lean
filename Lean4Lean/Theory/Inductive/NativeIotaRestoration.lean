import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Inductive.ConstructorArity
import Lean4Lean.Theory.Inductive.HypothesisTyping
import Lean4Lean.Theory.Inductive.Normalization
import Lean4Lean.Theory.Inductive.ProjectionProgram
import Lean4Lean.Theory.Inductive.RawShape
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.RestorationDefEq
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.SourceModelNames
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.CaseMotiveCoherence
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ConstantHeaderProvenance
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.NativeCaptureTransport
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.ProjectionProgramTyping
import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VLevel

/-! # Restoration and recursor-shape facts used by native iota soundness

These lemmas were proved alongside the executable verification of nested inductive
declarations, under `Lean4Lean/Verify/Inductive`. `Theory/Typing/NativeIotaSoundness.lean`
needs them, so they live here, in the Theory layer. No `Lean4Lean.Theory` module imports a
`Lean4Lean.Verify` module. The proofs are unchanged. -/

-- from Lean4Lean/Verify/Inductive/Recursor/GeneratedShapes.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem vars_eq_bvarRange (n below : Nat) :
    vars n below = VExpr.bvarRange n (n + below) := by
  apply List.ext_getElem
  · simp [vars, VExpr.bvarRange]
  · intro i hi hi'
    simp [vars, VExpr.bvarRange] at hi hi' ⊢
    congr 1
    omega
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Basic.lean
namespace Lean4Lean
namespace VerifyInductive
open InductiveSignature

theorem VExpr.getAppFnArgs_mkApps
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs =
      let (head, prior) := fn.getAppFnArgs
      (head, prior ++ args) := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args from rfl, ih]
      simp [List.append_assoc]
end VerifyInductive
end Lean4Lean

-- from Lean4Lean/Verify/Environment/Basic.lean
namespace Lean4Lean
open InductiveSignature

theorem VInductBlock.install_le
    (H : VInductBlock.install env block = some env') : env ≤ env' := by
  unfold VInductBlock.install at H
  cases htypes : env.addConstVals block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConstVals block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : (envCtors.addProjections block.projections).addConstVals
          block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        exact (VEnv.addConstVals_le htypes).trans <|
          (VEnv.addConstVals_le hctors).trans <|
            VEnv.addProjections_le.trans <|
              (VEnv.addConstVals_le hrecursors).trans VEnv.addDefEqRules_le
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/EliminatorAvoidance.lean
namespace Lean4Lean
open InductiveSignature

theorem CompiledInductive.types_ctors {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    block.types = source.typeConstants ∧ block.ctors = source.constructorConstants := by
  induction H using CompiledInductive.rec
    (motive_2 := fun _ _ _ => True) with
  | intro h _ _ => exact ⟨h.types, h.ctors⟩
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ => trivial
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/EliminatorAvoidance.lean
namespace Lean4Lean
open InductiveSignature

theorem VInductBlock.install_constants {env installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some installed) :
    ∀ v ∈ block.types ++ block.ctors, installed.constants v.name = some v.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  have hle : ctors ≤ (recs.addDefEqRules block.rules) :=
    VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hle.constants ((VEnv.addConstVals_le hc).constants (VEnv.addConstVals_get ht hv))
  · exact hle.constants (VEnv.addConstVals_get hc hv)
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestorationCommutation.lean
namespace Lean4Lean.InductiveSignature
open InductiveSignature

/-- Names on which `Restoration.expr` acts nontrivially. -/
def Restoration.restorableNames (r : Restoration) : List Name :=
  r.heads.map (·.auxiliary) ++ r.recursors.map Prod.fst
end Lean4Lean.InductiveSignature

-- from Lean4Lean/Verify/Inductive/Nested/RestorationCommutation.lean
namespace Lean4Lean.InductiveSignature
open InductiveSignature

theorem Restoration.heads_find?_eq_none {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) :
    r.heads.find? (fun h => h.auxiliary == name) = none := by
  apply List.find?_eq_none.mpr
  intro head hmem heq
  exact h (List.mem_map.mpr ⟨head, hmem, by simpa using heq⟩)
end Lean4Lean.InductiveSignature

-- from Lean4Lean/Verify/Inductive/Recursor/RestoredRealization.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- The constant head and parameters remaining after a family specialization
is restored. `arguments` is scoped under the recursor's common parameters,
not under the prior container's parameter telescope. -/
structure RestoredFamilyHead where
  name : Name
  levels : List VLevel
  arguments : List VExpr
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Recursor/RestoredRealization.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Constructor restoration follows the same specialization table as the
family restoration. The table is generated by `compilationRestoration`. -/
def Restoration.restoredHeadName (r : Restoration) (name : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.target
  | none => name
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Recursor/RestoredRealization.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Read the restored family application with the actual common parameters.
Failure remains explicit, including a partial auxiliary application. -/
def Instance.restoredFamilyHead {s : InductiveSignature}
    (g : Instance s) (r : Restoration) (owner : Fin s.families.size) :
    Option RestoredFamilyHead := do
  let application ← r.expr (g.familyApp owner (vars s.params.length 0) [])
  let (.const name levels, arguments) := application.getAppFnArgs | none
  return { name, levels, arguments }
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoringExpansion.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

private theorem specialization_liftN' {h : HeadSpecialization}
    (hc : ∀ e ∈ h.arguments, e.ClosedN h.nparams) (levels : List VLevel)
    (args : List VExpr) (n k : Nat) :
    (h.apply levels args).map (·.liftN n k) =
      h.apply levels (args.map (·.liftN n k)) := by
  unfold HeadSpecialization.apply
  simp only [List.length_map]
  split
  · rfl
  · rename_i hgood
    have hlen : h.nparams ≤ args.length := by
      apply Nat.le_of_not_gt
      intro ht
      simp [ht] at hgood
    simp only [Option.pure_def, Option.map_some, VExpr.liftN_mkApps, VExpr.liftN,
      List.map_append, List.map_map, Function.comp_def, List.map_drop]
    congr 2
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro e he
    rw [← List.map_take]
    apply VEnv.instantiateParams_liftN
    simpa only [List.length_take, Nat.min_eq_left hlen] using (hc e he).instL
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoringExpansion.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Restoration commutes with lifting when every head's specialization
arguments are scoped by its parameters. -/
theorem Restoration.expr_liftN (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (e : VExpr) (n k : Nat) :
    (r.expr e).map (·.liftN n k) = r.expr (e.liftN n k) := by
  suffices ∀ args, (Restoration.expr.go r e args).map (·.liftN n k) =
      Restoration.expr.go r (e.liftN n k) (args.map (·.liftN n k)) from this []
  induction e generalizing k with
  | app fn arg ihf iha =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have ha := iha k []
    simp only [List.map_nil] at ha
    rw [← ha]
    cases Restoration.expr.go r arg [] <;>
      simp only [Option.map_none, Option.map_some, bind, Option.bind_none,
        Option.bind_some, Option.map_none]
    exact ihf k (_ :: args)
  | const name levels =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    split
    · rename_i spec hs
      exact specialization_liftN' (hc spec (List.mem_of_find?_eq_some hs)) _ _ _ _
    · simp only [Option.map_some, VExpr.liftN_mkApps, VExpr.liftN]
  | bvar | sort | elim =>
    intro args
    simp only [Restoration.expr.go, VExpr.liftN, Option.map_some, VExpr.liftN_mkApps]
  | lam domain body ihd ihb | forallE domain body ihd ihb =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hd := ihd k []
    have hb := ihb (k + 1) []
    simp only [List.map_nil] at hd hb
    rw [← hd, ← hb]
    cases Restoration.expr.go r domain [] <;> cases Restoration.expr.go r body [] <;>
      simp [VExpr.liftN_mkApps, VExpr.liftN]
  | proj name i major ih =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hm := ih k []
    simp only [List.map_nil] at hm
    rw [← hm]
    cases Restoration.expr.go r major [] <;>
      simp [VExpr.liftN_mkApps, VExpr.liftN]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_eq_go (r : Restoration) (e : VExpr) :
    r.expr e = Restoration.expr.go r e [] := rfl
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_mkApps (r : Restoration) (f : VExpr) (args : List VExpr) :
    r.expr (VExpr.mkApps f args) =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f args' := by
  simp [Restoration.expr_eq_go, Restoration.go_mkApps]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

@[simp] theorem Restoration.expr_bvar (r : Restoration) (i : Nat) :
    r.expr (.bvar i) = some (.bvar i) := rfl
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

@[simp] theorem Restoration.expr_sort (r : Restoration) (u : VLevel) :
    r.expr (.sort u) = some (.sort u) := rfl
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.mapM_expr_bvars (r : Restoration) (l : List VExpr)
    (hl : ∀ e ∈ l, ∃ i, e = .bvar i) : l.mapM r.expr = some l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rcases hl a (by simp) with ⟨i, rfl⟩
    simp [List.mapM_cons, ih (fun e he => hl e (by simp [he]))]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.mapM_expr_vars (r : Restoration) (n below : Nat) :
    (vars n below).mapM r.expr = some (vars n below) :=
  r.mapM_expr_bvars _ (by simp [vars])
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_mkApps_bvar (r : Restoration) (i : Nat) (args : List VExpr) :
    r.expr (VExpr.mkApps (.bvar i) args) =
      (args.mapM r.expr).map (VExpr.mkApps (.bvar i)) := by
  rw [r.expr_mkApps]
  cases args.mapM r.expr <;> rfl
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Parameters, motives, minors, and indices of the generated recursor telescope. -/
def Instance.recursorPrefix {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- The generated major domain: the owner family at the parameter and index variables. -/
def Instance.recursorMajor {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  g.familyApp owner
    (vars s.params.length
      (s.families.size + s.constructors.size + s.families[owner].indices.length))
    (vars s.families[owner].indices.length 0)
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- The generated motive application ending the recursor telescope. -/
def Instance.recursorBody {s : InductiveSignature} (_g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps
    (.bvar (s.families[owner].indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val)))
    (vars s.families[owner].indices.length 1 ++ [.bvar 0])
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Instance.recursorType_eq {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    g.recursorType owner =
      VExpr.wrapForalls (g.recursorPrefix owner ++ [g.recursorMajor owner])
        (g.recursorBody owner) := by
  simp [Instance.recursorType, Instance.recursorPrefix, Instance.recursorMajor,
    Instance.recursorBody, insertBinders]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Instance.recursorPrefix_length {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    (g.recursorPrefix owner).length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
  simp [Instance.recursorPrefix, Instance.params, Instance.motives, Instance.minors,
    insertBinders, Nat.add_assoc]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_recursorMajor_source (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size)
    (hfind : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) = none)
    (hname : r.recursorName s.families[owner].name = s.families[owner].name) :
    r.expr (g.recursorMajor owner) = some (g.recursorMajor owner) := by
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
  simp only [Fin.getElem_fin] at hfind hname
  simp [Restoration.expr.go, hfind, hname]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RestoredRecursorShape.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

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
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/CompletedRecursorAlignment.lean
namespace Lean4Lean
open InductiveSignature

theorem VInductDecl.RawCtorShape.constructorShape
    {decl : VInductDecl} {family : VInductiveType} {ctor : VConstVal} {env : VEnv}
    (H : decl.RawCtorShape family ctor) (hnames : decl.sourceNames.Nodup)
    (hfamily : family ∈ decl.types)
    (hlookup : env.constants ctor.name = some ⟨decl.uvars, ctor.type⟩) :
    ∃ fields, Nonempty (VConstructorShape env ctor.name decl.uvars decl.nparams
      fields family.numIndices family.name) := by
  rcases H with ⟨doms, result, htype, hparamsLe, hvalid, hhead⟩
  rcases hvalid with ⟨target, htarget, htargetName, levels, hfn, hlevels, hargs, hparams⟩
  rcases htargetName with hnone | htargetName
  · cases hnone
  have heq : target = family := VInductDecl.type_eq_of_mem_name hnames htarget hfamily
    (Option.some.inj htargetName).symm
  subst target
  change result.getAppFnArgs.2.length = decl.nparams + family.numIndices at hargs
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (doms.length - decl.nparams) at hparams
  refine ⟨doms.length - decl.nparams, ⟨{
    type := ctor.type
    const := hlookup
    doms := doms
    indices := result.getAppFnArgs.2.drop decl.nparams
    type_eq := ?_
    doms_length := by omega
    indices_length := by simp only [List.length_drop, hargs]; omega }⟩⟩
  rw [htype]
  congr 1
  calc
    result = VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 :=
      (VExpr.mkApps_getAppFnArgs_eq result).symm
    _ = VExpr.mkApps (.const family.name (VLevel.params decl.uvars))
        ((result.getAppFnArgs.2.take decl.nparams) ++ result.getAppFnArgs.2.drop decl.nparams) := by
      rw [List.take_append_drop, hhead]
    _ = _ := by
      rw [hparams]
      congr 2
      exact InductiveSignature.vars_eq_bvarRange _ _
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/AssemblyNativeWhnf.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

@[simp] theorem vars_length' (n k : Nat) : (vars n k).length = n := by
  simp [vars]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/AssemblyNativeWhnf.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem vars_map_liftN (n k : Nat) :
    (vars n 0).map (fun arg => arg.liftN k) = vars n k := by
  simp only [vars, List.map_map, Function.comp_def, VExpr.liftN, liftVar]
  apply List.map_congr_left
  intro i _
  simp [Nat.add_comm]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/AssemblyNativeWhnf.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.find?_of_nodup {heads : List HeadSpecialization}
    (hnodup : (heads.map (·.auxiliary)).Nodup) {x : HeadSpecialization}
    (hx : x ∈ heads) : heads.find? (fun y => y.auxiliary == x.auxiliary) = some x := by
  induction heads with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : (y.auxiliary == x.auxiliary) = false := by
        have : y.auxiliary ≠ x.auxiliary := fun h =>
          hnodup.1 (h ▸ List.mem_map_of_mem hx)
        simpa using this
      simp only [hne]
      exact ih hnodup.2 hx
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/AssemblyNativeWhnf.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem declaration_ctor_mem (s : InductiveSignature) (index : Fin s.constructors.size)
    (howner : s.constructors[index].owner.val < s.declaration.types.length) :
    ({ name := s.constructors[index].name, uvars := s.uvars,
        type := s.constructorType s.constructors[index] } : VConstVal) ∈
      (s.declaration.types[s.constructors[index].owner.val]'howner).ctors := by
  simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
    List.mem_filterMap]
  refine ⟨s.constructors[index], Array.getElem_mem_toList _, ?_⟩
  simp
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_wrapLams_eq (r : Restoration) (doms : List VExpr) (body : VExpr) :
    r.expr (VExpr.wrapLams doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapLams doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapLams, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.lam d (VExpr.wrapLams ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapLams]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **The iota shape of a restored generated equation**, given the
restoration of its constructor application. -/
theorem Restoration.restored_iota_shape {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (index : Fin s.constructors.size) {env : VEnv} {df : VDefEq}
    {ctorName : Name} {levels : List VLevel} {params : List VExpr}
    (heq : r.equation (g.equation index) = some df)
    (hdef : env.defeqs df)
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hnotHead : r.heads.find?
      (fun h => h.auxiliary == g.recursorName s.constructors[index].owner) = none)
    (happ : r.expr (g.constructorApp s.constructors[index]
      (s.families.size + s.constructors.size) 0) =
      some (VExpr.mkApps (.const ctorName levels)
        (params.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
          vars s.constructors[index].fields.length 0))) :
    Nonempty (VIotaRuleShape env (r.recursorName (g.recursorName s.constructors[index].owner))
      g.uvars s.params.length params.length s.families.size s.constructors.size
      s.families[s.constructors[index].owner].indices.length ctorName levels
      s.constructors[index].fields.length df params) := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let lhsBody := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (s.params.length + extra) nf ++ indices ++ [major])
  let rhsBody := VExpr.mkApps (.bvar (nf + s.constructors.size - 1 - index.val))
    (vars nf 0 ++ (Instance.recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r)
  let typeBody := VExpr.mkApps
    (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (indices ++ [major])
  have hdomains : domains.length =
      s.params.length + s.families.size + s.constructors.size + nf := by
    simp [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, nf, Nat.add_assoc]
  have hlhs : (g.equation index).lhs = VExpr.wrapLams domains lhsBody := rfl
  have hrhs : (g.equation index).rhs = VExpr.wrapLams domains rhsBody := rfl
  have htype : (g.equation index).type = VExpr.wrapForalls domains typeBody := rfl
  have huv : (g.equation index).uvars = g.uvars := rfl
  simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at heq
  cases hl : r.expr (g.equation index).lhs with
  | none => simp [hl] at heq
  | some lhs =>
  cases hr : r.expr (g.equation index).rhs with
  | none => simp [hl, hr] at heq
  | some rhs =>
  cases ht : r.expr (g.equation index).type with
  | none => simp [hl, hr, ht] at heq
  | some type =>
  simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at heq
  subst heq
  rw [hlhs, r.expr_wrapLams_eq] at hl
  rw [hrhs, r.expr_wrapLams_eq] at hr
  rw [htype, r.expr_wrapForalls] at ht
  cases hD : domains.mapM r.expr with
  | none => simp [hD] at hl
  | some D' =>
  simp only [hD, Option.bind_some] at hl hr ht
  cases hlb : r.expr lhsBody with
  | none => simp [hlb] at hl
  | some lb =>
  cases hrb : r.expr rhsBody with
  | none => simp [hrb] at hr
  | some rb =>
  cases htb : r.expr typeBody with
  | none => simp [htb] at ht
  | some tb =>
  simp only [hlb, hrb, htb, Option.map_some, Option.some.injEq] at hl hr ht
  have hDlen : D'.length = domains.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hD)).symm
  -- the restored left-hand side body
  have hlb' := hlb
  simp only [lhsBody] at hlb'
  rw [r.expr_mkApps, List.mapM_append, List.mapM_append, r.mapM_expr_vars] at hlb'
  cases hI : indices.mapM r.expr with
  | none => simp [hI] at hlb'
  | some I' =>
  have hmajor : [major].mapM r.expr = some [VExpr.mkApps (.const ctorName levels)
      (params.map (fun arg => arg.liftN (extra + nf)) ++ vars nf 0)] := by
    have happ' : r.expr major = some (VExpr.mkApps (.const ctorName levels)
        (params.map (fun arg => arg.liftN (extra + nf)) ++ vars nf 0)) := happ
    simp [List.mapM_cons, happ']
  have hnotHead' : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none :=
    hnotHead
  simp only [hI, hmajor, Option.bind_some, Option.pure_def, Option.bind_eq_bind,
    Restoration.expr.go, hnotHead'] at hlb'
  have hIlen : I'.length = indices.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hI)).symm
  refine ⟨{
    defeq := hdef
    uvars := huv
    doms := D'
    lhsBody := lb
    rhsBody := rb
    typeBody := tb
    lhs_eq := hl.symm
    rhs_eq := hr.symm
    type_eq := ht.symm
    doms_length := by rw [hDlen, hdomains]
    indexArgs := I'
    indexArgs_length := by
      rw [hIlen]; simpa [indices, ctor] using hindices
    lhs_pattern := ?_ }⟩
  rw [← Option.some.inj hlb']
  simp only [hDlen, hdomains, vars_eq_bvarRange, Nat.add_zero, List.append_assoc,
    extra, nf, ctor, Nat.add_assoc]
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **Field count of a restored rule.** In a well-formed environment, a typed
equation with the iota shape of a recursor whose constructor has a rigid
major family supplies exactly the constructor's fields. -/
theorem VIotaRuleShape.fieldCount {env env' : VEnv} (henv : env.WF)
    {recName ctorName indName : Name}
    {recUvars nparams cnparams nmotives nminors nindices nf ctorUvars fields nindices' : Nat}
    {ctorLevels indLevels : List VLevel} {df : VDefEq} {ctorParams : List VExpr}
    (I : VIotaRuleShape env' recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nf df ctorParams)
    (hwf : df.WF env)
    (hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices
      indName indLevels ctorParams)
    (hctor : VConstructorShape env ctorName ctorUvars cnparams fields nindices' indName)
    (hrigid : env.Rigid indName) : fields = nf := by
  have hleft := hwf.1
  rw [I.lhs_eq, I.type_eq, I.uvars] at hleft
  rcases VEnv.HasType.wrapLams_inv henv (by trivial) hleft with ⟨hctx, hbody⟩
  rw [I.lhs_pattern] at hbody
  have hpre : (VExpr.bvarRange (nparams + nmotives + nminors) I.doms.length ++
      I.indexArgs).length = nparams + nmotives + nminors + nindices := by
    simp [I.indexArgs_length]
  have hbody' : env.HasType recUvars (I.doms.reverse ++ [])
      (VExpr.mkApps (.const recName (VLevel.params recUvars))
        ((VExpr.bvarRange (nparams + nmotives + nminors) I.doms.length ++ I.indexArgs) ++
          [VExpr.mkApps (.const ctorName ctorLevels)
            ((ctorParams.map fun p => p.liftN (nmotives + nminors + nf)) ++
              VExpr.bvarRange nf nf)])) I.typeBody := by
    simpa only [List.append_assoc] using hbody
  have ⟨_, hmajor, _⟩ := hrec.spine_typing henv hctx VLevel.params_wf VLevel.params_length
    hpre ⟨_, hbody'⟩
  have hsat := hctor.saturated_of_hasType henv hctx hrigid hmajor
  have hlen : ctorParams.length = cnparams := hrec.ctorParams_length
  simp only [List.length_append, List.length_map, VExpr.bvarRange_length, hlen] at hsat
  omega
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem ContainerSpecialization.directFamily_numIndices
    {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.directFamily uvars params = some direct) :
    direct.numIndices = a.source.numIndices := by
  unfold ContainerSpecialization.directFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, _, H⟩
    cases H
    rfl
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
open InductiveSignature

theorem CompiledInductive.sourceFacts {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    source.sourceNames.Nodup ∧
      (∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor) ∧
      ∀ ctor ∈ source.constructorConstants, ctor.uvars = source.uvars := by
  induction H using CompiledInductive.rec
    (motive_2 := fun _ _ _ => True) with
  | intro Hd _ _ =>
    exact ⟨Hd.sourceWF.2.1, Hd.sourceParameters.rawCtorShape, Hd.sourceWF.2.2.2.1⟩
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ => trivial
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
open InductiveSignature

/-- The constructors of a certified container are installed with their
recorded values and have the raw constructor shape of their container. -/
theorem CertifiedSpecializations.containerConstructors {env : VEnv} :
    ∀ {auxiliaries : List InductiveSignature.ContainerSpecialization},
      CertifiedSpecializations env auxiliaries →
      ∀ a ∈ auxiliaries, a.container.sourceNames.Nodup ∧
        ∀ type ∈ a.container.types, ∀ ctor ∈ type.ctors,
          a.container.RawCtorShape type ctor ∧
          env.constants ctor.name = some ⟨a.container.uvars, ctor.type⟩
  | [], _ => by intro a ha; cases ha
  | a0 :: rest, H => by
    cases H with
    | cons hcompiled _ hinstall hle hrest =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · have Hsrc := hcompiled.sourceFacts
      obtain ⟨-, hctors⟩ := hcompiled.types_ctors
      refine ⟨Hsrc.1, fun type htype ctor hctor => ⟨?_, ?_⟩⟩
      · exact Hsrc.2.1 type htype ctor hctor
      · have hmem : ctor ∈ a.container.constructorConstants :=
          List.mem_flatMap.mpr ⟨type, htype, hctor⟩
        have h := hle.constants (VInductBlock.install_constants hinstall ctor
          (List.mem_append_right _ (by rw [hctors]; exact hmem)))
        have hu : ctor.uvars = a.container.uvars := Hsrc.2.2 ctor hmem
        rw [h, ← hu]
    · exact CertifiedSpecializations.containerConstructors hrest a ha
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/RecursorProvenance.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **The constructor shape of a restored rule's constructor.** Every
generated constructor restores to a constant (a source constructor, or a
constructor of a certified container) whose stored type has the constructor
shape at the restored family head of its owner, for some field count. -/
theorem CompilationData.restoredConstructorShape
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (Hcert : CertifiedSpecializations env auxiliaries)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    {venv : VEnv} (hle : envCtors ≤ venv)
    (index : Fin s.constructors.size) (owner : Fin s.families.size)
    (howner : s.constructors[index].owner = owner) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      ∃ fields, Nonempty (VConstructorShape venv
        ((compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name)
        head.levels.length head.arguments.length fields
        s.families[owner].indices.length head.name) := by
  have henvLE : env ≤ envCtors :=
    (VEnv.addConstVals_le hadded).trans (VEnv.addConstVals_le hctorsAdded)
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have hown : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have hown' : owner.val < (source.types ++ direct).length := hlen ▸ hown
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val hown hown'
  have hdeclName : (s.declaration.types[owner.val]'hown).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hdeclIdx : (s.declaration.types[owner.val]'hown).numIndices =
      s.families[owner].indices.length := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'hown').name :=
    hdeclName.symm.trans Hat.name
  have hidxEq : ((source.types ++ direct)[owner.val]'hown').numIndices =
      s.families[owner].indices.length := Hat.indices.symm.trans hdeclIdx
  obtain ⟨sc, hsc, hscName⟩ : ∃ sc ∈ ((source.types ++ direct)[owner.val]'hown').ctors,
      s.constructors[index].name = sc.name := by
    have hmem := declaration_ctor_mem s index (by rw [howner]; exact hown)
    simp only [howner] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1⟩
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · rw [List.getElem_append_left hsrc] at hsc hidxEq
      have hscMem : sc ∈ source.constructorConstants :=
        List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded hscMem
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = sc.name := by
        simp only [Restoration.restoredHeadName, hcfind]
        exact hscName
      have hu : sc.uvars = source.uvars := Hd.sourceWF.2.2.2.1 sc hscMem
      have hlookup : venv.constants sc.name = some ⟨source.uvars, sc.type⟩ := by
        have h := hle.constants (VEnv.addConstVals_get hctorsAdded hscMem)
        rw [h, ← hu]
      have hraw := Hd.sourceParameters.rawCtorShape _ (List.getElem_mem hsrc) sc hsc
      rcases VInductDecl.RawCtorShape.constructorShape hraw Hd.sourceWF.2.1
        (List.getElem_mem hsrc) hlookup with ⟨fields, hshape⟩
      refine ⟨fields, ?_⟩
      rw [hchead]
      simpa only [vars_length', hlevelsLen, hnp, hidxEq, hname'] using hshape
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := hown'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.directFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨hargLen, hargsClosed, hlevLen, -, -⟩ := hwellFormed a ha
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length', hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · rw [List.getElem_append_right hge] at hsc hidxEq
      rw [ContainerSpecialization.directFamily_numIndices hdf] at hidxEq
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have hscMem : sc.name ∈ a.source.ctors.map a.constructorName := by
        have : sc.name ∈ (direct[owner.val - source.types.length]'hidx).ctors.map (·.name) :=
          List.mem_map_of_mem hsc
        rw [← hheads.2] at this
        simpa [Function.comp_def] using this
      obtain ⟨ctor, hctor, hctorName'⟩ := List.mem_map.mp hscMem
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc]
      obtain ⟨hnodupC, hctorsC⟩ := Hcert.containerConstructors a ha
      have hsrcMem : a.source ∈ a.container.types := List.getElem_mem _
      obtain ⟨hraw, hlookup⟩ := hctorsC a.source hsrcMem ctor hctor
      rcases VInductDecl.RawCtorShape.constructorShape hraw hnodupC hsrcMem
        ((henvLE.trans hle).constants hlookup) with ⟨fields, hshape⟩
      refine ⟨fields, ?_⟩
      rw [hchead]
      simpa only [List.length_map, hlevLen, hargLen, hidxEq] using hshape
end InductiveSignature
end Lean4Lean

-- from Lean4Lean/Verify/Inductive/Nested/AssemblyNativeWhnf.lean
namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **The restored family head of a compiled owner.** For a source family it
is the family itself at the instance's universe levels and the parameter
variables; for an auxiliary family it is the specialized container. Every
constructor of the owner restores to the restored constructor head applied
to the head's arguments and the fields. -/
theorem CompilationData.restoredFamilyHead_spec
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    (owner : Fin s.families.size) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      head.name = (compilationRestoration source auxiliaries).restoredHeadName
        s.families[owner].name ∧
      (∀ level ∈ head.levels, level.WF g.uvars) ∧
      (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
      (compilationRestoration source auxiliaries).expr (g.familyApp owner
        (vars s.params.length
          (s.families.size + s.constructors.size + s.families[owner].indices.length))
        (vars s.families[owner].indices.length 0)) =
        some (VExpr.mkApps (.const head.name head.levels)
          (head.arguments.map (fun arg => arg.liftN
            (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
            vars s.families[owner].indices.length 0)) ∧
      ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
        (((compilationRestoration source auxiliaries).heads.find?
            (fun h => h.auxiliary == s.families[owner].name) = none ∧
          (compilationRestoration source auxiliaries).restoredHeadName
            s.constructors[index].name = s.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, s.families[owner].name = a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, s.constructors[index].name = a.constructorName ctor) ∧
        (compilationRestoration source auxiliaries).expr
          (g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration source auxiliaries).restoredHeadName
              s.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
              vars s.constructors[index].fields.length 0)) := by
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have howner : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have howner' : owner.val < (source.types ++ direct).length := hlen ▸ howner
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val howner howner'
  have hdeclName : (s.declaration.types[owner.val]'howner).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'howner').name :=
    hdeclName.symm.trans Hat.name
  -- every constructor of the owner names a constructor of the corresponding family
  have hctorName : ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
      ∃ sc ∈ ((source.types ++ direct)[owner.val]'howner').ctors,
        s.constructors[index].name = sc.name := by
    intro index hindex
    have hmem := declaration_ctor_mem s index (by rw [hindex]; exact howner)
    simp only [hindex] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1⟩
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  have hfreshRecsC : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envCtors.constants p.1 = none :=
    fun p hp => hfreshCtors p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind]
    · exact Hadm.levels_wf
    · intro arg harg
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at harg
      obtain ⟨i, hi, rfl⟩ := harg
      simp [VExpr.ClosedN, hi]
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_source g owner hfind
          hrecName]
      simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp,
        vars_map_liftN]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_left hsrc] at hsc
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded
          (List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩)
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hcrec : (compilationRestoration source auxiliaries).recursorName
          s.constructors[index].name = s.constructors[index].name :=
        Restoration.recursorName_of_constants hfreshRecsC hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = s.constructors[index].name := by
        simp only [Restoration.restoredHeadName, hcfind]
      refine ⟨.inl ⟨hfind, hchead⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Restoration.expr.go, hcfind, hcrec, vars_map_liftN, Nat.add_zero]
      rfl
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := howner'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.directFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨-, hargsClosed, -, hlevelsWF, -⟩ := hwellFormed a ha
    have hclosed : ∀ arg ∈ h.arguments, arg.ClosedN h.nparams := hargsClosed
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length', hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind, h]
    · intro level hlevel
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hlevel
      exact VLevel.WF.inst Hadm.levels_wf
    · intro arg' harg'
      obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp harg'
      exact hclosedL arg harg
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_auxiliary g owner hfind
          hlevelsLen hnp.symm hclosed]
      simp only [List.map_map, Function.comp_def, h]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_right hge] at hsc
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have hscMem : sc.name ∈ a.source.ctors.map a.constructorName := by
        have : sc.name ∈ (direct[owner.val - source.types.length]'hidx).ctors.map (·.name) :=
          List.mem_map_of_mem hsc
        rw [← hheads.2] at this
        simpa [Function.comp_def] using this
      obtain ⟨ctor, hctor, hctorName'⟩ := List.mem_map.mp hscMem
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc]
      refine ⟨.inr ⟨a, ha, hname', ctor, hctor, hcName⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Restoration.expr.go, hcfind, HeadSpecialization.apply,
        hlevelsLen, hc, bne_self_eq_false, Bool.false_or, List.length_append, vars_length',
        hnp, Nat.add_zero]
      rw [if_neg (by simp), List.take_left' (vars_length' _ _),
        List.drop_left' (vars_length' _ _), hinst]
      simp only [List.map_map, Function.comp_def]
end InductiveSignature
end Lean4Lean
