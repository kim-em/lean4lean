import Lean4Lean.Theory.Typing.ProjectionCornerCaseElim
import Lean4Lean.Theory.Typing.ProjectionCornerIndexedWalk

/-! # The case eliminator of a registered indexed structure, in ordinary form

`CaseSchema.restored_structure_recursorType`: a registered case schema
types `.elim key owner (target :: levels)` at the restoration of the recursor type of its
one-family view. For the family of a structure (one constructor, possibly indexed), this restored type
is the ordinary recursor type of the one-constructor signature `caseView`, whose parameter,
index, field and constructor-index expressions are the restored ones. -/

namespace Lean4Lean
namespace InductiveSignature

/-- The one-family, one-constructor signature of an indexed structure case view. -/
def caseView (uvars : Nat) (isUnsafe : Bool) (fam : Family) (name : Name)
    (params fields cidx : List VExpr) : InductiveSignature where
  uvars := uvars
  params := params
  families := #[fam]
  constructors := #[⟨name, ⟨0, by simp⟩, fields.map Field.external, cidx⟩]
  isUnsafe := isUnsafe

theorem caseView_recursiveFields {uvars isUnsafe fam name params fields cidx} :
    Instance.recursiveFields (s := caseView uvars isUnsafe fam name params fields cidx)
      ⟨name, ⟨0, by simp [caseView]⟩, fields.map Field.external, cidx⟩ = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hfield
  rfl

theorem Restoration.mapM_expr_map_liftN (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams) (n k : Nat) :
    ∀ {l l' : List VExpr}, l.mapM r.expr = some l' →
      (l.map (·.liftN n k)).mapM r.expr = some (l'.map (·.liftN n k))
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: as, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    simp only [List.map_cons, List.mapM_cons]
    rw [← Restoration.expr_liftN r hc, ha, Option.map_some,
      Restoration.mapM_expr_map_liftN r hc n k has]
    rfl

/-- The restored case type of an indexed structure family is the ordinary recursor type of its
restored one-constructor view. -/
theorem CaseSchema.restored_structure_recursorType {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    {c : Constructor schema.signature.families.size}
    (hview : (schema.view owner).constructors = #[schema.caseConstructor c])
    {RP RF RI RCI : List VExpr}
    (hRP : schema.signature.params.mapM schema.restoration.expr = some RP)
    (hRF : (schema.signature.fieldTypes c).mapM schema.restoration.expr = some RF)
    (hRI : schema.signature.families[owner].indices.mapM schema.restoration.expr = some RI)
    (hRCI : c.indices.mapM schema.restoration.expr = some RCI)
    (hheads : ∀ h ∈ schema.restoration.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (hfS : schema.restoration.heads.find?
      (fun h => h.auxiliary == schema.signature.families[owner].name) = none)
    (hnS : schema.restoration.recursorName schema.signature.families[owner].name =
      schema.signature.families[owner].name)
    (hfc : schema.restoration.heads.find? (fun h => h.auxiliary == c.name) = none)
    (hnc : schema.restoration.recursorName c.name = c.name)
    (U : Nat) (ls : List VLevel) (target : VLevel) :
    schema.restoration.expr
        ((schema.specialize owner U ls target).recursorType (schema.viewOwner owner)) =
      some ((⟨U, ls, target, fun _ => default⟩ : Instance (caseView schema.signature.uvars
        schema.signature.isUnsafe ⟨schema.signature.families[owner].name, RI,
          schema.signature.families[owner].resultLevel⟩ c.name RP RF RCI)).recursorType
          ⟨0, by simp [caseView]⟩) := by
  let r := schema.restoration
  let gv := schema.specialize owner U ls target
  let fam' : Family := ⟨schema.signature.families[owner].name, RI,
    schema.signature.families[owner].resultLevel⟩
  let sv := caseView schema.signature.uvars schema.signature.isUnsafe fam' c.name RP RF RCI
  let gp : Instance sv := ⟨U, ls, target, fun _ => default⟩
  have hRPlen : RP.length = schema.signature.params.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
  have hRFlen : RF.length = (schema.signature.fieldTypes c).length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF)).symm
  have hRIlen : RI.length = schema.signature.families[owner].indices.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRI)).symm
  have hRCIlen : RCI.length = c.indices.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRCI)).symm
  have hcs : (schema.view owner).constructors.size = 1 := by rw [hview]; rfl
  let i0 : Fin (schema.view owner).constructors.size := ⟨0, by omega⟩
  have hc0 : (schema.view owner).constructors[i0] = schema.caseConstructor c := by
    have key : ∀ (a : Array (Constructor 1)) (ha : a = #[schema.caseConstructor c])
        (i : Fin a.size), a[i] = schema.caseConstructor c := by
      intro a ha i; subst ha; obtain ⟨i, hi⟩ := i; simp at hi; subst hi; rfl
    exact key _ hview i0
  rw [gv.recursorType_shape rfl hcs (schema.viewOwner owner) i0,
    gp.recursorType_shape rfl rfl ⟨0, by simp [sv, caseView]⟩ ⟨0, by simp [sv, caseView]⟩]
  rw [hc0, r.expr_wrapForalls]
  -- the pieces
  have hbv : ∀ (n k : Nat), ∀ e ∈ vars n k, ∃ i, e = VExpr.bvar i := by
    intro n k e he; simp only [vars, List.mem_map] at he; obtain ⟨_, _, rfl⟩ := he; exact ⟨_, rfl⟩
  have hfam : (schema.view owner).families[schema.viewOwner owner] =
      schema.signature.families[owner] := rfl
  have hfam' : sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)] = fam' := rfl
  have hsI : gv.sIndices (schema.viewOwner owner) =
      schema.signature.families[owner].indices.map (·.instL ls) := by
    unfold Instance.sIndices; rw [hfam]; rfl
  have hsI' : gp.sIndices ⟨0, by simp [sv, caseView]⟩ = RI.map (·.instL ls) := by
    unfold Instance.sIndices; rw [hfam']
  have hplen : (schema.view owner).params.length = sv.params.length := by
    simp [sv, caseView, CaseSchema.view, hRPlen]
  have hparams : gv.params.mapM r.expr = some gp.params :=
    Restoration.mapM_expr_instL r hRP ls
  have hidxs : (gv.sIndices (schema.viewOwner owner)).mapM r.expr =
      some (gp.sIndices ⟨0, by simp [sv, caseView]⟩) := by
    rw [hsI, hsI']; exact Restoration.mapM_expr_instL r hRI ls
  have hsIl : (gv.sIndices (schema.viewOwner owner)).length =
      (gp.sIndices ⟨0, by simp [sv, caseView]⟩).length := by
    rw [hsI, hsI']; simp [hRIlen]
  have hmotive : r.expr (gv.motive (schema.view owner).families[schema.viewOwner owner] 0) =
      some (gp.motive sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)] 0) := by
    rw [hfam, hfam']
    simp only [Instance.motive]
    rw [r.expr_wrapForalls, List.mapM_append,
      Restoration.mapM_expr_insertBinders r hheads (Restoration.mapM_expr_instL r hRI gv.levels) 0]
    simp only [List.mapM_cons, List.mapM_nil]
    rw [Restoration.expr_mkApps_const_fixed r hfS hnS (by
      intro e he; simp only [List.mem_append] at he
      rcases he with he | he <;> exact hbv _ _ e he)]
    simp only [Restoration.expr_sort, hplen, List.length_map, Instance.length_insertBinders, ← hRIlen]
    rfl
  let c' : Constructor sv.families.size := sv.constructors[(⟨0, by simp [sv, caseView]⟩ :
    Fin sv.constructors.size)]
  have hc' : c' = ⟨c.name, ⟨0, by simp [sv, caseView]⟩, RF.map Field.external, RCI⟩ := rfl
  have hsH : gv.sHyps (schema.caseConstructor c) = [] := by
    unfold Instance.sHyps; rw [CaseSchema.caseConstructor_recursiveFields]; rfl
  have hsH' : gp.sHyps c' = [] := by
    unfold Instance.sHyps; rw [hc', caseView_recursiveFields]; rfl
  have hsCI : gv.sCtorIndices (schema.caseConstructor c) = c.indices.map (·.instL ls) := by
    simp [Instance.sCtorIndices, CaseSchema.caseConstructor, gv, CaseSchema.specialize]
  have hsCI' : gp.sCtorIndices c' = RCI.map (·.instL ls) := by
    simp [Instance.sCtorIndices, hc', gp]
  have hsF : gv.sFields (schema.caseConstructor c) =
      (schema.signature.fieldTypes c).map (·.instL ls) := by
    simp only [Instance.sFields, CaseSchema.view_fieldTypes_case]; rfl
  have hsF' : gp.sFields c' = RF.map (·.instL ls) := by
    simp only [Instance.sFields]; rw [fieldTypes_external _ (by rw [hc'])]
  have hctorApp : r.expr (gv.constructorApp (schema.caseConstructor c) 1 0) =
      some (gp.constructorApp c' 1 0) := by
    simp only [Instance.constructorApp]
    rw [show (schema.caseConstructor c).name = c.name from rfl]
    rw [Restoration.expr_mkApps_const_fixed r hfc hnc (by
      intro e he; simp only [List.mem_append] at he
      rcases he with he | he <;> exact hbv _ _ e he)]
    simp only [Instance.constructorApp, hc']
    have h1 : List.length (α := Field (schema.view owner).families.size)
        (schema.caseConstructor c).fields = RF.length := by
      simp [CaseSchema.caseConstructor, hRFlen]
    have h2 : (schema.view owner).params.length = RP.length := by
      simp [CaseSchema.view, hRPlen]
    simp only [h1, h2, List.length_map]
    rfl
  have hown0 : (schema.caseConstructor c).owner.val = 0 := rfl
  have hminor : r.expr (gv.minor (schema.caseConstructor c) 0) = some (gp.minor c' 0) := by
    rw [gv.minor_shape rfl _ hown0, gp.minor_shape rfl c' (by rw [hc'])]
    rw [hsH, hsH', hsCI, hsCI', hsF, hsF']
    simp only [List.append_nil, List.length_nil, Nat.add_zero, VExpr.liftN_zero]
    rw [r.expr_wrapForalls, Restoration.mapM_expr_insertBinders r hheads
      (Restoration.mapM_expr_instL r hRF ls)]
    simp only [Option.bind_some]
    rw [r.expr_mkApps_bvar, List.mapM_append,
      Restoration.mapM_expr_map_liftN r hheads 1 _ (Restoration.mapM_expr_instL r hRCI ls)]
    simp only [List.mapM_cons, List.mapM_nil, hctorApp]
    simp [hRFlen]
  have hmajor : r.expr (gv.familyApp (schema.viewOwner owner)
      (vars (schema.view owner).params.length (2 + (gv.sIndices (schema.viewOwner owner)).length))
      (vars (gv.sIndices (schema.viewOwner owner)).length 0)) =
      some (gp.familyApp ⟨0, by simp [sv, caseView]⟩
        (vars sv.params.length (2 + (gp.sIndices ⟨0, by simp [sv, caseView]⟩).length))
        (vars (gp.sIndices ⟨0, by simp [sv, caseView]⟩).length 0)) := by
    simp only [Instance.familyApp, InductiveSignature.familyApp]
    rw [show (schema.view owner).families[schema.viewOwner owner].name =
      schema.signature.families[owner].name from rfl]
    rw [Restoration.expr_mkApps_const_fixed r hfS hnS (by
      intro e he; simp only [List.mem_append] at he
      rcases he with he | he <;> exact hbv _ _ e he)]
    rw [hplen, hsIl]
    rfl
  have hbody : r.expr (VExpr.mkApps (.bvar ((gv.sIndices (schema.viewOwner owner)).length + 2))
      (vars (gv.sIndices (schema.viewOwner owner)).length 1 ++ [.bvar 0])) =
      some (VExpr.mkApps (.bvar ((gp.sIndices ⟨0, by simp [sv, caseView]⟩).length + 2))
        (vars (gp.sIndices ⟨0, by simp [sv, caseView]⟩).length 1 ++ [.bvar 0])) := by
    rw [r.expr_mkApps_bvar, r.mapM_expr_bvars _ (by
      intro e he; simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hbv _ _ e he
      · exact ⟨_, rfl⟩), hsIl]
    rfl
  simp only [List.mapM_append, List.mapM_cons, List.mapM_nil, hparams, hmotive, hminor,
    hmajor, hbody, Restoration.mapM_expr_insertBinders r hheads hidxs, Option.bind_some,
    Option.pure_def, Option.map_some, bind, Option.bind_eq_bind]
  rfl

end InductiveSignature
end Lean4Lean
