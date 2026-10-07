import Lean4Lean.Theory.Typing.ProjectionCornerSig
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness

/-! # The case eliminator of a registered structure, in ordinary form

A registered case schema types `.elim key owner (target :: levels)` at the restoration of the
recursor type of its one-family view. For the family of a structure (one constructor, no
indices), this restored type is the ordinary recursor type of the one-constructor signature
`caseView` whose parameters and field domains are the restored ones. -/

namespace Lean4Lean
namespace InductiveSignature

/-- The one-family, one-constructor signature of a structure case view, with explicit
parameter and field domains. -/
def caseView (uvars : Nat) (isUnsafe : Bool) (fam : Family) (name : Name)
    (params fields : List VExpr) : InductiveSignature where
  uvars := uvars
  params := params
  families := #[fam]
  constructors := #[⟨name, ⟨0, by simp⟩, fields.map Field.external, []⟩]
  isUnsafe := isUnsafe

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

theorem view_families_getElem (owner : Fin schema.signature.families.size) :
    (schema.view owner).families[schema.viewOwner owner] = schema.signature.families[owner] := rfl

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

theorem caseView_recursiveFields {uvars isUnsafe fam name params fields} :
    Instance.recursiveFields (s := caseView uvars isUnsafe fam name params fields)
      ⟨name, ⟨0, by simp [caseView]⟩, fields.map Field.external, []⟩ = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hfield
  rfl

/-- The restored case type of a structure family is the ordinary recursor type of its
restored one-constructor view. -/
theorem CaseSchema.restored_structure_recursorType {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    {c : Constructor schema.signature.families.size}
    (hview : (schema.view owner).constructors = #[schema.caseConstructor c])
    (hI : schema.signature.families[owner].indices = []) (hCI : c.indices = [])
    {RP RF : List VExpr}
    (hRP : schema.signature.params.mapM schema.restoration.expr = some RP)
    (hRF : (schema.signature.fieldTypes c).mapM schema.restoration.expr = some RF)
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
        schema.signature.isUnsafe schema.signature.families[owner] c.name RP RF)).recursorType
          ⟨0, by simp [caseView]⟩) := by
  let r := schema.restoration
  let gv := schema.specialize owner U ls target
  let sv := caseView schema.signature.uvars schema.signature.isUnsafe
    schema.signature.families[owner] c.name RP RF
  let gp : Instance sv := ⟨U, ls, target, fun _ => default⟩
  have hRPlen : RP.length = schema.signature.params.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
  have hRFlen : RF.length = (schema.signature.fieldTypes c).length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF)).symm
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
  have hfam' : sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)] =
      schema.signature.families[owner] := rfl
  have hsI : gv.sIndices (schema.viewOwner owner) = [] := by
    unfold Instance.sIndices; rw [hfam]; exact congrArg (List.map _) hI
  have hsI' : gp.sIndices ⟨0, by simp [sv, caseView]⟩ = [] := by
    unfold Instance.sIndices; rw [hfam']; exact congrArg (List.map _) hI
  have hplen : (schema.view owner).params.length = sv.params.length := by
    simp [sv, caseView, view, hRPlen]
  have hparams : gv.params.mapM r.expr = some gp.params :=
    Restoration.mapM_expr_instL r hRP ls
  have hmotive : r.expr (gv.motive (schema.view owner).families[schema.viewOwner owner] 0) =
      some (gp.motive sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)] 0) := by
    rw [hfam, hfam']
    simp only [Instance.motive, hI, List.map_nil, insertBinders, List.zipIdx_nil,
      List.nil_append, List.length_nil, Nat.add_zero]
    rw [r.expr_wrapForalls]
    simp only [List.mapM_cons, List.mapM_nil]
    rw [Restoration.expr_mkApps_const_fixed r hfS hnS (by
      intro e he; simp only [List.mem_append] at he
      rcases he with he | he <;> exact hbv _ _ e he)]
    simp only [Restoration.expr_sort, hplen]
    rfl
  let c' : Constructor sv.families.size := sv.constructors[(⟨0, by simp [sv, caseView]⟩ :
    Fin sv.constructors.size)]
  have hc' : c' = ⟨c.name, ⟨0, by simp [sv, caseView]⟩, RF.map Field.external, []⟩ := rfl
  have hsH : gv.sHyps (schema.caseConstructor c) = [] := by
    unfold Instance.sHyps; rw [CaseSchema.caseConstructor_recursiveFields]; rfl
  have hsH' : gp.sHyps c' = [] := by
    unfold Instance.sHyps; rw [hc', caseView_recursiveFields]; rfl
  have hsCI : gv.sCtorIndices (schema.caseConstructor c) = [] := by
    simp [Instance.sCtorIndices, CaseSchema.caseConstructor, hCI]
  have hsCI' : gp.sCtorIndices c' = [] := by
    simp [Instance.sCtorIndices, hc']
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
    simp only [List.append_nil, List.map_nil, List.nil_append, List.length_nil, Nat.add_zero]
    rw [r.expr_wrapForalls, Restoration.mapM_expr_insertBinders r hheads
      (Restoration.mapM_expr_instL r hRF ls)]
    simp only [Option.bind_some]
    rw [r.expr_mkApps_bvar]
    simp only [List.mapM_cons, List.mapM_nil, hctorApp]
    simp [hRFlen]
  have hmajor : r.expr (gv.familyApp (schema.viewOwner owner)
      (vars (schema.view owner).params.length (2 + 0)) (vars 0 0)) =
      some (gp.familyApp ⟨0, by simp [sv, caseView]⟩ (vars sv.params.length (2 + 0))
        (vars 0 0)) := by
    simp only [Instance.familyApp, InductiveSignature.familyApp]
    rw [show (schema.view owner).families[schema.viewOwner owner].name =
      schema.signature.families[owner].name from rfl]
    rw [Restoration.expr_mkApps_const_fixed r hfS hnS (by
      intro e he; simp only [List.mem_append] at he
      rcases he with he | he <;> exact hbv _ _ e he)]
    rw [hplen]
    rfl
  have hbody : r.expr (VExpr.mkApps (.bvar (0 + 2)) (vars 0 1 ++ [.bvar 0])) =
      some (VExpr.mkApps (.bvar (0 + 2)) (vars 0 1 ++ [.bvar 0])) := by
    rw [r.expr_mkApps_bvar, r.mapM_expr_bvars _ (by
      intro e he; simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hbv _ _ e he
      · exact ⟨_, rfl⟩)]
    rfl
  rw [hsI, hsI']
  simp only [List.length_nil] at hmajor hbody ⊢
  simp only [List.mapM_append, List.mapM_cons, List.mapM_nil, hparams, hmotive, hminor,
    hmajor, hbody, insertBinders, List.zipIdx_nil, List.map_nil, Option.bind_some,
    Option.pure_def, Option.map_some, bind, Option.bind_eq_bind]
  rfl

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

/-- The ordinary recursor type into `Prop` of the case view of a registered structure is a
type, given that the view's constructor type is the registered constructor type. -/
theorem caseView_recursorType_isType (henv : env.WF)
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    (hni : info.nindices = 0)
    {uvars : Nat} {isUnsafe : Bool} {fam : Family} {RP RF : List VExpr}
    (hfam : fam.name = S) (hI : fam.indices = []) (huv : uvars = info.uvars)
    (hnp : RP.length = info.nparams)
    (hdef : env.IsDefEqU info.uvars []
      ((caseView uvars isUnsafe fam info.ctorName RP RF).constructorType
        ⟨info.ctorName, ⟨0, by simp [caseView]⟩, RF.map Field.external, []⟩) info.ctorType) :
    env.IsType U []
      ((⟨U, ls, .zero, fun _ => default⟩ : Instance (caseView uvars isUnsafe fam info.ctorName
        RP RF)).recursorType ⟨0, by simp [caseView]⟩) := by
  let sv := caseView uvars isUnsafe fam info.ctorName RP RF
  let gp : Instance sv := ⟨U, ls, .zero, fun _ => default⟩
  let c' : Constructor sv.families.size :=
    ⟨info.ctorName, ⟨0, by simp [sv, caseView]⟩, RF.map Field.external, []⟩
  have hR := gp.ordinary_recursorType (s := sv) rfl rfl ⟨0, by simp [sv, caseView]⟩
    ⟨0, by simp [sv, caseView]⟩ (c := c') rfl rfl rfl hI rfl
  change env.IsType U [] (gp.recursorType ⟨0, by simp [sv, caseView]⟩)
  rw [hR]
  -- notation
  have hF : sv.fieldTypes c' = RF := fieldTypes_external _ rfl
  have hsF : gp.sFields c' = RF.map (·.instL ls) := by simp only [Instance.sFields, hF]; rfl
  have hsH : gp.sHyps c' = [] := by
    unfold Instance.sHyps; rw [caseView_recursiveFields]; rfl
  have hP : gp.params = RP.map (·.instL ls) := rfl
  let P := RP.map (·.instL ls)
  let F := RF.map (·.instL ls)
  have hnpP : P.length = info.nparams := by simp [P, hnp]
  have hlsU : ls.length = uvars := hlslen.trans huv.symm
  -- the view's constructor type at `ls` is the registered constructor type
  let R := VExpr.mkApps (.const S ls) (vars RP.length RF.length)
  have hC : (sv.constructorType c').instL ls = VExpr.wrapForalls (P ++ F) R := by
    simp only [InductiveSignature.constructorType, hF, InductiveSignature.familyApp,
      VExpr.instL_wrapForalls, List.map_append, VExpr.instL_mkApps, VExpr.instL, R, P, F]
    simp only [sv, caseView, hfam, List.append_nil, VLevel.inst_map_id hlsU]
    congr 1
    simp [c', hfam, InductiveSignature.Instance.instL_vars]
    congr 2
    exact List.length_map ..
  -- the registered constructor
  obtain ⟨decl, type, ctor, -, -, -, -, hdu, hdn, -, -, -, hctorType, -, hwf, -, -, -⟩ :=
    Ordered.projectionShape henv.ordered hinfo
  have hctorT : env.IsType U [] (info.ctorType.instL ls) := by
    have h := hwf.instL (ls := ls) hls
    rw [hctorType] at h
    simpa using h
  have hdefL : env.IsDefEqU U [] (VExpr.wrapForalls (P ++ F) R) (info.ctorType.instL ls) := by
    have h := hdef.instL hls
    rw [hC] at h
    simpa using h
  have hCT : env.IsType U [] (VExpr.wrapForalls (P ++ F) R) :=
    IsType.defeqU_l henv trivial hdefL.symm hctorT
  have hPF := IsType.wrapForalls_inv henv (Γ := []) trivial hCT
  simp only [List.append_nil] at hPF
  obtain ⟨hctxPF, hRT⟩ := hPF
  have hctxP : OnCtx P.reverse (env.IsType U) := by
    have h := hctxPF
    rw [List.reverse_append] at h
    exact OnCtx.of_append h
  -- the family applied to the parameter variables is a type
  obtain ⟨typeConst, normalized, ownParams, rest, exprType, ctorParams, tail, hlookup, hnorm,
    hown, hctorP, hctx, indices, result, hind, hres⟩ := Ordered.projectionShape_params henv hinfo
  rw [hni] at hind
  cases Option.some.inj hind
  obtain ⟨hshapeN, hownl⟩ := takeForalls_eq_wrapForalls' hown
  obtain ⟨hshapeC, hctorl⟩ := takeForalls_eq_wrapForalls' hctorP
  have hdefL' : env.IsDefEqU U [] (VExpr.wrapForalls P (VExpr.wrapForalls F R))
      (VExpr.wrapForalls (ctorParams.map (·.instL ls)) (tail.instL ls)) := by
    rw [← VExpr.wrapForalls_append, ← VExpr.instL_wrapForalls, ← hshapeC]; exact hdefL
  have hctxPC := IsDefEqU.wrapForalls_context' henv (Γ₀ := []) trivial .zero
    (by simp [hnpP, hctorl]) hdefL'
  simp only [List.append_nil] at hctxPC
  have hctxOC := IsDefEqCtx.instL hls hctx
  have hPO : IsDefEqCtx env U [] P.reverse (ownParams.map (·.instL ls)).reverse := by
    have h2 := hctxOC.symm henv.ordered
    rw [← List.map_reverse, ← List.map_reverse] at hctxPC
    exact IsDefEqCtx.trans_empty henv (by simpa [List.map_reverse] using hctxPC)
      (by simpa [List.map_reverse] using h2)
  have hPcl := OnCtx.closed_reverse henv.ordered hctxP
  have hT0 := TelInst.ident (env := env) (U := U) [] hPcl
  simp only [List.append_nil] at hT0
  have hT1 := TelInst.of_ctxDefEq henv hctxP hT0 hPO
  obtain ⟨uR, huR⟩ := hRT
  obtain ⟨_, hRhd⟩ := VExpr.WF.of_mkApps henv.ordered hctxPF (f := .const S ls) ⟨_, huR⟩
  obtain ⟨ci, hci, _, hlen⟩ := HasType.const_inv henv.ordered hctxPF hRhd
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hnormL := (hnorm.instL hls).weak0 henv.ordered (Γ := P.reverse)
  have hconst : env.HasType U P.reverse (.const S ls) (typeConst.type.instL ls) := .const hlookup hls hlen
  have hconst' := hconst.defeqU_r henv hctxP ⟨_, hnormL⟩
  rw [hshapeN, VExpr.instL_wrapForalls] at hconst'
  have hMajT := HasType.mkApps_of_tel henv hctxP hconst' hT1
  have hTC : env.IsType U [] (typeConst.type.instL ls) :=
    (henv.ordered.constWF hlookup).instL hls
  have hNT : env.IsType U [] (normalized.instL ls) :=
    IsType.defeqU_l henv trivial ⟨_, hnorm.instL hls⟩ hTC
  rw [hshapeN, VExpr.instL_wrapForalls] at hNT
  have hΔo : OnCtx (ownParams.map (·.instL ls)).reverse (env.IsType U) := by
    simpa using (IsType.wrapForalls_inv henv (Γ := []) trivial hNT).1
  have hresL : env.IsDefEq U (ownParams.map (·.instL ls)).reverse (rest.instL ls)
      (.sort (info.resultLevel.inst ls)) (.sort (info.resultLevel.inst ls).succ) := by
    simpa [List.map_reverse, VExpr.instL, VLevel.inst] using hres.instL hls
  have hinst := IsDefEq.closed_instOuter_congr henv hctxP hΔo hresL hT1.1 hT1.1
    (fun j hj _ hd => hT1.2 j hj hd)
  simp only [VExpr.instOuter_sort] at hinst
  have hMaj : env.HasType U P.reverse (VExpr.mkApps (.const S ls) (bvarRange P.length P.length))
      (.sort (info.resultLevel.inst ls)) := hinst.defeq hMajT
  -- the telescope pieces
  have hsM : gp.sMajor ⟨0, by simp [sv, caseView]⟩ =
      VExpr.mkApps (.const S ls) (bvarRange P.length P.length) := by
    simp only [Instance.sMajor]
    have e1 : (sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)]).indices = [] := hI
    have e2 : (sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)]).name = S := hfam
    rw [e1, e2]
    simp only [List.length_nil, List.append_nil]
    rw [VEnv.vars_eq_bvarRange, Nat.add_zero]
    simp [sv, caseView, P, gp, vars]
  have hsC : gp.sCtorApp c' = VExpr.mkApps (.const info.ctorName ls)
      (bvarRange (P.length + F.length) (P.length + F.length)) := by
    simp only [Instance.sCtorApp, hsF]
    simp [sv, caseView, P, F, c', gp]
  rw [hsH, hsF, hsM, hsC, hP]
  simp only [List.append_nil, List.length_nil, Nat.add_zero, VExpr.liftN_zero]
  let Maj := VExpr.mkApps (.const S ls) (bvarRange P.length P.length)
  let MotT := VExpr.forallE Maj (.sort .zero)
  let Ctor := VExpr.mkApps (.const info.ctorName ls)
    (bvarRange (P.length + F.length) (P.length + F.length))
  have hMot : env.IsType U P.reverse MotT :=
    IsType.forallE ⟨_, hMaj⟩ ⟨_, HasType.sort (by trivial)⟩
  -- the constructor at the parameter and field variables
  have hctorC := Ordered.projectionConstructor henv.ordered hinfo
  have hCtor : env.HasType U (P ++ F).reverse Ctor R := by
    have h1 : env.HasType U (P ++ F).reverse (.const info.ctorName ls) (info.ctorType.instL ls) :=
      .const hctorC hls hlslen
    have h2 := h1.defeqU_r henv hctxPF (hdefL.symm.weak0 henv.ordered)
    have hPFcl := OnCtx.closed_reverse henv.ordered hctxPF
    have hT := TelInst.ident (env := env) (U := U) [] hPFcl
    simp only [List.append_nil, List.length_append] at hT
    have h3 := HasType.mkApps_of_tel henv hctxPF h2 hT
    have hRcl : R.ClosedN (P.length + F.length) := by
      simp only [R]
      apply VExpr.ClosedN.mkApps_closed (show (VExpr.const S ls).ClosedN _ from trivial)
      intro a ha
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      show _ < _
      simp [P, F]; omega
    rw [VExpr.instOuter_range_bvar' _ _ _ hRcl (Nat.le_refl _), Nat.sub_self,
      VExpr.liftN_zero] at h3
    exact h3
  -- the minor premise
  have hFctx : OnCtx ((insertBinders F 1).reverse ++ [MotT] ++ P.reverse) (env.IsType U) :=
    OnCtx.insert_binders henv.ordered (X := [MotT])
      (by simpa [List.reverse_append] using hctxPF) ⟨hctxP, hMot⟩
  have hW : Ctx.LiftN 1 F.length (F.reverse ++ P.reverse)
      ((insertBinders F 1).reverse ++ [MotT] ++ P.reverse) := by
    have h := insertBinders_liftN' F [MotT] P.reverse 1 rfl F.length (Nat.le_refl _)
    rwa [List.take_of_length_le (Nat.le_refl _),
      List.take_of_length_le (by rw [insertBinders_len]; exact Nat.le_refl _)] at h
  have hCtorW := hCtor.weakN henv.ordered (by simpa [List.reverse_append] using hW)
  have hlook := Lookup.reverse_append (P ++ [MotT] ++ insertBinders F 1) [] P.length
    (by simp)
  have hctxEq : (P ++ [MotT] ++ insertBinders F 1).reverse ++ [] =
      (insertBinders F 1).reverse ++ [MotT] ++ P.reverse := by simp
  rw [hctxEq] at hlook
  have hidx : (P ++ [MotT] ++ insertBinders F 1).length - 1 - P.length = F.length := by
    simp [insertBinders_len]
  have hget : (P ++ [MotT] ++ insertBinders F 1)[P.length]'(by simp) = MotT := by
    simp
  have hlen' : (P ++ [MotT] ++ insertBinders F 1).length - P.length = F.length + 1 := by
    simp [insertBinders_len]
  rw [hidx, hget, hlen'] at hlook
  have hmot : env.HasType U ((insertBinders F 1).reverse ++ [MotT] ++ P.reverse)
      (.bvar F.length) (MotT.liftN (F.length + 1)) := .bvar hlook
  have hMajLift : Maj.liftN (F.length + 1) = R.liftN 1 F.length := by
    simp only [Maj, R, VExpr.liftN_mkApps, VExpr.liftN]
    congr 1
    have hFR : F.length = RF.length := by simp [F]
    have hPR : P.length = RP.length := by simp [P]
    rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _), hFR, hPR]
    have hv : (vars RP.length RF.length).map (fun x => x.liftN 1 RF.length) =
        vars RP.length (RF.length + 1) := by
      simp only [vars, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, VExpr.liftN]
      congr 1
      simp only [liftVar]
      split <;> omega
    rw [hv, VEnv.vars_eq_bvarRange]
  have hMinBody : env.HasType U ((insertBinders F 1).reverse ++ [MotT] ++ P.reverse)
      (VExpr.mkApps (.bvar F.length) [Ctor.liftN 1 F.length]) (.sort .zero) := by
    have hm : env.HasType U ((insertBinders F 1).reverse ++ [MotT] ++ P.reverse)
        (.bvar F.length) (.forallE (R.liftN 1 F.length) (.sort .zero)) := by
      have := hmot
      simp only [MotT, VExpr.liftN, hMajLift] at this
      exact this
    exact HasType.app hm (by simpa using hCtorW)
  have hMin : env.IsType U (MotT :: P.reverse)
      (VExpr.wrapForalls (insertBinders F 1) (VExpr.mkApps (.bvar F.length)
        [Ctor.liftN 1 F.length])) :=
    IsType.wrapForalls_of (by simpa using hFctx) ⟨_, by simpa using hMinBody⟩
  let Min := VExpr.wrapForalls (insertBinders F 1) (VExpr.mkApps (.bvar F.length)
    [Ctor.liftN 1 F.length])
  have hMaj2 : env.HasType U (Min :: MotT :: P.reverse) (Maj.liftN 2)
      (.sort (info.resultLevel.inst ls)) := by
    have := hMaj.weakN henv.ordered (Ctx.LiftN.zero (n := 2) [Min, MotT] (Γ := P.reverse) rfl)
    exact this
  have hctx : OnCtx ((P ++ [MotT] ++ [Min] ++ [Maj.liftN 2]).reverse ++ []) (env.IsType U) := by
    simp only [List.append_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons_append]
    exact ⟨⟨⟨hctxP, hMot⟩, hMin⟩, ⟨_, hMaj2⟩⟩
  have hbody : env.IsType U ((P ++ [MotT] ++ [Min] ++ [Maj.liftN 2]).reverse ++ [])
      (.app (.bvar 2) (.bvar 0)) := by
    simp only [List.append_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons_append]
    have h2 : env.HasType U (Maj.liftN 2 :: Min :: MotT :: P.reverse) (.bvar 2)
        (.forallE (Maj.liftN 3) (.sort .zero)) := by
      have := HasType.bvar (env := env) (U := U)
        (Lookup.succ (Lookup.succ (Lookup.zero (ty := MotT) (Γ := P.reverse)) (A := Min))
          (A := Maj.liftN 2))
      simpa [MotT, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using this
    have h0 : env.HasType U (Maj.liftN 2 :: Min :: MotT :: P.reverse) (.bvar 0) (Maj.liftN 3) := by
      have := HasType.bvar (env := env) (U := U)
        (Lookup.zero (ty := Maj.liftN 2) (Γ := Min :: MotT :: P.reverse))
      simpa [VExpr.lift, VExpr.liftN_liftN] using this
    exact ⟨_, HasType.app h2 h0⟩
  exact IsType.wrapForalls_of hctx hbody

end VEnv
end Lean4Lean
