import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaHistory
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.CompilationMajors

/-! # The syntax of the restored rules of a nested block

A nested compilation's block is the restoration (`compilationRestoration`) of the generator's
output: an auxiliary family `Aux` is restored to its container family `I` at the specialization
arguments `Ds` (`HeadSpecialization.apply`), an auxiliary constructor to the container's
constructor at `Ds`, and the generated recursor names are renamed. This file computes the
restored recursor types, minors and equations (`Model.Nested.*`), classifies the constructors
of a nested signature into the source declaration's and the containers' (`ctor_cases`), and
proves the injectivity facts the model needs. -/

namespace Lean4Lean
namespace VEnv
namespace Model
namespace Nested
open InductiveSignature

/-! ## Lists under `mapM` -/

theorem mapM_length {f : VExpr → Option VExpr} : ∀ {l l' : List VExpr},
    l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', -, l'', hl, rfl⟩ := h
    simp [mapM_length hl]

theorem mapM_getElem? {f : VExpr → Option VExpr} : ∀ {l l' : List VExpr} {i : Nat} {a : VExpr},
    l.mapM f = some l' → l[i]? = some a → ∃ a', f a = some a' ∧ l'[i]? = some a'
  | [], _, _, _, _, h => by simp at h
  | b :: l, l', i, a, hm, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
    obtain ⟨b', hb, l'', hl, rfl⟩ := hm
    cases i with
    | zero => simp at h; subst h; exact ⟨b', hb, rfl⟩
    | succ i =>
      simp at h
      obtain ⟨a', h1, h2⟩ := mapM_getElem? hl h
      exact ⟨a', h1, by simpa using h2⟩

theorem mapM_get {f : VExpr → Option VExpr} {l l' : List VExpr} (h : l.mapM f = some l')
    (i : Nat) (hi : i < l.length) :
    f l[i] = some (l'[i]'(by rw [mapM_length h]; exact hi)) := by
  obtain ⟨a', h1, h2⟩ := mapM_getElem? h (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem (by rw [mapM_length h]; exact hi)] at h2
  rw [h1, h2]

theorem mapM_append {f : VExpr → Option VExpr} {l₁ l₂ l' : List VExpr}
    (h : (l₁ ++ l₂).mapM f = some l') :
    ∃ l₁' l₂', l₁.mapM f = some l₁' ∧ l₂.mapM f = some l₂' ∧ l' = l₁' ++ l₂' := by
  rw [List.mapM_append] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨l₁', h1, l₂', h2, rfl⟩ := h
  exact ⟨l₁', l₂', h1, h2, rfl⟩

theorem mapM_map_of {f f' : VExpr → Option VExpr} {g g' : VExpr → VExpr} :
    ∀ {l l' : List VExpr}, (∀ x y, f x = some y → f' (g x) = some (g' y)) →
    l.mapM f = some l' → (l.map g).mapM f' = some (l'.map g')
  | [], l', _, h => by simp at h; subst h; rfl
  | a :: l, l', H, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, l'', hl, rfl⟩ := h
    simp only [List.map_cons, List.mapM_cons, H _ _ ha, mapM_map_of H hl]
    rfl

/-! ## Restoration of telescopes and spines -/

theorem expr_wrapForalls_parts {r : Restoration} {ds : List VExpr} {b out : VExpr}
    (h : r.expr (.wrapForalls ds b) = some out) :
    ∃ ds' b', ds.mapM r.expr = some ds' ∧ r.expr b = some b' ∧ out = .wrapForalls ds' b' := by
  rw [Restoration.expr_wrapForalls] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ds', h1, b', h2, rfl⟩ := h
  exact ⟨ds', b', h1, h2, rfl⟩

theorem expr_wrapLams_parts {r : Restoration} {ds : List VExpr} {b out : VExpr}
    (h : r.expr (.wrapLams ds b) = some out) :
    ∃ ds' b', ds.mapM r.expr = some ds' ∧ r.expr b = some b' ∧ out = .wrapLams ds' b' := by
  rw [Restoration.expr_wrapLams] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ds', h1, b', h2, rfl⟩ := h
  exact ⟨ds', b', h1, h2, rfl⟩

/-- The head of a restored constant spine whose name is a specialized head. -/
theorem go_head {r : Restoration} (hr : r.Scoped) {spec : HeadSpecialization}
    (hmem : spec ∈ r.heads) (lv : List VLevel) (args : List VExpr) :
    Restoration.expr.go r (.const spec.auxiliary lv) args = spec.apply lv args := by
  unfold Restoration.expr.go
  cases hf : r.heads.find? (fun h => h.auxiliary == spec.auxiliary) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf spec hmem
    simp at hfalse
  | some found =>
    have hfound := List.mem_of_find?_eq_some hf
    have hname : found.auxiliary = spec.auxiliary := by simpa using List.find?_some hf
    have heq := List.eq_of_mem_of_nodup_map hr.1 hfound hmem hname
    subst heq
    rfl

/-- The head of a restored constant spine whose name is not a specialized head. -/
theorem go_nonhead {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) (lv : List VLevel) (args : List VExpr) :
    Restoration.expr.go r (.const name lv) args =
      some (.mkApps (.const (r.recursorName name) lv) args) := by
  simp only [Restoration.expr.go, Restoration.heads_find?_eq_none h]

theorem instantiateParams_vars {e : VExpr} {n : Nat} (he : e.ClosedN n) (k : Nat) :
    instantiateParams e (vars n k) = e.liftN k := by
  rw [← (VExpr.subst_id (e := e.liftN k)), VExpr.liftN_subst]
  unfold instantiateParams
  apply VExpr.subst_congr_closedN he
  intro i hi
  have hl : (vars n k).length = n := vars_len n k
  rw [dif_pos (by omega)]
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN, VExpr.Subst.id]
  rw [show (vars n k)[(vars n k).length - 1 - i] = .bvar (k + i) by
    simp only [vars_unfold, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_map, List.length_reverse, List.length_range]
    congr 1; omega]
  rw [liftVar_le (by omega)]

theorem vars_map_instL_liftN (np d : Nat) (lv : List VLevel) :
    (vars np 0).map (fun e => (e.instL lv).liftN d) = vars np d := by
  simp only [vars_unfold, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, VExpr.instL, VExpr.liftN, liftVar]
  rw [if_neg (by omega)]
  congr 1; omega

theorem mapM_expr_vars (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  rw [vars_unfold]
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [List.map_cons, List.mapM_cons, ih]
    rfl

/-! ## Specialized spines

`Spec r name np target lvf Ds0`: restoring a spine of the constant `name` at levels `lv` over
the `np` parameter variables (beneath `d` binders) and further arguments `rest` gives the
constant `target` at the levels `lvf lv` over the specialization arguments `Ds0` (scoped over
the parameters) and the restored further arguments. A source family or constructor is its own
specialization at the parameter variables; an auxiliary one is its container's at the
specialization arguments. -/
structure Spec (r : Restoration) (name : Name) (np : Nat) (target : Name)
    (lvf : List VLevel → List VLevel) (Ds0 : List VExpr) : Prop where
  closed : ∀ e ∈ Ds0, e.ClosedN np
  lvf_inst : ∀ lv ls, (lvf lv).map (·.inst ls) = lvf (lv.map (·.inst ls))
  spine : ∀ lv d (rest : List VExpr) out,
    r.expr (.mkApps (.const name lv) (vars np d ++ rest)) = some out →
    ∃ rest', rest.mapM r.expr = some rest' ∧
      out = .mkApps (.const target (lvf lv)) (Ds0.map (fun e => (e.instL lv).liftN d) ++ rest')

theorem Spec.of_nonhead {r : Restoration} {name : Name} (np : Nat)
    (hh : name ∉ r.heads.map (·.auxiliary)) (hrec : name ∉ r.recursors.map Prod.fst) :
    Spec r name np name id (vars np 0) where
  closed e he := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (by rw [vars_unfold] at he; exact he)
    simp only [List.mem_reverse, List.mem_range] at hi
    show 0 + i < np
    omega
  lvf_inst _ _ := rfl
  spine lv d rest out h := by
    rw [Restoration.expr_mkApps] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨args', hargs, hout⟩ := h
    obtain ⟨l1, l2, h1, h2, rfl⟩ := mapM_append hargs
    rw [mapM_expr_vars] at h1
    cases h1
    rw [go_nonhead hh, Restoration.recursorName_of_not_mem hrec] at hout
    refine ⟨l2, h2, ?_⟩
    rw [← Option.some.inj hout, vars_map_instL_liftN]
    rfl

theorem Spec.of_head {r : Restoration} (hr : r.Scoped) {spec : HeadSpecialization}
    (hmem : spec ∈ r.heads) :
    Spec r spec.auxiliary spec.nparams spec.target (fun lv => spec.levels.map (·.inst lv))
      spec.arguments where
  closed e he := ((hr.2.2.1 spec hmem).2 e he)
  lvf_inst lv ls := by simp only [List.map_map, Function.comp_def, VLevel.inst_inst]
  spine lv d rest out h := by
    rw [Restoration.expr_mkApps] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨args', hargs, hout⟩ := h
    obtain ⟨l1, l2, h1, h2, rfl⟩ := mapM_append hargs
    rw [mapM_expr_vars] at h1
    cases h1
    rw [go_head hr hmem] at hout
    unfold HeadSpecialization.apply at hout
    split at hout
    · cases hout
    · have hl : (vars spec.nparams d).length = spec.nparams := vars_len _ _
      refine ⟨l2, h2, ?_⟩
      simp only [Option.pure_def, Option.some.injEq] at hout
      rw [← hout, List.take_left' hl, List.drop_left' hl]
      congr 2
      apply List.map_congr_left
      intro e he
      exact instantiateParams_vars ((hr.2.2.1 spec hmem).2 e he).instL d

/-! ## The families and constructors of a nested signature -/

/-- The constructors of a specialized family: the container's constructors, renamed, at the
specialization. -/
theorem specializedFamily_ctor {a : ContainerSpecialization} {uv : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily uv params = some direct)
    {fc : VConstVal} (hfc : fc ∈ direct.ctors) :
    ∃ c ∈ a.source.ctors, ∃ T, specializeType (c.type.instL a.levels) a.arguments = some T ∧
      fc = { name := a.constructorName c, uvars := uv, type := VExpr.wrapForalls params T } := by
  unfold ContainerSpecialization.specializedFamily at H
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at H
  obtain ⟨type, -, ctors, hctors, rfl⟩ := H
  obtain ⟨c, hc, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp hctors) fc hfc
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hrel
  obtain ⟨T, hT, rfl⟩ := hrel
  exact ⟨c, hc, T, hT, rfl⟩

theorem specializedFamily_resultLevel {a : ContainerSpecialization} {uv : Nat}
    {params : List VExpr} {direct : VInductiveType} (H : a.specializedFamily uv params = some direct) :
    direct.resultLevel = a.source.resultLevel.inst a.levels := by
  unfold ContainerSpecialization.specializedFamily at H
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at H
  obtain ⟨_, _, _, _, rfl⟩ := H
  rfl

/-- **The constructor of a nested signature**: a source constructor of a source family, or an
auxiliary constructor of an auxiliary family, restored to a container constructor at the
specialization; in both cases the restoration of the family's and the constructor's spines. -/
theorem ctor_cases {base : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock}
    (C : CompilationData base source expanded s g aux block) (index : Fin s.constructors.size) :
    ∃ envTypes, base.addConstVals source.typeConstants = some envTypes ∧
    ((∃ t ∈ source.types, ∃ fc ∈ t.ctors,
      s.families[s.constructors[index].owner].name = t.name ∧
      s.constructors[index].name = fc.name ∧
      RestoresFamily (compilationRestoration source aux) envTypes source.uvars
        (s.declarationFamily s.constructors[index].owner) t ∧
      RestoresType (compilationRestoration source aux) envTypes source.uvars
        (s.constructorType s.constructors[index]) fc.type ∧
      Spec (compilationRestoration source aux) t.name s.params.length t.name id
        (vars s.params.length 0) ∧
      Spec (compilationRestoration source aux) fc.name s.params.length fc.name id
        (vars s.params.length 0)) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, ∃ T,
      s.families[s.constructors[index].owner].name = a.auxiliary ∧
      s.constructors[index].name = a.constructorName c ∧
      specializeType (c.type.instL a.levels) a.arguments = some T ∧
      RestoresType (compilationRestoration source aux) envTypes source.uvars
        (s.constructorType s.constructors[index]) (VExpr.wrapForalls s.params T) ∧
      s.families[s.constructors[index].owner].resultLevel ≈ a.source.resultLevel.inst a.levels ∧
      a.WellFormed envTypes source s.params ∧
      Spec (compilationRestoration source aux) a.auxiliary s.params.length a.source.name
        (fun lv => a.levels.map (·.inst lv)) a.arguments ∧
      Spec (compilationRestoration source aux) (a.constructorName c) s.params.length c.name
        (fun lv => a.levels.map (·.inst lv)) a.arguments)) := by
  have hnp : s.params.length = source.nparams := C.model.nparams.trans C.nparams
  obtain ⟨envTypes, direct, htypes, hdirect, hwf, hfamilies⟩ := C.correspondence
  refine ⟨envTypes, htypes, ?_⟩
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨fc, hfc, hrelc⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  have hname : s.families[s.constructors[index].owner].name = family.name := hrel.name
  have hcname : s.constructors[index].name = fc.name := hrelc.1
  have hscoped := C.restorationScoped
  rcases List.mem_append.mp hfamily with hsrc | hdir
  · left
    have hnot : ∀ n ∈ familyNames source.types,
        n ∉ (compilationRestoration source aux).heads.map (·.auxiliary) ∧
        n ∉ (compilationRestoration source aux).recursors.map Prod.fst := by
      intro n hn
      refine ⟨fun h => C.toCaseCompilationData.source_head_disjoint hn h, fun h => ?_⟩
      obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
      exact C.source_recursors_disjoint hn (C.recursor_source_mem hpair)
    have hfn : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_self⟩
    have hcn : fc.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨fc, hfc, rfl⟩)⟩
    exact ⟨family, hsrc, fc, hfc, hname, hcname, hrel, hrelc.2.2,
      Spec.of_nonhead _ (hnot _ hfn).1 (hnot _ hfn).2,
      Spec.of_nonhead _ (hnot _ hcn).1 (hnot _ hcn).2⟩
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hdir
    obtain ⟨c, hc, T, hT, rfl⟩ := specializedFamily_ctor hdf hfc
    have hfa : family.name = a.auxiliary := ContainerSpecialization.directFamily_name hdf
    have hmemF : HeadSpecialization.mk a.auxiliary source.uvars source.nparams a.source.name
        a.levels a.arguments ∈ (compilationRestoration source aux).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hmemC : HeadSpecialization.mk (a.constructorName c) source.uvars source.nparams c.name
        a.levels a.arguments ∈ (compilationRestoration source aux).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
    have hsF := Spec.of_head hscoped hmemF
    have hsC := Spec.of_head hscoped hmemC
    simp only at hsF hsC
    rw [← hnp] at hsF hsC
    refine ⟨a, ha, c, hc, T, hname.trans hfa, hcname, hT, hrelc.2.2, ?_, hwf a ha, hsF, hsC⟩
    have := hrel.resultLevel
    rwa [specializedFamily_resultLevel hdf] at this

theorem mapM_map_inv {f : VExpr → Option VExpr} {φ : VExpr → VExpr}
    (hφ : ∀ x, f (φ x) = (f x).map φ) :
    ∀ {l L : List VExpr}, (l.map φ).mapM f = some L → ∃ l', l.mapM f = some l' ∧ L = l'.map φ
  | [], L, h => by simp at h; subst h; exact ⟨[], rfl, rfl⟩
  | a :: l, L, h => by
    simp only [List.map_cons, List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, hb, L', hL', rfl⟩ := h
    rw [hφ] at hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨l', hl', rfl⟩ := mapM_map_inv hφ hL'
    exact ⟨a' :: l', by rw [List.mapM_cons, ha', hl']; rfl, rfl⟩

theorem Spec.target_unique {r : Restoration} {n t₁ t₂ : Name} {np : Nat}
    {f₁ f₂ : List VLevel → List VLevel} {D₁ D₂ : List VExpr}
    (h₁ : Spec r n np t₁ f₁ D₁) (h₂ : Spec r n np t₂ f₂ D₂) {lv : List VLevel} {d : Nat}
    {rest : List VExpr} {out : VExpr}
    (h : r.expr (.mkApps (.const n lv) (vars np d ++ rest)) = some out) : t₁ = t₂ := by
  obtain ⟨_, -, e₁⟩ := h₁.spine lv d rest out h
  obtain ⟨_, -, e₂⟩ := h₂.spine lv d rest out h
  exact VExpr.mkApps_const_name_inj (e₁.symm.trans e₂)

/-- Restoration commutes with lifting (for the heads of a scoped table). -/
theorem expr_liftN_some {r : Restoration} (hsc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {e e' : VExpr} (h : r.expr e = some e') (n k : Nat) : r.expr (e.liftN n k) = some (e'.liftN n k) := by
  rw [← Restoration.expr_liftN r hsc, h]; rfl

theorem expr_instL_some {r : Restoration} {e e' : VExpr} (h : r.expr e = some e')
    (ls : List VLevel) : r.expr (e.instL ls) = some (e'.instL ls) := by
  rw [← Restoration.expr_instL, h]; rfl

/-- **A restored minor premise**: a telescope whose body applies the constructor's motive to the
restored indices and to the restored constructor application. -/
theorem restored_minor {s : InductiveSignature} (g : Instance s) {r : Restoration}
    (hsc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (ctor : Constructor s.families.size) (prior : Nat) {c0 : Name}
    {lvf : List VLevel → List VLevel} {Ds0 : List VExpr}
    (hS : Spec r ctor.name s.params.length c0 lvf Ds0) {out : VExpr}
    (h : r.expr (g.minor ctor prior) = some out) :
    ∃ Dm ctorIdx margs, Dm.length = ctor.fields.length + (Instance.recursiveFields ctor).length ∧
      (ctor.indices.map (·.instL g.levels)).mapM r.expr = some ctorIdx ∧
      out = .wrapForalls Dm (.mkApps (.bvar (ctor.fields.length + (Instance.recursiveFields ctor).length +
          prior + (s.families.size - 1 - ctor.owner.val)))
        (ctorIdx.map (fun e => (e.liftN (Instance.recursiveFields ctor).length).liftN
            (s.families.size + prior) (ctor.fields.length + (Instance.recursiveFields ctor).length)) ++
          [.mkApps (.const c0 (lvf g.levels)) margs])) := by
  unfold Instance.minor at h
  obtain ⟨Dm, b, hDm, hb, rfl⟩ := expr_wrapForalls_parts h
  rw [Restoration.expr_mkApps_bvar] at hb
  obtain ⟨args', hargs, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨l1, l2, h1, h2, rfl⟩ := mapM_append hargs
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h2
  obtain ⟨major, hmaj, _, rfl, rfl⟩ := h2
  obtain ⟨rest', hrest, rfl⟩ := hS.spine _ _ _ _ hmaj
  obtain ⟨ctorIdx, hci, rfl⟩ := mapM_map_inv (φ := fun e => (e.liftN (Instance.recursiveFields ctor).length).liftN
      (s.families.size + prior) (ctor.fields.length + (Instance.recursiveFields ctor).length))
    (fun x => by
      show r.expr _ = _
      rw [← Restoration.expr_liftN r hsc, ← Restoration.expr_liftN r hsc]
      cases r.expr x <;> rfl)
    (l := ctor.indices.map (·.instL g.levels)) (by simpa [List.map_map, Function.comp_def] using h1)
  have hl : (Dm.length = ctor.fields.length + (Instance.recursiveFields ctor).length) := by
    rw [mapM_length hDm]
    simp [insertBinders, fieldTypes]
  simp only [List.length_map, List.length_zipIdx]
  exact ⟨Dm, ctorIdx, _, hl, hci, rfl⟩

theorem expr_liftN_map {r : Restoration}
    (hsc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams) (n k : Nat) (x : VExpr) :
    r.expr (x.liftN n k) = (r.expr x).map (·.liftN n k) := by
  rw [← Restoration.expr_liftN r hsc]

/-- **A restored generated equation**: its binders are the restored binders of the generated
equation, its left side applies the renamed recursor to the restored lead and to the restored
constructor application, its right side is a restored body under the same binders. -/
theorem restored_equation {base : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock}
    (C : CompilationData base source expanded s g aux block) (index : Fin s.constructors.size)
    {c0 : Name} {lvf : List VLevel → List VLevel} {Ds0 : List VExpr}
    (hS : Spec (compilationRestoration source aux) s.constructors[index].name s.params.length c0
      lvf Ds0) {df : VDefEq}
    (h : (compilationRestoration source aux).equation (g.equation index) = some df) :
    ∃ ds' ctorIdx body' args',
      (g.eqDoms index).mapM (compilationRestoration source aux).expr = some ds' ∧
      (s.constructors[index].indices.map (·.instL g.levels)).mapM
        (compilationRestoration source aux).expr = some ctorIdx ∧
      df.lhs = .wrapLams ds' (.mkApps (.const ((compilationRestoration source aux).recursorName
          (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
            s.constructors[index].fields.length ++
          ctorIdx.map (·.liftN (s.families.size + s.constructors.size)
            s.constructors[index].fields.length) ++
          [.mkApps (.const c0 (lvf g.levels))
            (Ds0.map (fun e => (e.instL g.levels).liftN
              (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
              vars s.constructors[index].fields.length 0)])) ∧
      df.rhs = .wrapLams ds' body' ∧
      body' = .mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size - 1 -
        index.val)) args' ∧
      df.uvars = g.uvars := by
  have hsc : ∀ h ∈ (compilationRestoration source aux).heads, ∀ e ∈ h.arguments,
      e.ClosedN h.nparams := fun h hh => (C.restorationScoped.2.2.1 h hh).2
  obtain ⟨hl, hr, -⟩ := Restoration.equation_parts h
  have huv : df.uvars = g.uvars := by
    simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, h⟩ := h
    cases h; rfl
  rw [g.equation_lhs_eq] at hl
  rw [g.equation_rhs_eq] at hr
  obtain ⟨ds', l, hds, hl', el⟩ := expr_wrapLams_parts hl
  obtain ⟨ds2, b, hds2, hb, er⟩ := expr_wrapLams_parts hr
  cases hds.symm.trans hds2
  -- the right side's body
  simp only [Instance.eqBody] at hb
  rw [Restoration.expr_mkApps_bvar] at hb
  obtain ⟨args', -, rfl⟩ := Option.map_eq_some_iff.1 hb
  -- the left side's body
  rw [Restoration.expr_mkApps] at hl'
  simp only [Option.bind_eq_some_iff] at hl'
  obtain ⟨as, has, hout⟩ := hl'
  rw [go_nonhead (fun hm => by
    obtain ⟨spec, hspec, he⟩ := List.mem_map.1 hm
    exact C.heads_not_recursors _ spec hspec he)] at hout
  obtain ⟨l1, l2, h1, h2, rfl⟩ := mapM_append has
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h2
  obtain ⟨major, hmaj, _, rfl, rfl⟩ := h2
  simp only [eqMs, eqFs, Nat.add_zero] at hmaj
  rw [show (List.range s.constructors[index].fields.length).reverse.map VExpr.bvar =
    vars s.constructors[index].fields.length 0 from (vars_zero _).symm] at hmaj
  obtain ⟨rest', hrest, rfl⟩ := hS.spine _ _ _ _ hmaj
  rw [mapM_expr_vars] at hrest
  cases hrest
  simp only [Instance.eqLead] at h1
  obtain ⟨l11, l12, h11, h12, rfl⟩ := mapM_append h1
  rw [mapM_expr_vars] at h11
  cases h11
  simp only [Instance.eqIndices] at h12
  obtain ⟨ctorIdx, hci, rfl⟩ := mapM_map_inv
    (φ := fun e => e.liftN (s.families.size + s.constructors.size) s.constructors[index].fields.length)
    (fun x => expr_liftN_map hsc _ _ x)
    (l := s.constructors[index].indices.map (·.instL g.levels))
    (by simpa [List.map_map, Function.comp_def] using h12)
  refine ⟨ds', ctorIdx, _, args', hds, hci, ?_, er, rfl, huv⟩
  rw [el, ← Option.some.inj hout]

theorem recursor_parts {r : Restoration} {value value' : VConstVal}
    (h : r.recursor value = some value') :
    value'.name = r.recursorName value.name ∧ value'.uvars = value.uvars ∧
      r.expr value.type = some value'.type := by
  simp only [Restoration.recursor, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨rfl, rfl, ht⟩

theorem expr_recBody {s : InductiveSignature} (g : Instance s) (r : Restoration)
    (o : Fin s.families.size) : r.expr (g.recBody o) = some (g.recBody o) := by
  simp only [Instance.recBody]
  rw [Restoration.expr_mkApps_bvar, List.mapM_append, mapM_expr_vars]
  rfl

/-- **The restored recursor of a rule**: a recursor of the declaration whose name is the renamed
generated recursor name of a family is the restoration of that family's generated recursor. -/
theorem restored_recursor {base : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock}
    (C : CompilationData base source expanded s g aux block) (hrecsOf : source.RecsOf block)
    {rec : VRecursor} (hrec : rec ∈ source.recs) (o : Fin s.families.size)
    (hname : rec.name = (compilationRestoration source aux).recursorName (g.recursorName o)) :
    ∃ dsH', (g.recDoms o).mapM (compilationRestoration source aux).expr = some dsH' ∧
      rec.type = .wrapForalls dsH' (g.recBody o) ∧ rec.uvars = g.uvars := by
  have hrs := List.mapM_eq_some.mp C.recursors
  obtain ⟨rr, hrr, hr⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrs (g.recursor o)
    (g.recursor_mem o)
  obtain ⟨hn, hu, ht⟩ := recursor_parts hr
  have hmem : rec.toVConstVal ∈ block.recursors := by
    rw [← hrecsOf.recursors]; exact List.mem_map_of_mem hrec
  have hnd : (block.recursors.map (·.name)).Nodup := by
    have := C.names
    simp only [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  have heq : rec.toVConstVal = rr :=
    VEnv.inj_on_of_nodup_map hnd hmem hrr (hname.trans hn.symm)
  rw [show (g.recursor o).type = .wrapForalls (g.recDoms o) (g.recBody o) from
    g.recursorType_eq_recDoms o] at ht
  obtain ⟨dsH', b, hds, hb, et⟩ := expr_wrapForalls_parts ht
  rw [expr_recBody] at hb
  cases hb
  refine ⟨dsH', hds, ?_, ?_⟩
  · show rec.toVConstVal.type = _
    rw [heq, et]
  · show rec.toVConstVal.uvars = _
    rw [heq, hu]; rfl

/-- **The counts of a rule read off a restored equation.** -/
theorem rule_counts {env base : VEnv} {decl expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock}
    (hdecl : decl.WF env) (hrecsOf : decl.RecsOf block)
    (C : CompilationData base decl expanded s g aux block)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (index : Fin s.constructors.size) {c0 : Name} {lvf : List VLevel → List VLevel}
    {Ds0 : List VExpr}
    (hS : Spec (compilationRestoration decl aux) s.constructors[index].name s.params.length c0
      lvf Ds0) {df : VDefEq}
    (hres : (compilationRestoration decl aux).equation (g.equation index) = some df)
    (H : VRecRule.OfEquation rec ru df) :
    rec.name = (compilationRestoration decl aux).recursorName
        (g.recursorName s.constructors[index].owner) ∧
      ru.ctor = c0 ∧ ru.rhs = df.rhs ∧
      rec.numParams + rec.numMotives + rec.numMinors =
        s.params.length + (s.families.size + s.constructors.size) ∧
      rec.numIndices = s.families[s.constructors[index].owner].indices.length ∧
      ru.ctorParams = Ds0.length ∧ ru.nfields = s.constructors[index].fields.length ∧
      s.constructors[index].indices.length =
        s.families[s.constructors[index].owner].indices.length := by
  obtain ⟨ds', ctorIdx, body', args', hds, hci, hl, hr, hb, -⟩ := restored_equation C index hS hres
  have harity : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length :=
    C.model.constructorArity s.constructors[index] (by simp)
  obtain ⟨hrhs, hhead, hlen, major, hmajor, hmc, hml⟩ := H
  rw [hl, VExpr.lamBody_wrapLams, VExpr.lamBody_mkApps_const] at hhead hlen hmajor
  rw [VExpr.headConst?_eq_some] at hhead
  obtain ⟨us, hus⟩ := hhead
  simp only [VExpr.getAppFn_mkApps, VExpr.getAppFn] at hus
  have hname := (VExpr.const.inj hus).1.symm
  rw [VExpr.getAppArgs_mkApps] at hlen hmajor
  simp only [VExpr.getAppArgs, List.nil_append, List.length_append, List.length_singleton,
    List.length_map, vars_len] at hlen
  simp only [VExpr.getAppArgs, List.nil_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hmajor
  subst hmajor
  rw [VExpr.headConst?_eq_some] at hmc
  obtain ⟨us', hus'⟩ := hmc
  rw [VExpr.getAppFn_mkApps] at hus'
  simp only [VExpr.getAppFn, VExpr.const.injEq] at hus'
  rw [VExpr.getAppArgs_mkApps] at hml
  simp only [VExpr.getAppArgs, List.nil_append, List.length_append, List.length_map,
    vars_len] at hml
  -- the recursor's indices
  obtain ⟨dsH', hdsH, htype, -⟩ := restored_recursor C hrecsOf hrec _ hname
  obtain ⟨-, -, -, j, hj, -, hbody⟩ := hdecl.rec_shape rec hrec
  rw [htype] at hbody
  simp only [Instance.recBody] at hbody
  rw [VExpr.mkApps_snoc, Model.piBody_wrapForalls_app, ← VExpr.mkApps_snoc] at hbody
  have hlenI := getAppArgs_length_eq_of_mkApps_bvar hbody
  simp only [List.length_append, vars_len, List.length_singleton,
    VExpr.bvarsDesc_length, insertBinders, List.length_map, List.length_zipIdx] at hlenI
  have hci_l := mapM_length hci
  simp only [List.length_map] at hci_l
  have hmaj' : rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices =
      s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].indices.length := by
    simp only [VRecursor.getMajorIdx] at hlen
    omega
  -- the number of fields, from the rule's shape
  obtain ⟨_, -, _, -, -, -, hrs⟩ := hdecl.rule_shape rec hrec ru hru
  have hla := hrs.1
  rw [← hrhs, hr, lamArity_wrapLams, mapM_length hds, Instance.eqDoms_length, hb,
    lamArity_mkApps_bvar] at hla
  refine ⟨hname, hus'.1.symm, hrhs.symm, by omega, by omega, by omega, by omega, harity⟩

end Nested
end Model
end VEnv
end Lean4Lean
