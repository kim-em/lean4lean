import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaPat

/-! # The static data of the ι rules of an ordinary block

For the generated equation `g.equation index` of an ordinary compilation, the generated
recursor's type carries the `IotaStatic` data of the rule (`Instance.iotaStatic`): its telescope
is `recDoms`, its major domain is the family applied to the parameter and index variables, and
the constructor's minor premise `g.minor` records the constructor's indices, which the equation's
lead `eqLead` carries lifted over the motives and minors. -/

namespace Lean4Lean

theorem VExpr.mkApps_snoc_last_inj {f f' x x' : VExpr} {l l' : List VExpr}
    (h : VExpr.mkApps f (l ++ [x]) = VExpr.mkApps f' (l' ++ [x'])) : x = x' := by
  rw [VExpr.mkApps_snoc, VExpr.mkApps_snoc] at h
  injection h

theorem VExpr.mkApps_const_name_inj {c c' : Name} {ls ls' : List VLevel} {a a' : List VExpr}
    (h : VExpr.mkApps (.const c ls) a = VExpr.mkApps (.const c' ls') a') : c = c' := by
  have := congrArg VExpr.getAppFn h
  simp only [VExpr.getAppFn_mkApps, VExpr.getAppFn] at this
  injection this

namespace InductiveSignature.Instance
open VEnv.Model

variable {s : InductiveSignature} (g : Instance s)

theorem recDoms_minor (owner : Fin s.families.size) (i : Fin s.constructors.size) :
    (g.recDoms owner)[s.params.length + s.families.size + i.val]? =
      some (g.minor s.constructors[i] i.val) := by
  have hpl : g.params.length = s.params.length := params_length g
  have hml : g.motives.length = s.families.size := motives_length g
  have hnl : g.minors.length = s.constructors.size := minors_length g
  simp only [recDoms, List.append_assoc]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    List.getElem?_append_left (by omega)]
  simp only [hpl, hml, show s.params.length + s.families.size + i.val - s.params.length -
    s.families.size = i.val by omega, minors, List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

theorem minor_endsInCtor {c : Name} {ctor : Constructor s.families.size} {prior : Nat}
    (h : EndsInCtor c (g.minor ctor prior)) : c = ctor.name := by
  obtain ⟨f, args, lsC, margs, e⟩ := h
  simp only [minor, constructorApp] at e
  rw [VExpr.mkApps_snoc, piBody_wrapForalls_app, ← VExpr.mkApps_snoc] at e
  exact VExpr.mkApps_const_name_inj (VExpr.mkApps_snoc_last_inj e).symm


/-- **The `IotaStatic` data of a generated equation.** -/
theorem iotaStatic (index : Fin s.constructors.size)
    (harity : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hnames : ∀ i : Fin s.constructors.size,
      s.constructors[i].name = s.constructors[index].name → i = index) :
    IotaStatic (g.recursor s.constructors[index].owner).toVConstant s.constructors[index].name
      (s.params.length + (s.families.size + s.constructors.size))
      s.families[s.constructors[index].owner].indices.length
      s.constructors[index].fields.length
      (g.eqDoms index) (g.recDoms s.constructors[index].owner)
      (g.recBody s.constructors[index].owner) s.families[s.constructors[index].owner].name
      g.levels
      (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length) ++
        vars s.families[s.constructors[index].owner].indices.length 0)
      (g.eqLead index) := by
  have hpos := g.recDoms_minor s.constructors[index].owner index
  refine ⟨g.eqDoms_length index, g.recursorType_eq_recDoms _, by rw [g.recDoms_length],
    by rw [show s.params.length + (s.families.size + s.constructors.size) +
      s.families[s.constructors[index].owner].indices.length = s.params.length +
      (s.families.size + s.constructors.size) +
      s.families[s.constructors[index].owner].indices.length from rfl]; exact g.recDoms_major _,
    s.params.length, s.params.length + s.families.size + index.val,
    (recursiveFields s.constructors[index]).length,
    s.constructors[index].fields.length + (recursiveFields s.constructors[index]).length +
      index.val + (s.families.size - 1 - s.constructors[index].owner.val),
    s.constructors[index].indices.map (·.instL g.levels),
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + index.val) ++
      (recursiveFields s.constructors[index]).zipIdx.map (fun ((field, r), i) =>
        g.hypothesis s.constructors[index] index.val i field r),
    vars s.params.length ((s.families.size + index.val) + s.constructors[index].fields.length +
        (recursiveFields s.constructors[index]).length) ++
      vars s.constructors[index].fields.length (recursiveFields s.constructors[index]).length,
    g.levels,
    by omega, by have := index.isLt; omega, by simpa using harity, ?_, ?_, ?_, ?_⟩
  · simp [insertBinders, fieldTypes]
  · rw [hpos]
    simp only [minor, constructorApp, Option.some.injEq, List.length_map,
      List.length_zipIdx, show s.params.length + s.families.size + index.val - s.params.length =
        s.families.size + index.val by omega, Function.comp_def]
  · simp only [eqLead, iotaLead, eqIndices, vars, List.map_map]
    congr 1
    · congr 1; funext i; simp; omega
    · congr 1; funext e; simp only [Function.comp]; congr 1; omega
  · intro pos' A h1 h2 hA hE
    obtain ⟨i', rfl⟩ : ∃ i', pos' = s.params.length + s.families.size + i' :=
      ⟨pos' - (s.params.length + s.families.size), by omega⟩
    have hi' : i' < s.constructors.size := by omega
    rw [g.recDoms_minor _ ⟨i', hi'⟩] at hA
    cases hA
    have := hnames ⟨i', hi'⟩ (g.minor_endsInCtor hE).symm
    have : i' = index.val := congrArg Fin.val this
    omega

end InductiveSignature.Instance

end Lean4Lean
