import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.Typing.NativeIotaPatterns
import Lean4Lean.Theory.Inductive.CaseCapture

/-! Coverage of the installed native iota equations by the full presentation.

A restored native equation is a lambda telescope over the recursor's
parameters, motives and minors and the constructor's fields; its left side
applies the recursor to the first of these binders, the constructor's indices
and the constructor applied to (possibly specialized) parameters followed by
its field binders. At every universe specialization whose source level is not
zero, or for a small target, the native iota pattern reduces the body to the
right side applied to all binders, which beta-reduces to the right side. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature
open private restored_constructor_arguments restoration_vars
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas

/-- The restoration of a registered native instance specializes exactly the
signature's common parameters. -/
theorem NativeRecursorRegistered.restoration_nparams {data : NativeRecursorData}
    (H : NativeRecursorRegistered env data) :
    ∀ head ∈ data.schema.restoration.heads, head.nparams = data.schema.signature.params.length := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _⟩ := H
  intro head hhead
  rw [hr] at hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  have hn := hdata.model.nparams.trans hdata.nparams
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm


private theorem vars_join' (p f : Nat) : vars p f ++ vars f 0 = vars (p + f) 0 := by
  rw [Nat.add_comm p f]
  simp [vars, List.range_add, List.reverse_append, List.map_append, List.map_map]

/-- The exact syntax of a restored native equation. -/
theorem NativeRecursorRegistered.equation_shape {data : NativeRecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    (H : NativeRecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) :
    ∃ domains idx cl cp rhsBody typeBody,
      equation.lhs = VExpr.wrapLams domains (.app
        (VExpr.mkApps (.const data.name (VLevel.params data.uvars))
          (vars data.indexOffset data.schema.signature.constructors[index].fields.length ++ idx))
        (VExpr.mkApps (.const (data.ruleConstructor index) cl)
          (cp ++ vars data.schema.signature.constructors[index].fields.length 0))) ∧
      equation.rhs = VExpr.wrapLams domains rhsBody ∧
      equation.type = VExpr.wrapForalls domains typeBody ∧
      domains.length = data.indexOffset + data.schema.signature.constructors[index].fields.length ∧
      idx.length = data.schema.signature.constructors[index].indices.length := by
  let r := data.schema.restoration
  let g := data.nativeInstance
  let s := data.schema.signature
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let major := g.constructorApp ctor extra 0
  have hrestore : r.equation (g.equation index) = some equation := hgen
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  have hdomlen : domains.length = np + nf := by
    simp only [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, InductiveSignature.fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList]
    simp only [np, nf, extra, s, ctor]
    omega
  have hnp : np = data.indexOffset := by
    simp only [np, extra, s, NativeRecursorData.indexOffset, NativeRecursorData.numParams,
      Nat.add_assoc]
  obtain ⟨ds', lhs', rhs', type', hl', hr', ht', hel, her, het, hlen⟩ :=
    restored_common_telescope hl hr ht
  have hlhs0 : r.expr (VExpr.mkApps (g.recursorHead .native ctor.owner)
      (vars np nf ++ indices ++ [major])) = some lhs' := hl'
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp [List.mapM_append, restoration_vars, List.mapM_cons, Restoration.expr.go] at hlhs0
  obtain ⟨allArgs, ⟨restArgs, ⟨indices', hi, majorArgs, ⟨major', hmajor, rfl⟩, rfl⟩, rfl⟩, hout⟩ := hlhs0
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    obtain ⟨base, installBase, source, expanded, g', auxiliaries, block, installed,
      hdata, _, _, hr0, _, hu, hl0, ht0, _⟩ := H
    have hinst : data.nativeInstance = g' := by
      cases g' with
      | mk U levels target recNames =>
        simp only [NativeRecursorData.nativeInstance, Instance.mk.injEq]
        exact ⟨hu, hl0, ht0, funext fun owner => (hdata.recursorNames owner).symm⟩
    apply List.find?_eq_none.mpr
    intro spec hs
    have := hdata.heads_not_recursors ctor.owner spec (by rw [← hr0]; exact hs)
    simpa only [beq_iff_eq, g, hinst] using this
  have hlhs : lhs' = .app
      (VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars))
        (vars np nf ++ indices')) major' := by
    simpa [Instance.recursorHead, Restoration.expr.go, hnone, VExpr.mkApps,
      List.foldl_append] using hout.symm
  have hparams : ∀ h ∈ r.heads, h.nparams ≤ s.params.length := fun h hh =>
    Nat.le_of_eq (H.restoration_nparams h hh)
  obtain ⟨cn, cl, cp, hc⟩ := restored_constructor_arguments hparams hmajor
  obtain ⟨cl', ca', hca⟩ := r.const_mkApps hmajor
  have hmajor' : major' = VExpr.mkApps (.const (r.headName ctor.name) cl) (cp ++ vars nf 0) := by
    rw [hca] at hc ⊢
    rw [spine_mkApps_exact _ _ rfl] at hc
    cases hc
    rfl
  have hidx : indices'.length = ctor.indices.length := by
    have length_eq : ∀ {xs ys}, List.Forall₂ (fun x y => r.expr x = some y) xs ys →
        ys.length = xs.length := by
      intro xs ys hrel
      induction hrel with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    simpa [indices] using length_eq (List.mapM_eq_some.mp hi)
  refine ⟨ds', indices', cl, cp, rhs', type', ?_, her, het, ?_, hidx⟩
  · rw [hel, hlhs, hmajor']
    have hname : r.recursorName (g.recursorName ctor.owner) = data.name := by
      show r.recursorName (data.schema.signature.families[
        data.schema.signature.constructors[index].owner].name.str "rec") = _
      simp only [howner]; rfl
    rw [hname, hnp]
    rfl
  · rw [hlen, hdomlen, hnp]

end Lean4Lean.VEnv
