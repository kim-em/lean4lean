import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! # The recursor shapes of an ordinary block

The recursor and constructor telescopes (`RecursorShapes`, wave 1A) of the recursors installed
by a recursor check: the recursor type is the generator's `Instance.recursorType`, literally a
recursor telescope over its major family; each rule fires on a source constructor of the major
family, whose raw shape (`RawCtorShape`) is the constructor telescope. Recorded in the installed
block's descriptor (`InstalledBlock.WF.shapes`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace InductiveSignature

theorem vars_eq_bvarRange (n below : Nat) : vars n below = VExpr.bvarRange n (below + n) := by
  unfold vars VExpr.bvarRange
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp at h1
  simp [List.getElem_reverse]
  omega

theorem bvarRange_liftN (n k : Nat) :
    (VExpr.bvarRange n n).map (VExpr.liftN k) = VExpr.bvarRange n (n + k) := by
  unfold VExpr.bvarRange
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp at h1
  simp [VExpr.liftN, liftVar]
  omega

theorem bvarRange_closedN (n : Nat) : ∀ p ∈ VExpr.bvarRange n n, p.ClosedN n := by
  intro p hp
  simp only [VExpr.bvarRange, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  simp [VExpr.ClosedN]; omega

theorem insertBinders_length (l : List VExpr) (k : Nat) : (insertBinders l k).length = l.length := by
  simp [insertBinders]

/-- The generated recursor type is a recursor telescope over its major family. -/
theorem Instance.recursorType_shape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    ∃ doms result, g.recursorType owner = VExpr.wrapForalls doms result ∧
      doms.length = s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length + 1 ∧
      doms[s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length]? =
        some (VExpr.mkApps (.const s.families[owner].name g.levels)
          (((VExpr.bvarRange s.params.length s.params.length).map fun p =>
              p.liftN (s.families.size + s.constructors.size +
                s.families[owner].indices.length)) ++
            VExpr.bvarRange s.families[owner].indices.length s.families[owner].indices.length)) := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [Instance.params, Instance.motives, Instance.minors, insertBinders_length]
    omega
  · have hp : g.params.length = s.params.length := by simp [Instance.params]
    have hm : g.motives.length = s.families.size := by simp [Instance.motives]
    have hn : g.minors.length = s.constructors.size := by simp [Instance.minors]
    have hi : (insertBinders (s.families[owner].indices.map (·.instL g.levels))
        (s.families.size + s.constructors.size)).length = s.families[owner].indices.length := by
      simp [insertBinders_length]
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp only [hp, hm, hn, hi]
    rw [show s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length - s.params.length - s.families.size -
        s.constructors.size - s.families[owner].indices.length = 0 by omega]
    simp only [List.getElem?_cons_zero, Option.some.injEq]
    simp only [Instance.familyApp, InductiveSignature.familyApp, vars_eq_bvarRange,
      bvarRange_liftN]
    rw [Nat.zero_add]
    congr 3; omega

end InductiveSignature

/-- A raw constructor shape is a constructor telescope: parameters and fields ending in the
family at the universe parameters, applied to the parameter variables and the indices. -/
theorem VInductDecl.RawCtorShape.toShape {decl : VInductDecl} {type : VInductiveType}
    {ctor : VConstVal} (H : decl.RawCtorShape type ctor) (htype : type ∈ decl.types)
    (hnodup : (decl.types.map (·.name)).Nodup) :
    ∃ doms indices, ctor.type = VExpr.wrapForalls doms
        (VExpr.mkApps (.const type.name (VLevel.params decl.uvars))
          (VExpr.bvarRange decl.nparams (decl.nparams + (doms.length - decl.nparams)) ++
            indices)) ∧
      decl.nparams ≤ doms.length ∧ indices.length = type.numIndices := by
  obtain ⟨doms, result, hty, hle, hraw, hhead⟩ := H
  have hres := VExpr.mkApps_getAppFnArgs result
  rcases hgf : result.getAppFnArgs with ⟨fn, args⟩
  rw [hgf] at hres hhead
  simp only [VInductDecl.RawIndAppAt, hgf] at hraw
  obtain ⟨type', htype', htgt, levels, hfn, -, hlen, htake⟩ := hraw
  have hname : type'.name = type.name := by
    rcases htgt with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have heq : type' = type := List.eq_of_mem_of_nodup_map hnodup htype' htype hname
  subst heq
  refine ⟨doms, args.drop decl.nparams, ?_, hle, by simp [hlen]⟩
  rw [hty, ← hres, show fn = .const type'.name (VLevel.params decl.uvars) from hhead]
  congr 2
  conv => lhs; rw [← List.take_append_drop decl.nparams args]
  rw [htake, VInductDecl.paramVars, show ((List.range decl.nparams).reverse.map fun i =>
      VExpr.bvar (doms.length - decl.nparams + i)) =
      InductiveSignature.vars decl.nparams (doms.length - decl.nparams) from rfl,
    InductiveSignature.vars_eq_bvarRange, Nat.add_comm]

namespace VerifyInductive

theorem VExpr.piArity_mkApps_const (n : Name) (ls : List VLevel) :
    ∀ (args : List VExpr) (f : VExpr), (f = .const n ls ∨ ∃ a b, f = .app a b) →
      (VExpr.mkApps f args).piArity = 0
  | [], f, h => by
    rcases h with rfl | ⟨a, b, rfl⟩ <;> rfl
  | a :: as, f, _ => VExpr.piArity_mkApps_const n ls as (.app f a) (.inr ⟨_, _, rfl⟩)

theorem VExpr.piArity_wrapForalls_mkApps_const (doms args : List VExpr) (n : Name)
    (ls : List VLevel) :
    (VExpr.wrapForalls doms (VExpr.mkApps (.const n ls) args)).piArity = doms.length := by
  induction doms with
  | nil => exact VExpr.piArity_mkApps_const n ls args _ (.inl rfl)
  | cons d ds ih => simp [VExpr.wrapForalls, VExpr.piArity] at ih ⊢; exact ih

/-- The recursor shapes of the recursors installed by a recursor check, given the `AddInduct`
of the block over the source map (which identifies the constructor infos the rules fire on). -/
theorem RecursorCheck.recursorShapes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (T : RuleTranslations H)
    (hnp : ∀ {n cval}, outEnv.constants.find? n = some (.ctorInfo cval) →
      (∃ src ∈ decl.constructorConstants, src.name = n) → cval.numParams = decl.nparams) :
    ∀ rval ∈ H.rvals, RecursorShapesAt outEnv.constants H.outVEnv rval := by
  intro rval hrval
  obtain ⟨i, hiR, rfl⟩ := List.getElem_of_mem hrval
  have hlenR : H.rvals.length = H.recs.length := List.Forall₂.length_eq H.trRecs
  have hlenF : (List.finRange H.signature.families.size).length = H.rvals.length :=
    List.Forall₂.length_eq H.metadata
  have hi : i < H.recs.length := hlenR ▸ hiR
  have hiF : i < (List.finRange H.signature.families.size).length := hlenF ▸ hiR
  have htr := Lean4Lean.List.Forall₂.getElem_of H.trRecs i hiR hi
  have hmeta := Lean4Lean.List.Forall₂.getElem_of H.metadata i hiF hiR
  have hrules := Lean4Lean.List.Forall₂.getElem_of T.trRules i hiF hiR
  generalize howner : (List.finRange H.signature.families.size)[i] = owner at hmeta hrules
  have hrec : H.recs[i].toVConstVal = H.generation.recursor owner := by
    have h := congrArg (fun l => l[i]?) H.recursors_eq
    simp only [InductiveSignature.Instance.recursors, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiF, Option.map_some,
      Option.some.injEq, howner] at h
    exact h
  -- the recursor constant
  have hconst : H.outVEnv.constants H.rvals[i].name =
      some ⟨H.rvals[i].levelParams.length, H.generation.recursorType owner⟩ := by
    have h := VEnv.addRecs_find H.recsAdded H.recs[i] (List.getElem_mem hi)
    have hname : (ConstantInfo.recInfo H.rvals[i]).name = H.recs[i].toVConstVal.name :=
      htr.tr.2
    rw [hrec] at hname h
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    rw [hname]
    rw [h]
    simp [InductiveSignature.Instance.recursor, VConstVal.toVConstant, hmeta.uvars]
  obtain ⟨doms, result, htype, hdomslen, hmajor⟩ := H.generation.recursorType_shape owner
  refine ⟨⟨H.signature.params.length, H.generation.levels,
    VExpr.bvarRange H.signature.params.length H.signature.params.length, ⟨{
      ctorParams_length := by simp
      ctorParams_closed := by rw [hmeta.numParams]; exact InductiveSignature.bvarRange_closedN _
      type := H.generation.recursorType owner
      const := hconst
      doms := doms
      result := result
      type_eq := htype
      doms_length := by
        rw [hmeta.numParams, hmeta.numMotives, hmeta.numMinors, hmeta.numIndices]; exact hdomslen
      major_eq := by
        rw [hmeta.numParams, hmeta.numMotives, hmeta.numMinors, hmeta.numIndices, hmeta.major]
        exact hmajor }⟩, ?_⟩, ?_⟩
  · intro rule hrule
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrule
    have hj' : j < H.recs[i].rules.length := List.Forall₂.length_eq htr.rules ▸ hj
    have hjO : j < (H.signature.ownedConstructors owner).length :=
      (List.Forall₂.length_eq hrules).symm ▸ hj
    have hrr := Lean4Lean.List.Forall₂.getElem_of hrules j hjO hj
    have hru := Lean4Lean.List.Forall₂.getElem_of htr.rules j hj hj'
    generalize hindex : (H.signature.ownedConstructors owner)[j] = index at hrr
    have howner' : H.signature.constructors[index].owner = owner := by
      have hmem := List.getElem_mem (l := H.signature.ownedConstructors owner) hjO
      rw [hindex] at hmem
      simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
      exact hmem.2
    obtain ⟨source, hsource, hfname, -, hfidx, -, hfctors⟩ := H.models.family owner
    have hnames := TrInductDeclCore.sourceNames_nodup R.core
    have htypesNodup : (decl.types.map (·.name)).Nodup := by
      have := (List.nodup_append.mp hnames).1
      simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using this
    obtain ⟨src, hsrc, hsname, hsuv, -⟩ := H.models.constructorInFamily hnames index
      R.core.typesAdded hsource (by rw [howner']; exact hfctors)
    obtain ⟨cdoms, indices, hctype, hle, hidx⟩ :=
      (R.formation.rawShapes source hsource src hsrc).toShape hsource htypesNodup
    have stC : decl.addCtors R.headerVEnv = some R.ctorVEnv := by
      rw [VInductDecl.addCtors_eq_addConstVals]; exact R.core.ctorsAdded
    have hsrcC : R.ctorVEnv.constants src.name = some src.toVConstant :=
      VEnv.addCtors_find stC source hsource src hsrc
    have hleC : R.ctorVEnv ≤ H.outVEnv := VEnv.addProjections_le.trans (VEnv.addRecs_le H.recsAdded)
    have hrulector : H.rvals[i].rules[j].ctor = src.name := hrr.ctor.trans hsname
    have hsrcMem : ∃ s ∈ decl.constructorConstants, s.name = H.rvals[i].rules[j].ctor :=
      ⟨src, List.mem_flatMap.2 ⟨source, hsource, hsrc⟩, hrulector.symm⟩
    obtain ⟨hctor, hnfields, ⟨cval, hcval, hcparams⟩, -⟩ := hru
    have hcvalNp := hnp hcval hsrcMem
    obtain ⟨ci, hci, hshape⟩ := H.rules_ctor _ (List.getElem_mem hi) _ (List.getElem_mem hj')
    rw [hctor, hrulector, hsrcC] at hci
    cases hci
    have harity := hshape.1
    rw [hctype, VExpr.piArity_wrapForalls_mkApps_const, hcparams, hcvalNp, hnfields] at harity
    have hnp' : decl.nparams = H.signature.params.length := H.models.nparams.symm
    have huv : H.generation.levels.length = decl.uvars :=
      H.admissible.levels_length.trans H.models.uvars
    refine ⟨H.generation.levels.length, rfl, ⟨{
      type := src.type
      const := by
        rw [hrulector, hleC.constants hsrcC, huv, ← hsuv.symm.trans H.models.uvars]
      doms := cdoms
      indices := indices
      type_eq := by
        rw [hctype, huv, hmeta.major, hfname, ← hnp']
        congr 4
        omega
      doms_length := by rw [← hnp']; omega
      indices_length := by rw [hidx, hmeta.numIndices, hfidx] }⟩, ?_⟩
    intro cval' hcval'
    rw [hnp hcval' hsrcMem, hnp']
  · intro rule hrule
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrule
    have hj' : j < H.recs[i].rules.length := List.Forall₂.length_eq htr.rules ▸ hj
    obtain ⟨-, -, ⟨cval, hcval, -⟩, -⟩ := Lean4Lean.List.Forall₂.getElem_of htr.rules j hj hj'
    exact ⟨cval, hcval⟩

end VerifyInductive

end Lean4Lean
