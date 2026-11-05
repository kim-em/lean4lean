import Lean4Lean.Theory.Typing.Confluence.SingletonAlign

/-! # Beta shape of unindexed singleton equation instances -/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- Applying the stored equation to the actual pattern captures beta-reduces
its left side to the original recursor prefix and a reconstructed major.
No equality of constructor parameters, levels or fields is required. -/
theorem singletonInstance_unindexed_beta
    {data : RecursorData} {decl : VInductDecl} {env₀ env₁ : VEnv}
    {rec : VRecursor} {ru : VRecRule} {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} {levels : List VLevel} {recArgs ctorArgs : List VExpr}
    (hAt : RecursorRegisteredAt env data decl env₀ env₁)
    (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (hgen : data.equation index = some equation) (hof : VRecRule.OfEquation rec ru equation)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero)
    (hn : data.numIndices = 0) (hlv : levels.length = data.uvars)
    (h1 : recArgs.length = rec.getMajorIdx) (h2 : ctorArgs.length = ru.ctorParams + ru.nfields) :
    ∃ major, BetaRed (mkApps (equation.lhs.instL levels)
      (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
        ctorArgs.drop ru.ctorParams))
      (.app (mkApps (.const rec.name levels) recArgs) major) := by
  have H := hAt.registered
  have F := RecursorData.singletonSignature H hlarge (packed := levels) hzero
  obtain ⟨base, expanded, g, auxiliaries, block, hdata, hprior, hbase, hr, hsf, hu, hl, htg,
    hwf, hadd, hrecs, he, hbwf⟩ := hAt
  have hinst := RecursorRegistered.recursorInstance_eq hdata hu hl htg
  have hres0 : compilationRestoration decl auxiliaries = {} := hr.symm.trans F.restoration
  have haux : auxiliaries = [] := hdata.noAuxiliaries_of_singleton F.families
  have hg : (compilationRestoration decl auxiliaries).equation (g.equation index) =
      some equation := by
    simpa only [RecursorData.equation, hinst, hr] using hgen
  rw [hres0, Restoration.equation_empty] at hg
  cases Option.some.inj hg
  subst hinst
  generalize hgdef : data.recursorInstance = g at *
  let s := data.schema.signature
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length
  let D := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let idx := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let fn := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (np + extra) nf ++ idx)
  let major := VExpr.mkApps (.const ctor.name g.levels) (vars np (extra + nf) ++ vars nf 0)
  let lb := VExpr.app fn major
  have hlb : (g.equation index).lhs = VExpr.wrapLams D lb := by
    simp only [Instance.equation, Instance.recursorHead, Instance.constructorApp, D, lb, fn,
      major, idx, ctor, s, np, nf, extra, Nat.add_zero]
    rw [List.append_assoc (vars _ _), ← List.append_assoc, VExpr.mkApps_append]; rfl
  have hDlen : D.length = np + extra + nf := by
    simp only [D, Instance.params, Instance.motives, Instance.minors, insertBinders,
      InductiveSignature.fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList, np, nf, extra, s, ctor]
    omega
  -- the rule's counts
  have hof2 := hof.2.1
  have hof3 := hof.2.2.1
  obtain ⟨maj, hmaj1, hmaj2, hmaj3⟩ := hof.2.2.2
  rw [hlb, VExpr.lamBody_wrapLams_app] at hof2 hof3 hmaj1
  have hrname : rec.name = g.recursorName ctor.owner := by
    simp only [VExpr.headConst?, fn, VExpr.getAppFn_mkApps,
      VExpr.getAppFn] at hof2
    exact (Option.some.inj hof2).symm
  simp only [fn, VExpr.getAppArgs_mkApps, VExpr.getAppArgs,
    List.nil_append, List.length_append, List.length_singleton] at hof3 hmaj1
  have hmajEq : maj = major := by
    simpa using hmaj1.symm
  subst hmajEq
  have hctorName : ru.ctor = ctor.name := by
    simp only [major, VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn] at hmaj2
    exact (Option.some.inj hmaj2).symm
  have hcpnf : ru.ctorParams + ru.nfields = np + nf := by
    simp only [major, VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append,
      List.length_append] at hmaj3
    simpa [vars] using hmaj3.symm
  have hvl : ∀ n k, (vars n k).length = n := fun n k => by simp [vars]
  have hmajorIdx : rec.getMajorIdx = np + extra + idx.length := by
    rw [hvl] at hof3; omega
  have hnp : np = decl.nparams := hdata.model.nparams.trans hdata.nparams
  have hcp : ru.ctorParams = np := by
    rcases hwf.rules_ctorParams rec hrec ru hru with ⟨c, hcm, hcn, hcp⟩ | ⟨D', hD', c, hcm, hcn, hcp⟩
    · rw [hcp, hnp]
    · exfalso
      rcases hdata.constructor_name_cases index with ⟨c', hc'm, hc'n⟩ | ⟨a, ha, -⟩
      · rw [hres0] at hc'n
        simp only [Restoration.headName, Restoration.recursorName] at hc'n
        have hcn' : c.name = c'.name := by
          rw [← hcn, hctorName]; exact hc'n
        obtain ⟨type', htype', hctor'⟩ := List.mem_flatMap.1 hc'm
        have hfresh := addInduct_ctor_fresh hadd htype' hctor'
        obtain ⟨type, htype, hctor⟩ := List.mem_flatMap.1 hcm
        cases hD' with
        | intro _ _ _ _ _ hadd' hle' =>
          have := hle'.constants (addInduct_ctor_find hadd' htype hctor)
          rw [hcn', hfresh] at this
          cases this
      · rw [haux] at ha; cases ha
  have hnf' : ru.nfields = nf := by omega
  obtain ⟨rb, hrb, krb, argsrb, hrbShape⟩ : ∃ rb, (g.equation index).rhs = VExpr.wrapLams D rb ∧
      ∃ k args', rb = VExpr.mkApps (.bvar k) args' :=
    ⟨_, rfl, _, _, rfl⟩
  have hk : rec.numParams + rec.numMotives + rec.numMinors = np + extra := by
    obtain ⟨j, hj, A, -, -, -, hshape⟩ := hwf.rule_shape rec hrec ru hru
    have h1 := hshape.1
    rw [← hof.1, hrb, hrbShape, VExpr.lamArity_wrapLams_mkApps_bvar, hDlen, hnf'] at h1
    omega
  have howner : ctor.owner = data.owner := by
    have hf : data.schema.signature.families.size = 1 := F.families
    have ha := ctor.owner.isLt
    have hb := data.owner.isLt
    exact Fin.ext (by simp only [ctor, s] at ha ⊢; omega)
  have hidx : idx = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [idx, List.length_map]
    have har := F.arity ctor (Array.getElem_mem_toList ..)
    have har' : ctor.indices.length = data.schema.signature.families[data.owner].indices.length := by
      simpa only [howner] using har
    exact har'.trans hn
  have hlen : recArgs.length = np + extra := by simpa [hidx] using h1.trans hmajorIdx
  let args := recArgs ++ ctorArgs.drop np
  have ha : args.length = np + extra + nf := by
    simp only [args, List.length_append, List.length_drop, hlen]
    omega
  have hargs : recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
      ctorArgs.drop ru.ctorParams = args := by
    rw [hk, hcp, List.take_of_length_le (by omega)]
  have hguv : g.uvars = data.uvars := by rw [← hgdef]; rfl
  have hfn : (fn.instL levels).instOuter args = mkApps (.const rec.name levels) recArgs := by
    simp only [fn, hidx, List.append_nil, instL_mkApps, instL,
      instOuter_mkApps, instOuter_const]
    rw [VLevel.inst_map_id (hlv.trans hguv.symm), ← hrname]
    have hv : (vars (np + extra) nf).map (fun a => (a.instL levels).instOuter args) = recArgs := by
      suffices hh : ((vars (np + extra) nf).map (instL levels)).map (·.instOuter args) = recArgs by
        simpa only [List.map_map, Function.comp_def] using hh
      rw [vars_instL, map_instOuter_vars _ _ _ (by omega), ha,
        Nat.sub_self, List.drop_zero]
      exact List.take_left' hlen
    simpa only [List.map_map, Function.comp_def] using congrArg (mkApps (.const rec.name levels)) hv
  refine ⟨(major.instL levels).instOuter args, ?_⟩
  rw [hargs, hlb, instL_wrapLams]
  have HB := BetaRed.mkApps_wrapLams (D.map (·.instL levels)) (lb.instL levels) args
    (by simp only [List.length_map, hDlen, ha]; exact Nat.le_refl _)
  have hd : (D.map (·.instL levels)).length = args.length := by simp [hDlen, ha]
  rw [hd, List.take_length, List.drop_length] at HB
  simpa only [mkApps, List.foldl_nil, lb, instL, instOuter_app', hfn] using HB

end Lean4Lean.VEnv
