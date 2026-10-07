import Lean4Lean.Verify.Inductive.Nested.LoweredRulesAvoid

/-! Recursor provenance of a validated nested run.

`NestedValidatedRunResult.hprovenance_of` discharges the `Hprovenance`
hypothesis of `NestedValidatedRunResult.assemblyNative_of_run`.

The hypothesis quantifies over an arbitrary specialization list carrying
`RestorationTableData`. The first part of this file shows that the restoration
`compilationRestoration decl auxiliaries` is determined by the table data
(`RestorationTableData.expr_eq`), so the specialization list of
`restorationTablesRestoringAll`, for which all the formation evidence is
available, may be used instead. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

/-! ### The restoration is determined by the restoration table data -/

section TableUniqueness

variable {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
  {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}

private theorem heads_nodup {aux : List ContainerSpecialization}
    (D : RestorationTableData decl aux result env auxRec Us₀) :
    ((compilationRestoration decl aux).heads.map (·.auxiliary)).Nodup := by
  rw [compilationRestoration_heads_auxiliary]
  exact D.headNodup

/-- The family data of a specialization is fixed by the tables. -/
theorem RestorationTableData.family_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀)
    {a : ContainerSpecialization} (ha : a ∈ aux₁) :
    ∃ b ∈ aux₀, b.auxiliary = a.auxiliary ∧ b.source.name = a.source.name ∧
      b.levels = a.levels ∧ b.arguments = a.arguments := by
  obtain ⟨nested, hn⟩ := D₁.familyLookup a ha
  obtain ⟨b, hb, hbaux, hbspec⟩ := D₀.familyKey _ nested hn
  obtain ⟨a', ha', ha'aux, ha'spec⟩ := D₁.familyKey _ nested hn
  -- `a` and `a'` have the same family head
  let hA : HeadSpecialization :=
    ⟨a.auxiliary, decl.uvars, decl.nparams, a.source.name, a.levels, a.arguments⟩
  let hA' : HeadSpecialization :=
    ⟨a'.auxiliary, decl.uvars, decl.nparams, a'.source.name, a'.levels, a'.arguments⟩
  have hmemA : hA ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have hmemA' : hA' ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a', ha', List.mem_cons_self⟩
  have h1 := Restoration.find?_of_nodup (heads_nodup D₁) hmemA
  have h2 := Restoration.find?_of_nodup (heads_nodup D₁) hmemA'
  have hauxEq : hA'.auxiliary = hA.auxiliary := ha'aux
  rw [hauxEq, h1] at h2
  have hAA : hA = hA' := Option.some.inj h2
  simp only [hA, hA', HeadSpecialization.mk.injEq] at hAA
  obtain ⟨-, -, -, hsrc, hlev, hargs⟩ := hAA
  obtain ⟨hs, hl, hr⟩ := AuxNestedSpec.unique hbspec ha'spec
  exact ⟨b, hb, hbaux, hs.trans hsrc.symm, hl.trans hlev.symm,
    hr.trans hargs.symm⟩

/-- Every head of one table is a head of any other table of the same run. -/
theorem RestorationTableData.find_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀)
    {n : Name} {h : HeadSpecialization}
    (hfind : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) =
      some h) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) = some h := by
  have hmem := List.mem_of_find?_eq_some hfind
  have hn : h.auxiliary = n := by simpa using List.find?_some hfind
  subst hn
  obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hmem
  obtain ⟨b, hb, hbaux, hbsrc, hblev, hbargs⟩ := D₀.family_transfer D₁ ha
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
  rcases hh with rfl | ⟨ctor, hctor, rfl⟩
  · let hB : HeadSpecialization :=
      ⟨b.auxiliary, decl.uvars, decl.nparams, b.source.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have := Restoration.find?_of_nodup (heads_nodup D₀) hmemB
    simp only [hB, hbaux, hbsrc, hblev, hbargs] at this
    exact this
  · obtain ⟨info, hc, hind⟩ := D₁.ctorInstalled a ha ctor hctor
    obtain ⟨ctor', hctor', hcname⟩ :=
      D₀.ctorLookup _ info hc b hb (hind.trans hbaux.symm)
    have hrenA : (a.constructorName ctor).replacePrefix a.auxiliary a.source.name =
        ctor.name :=
      (namePrefix_of_replacePrefix_ne (D₁.ctorRenamed a ha ctor hctor)).replacePrefix_replacePrefix _
    have hrenB : (b.constructorName ctor').replacePrefix b.auxiliary b.source.name =
        ctor'.name :=
      (namePrefix_of_replacePrefix_ne (D₀.ctorRenamed b hb ctor' hctor')).replacePrefix_replacePrefix _
    have hname : ctor'.name = ctor.name := by
      rw [← hrenA, ← hrenB, ← hcname, hbaux, hbsrc]
    let hB : HeadSpecialization :=
      ⟨b.constructorName ctor', decl.uvars, decl.nparams, ctor'.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨ctor', hctor', rfl⟩)⟩
    have := Restoration.find?_of_nodup (heads_nodup D₀) hmemB
    simp only [hB, ← hcname, hname, hblev, hbargs] at this
    exact this

theorem RestorationTableData.find_eq {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (n : Name) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) =
      (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) := by
  cases h1 : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) with
  | some h => exact D₀.find_transfer D₁ h1
  | none =>
    cases h0 : (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) with
    | none => rfl
    | some h =>
      have := D₁.find_transfer D₀ h0
      rw [h1] at this
      cases this

theorem Restoration.go_congr {r r' : Restoration}
    (hfind : ∀ n, r.heads.find? (fun h => h.auxiliary == n) =
      r'.heads.find? (fun h => h.auxiliary == n))
    (hrec : ∀ n, r.recursorName n = r'.recursorName n) :
    ∀ (e : VExpr) (args : List VExpr),
      Restoration.expr.go r e args = Restoration.expr.go r' e args := by
  intro e
  induction e with
  | bvar | sort | elim => intro args; rfl
  | const name levels =>
    intro args
    simp only [Restoration.expr.go, hfind name, hrec name]
  | app fn arg ihf iha =>
    intro args
    simp only [Restoration.expr.go, iha, ihf]
  | lam d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | forallE d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | proj n i m ih =>
    intro args
    simp only [Restoration.expr.go, ih]

/-- **The restoration is determined by the restoration table data.** -/
theorem RestorationTableData.expr_eq {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (e : VExpr) :
    (compilationRestoration decl aux₀).expr e = (compilationRestoration decl aux₁).expr e :=
  Restoration.go_congr (D₀.find_eq D₁)
    (fun n => (D₀.recursorName n).trans (D₁.recursorName n).symm) e []

theorem RestorationTableData.restorable_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) {n : Name}
    (hn : n ∈ (compilationRestoration decl aux₁).restorableNames) :
    n ∈ (compilationRestoration decl aux₀).restorableNames := by
  simp only [Restoration.restorableNames, List.mem_append] at hn ⊢
  rcases hn with hn | hn
  · left
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn
    have h1 := Restoration.find?_of_nodup (heads_nodup D₁) hh
    have h0 := D₀.find_transfer D₁ h1
    exact List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some h0, rfl⟩
  · right
    rw [compilationRestoration_recursors_fst] at hn ⊢
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    obtain ⟨b, hb, hbaux, -⟩ := D₀.family_transfer D₁ ha
    exact List.mem_map.mpr ⟨b, hb, by rw [hbaux]⟩

end TableUniqueness

end VerifyInductive

/-! ### Shapes of restored recursors and their rules -/

namespace InductiveSignature

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

/-- The recursor shape of a restored recursor at the specialization head of
its realization. -/
theorem RestoredRecursorRealization.shape_of_head {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {sourceNames : List Name} {venv : VEnv}
    {owner : Fin s.families.size} {rec : Lean.RecursorVal}
    (H : RestoredRecursorRealization g r sourceNames venv owner rec)
    (hconst : ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩)
    {head : RestoredFamilyHead}
    (hargs : ∀ arg ∈ head.arguments, arg.ClosedN s.params.length)
    (happ : r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0))) :
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams
      head.arguments.length rec.numMotives rec.numMinors rec.numIndices
      head.name head.levels head.arguments) := by
  rcases hconst with ⟨type, htype, hconst⟩
  rcases r.expr_recursorType_eq_some htype with ⟨pre, major, hpre, hm, rfl⟩
  have hprelen : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hmaj : major = VExpr.mkApps (.const head.name head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
        vars s.families[owner].indices.length 0) :=
    Option.some.inj (hm.symm.trans happ)
  refine ⟨{
    ctorParams_length := rfl
    ctorParams_closed := by rw [H.numParams]; exact hargs
    type := _
    const := hconst
    doms := pre ++ [major]
    result := g.recursorBody owner
    type_eq := rfl
    doms_length := by
      simp [hprelen, H.numParams, H.numMotives, H.numMinors, H.numIndices]
    major_eq := ?_ }⟩
  rw [H.numParams, H.numMotives, H.numMinors, H.numIndices, ← hprelen,
    List.getElem?_concat_length, hmaj, vars_eq_bvarRange, Nat.add_zero]

theorem _root_.List.mapM_append_eq_some {f : α → Option β} {a b : List α} {c : List β}
    (h : (a ++ b).mapM f = some c) :
    ∃ ca cb, a.mapM f = some ca ∧ b.mapM f = some cb ∧ c = ca ++ cb := by
  rw [List.mapM_append] at h
  cases ha : a.mapM f with
  | none => simp [ha] at h
  | some ca =>
    cases hb : b.mapM f with
    | none => simp [ha, hb] at h
    | some cb =>
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨ca, cb, rfl, rfl, h.symm⟩

/-- **Field-domain agreement of a typed iota equation, by strengthening.** The
left-hand side of a well-typed equation with the iota pattern types each field
pattern variable both at its own binder and along the constructor's telescope;
unique typing identifies the two in the equation's full telescope, and
`VEnv.IsDefEqU.weakN_iff` moves the identification to the prefix ending at the
field. This supplies `VIotaRuleShape.ctor_doms` for restored nested rules. -/
theorem iotaCtorDoms_of_lhsTyping {env : VEnv} (henv : VEnv.WF env)
    {recName ctorName indName : Name}
    {recUvars nparams cnparams nmotives nminors nindices nfields : Nat}
    {ctorLevels : List VLevel} {ctorParams : List VExpr} {df : VDefEq}
    {doms : List VExpr} {lhsBody typeBody : VExpr} {indexArgs : List VExpr}
    (hwf : df.WF env) (huv : df.uvars = recUvars)
    (hlhs : df.lhs = VExpr.wrapLams doms lhsBody)
    (htype : df.type = VExpr.wrapForalls doms typeBody)
    (hlen : doms.length = nparams + nmotives + nminors + nfields)
    (hidx : indexArgs.length = nindices)
    (hpat : lhsBody = VExpr.mkApps (.const recName (VLevel.params recUvars))
      (VExpr.bvarRange (nparams + nmotives + nminors) doms.length ++ indexArgs ++
        [VExpr.mkApps (.const ctorName ctorLevels)
          ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
            VExpr.bvarRange nfields nfields)]))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices
      indName ctorLevels ctorParams) :
    ∀ ctorUvars ctorDoms ctorBody,
    env.constants ctorName = some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
    ctorDoms.length = cnparams + nfields →
    ∀ i, i < nfields → ∀ (hd : nparams + nmotives + nminors + i < doms.length)
      (hc : cnparams + i < ctorDoms.length),
    env.IsDefEqU recUvars ((doms.take (nparams + nmotives + nminors + i)).reverse)
      doms[nparams + nmotives + nminors + i]
      ((ctorDoms[cnparams + i].instL ctorLevels).instOuter
        ((ctorParams.map fun p => p.liftN (nmotives + nminors + i)) ++
          VExpr.bvarRange i i)) := by
  intro ctorUvars ctorDoms ctorBody hconst hclen i hi hd hcd
  generalize hm : nparams + nmotives + nminors = m at *
  -- the left-hand side under the equation's telescope
  have hleft := hwf.1
  rw [hlhs, htype, huv] at hleft
  rcases VEnv.HasType.wrapLams_inv henv (by trivial) hleft with ⟨hctx, hbody⟩
  rw [hpat] at hbody
  have hpre : (VExpr.bvarRange m doms.length ++ indexArgs).length =
      nparams + nmotives + nminors + nindices := by
    simp [hidx, hm]
  have hbody' : env.HasType recUvars (doms.reverse ++ [])
      (VExpr.mkApps (.const recName (VLevel.params recUvars))
        ((VExpr.bvarRange m doms.length ++ indexArgs) ++
          [VExpr.mkApps (.const ctorName ctorLevels)
            ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
              VExpr.bvarRange nfields nfields)])) typeBody := by
    simpa only [List.append_assoc] using hbody
  have ⟨_, hmajor, _⟩ := Hrec.spine_typing henv hctx VLevel.params_wf VLevel.params_length
    hpre ⟨_, hbody'⟩
  -- the constructor constant and its spine
  obtain ⟨_, hhead⟩ := VEnv.HasType.mkApps_head henv.ordered hctx hmajor
  obtain ⟨ci, hci, hlw, hll⟩ := VEnv.HasType.const_inv henv hctx hhead
  rw [hconst] at hci
  cases hci
  have hcT := VEnv.HasType.const (Γ := doms.reverse ++ []) hconst hlw hll
  rw [VExpr.instL_wrapForalls] at hcT
  have hplen : ctorParams.length = cnparams := Hrec.ctorParams_length
  have hargsLen : ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
      VExpr.bvarRange nfields nfields).length = (ctorDoms.map (VExpr.instL ctorLevels)).length := by
    simp [hplen, hclen]
  have ⟨hcargs, _⟩ := VEnv.HasType.mkApps_wrapForalls henv hctx hcT ⟨_, hmajor⟩ hargsLen
  have hv := hcargs (cnparams + i) (by simp [hplen]; omega) (by simp; omega)
  rw [List.getElem_append_right (by simp [hplen]), List.take_append,
    List.take_of_length_le (by simp [hplen])] at hv
  simp only [List.length_map, hplen, Nat.add_sub_cancel_left] at hv
  rw [VExpr.bvarRange_getElem _ _ _ hi, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hi)] at hv
  -- closedness of the constructor's domains
  have ⟨hctorC, _⟩ := VEnv.VEnv.constant_doms_closed henv hconst hlw
  have hcC := hctorC (cnparams + i) (by simp; omega)
  have hjn : m + i < doms.length := hd
  have hY : (((ctorDoms.map (VExpr.instL ctorLevels))[cnparams + i]'(by simp; omega)).instOuter
      ((ctorParams.map fun p => p.liftN (nmotives + nminors + i)) ++
        VExpr.bvarRange i i)).liftN (doms.length - (m + i)) =
      ((ctorDoms.map (VExpr.instL ctorLevels))[cnparams + i]'(by simp; omega)).instOuter
        ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
          VExpr.bvarRange i nfields) := by
    rw [VExpr.liftN_instOuter _ _ (by simpa [hplen] using hcC), List.map_append,
      VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
    simp only [List.map_map, Function.comp_def, VExpr.liftN_liftN]
    rw [show nmotives + nminors + i + (doms.length - (m + i)) = nmotives + nminors + nfields by
        omega,
      show i + (doms.length - (m + i)) = nfields by omega]
  rw [← hY] at hv
  -- the pattern variable at its own binder
  have hbvT : env.HasType recUvars (doms.reverse ++ []) (.bvar (doms.length - 1 - (m + i)))
      (doms[m + i].liftN (doms.length - (m + i))) :=
    .bvar (Lookup.reverse_append doms [] (m + i) hjn)
  rw [show doms.length - 1 - (m + i) = nfields - 1 - i by omega] at hbvT
  have hU := hbvT.uniqU henv hctx hv
  have W : Ctx.LiftN (doms.length - (m + i)) 0 ((doms.take (m + i)).reverse ++ [])
      (doms.reverse ++ []) := by
    have := Ctx.LiftN.zero (Γ := (doms.take (m + i)).reverse ++ [])
      ((doms.drop (m + i)).reverse) (n := doms.length - (m + i)) (by simp)
    rwa [← List.append_assoc, ← List.reverse_append, List.take_append_drop] at this
  sorry -- E1MERGE-TEMP

/-- **The iota shape of a restored generated equation**, given the
restoration of its constructor application. -/
theorem Restoration.restored_iota_shape {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (index : Fin s.constructors.size) {env₀ env : VEnv} {df : VDefEq}
    {ctorName : Name} {levels : List VLevel} {params : List VExpr}
    (heq : r.equation (g.equation index) = some df)
    (hdef : env.defeqs df)
    (henv₀ : VEnv.WF env₀) (hle : env₀ ≤ env) (hconsts : ∀ n, env.constants n = env₀.constants n)
    (hwf : df.WF env₀)
    (hrecType : ∃ type, r.expr (g.recursorType s.constructors[index].owner) = some type ∧
      env₀.constants (r.recursorName (g.recursorName s.constructors[index].owner)) =
        some ⟨g.uvars, type⟩)
    {indName : Name}
    (Hrec : VRecursorShape env₀ (r.recursorName (g.recursorName s.constructors[index].owner))
      g.uvars s.params.length params.length s.families.size s.constructors.size
      s.families[s.constructors[index].owner].indices.length indName levels params)
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
  have hpat : lb = VExpr.mkApps
      (.const (r.recursorName (g.recursorName s.constructors[index].owner))
        (VLevel.params g.uvars))
      (VExpr.bvarRange (s.params.length + s.families.size + s.constructors.size) D'.length ++
        I' ++
        [VExpr.mkApps (.const ctorName levels)
          ((params.map fun p => p.liftN (s.families.size + s.constructors.size +
            s.constructors[index].fields.length)) ++
            VExpr.bvarRange s.constructors[index].fields.length
              s.constructors[index].fields.length)]) := by
    rw [← Option.some.inj hlb']
    simp only [hDlen, hdomains, vars_eq_bvarRange, Nat.add_zero, List.append_assoc,
      extra, nf, ctor, Nat.add_assoc]
  have hDlen' : D'.length = s.params.length + s.families.size + s.constructors.size +
      s.constructors[index].fields.length := by rw [hDlen, hdomains]
  have hIlen' : I'.length = s.families[s.constructors[index].owner].indices.length := by
    rw [hIlen]; simpa [indices, ctor] using hindices
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
    doms_length := hDlen'
    indexArgs := I'
    indexArgs_length := hIlen'
    lhs_pattern := hpat
    rec_doms := ?_
    ctor_doms := ?_ }⟩
  · -- the parameter, motive and minor binders are restored as in the recursor
    intro recDoms recBody hc hlenR j hj
    obtain ⟨type, hty, hconstR⟩ := hrecType
    rw [hconsts, hconstR] at hc
    obtain ⟨pre, major', hpre, -, htypeEq⟩ := r.expr_recursorType_eq_some hty
    have htype' : VExpr.wrapForalls (pre ++ [major'])
        (g.recursorBody s.constructors[index].owner) = VExpr.wrapForalls recDoms recBody := by
      have := congrArg VConstant.type (Option.some.inj hc)
      simpa [htypeEq] using this
    have hprelen : pre.length = s.params.length + s.families.size +
        s.constructors.size + s.families[s.constructors[index].owner].indices.length := by
      rw [← g.recursorPrefix_length s.constructors[index].owner]
      exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
    obtain ⟨hrec, -⟩ := VExpr.wrapForalls_inj_of_length (by simp [hprelen, hlenR]) htype'
    subst hrec
    obtain ⟨A, B, hA, -, rfl⟩ := List.mapM_append_eq_some
      (a := g.params ++ g.motives ++ g.minors) hD
    obtain ⟨A', C, hA', -, rfl⟩ := List.mapM_append_eq_some
      (a := g.params ++ g.motives ++ g.minors) (by simpa [Instance.recursorPrefix] using hpre)
    rw [hA] at hA'
    cases hA'
    have hAlen : A.length = s.params.length + s.families.size + s.constructors.size := by
      rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hA)]
      simp [Instance.params, Instance.motives, Instance.minors]; omega
    rw [List.getElem?_append_left (by omega), List.append_assoc,
      List.getElem?_append_left (by omega)]
  · -- the field binders agree with the constructor's field domains
    intro ctorUvars ctorDoms ctorBody hc hclen i hi hd hcd
    rw [hconsts] at hc
    exact (iotaCtorDoms_of_lhsTyping henv₀ hwf huv hl.symm ht.symm hDlen' hIlen' hpat Hrec
      ctorUvars ctorDoms ctorBody hc hclen i hi hd hcd).mono hle

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

/-! ### Constructor shapes of certified containers -/

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

namespace InductiveSignature

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

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

private theorem forall₂_imp_mem_right' {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, b ∈ l₂ → R a b → S a b) → List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H =>
    .cons (H _ _ List.mem_cons_self h)
      (forall₂_imp_mem_right' t fun a b hb h => H a b (List.mem_cons_of_mem _ hb) h)

private theorem names_of_trTypes' {env envTypes : VEnv} {lparams : List Name} :
    ∀ {types : List InductiveType} {decls : List VInductiveType},
      List.Forall₂ (TrInductiveType env envTypes lparams) types decls →
      types.map (·.name) = decls.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [List.map_cons, names_of_trTypes' t, List.cons.injEq, and_true]
    exact h.header.name.symm

private theorem Restoration.recursor_name' {r : Restoration} {v w : VConstVal}
    (h : r.recursor v = some w) : w.name = r.recursorName v.name := by
  simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at h
  cases ht : r.expr v.type with
  | none => simp [ht] at h
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at h
    rw [← h]

/-- **The major inductive of a restored recursor is an inductive type of the
output environment**: a restored source family header, or the container
family of the nested occurrence recorded by lowering. -/
theorem NestedValidatedRunResult.restoredMajorFound
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t) :
    ∃ info, outEnv.constants.find? Hstep.restored.newInfo.getMajorInduct =
      some (.inductInfo info) := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.production.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.production.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, -, h1, -⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, h1⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement VEnv.empty lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  obtain ⟨entries, Htrace, -, hheaders⟩ := E.restoration.freshTraceRecursorSteps hwf
  have houtWF : outEnv.constants.WF := Htrace.targetWF hwf
  rw [hmi]
  rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfindN, hfn⟩
  · have hsourceLength : sourceTypes.length = sourceDecl.types.length := by
      have Hcore := E.nativeSource.core
      rw [E.nativeSourceDecl_eq] at Hcore
      exact Lean4Lean.List.Forall₂.length_eq Hcore.types
    have hlt : owner.val < sourceDecl.types.length := by
      by_contra hge
      apply hnot
      rw [compilationRestoration_heads_auxiliary,
        auxiliarySpecializations_headNames Haux Hexpansion]
      apply mem_familyNames_of_type
      exact List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
        simp only [List.getElem_drop]; congr 1; omega⟩
    have hmemNames : (E.production.loweredDecl.types[owner.val]'hi').name ∈
        sourceTypes.map (·.name) := by
      rw [E.sourceNames_eq]
      exact List.mem_map_of_mem
        (List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩)
    obtain ⟨t0, ht0, ht0name⟩ := List.mem_map.mp hmemNames
    obtain ⟨s1, t1, Hind, hmemH⟩ := hheaders t0 ht0
    have hfindH := Htrace.findEntry hwf hmemH
    have hhname : (ConstantInfo.inductInfo Hind.restored.header.newInfo).name = t0.name := by
      change Hind.restored.header.newInfo.name = t0.name
      rw [Hind.restored.header.restored]
      exact (E.loweredSourceKeyed ht0 Hind.lookup : Hind.oldInfo.name = t0.name)
    rw [hhname, Kernel.Environment.find?_eq_constants houtWF] at hfindH
    rw [hceq, ← ht0name]
    exact ⟨_, hfindH⟩
  · obtain ⟨I0, ls0, info0, hfn0, hfind0⟩ := E.auxNestedHead wf Hsources hfindN
    rw [hfn] at hfn0
    simp only [Expr.const.injEq] at hfn0
    rw [hfn0.1]
    rw [Kernel.Environment.find?_eq_constants hwf] at hfind0
    exact ⟨_, Htrace.preservesSourceMapFind hwf hfind0⟩

/-- **Recursor provenance of a validated nested run**: the `Hprovenance`
hypothesis of `NestedValidatedRunResult.assemblyNative_of_run`, given that
lowering recorded a nested occurrence (`hnested`, the condition under which
the run restores at all; it makes the expanded block mutual, so no restored
recursor is K-like). The freshness premise (restorable names outside the
renamed recursor names) is not needed: it holds for every final assembly
shape (`finalBaseVEnv_restorableNames_fresh_of_not_renamed`). -/
theorem NestedValidatedRunResult.hprovenance_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) (hcorner : ProjectionWalkCorner) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.finalBaseVEnv.constants n = none) →
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) →
        InductiveRecursorProvenance .unsafe sourceProdEnv.constants
          (ves.venv (if isUnsafe then .unsafe else .safe)) outEnv.constants
          (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules)) := by
  intro aux₁ D₁ C hC _ HCrules₁
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  -- transfer the hypotheses to the specialization list of the tables
  have hexpr : ∀ e, (compilationRestoration sourceDecl auxiliaries).expr e =
      (compilationRestoration sourceDecl aux₁).expr e := D.expr_eq D₁
  have hfreshFinal := E.finalBaseVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC D
  have HCrules : List.Forall₂
      (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
        C.finalBaseVEnv)
      (List.finRange E.production.compilationSignature.constructors.size)
      (C.primaryRules ++ C.auxiliaryRules) := by
    refine Lean4Lean.List.Forall₂.imp (fun k rule h => ?_) HCrules₁
    obtain ⟨owner, j, s, t, Hstep, hj, hk, hu, ht, hl, hty⟩ := h
    exact ⟨owner, j, s, t, Hstep, hj, hk, hu, ht, (hexpr _).trans hl, (hexpr _).trans hty⟩
  -- the compilation data (as in `assemblyNative_of_run`)
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D
  rw [← hheads] at HL
  have hequations := E.restoredEquations_of_realizationModulo wf Hsources hheads hparamsSize
    D hscoped HL
    (RestoredRulesRealizationModulo.filter_restorable ⟨C.finalBaseVEnv, hfreshFinal, HCrules⟩)
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC hadded
    henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have htypesEq : C.canonical.venvTypes = envTypes := by
    have h := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.canonical.venvCtors := by
    have h := C.canonical.ctorsAdded.abstract
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.canonical.recursorsAdded.abstract
  have hle : C.canonical.venvCtors.addProjections sourceDecl.projectionEntries ≤
      C.finalBaseVEnv := VEnv.addConstVals_le hrecAdded
  have hleCtors : C.canonical.venvCtors ≤ C.finalBaseVEnv := VEnv.addProjections_le.trans hle
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hcore
    exact names_of_trTypes' Hcore.types
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf
  -- the realization of the restored recursor of an entry
  have Hreal : ∀ (owner : Fin E.production.compilationSignature.families.size)
      (entry : ConstantInfo × VConstVal), entry ∈ C.recursorEntries →
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name))
        (E.production.compilationInstance.recursorName owner) s t),
      (compilationRestoration sourceDecl auxiliaries).recursor
        (E.production.compilationInstance.recursor owner) = some entry.2 →
      RestoredRecursorStepValue
        (C.canonical.venvCtors.addProjections sourceDecl.projectionEntries) Hstep entry.2 →
      RestoredRecursorRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.finalBaseVEnv owner Hstep.restored.newInfo := by
    intro owner entry hentry s t Hstep hrec Hw
    obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
      Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
    have hinstalled : C.finalBaseVEnv.constants Hstep.restored.newInfo.name ≠ none := by
      have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
      have hname : entry.2.name = Hstep.restored.newInfo.name :=
        Hw.1.trans Hstep.restored.restoration.name.symm
      rw [← hname, hget]
      simp
    have Hrules' := E.restoredRuleRealizations D hctorNames Hdata.recursorNames
      Hdata.heads_not_recursors hfreshFinal (E.auxRecName_not_renamed wf Hsources D)
      Hdata.equations HCrules owner Hstep hinstalled head Hctor
    refine E.restoredRecursorRealization_of_step D hnames owner Hstep hle hrec Hw
      ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
    rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
      owner Hstep, hheadName]
  -- the source environment and the final base environment
  have Hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe) sourceProdEnv
      (ves.venv (if isUnsafe then .unsafe else .safe)) :=
    (wf.tr (safety := if isUnsafe then .unsafe else .safe)).toCheckingValid
      (wf.hasPrimitives (safety := if isUnsafe then .unsafe else .safe))
      wf.safePrimitives wf.typeAnnotationWrappers wf.constructorOwners
      wf.projectionRegistryCoherent hcorner
  have hheadsSrc := Hvalid.recursors.heads
  have hsrcWF : sourceProdEnv.constants.WF := Hvalid.tr.map_wf
  have hfinalWF : C.finalBaseVEnv.WF := (C.canonical.validCore Hvalid.toValidCore).tr.wf
  have hrulesWF : ∀ df ∈ C.primaryRules ++ C.auxiliaryRules, df.WF C.finalBaseVEnv := by
    intro df hdf
    rcases List.mem_append.mp hdf with hp | ha
    · exact C.primaryIota.rulesWF df hp
    · exact C.auxiliaryWF.rulesWF (by simp) df ha
  obtain ⟨entries, Htrace, hsteps, -⟩ := E.restoration.freshTraceRecursorSteps hsrcWF
  have houtWF : outEnv.constants.WF := Htrace.targetWF hsrcWF
  -- every inductive type of the output environment is rigid in the final base
  have hrigid : ∀ n info, outEnv.constants.find? n = some (.inductInfo info) →
      C.finalBaseVEnv.Rigid n := by
    intro n info h
    have h' : outEnv.find? n = some (.inductInfo info) := by
      rw [Kernel.Environment.find?_eq_constants houtWF]; exact h
    have hsrc : (ves.venv (if isUnsafe then .unsafe else .safe)).Rigid n := by
      rcases Htrace.entryOrigin hsrcWF h' with hold | ⟨entry, hentry, hname, -⟩
      · rw [Kernel.Environment.find?_eq_constants hsrcWF] at hold
        exact hheadsSrc.rigid hold
      · have hnone := Htrace.sourceFresh hsrcWF hentry
        rw [← hname, Kernel.Environment.find?_eq_constants hsrcWF] at hnone
        exact hheadsSrc.rigid_of_fresh hnone
    intro df hdf ls
    exact hsrc df (C.canonical.defeqs df hdf) ls
  -- the equation list
  have Heqs := List.mapM_eq_some.mp Hdata.equations
  -- the alignment of one restored recursor
  have Hcore : ∀ (owner : Fin E.production.compilationSignature.families.size)
      (entry : ConstantInfo × VConstVal), entry ∈ C.recursorEntries →
      ∀ rec : Lean.RecursorVal,
      (compilationRestoration sourceDecl auxiliaries).recursor
        (E.production.compilationInstance.recursor owner) = some entry.2 →
      RestoredRecursorRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.finalBaseVEnv owner rec →
      (∃ info, outEnv.constants.find? rec.getMajorInduct = some (.inductInfo info)) →
      RecursorAlignmentCore
        (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules)) rec := by
    intro owner entry hentry rec hrec R hmajorFound
    have hconst := restoredRecursor_constant hrec
      (VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)) R.name R.uvars
    obtain ⟨head, hhead, hmajor, -, hargs, happ, hrules⟩ := R.specialization
    obtain ⟨hshape⟩ := R.shape_of_head hconst hargs happ
    have hrigidHead : C.finalBaseVEnv.Rigid head.name := by
      obtain ⟨info, hinfo⟩ := hmajorFound
      rw [hmajor] at hinfo
      exact hrigid _ info hinfo
    refine ⟨head.arguments.length, head.levels, head.arguments,
      ⟨by rw [hmajor]; exact hshape.mono VEnv.addDefEqRules_le⟩, ?_⟩
    intro rule hmem
    obtain ⟨index, hindex, RR⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrules rule hmem
    have howner : E.production.compilationSignature.constructors[index].owner = owner := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp hindex).2
    obtain ⟨df, heq, -, htr⟩ := RR.equation
    have hdfMem : df ∈ C.primaryRules ++ C.auxiliaryRules := by
      obtain ⟨d, hd, hdeq⟩ := Lean4Lean.List.Forall₂.forall_exists_l Heqs
        (E.production.compilationInstance.equation index)
        (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
      rw [heq] at hdeq
      cases hdeq
      exact hd
    have hdef : (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules)).defeqs df :=
      VEnv.addDefEqRules_defeqs_iff.mpr (.inr hdfMem)
    have hindices := Hdata.model.constructorArity _
      (Array.getElem_mem_toList (xs := E.production.compilationSignature.constructors) index.isLt)
    have hnotHead : (compilationRestoration sourceDecl auxiliaries).heads.find?
        (fun h => h.auxiliary == E.production.compilationInstance.recursorName
          E.production.compilationSignature.constructors[index].owner) = none := by
      apply Restoration.heads_find?_eq_none
      intro hm
      obtain ⟨h, hh, he⟩ := List.mem_map.mp hm
      exact Hdata.heads_not_recursors _ h hh he
    have hrecType : ∃ type, (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.recursorType
          E.production.compilationSignature.constructors[index].owner) = some type ∧
        C.finalBaseVEnv.constants ((compilationRestoration sourceDecl auxiliaries).recursorName
          (E.production.compilationInstance.recursorName
            E.production.compilationSignature.constructors[index].owner)) =
          some ⟨E.production.compilationInstance.uvars, type⟩ := by
      subst howner; rw [← R.name, ← R.uvars]; exact hconst
    have Hrec : VRecursorShape C.finalBaseVEnv
        ((compilationRestoration sourceDecl auxiliaries).recursorName
          (E.production.compilationInstance.recursorName
            E.production.compilationSignature.constructors[index].owner))
        E.production.compilationInstance.uvars
        E.production.compilationSignature.params.length head.arguments.length
        E.production.compilationSignature.families.size
        E.production.compilationSignature.constructors.size
        E.production.compilationSignature.families[
          E.production.compilationSignature.constructors[index].owner].indices.length
        head.name head.levels head.arguments := by
      have h := hshape
      rw [R.name, R.uvars, R.numParams, R.numMotives, R.numMinors, R.numIndices] at h
      subst howner; exact h
    obtain ⟨I⟩ := Restoration.restored_iota_shape E.production.compilationInstance
      (compilationRestoration sourceDecl auxiliaries) index heq hdef hfinalWF
      VEnv.addDefEqRules_le (fun _ => by simp) (hrulesWF df hdfMem) hrecType Hrec
      hindices hnotHead RR.constructorApplication
    obtain ⟨head2, hhead2, fields, ⟨hctorShape⟩⟩ := Hdata.restoredConstructorShape Hcertified
      hadded hctorsAdded hfresh hfreshCtors hleCtors index owner howner
    have hhh : head2 = head := Option.some.inj (hhead2.symm.trans hhead)
    subst hhh
    rw [← RR.ctor] at hctorShape
    subst howner
    have I' : VIotaRuleShape (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules))
        rec.name rec.levelParams.length rec.numParams head2.arguments.length rec.numMotives
        rec.numMinors rec.numIndices rule.ctor head2.levels rule.nfields df
        head2.arguments := by
      rw [R.name, R.uvars, R.numParams, R.numMotives, R.numMinors, R.numIndices, RR.nfields]
      exact I
    have hfields := VIotaRuleShape.fieldCount hfinalWF I' (hrulesWF df hdfMem) hshape
      hctorShape hrigidHead
    subst hfields
    refine ⟨df, { shape := ⟨I'⟩, rhs := htr.mono VEnv.addDefEqRules_le, ctor := ?_ }⟩
    refine ⟨head2.levels.length, rfl, ?_⟩
    rw [R.numIndices, hmajor]
    exact ⟨hctorShape.mono VEnv.addDefEqRules_le⟩
  refine { recursor := ?_, defeq := ?_ }
  · intro name rec hfind
    have hfind' : outEnv.find? name = some (.recInfo rec) := by
      rw [Kernel.Environment.find?_eq_constants houtWF]; exact hfind
    rcases Htrace.entryOrigin hsrcWF hfind' with hold | ⟨entry, hentry, hname, hfound⟩
    · left
      rwa [Kernel.Environment.find?_eq_constants hsrcWF] at hold
    right
    intro _
    obtain ⟨oldRecName, hold, s, t, Hstep, hreq⟩ := hsteps entry hentry rec hfound.symm
    subst hreq
    rw [← E.recursorNames_order C.sourceNonempty] at hold
    obtain ⟨owner, -, rfl⟩ := List.mem_map.mp hold
    obtain ⟨entry', hentry', s', t', Hstep', hentry1, hrec, Hw⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
    have hnew : Hstep'.restored.newInfo = Hstep.restored.newInfo := (Hstep'.info_eq Hstep).2
    have R := Hreal owner entry' hentry' s' t' Hstep' hrec Hw
    rw [hnew] at R
    have hmajorFound := E.restoredMajorFound wf Hsources Haux Hexpansion hnodup hparamsSize D
      owner Hstep
    refine ⟨Hcore owner entry' hentry' _ hrec R hmajorFound, ?_, hmajorFound⟩
    intro hk
    rw [R.k_eq_false (E.one_lt_familiesSize hnested)] at hk
    cases hk
  · intro df hdf
    rcases VEnv.addDefEqRules_defeqs_iff.mp hdf with hold | hnew
    · exact .inl (C.canonical.defeqs df hold)
    right
    obtain ⟨e, he, hedf⟩ := Lean4Lean.List.Forall₂.forall_exists_r Heqs df hnew
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp he
    have hleft : (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.equation index).lhs = some df.lhs := by
      simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at hedf
      cases hl : (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.compilationInstance.equation index).lhs with
      | none => simp [hl] at hedf
      | some lhs =>
        simp only [hl, Option.bind_some] at hedf
        cases hr : (compilationRestoration sourceDecl auxiliaries).expr
            (E.production.compilationInstance.equation index).rhs with
        | none => simp [hr] at hedf
        | some rhs =>
          simp only [hr, Option.bind_some] at hedf
          cases hty : (compilationRestoration sourceDecl auxiliaries).expr
              (E.production.compilationInstance.equation index).type with
          | none => simp [hty] at hedf
          | some ty =>
            simp only [hty, Option.bind_some, Option.some.injEq] at hedf
            rw [← hedf]
    have hhead := Restoration.wrapLams_head_const
      (Hdata.heads_not_recursors E.production.compilationSignature.constructors[index].owner)
      (VExpr.getAppFnArgs_mkApps_head _ _) hleft
    obtain ⟨entry, hentry, s, t, Hstep, hentry1, hrec, -⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l hinfos
        E.production.compilationSignature.constructors[index].owner (List.mem_finRange _)
    have hfindE := C.find_recursorEntry hwf entry hentry
    rw [Restoration.recursor_name' hrec, hentry1,
      Kernel.Environment.find?_eq_constants houtWF] at hfindE
    exact ⟨_, _, _, hhead, hfindE⟩

end VerifyInductive

end Lean4Lean
