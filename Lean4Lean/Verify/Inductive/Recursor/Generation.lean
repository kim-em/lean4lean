import Lean4Lean.Verify.Inductive.Recursor.BlueprintRules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem LocalForallSelection.size
    (H : LocalForallSelection lctx xs) : xs.size = H.fvars.length := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simp

theorem LocalForallSelection.fvarsIn
    (H : LocalForallSelection lctx xs) (Hlctx : lctx.WF) :
    ∀ e ∈ xs, e.FVarsIn (· ∈ lctx.fvars) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  intro e he
  rw [List.mem_toArray, List.mem_map] at he
  rcases he with ⟨fv, hfv, rfl⟩
  simp only [Expr.FVarsIn]
  rcases declarations fv hfv with
    ⟨index, name, type, bi, kind, hfind⟩
  rw [Hlctx.find?_eq_find?_toList] at hfind
  rw [LocalContext.fvars]
  exact List.mem_map.mpr
    ⟨.cdecl index fv name type bi kind,
      List.mem_of_find?_eq_some hfind, rfl⟩

theorem LocalForallSelection.fvar_mem
    (H : LocalForallSelection lctx xs) (hfv : (.fvar fv : Expr) ∈ xs) :
    fv ∈ H.fvars := by
  rcases H with ⟨fvars, rfl, declarations⟩
  rw [List.mem_toArray, List.mem_map] at hfv
  rcases hfv with ⟨other, hother, heq⟩
  cases heq
  exact hother

/-- The binder domain selected by `LocalContext.mkForall` is the exact local
declaration type, simultaneously closed over the strictly earlier selected
free variables.  This is the source-syntax provenance needed to compare a
generated recursor domain with its independently recorded origin type. -/
theorem LocalContext.mkBindingList_forallBinderAt
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (LocalContext.mkBindingList false lctx fvars body) i
      (type.abstractList (fvars.take i)) := by
  induction fvars generalizing i body with
  | nil => simp at hi
  | cons fv fvars ih =>
    have htailDecl : ∀ other ∈ fvars, ∃ index name type bi kind,
        lctx.find? other = some (.cdecl index other name type bi kind) := by
      intro other hother
      exact hdecl other (by simp [hother])
    have hnodupParts := List.nodup_cons.mp hnodup
    rw [LocalContext.mkBindingList_cons
      (fun other hother => by
        rcases htailDecl other hother with
          ⟨index, name, type, bi, kind, hlookup⟩
        exact ⟨.cdecl index other name type bi kind, hlookup⟩)
      hnodup]
    cases i with
    | zero =>
      have hhead := hselected
      simp only [List.getElem_cons_zero] at hhead
      simp only [LocalContext.mkBindingList1, hhead,
        List.take_zero, Expr.abstractList]
      exact .here
    | succ i =>
      have hiTail : i < fvars.length := by simp at hi; omega
      rcases hdecl fv (by simp) with
        ⟨headIndex, headName, headType, headBi, headKind, hheadDecl⟩
      have htailSelected : lctx.find? fvars[i] =
          some (.cdecl index fvars[i] name type bi kind) := by
        simpa using hselected
      have Htail := ih htailDecl hnodupParts.2 i hiTail htailSelected
        (body := body)
      have Habstract := Htail.abstract1 fv 0
      have hprefixNodup : (fv :: fvars.take i).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hnodupParts.1
          (List.mem_of_mem_take hmem),
          hnodupParts.2.take⟩
      have hdomain :
          (type.abstractList (fvars.take i)).abstract1 fv i =
            type.abstractList (fv :: fvars.take i) := by
        have Hclose := Expr.abstractList_after_inner
          (e := type) (outer := [fv]) (inner := fvars.take i)
          (k := 0) (by simpa using hprefixNodup)
        simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hiTail)] using
          Hclose
      simp only [Nat.zero_add] at Habstract
      rw [hdomain] at Habstract
      simpa [LocalContext.mkBindingList1, hheadDecl] using
        Expr.ForallBinderAt.there Habstract

/-- `mkForall` specialization of the positional declaration theorem for an
explicit list of selected free variables. -/
theorem LocalContext.mkForall_fvars_forallBinderAt
    {lctx : LocalContext} {fvars : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (lctx.mkForall (fvars.map Expr.fvar).toArray body) i
      (type.abstractList (fvars.take i)) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_forallBinderAt hdecl hnodup i hi
    index name type bi kind hselected

/-- `LocalForallSelection` form of the positional source-domain theorem. -/
theorem LocalForallSelection.forallBinderAt
    (H : LocalForallSelection c.lctx xs) (hnodup : H.fvars.Nodup)
    (D : BoundFVarDeclarationAt c xs i) :
    Expr.ForallBinderAt (c.lctx.mkForall xs body) i
      (D.type.abstractList (H.fvars.take i)) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
  have hifvars : i < fvars.length := by simpa using D.inBounds
  have hselectedFVar : fvars[i] = D.fvar := by
    have hexpression : Expr.fvar fvars[i] = Expr.fvar D.fvar := by
      simpa [hifvars] using D.expression
    exact Expr.fvar.inj hexpression
  apply LocalContext.mkBindingList_forallBinderAt declarations hnodup i
    hifvars D.index D.userName D.type D.binderInfo D.kind
  rw [hselectedFVar]
  exact D.declaration

/-- The hypothesis binder at position `j` in a generated minor is the exact
local declaration type used by the first pass, closed first over preceding
hypotheses and then over the outer constructor fields. -/
theorem RecInfoMinorTypeShape.hypothesisBinderAt
    (S : RecInfoMinorTypeShape)
    (D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j) :
    Expr.ForallBinderAt S.origin (S.fields.size + j)
      ((D.type.abstractList (S.hypotheses_bound.fvars.take j)).abstractList
        S.fields_bound.fvars j) := by
  let Hselection := S.hypotheses_bound.toLocalForallSelection S.sourceFullWF
  have HinnerFull := Hselection.forallBinderAt S.hypotheses_nodup D
    (body := S.motiveApp)
  have Hinner : Expr.ForallBinderAt
      (S.sourceContext.mkForall S.hypotheses S.motiveApp) j
      (D.type.abstractList (S.hypotheses_bound.fvars.take j)) := by
    rw [← S.sourceContext_eq]
    exact HinnerFull
  have HinnerClosed := Hinner.abstractList S.fields_bound.fvars 0
  have Hfields := S.fieldTelescope
    (S.sourceContext.mkForall S.hypotheses S.motiveApp)
  have Hsource : Expr.ForallBinderAt S.sourceType (S.fields.size + j)
      ((D.type.abstractList (S.hypotheses_bound.fvars.take j)).abstractList
        S.fields_bound.fvars j) := by
    rw [S.sourceType_eq]
    simpa only [Nat.zero_add] using Hfields.prependBinderAt HinnerClosed
  have hconsumed : S.sourceType.consumeTypeAnnotationsVerified = S.sourceType :=
    Hsource.consumeTypeAnnotationsVerified_eq_self
  have horigin : S.origin = S.sourceType :=
    S.consumed_eq.symm.trans hconsumed
  rw [horigin]
  exact Hsource

theorem LocalForallSelection.forallTelescope
    (H : LocalForallSelection lctx xs) (body : Expr) :
    Expr.ForallTelescope (lctx.mkForall xs body) xs.size
      (body.abstractList H.fvars) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simpa using LocalContext.mkForall_fvars_forallTelescope declarations

/-- Prepending one retained binder group to an existing telescope preserves
the inner telescope and abstracts its residual below exactly the inner arity. -/
theorem LocalForallSelection.prependTelescope
    (Hsel : LocalForallSelection lctx xs)
    (Hinner : Expr.ForallTelescope inner innerArity result) :
    Expr.ForallTelescope (lctx.mkForall xs inner)
      (xs.size + innerArity)
      (result.abstractList Hsel.fvars innerArity) := by
  exact (Hsel.forallTelescope inner).trans <| by
    simpa using Hinner.abstractList Hsel.fvars

/-- Prepend one retained binder group to an exact inner binder while
simultaneously closing its declaration type over the outer group.  The
explicit inner-prefix list makes this reusable for each successive group of
the generated recursor telescope. -/
theorem LocalForallSelection.prependBinderAtClosed
    {type : Expr}
    (Houter : LocalForallSelection lctx outer)
    (Hinner : Expr.ForallBinderAt inner i
      (type.abstractList innerPrefix))
    (hinnerLength : innerPrefix.length = i)
    (hnodup : (Houter.fvars ++ innerPrefix).Nodup) :
    Expr.ForallBinderAt (lctx.mkForall outer inner) (outer.size + i)
      (type.abstractList (Houter.fvars ++ innerPrefix)) := by
  have Hclosed := Hinner.abstractList Houter.fvars 0
  have hdomain :
      (type.abstractList innerPrefix).abstractList Houter.fvars i =
        type.abstractList (Houter.fvars ++ innerPrefix) := by
    have Hclose := Expr.abstractList_after_inner
      (e := type) (outer := Houter.fvars) (inner := innerPrefix)
      (k := 0) hnodup
    simpa [hinnerLength] using Hclose
  have Hprefix := Houter.forallTelescope inner
  have Hresult := Hprefix.prependBinderAt Hclosed
  simpa only [Nat.zero_add, hdomain] using Hresult

def RecursorLocalSelections.residual
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (body : Expr) : Expr :=
  let afterMajor := body.abstractList H.major.fvars
  let afterIndices := afterMajor.abstractList H.indices.fvars 1
  let afterMinors := afterIndices.abstractList H.minors.fvars
    (recInfos[ownerIdx]!.indices.size + 1)
  let afterMotives := afterMinors.abstractList H.motives.fvars
    ((recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
  afterMotives.abstractList H.params.fvars
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)

def concreteRecursorResult
    (numMotives numMinors numIndices ownerIdx : Nat) : Expr :=
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indexVars := (List.ofFn fun i : Fin numIndices =>
    Expr.bvar (1 + (numIndices - 1 - i))).toArray
  .app (mkAppN (.bvar motiveOffset) indexVars) (.bvar 0)

private theorem indexBVarOffsets_eq (n : Nat) :
    List.ofFn (fun i : Fin n => 1 + (n - 1 - i)) =
      (List.range n).reverse.map (fun i => i + 1) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    simp only [List.getElem_ofFn]
    rw [List.getElem_map, List.getElem_reverse]
    simp only [List.length_range]
    rw [List.getElem_range]
    omega

/-- Translation of the normalized executable result is forced to be the
same de Bruijn application used by the abstract recursor specification. -/
theorem TrExprS.concreteRecursorResult_eq
    (howner : ownerIdx < numMotives)
    (htotal : numParams + numMotives + numMinors + numIndices + 1 ≤
      domains.length)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      result) :
    result = VExpr.mkApps
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (((List.range numIndices).reverse.map fun i => .bvar (i + 1)) ++
        [.bvar 0]) := by
  unfold concreteRecursorResult at H
  cases H with
  | app _ _ hfn hmajor =>
    have hmajorEq := TrExprS.bvar_eq_of_abstractForallContext hmajor
      (by omega)
    let indices := List.ofFn fun i : Fin numIndices =>
      1 + (numIndices - 1 - i)
    have hindexBound : ∀ i ∈ indices, i < domains.length := by
      intro i hi
      simp only [indices, List.mem_ofFn] at hi
      rcases hi with ⟨j, rfl⟩
      omega
    have hmotiveBound :
        1 + numIndices + numMinors + (numMotives - 1 - ownerIdx) <
          domains.length := by omega
    have hfn' := hfn
    unfold mkAppN at hfn'
    rw [← Array.foldl_toList] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (List.foldl mkApp
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))
        (List.ofFn ((fun i => Expr.bvar i) ∘
          fun i : Fin numIndices => 1 + (numIndices - 1 - i)))) _ at hfn'
    rw [← List.map_ofFn, List.foldl_map] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (indices.foldl (fun fn i => .app fn (.bvar i))
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))) _ at hfn'
    have hfnEq := TrExprS.foldl_bvars_eq domains Δ indices hindexBound
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext Hout
        hmotiveBound)
      hfn'
    rw [hmajorEq, hfnEq]
    unfold VExpr.mkApps
    have hindices : indices =
        (List.range numIndices).reverse.map (fun i => i + 1) := by
      exact indexBVarOffsets_eq numIndices
    rw [hindices, ← List.foldl_map]
    simp [Function.comp_def]

/-- Distinct retained binders make the executable five-stage abstraction
compute to the canonical de Bruijn result used by the abstract recursor
specification. -/
theorem RecursorLocalSelections.residual_eq_concreteRecursorResult
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size) (hnoalias : H.NoAlias) :
    H.residual
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) =
      concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx := by
  let motiveFVars := H.motives.fvars
  let minorFVars := H.minors.fvars
  let indexFVars := H.indices.fvars
  let majorFVars := H.major.fvars
  have hmotivesLen : motiveFVars.length = recInfos.size := by
    have h := H.motives.size
    simpa [motiveFVars] using h.symm
  have hownerMotive : ownerIdx < motiveFVars.length := by
    simpa [hmotivesLen] using howner
  have hindicesLen : indexFVars.length =
      recInfos[ownerIdx]!.indices.size := by
    simpa [indexFVars] using H.indices.size.symm
  have hmajorLen : majorFVars.length = 1 := by
    simpa [majorFVars] using H.major.size.symm
  have hmotive : recInfos[ownerIdx]!.motive =
      .fvar motiveFVars[ownerIdx] := by
    have hget := congrArg (fun xs => xs[ownerIdx]!) H.motives.expressions
    simpa [motiveFVars, Array.getElem!_eq_getD, Array.getD, howner,
      hownerMotive] using hget
  have hindices : recInfos[ownerIdx]!.indices =
      (indexFVars.map Expr.fvar).toArray := H.indices.expressions
  have hmajor : recInfos[ownerIdx]!.major = .fvar majorFVars[0] := by
    have hget := congrArg (fun xs => xs[0]!) H.major.expressions
    simpa [majorFVars, hmajorLen] using hget
  let body : Expr := .app (mkAppN (.fvar motiveFVars[ownerIdx])
    (indexFVars.map Expr.fvar).toArray) (.fvar majorFVars[0])
  have hbody :
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) = body := by
    simp [body, hmotive, hindices, hmajor]
  rw [hbody]
  let parts := hnoalias.parts
  have hmotiveMajor : motiveFVars[ownerIdx] ∉ majorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hmotiveIndices : motiveFVars[ownerIdx] ∉ indexFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hmotiveMinors : motiveFVars[ownerIdx] ∉ minorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hindicesMajor : ∀ fv ∈ indexFVars, fv ∉ majorFVars := by
    intro fv hfv hmem
    exact parts.indices_major fv hfv fv hmem rfl
  let afterMajor := body.abstractList majorFVars
  have hmajorBound : 0 < majorFVars.length := by omega
  have hmajorOffset : majorFVars.length - 1 = 0 := by omega
  have hAfterMajor : afterMajor =
      .app (mkAppN (.fvar motiveFVars[ownerIdx])
        (indexFVars.map Expr.fvar).toArray) (.bvar 0) := by
    unfold afterMajor body
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveMajor,
      Expr.abstractList_fvarArray_of_disjoint indexFVars majorFVars 0
        hindicesMajor,
      Expr.abstractList_fvar_getElem parts.major 0 hmajorBound]
    simp [majorFVars, hmajorOffset]
  let indexBVars := (List.ofFn fun i : Fin indexFVars.length =>
    Expr.bvar (1 + (indexFVars.length - 1 - i))).toArray
  let afterIndices := afterMajor.abstractList indexFVars 1
  have hAfterIndices : afterIndices =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterIndices
    rw [hAfterMajor]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveIndices,
      Expr.abstractList_fvarArray indexFVars 1 parts.indices]
    rw [Expr.abstractList_bvar_lt indexFVars (by omega : 0 < 1)]
  let afterMinors := afterIndices.abstractList minorFVars
    (indexFVars.length + 1)
  have hAfterMinors : afterMinors =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterMinors
    rw [hAfterIndices]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveMinors,
      Expr.abstractList_indexBVars minorFVars indexFVars.length
        (indexFVars.length + 1) (by omega),
      Expr.abstractList_bvar_lt minorFVars (by omega : 0 < indexFVars.length + 1)]
  let motiveBase := minorFVars.length + indexFVars.length + 1
  let afterMotives := afterMinors.abstractList motiveFVars motiveBase
  have hAfterMotives : afterMotives =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    unfold afterMotives
    rw [hAfterMinors]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_getElem parts.motives ownerIdx hownerMotive,
      Expr.abstractList_indexBVars motiveFVars indexFVars.length motiveBase
        (by simp [motiveBase]; omega)]
    rw [Expr.abstractList_bvar_lt motiveFVars (by simp [motiveBase])]
  let allBase := motiveFVars.length + motiveBase
  have hAfterParams : afterMotives.abstractList H.params.fvars allBase =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    rw [hAfterMotives]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega),
      Expr.abstractList_indexBVars H.params.fvars indexFVars.length allBase
        (by simp [allBase, motiveBase]; omega),
      Expr.abstractList_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega)]
  dsimp only [RecursorLocalSelections.residual]
  change ((afterIndices.abstractList minorFVars
      (recInfos[ownerIdx]!.indices.size + 1)).abstractList motiveFVars
        ((recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)).abstractList H.params.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1) = _
  rw [← hindicesLen, H.minors.size, H.motives.size]
  simpa [afterMotives, afterMinors, afterIndices, afterMajor,
    concreteRecursorResult, indexBVars, motiveBase, allBase,
    motiveFVars, minorFVars, indexFVars,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAfterParams

/-- Exact concrete telescope produced by the five nested `mkForall` calls in
`AddInductive.run`. -/
theorem RecursorLocalSelections.forallTelescope
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (body : Expr) :
    Expr.ForallTelescope
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major] body)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1)
      (H.residual body) := by
  have hMajor := H.major.prependTelescope (.nil body)
  have hIndices := H.indices.prependTelescope hMajor
  have hMinors := H.minors.prependTelescope hIndices
  have hMotives := H.motives.prependTelescope hMinors
  have hParams := H.params.prependTelescope hMotives
  simpa [RecursorLocalSelections.residual, Nat.add_assoc] using hParams

/-- Every retained parameter slot has the same concrete domain in every
generated recursor.  The owner-specific suffix only supplies the body below
the common parameter prefix. -/
theorem RecursorLocalSelections.parameterBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c stats.params paramIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false) paramIdx
      (D.type.abstractList (H.params.fvars.take paramIdx)) := by
  dsimp only
  exact (H.params.forallBinderAt hnoalias.parts.params D).inferImplicit
    1000 false

/-- Every retained motive slot has a source domain independent of the
recursor owner.  It is closed over the common parameters and the strictly
earlier motives; the owner's indices and major occur only below this slot. -/
theorem RecursorLocalSelections.motiveBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c
      (recInfos.map (·.motive)) motiveIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + motiveIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars.take motiveIdx)) := by
  dsimp only
  let motiveBody :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) motiveBody
  let parts := hnoalias.parts
  have hmotiveFVars : motiveIdx < H.motives.fvars.length := by
    rw [← H.motives.size]
    exact D.inBounds
  have Hmotive : Expr.ForallBinderAt motiveSource motiveIdx
      (D.type.abstractList (H.motives.fvars.take motiveIdx)) := by
    exact H.motives.forallBinderAt parts.motives D
      (body := motiveBody)
  have HmotiveClosed := Hmotive.abstractList H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++ H.motives.fvars.take motiveIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, parts.motives.take, ?_⟩
    intro param hparam motive hmotive heq
    exact parts.params_later param hparam motive
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hmotive))) heq
  have hdomain :
      (D.type.abstractList (H.motives.fvars.take motiveIdx)).abstractList
          H.params.fvars motiveIdx =
        D.type.abstractList
          (H.params.fvars ++ H.motives.fvars.take motiveIdx) := by
    have Hclose := Expr.abstractList_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars.take motiveIdx) (k := 0) hprefixNodup
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hmotiveFVars)] using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have Hraw := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, hdomain] using HmotiveClosed)
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  simpa [motiveSource, motiveBody, hparamsLength] using
    Hraw.inferImplicit 1000 false

/-- The owner motive slot of the concrete production recursor closes the
exact retained motive declaration over precisely the common parameters and
strictly earlier motives.  The subsequent `inferImplicit` pass preserves
that domain and changes only binder annotations. -/
theorem RecursorLocalSelections.ownerMotiveBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c
      (recInfos.map (·.motive)) ownerIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + ownerIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars.take ownerIdx)) := by
  dsimp only
  let motiveBody :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) motiveBody
  let parts := hnoalias.parts
  have hownerFVars : ownerIdx < H.motives.fvars.length := by
    rw [← H.motives.size]
    exact D.inBounds
  have Hmotive : Expr.ForallBinderAt motiveSource ownerIdx
      (D.type.abstractList (H.motives.fvars.take ownerIdx)) := by
    exact H.motives.forallBinderAt parts.motives D
      (body := motiveBody)
  have HmotiveClosed := Hmotive.abstractList H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++ H.motives.fvars.take ownerIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, parts.motives.take, ?_⟩
    intro param hparam motive hmotive heq
    exact parts.params_later param hparam motive
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hmotive))) heq
  have hdomain :
      (D.type.abstractList (H.motives.fvars.take ownerIdx)).abstractList
          H.params.fvars ownerIdx =
        D.type.abstractList
          (H.params.fvars ++ H.motives.fvars.take ownerIdx) := by
    have Hclose := Expr.abstractList_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars.take ownerIdx) (k := 0) hprefixNodup
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hownerFVars)] using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have Hraw := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, hdomain] using HmotiveClosed)
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  simpa [motiveSource, motiveBody, hparamsLength] using
    Hraw.inferImplicit 1000 false

/-- The flattened minor slot of the concrete production recursor closes the
exact recorded minor declaration over all parameters, all motives, and the
strictly earlier minors.  This is the source-side identity used to compare
the translated generated domain with the independently retained minor
semantics. -/
theorem RecursorLocalSelections.minorBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c
      (recInfos.flatMap (·.minors)) minorIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars ++
          H.minors.fvars.take minorIdx)) := by
  dsimp only
  let minorBody :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) minorBody
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have hminorFVars : minorIdx < H.minors.fvars.length := by
    rw [← H.minors.size]
    exact D.inBounds
  have Hminor : Expr.ForallBinderAt minorSource minorIdx
      (D.type.abstractList (H.minors.fvars.take minorIdx)) := by
    exact H.minors.forallBinderAt parts.minors D (body := minorBody)
  have HminorMotives := Hminor.abstractList H.motives.fvars 0
  have hmotivesMinorsNodup :
      (H.motives.fvars ++ H.minors.fvars.take minorIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.motives, parts.minors.take, ?_⟩
    intro motive hmotive minor hminor heq
    exact parts.motives_later motive hmotive minor
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hminor))) heq
  have hdomainMotives :
      (D.type.abstractList (H.minors.fvars.take minorIdx)).abstractList
          H.motives.fvars minorIdx =
        D.type.abstractList
          (H.motives.fvars ++ H.minors.fvars.take minorIdx) := by
    have Hclose := Expr.abstractList_after_inner
      (e := D.type) (outer := H.motives.fvars)
      (inner := H.minors.fvars.take minorIdx) (k := 0)
      hmotivesMinorsNodup
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars)] using Hclose
  have Hmotives := H.motives.forallTelescope minorSource
  have HthroughMotives := Hmotives.prependBinderAt (by
    simpa [Nat.zero_add, hdomainMotives] using HminorMotives)
  have HthroughParams := HthroughMotives.abstractList H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++
        (H.motives.fvars ++ H.minors.fvars.take minorIdx)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, hmotivesMinorsNodup, ?_⟩
    intro param hparam later hlater heq
    rcases List.mem_append.mp hlater with hmotive | hminor
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inl hmotive)) heq
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hminor))))) heq
  have hdomainParams :
      (D.type.abstractList
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractList
          H.params.fvars (H.motives.fvars.length + minorIdx) =
        D.type.abstractList
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    have Hclose := Expr.abstractList_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars ++ H.minors.fvars.take minorIdx)
      (k := 0) hprefixNodup
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars), List.append_assoc]
      using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  have hmotivesLength : H.motives.fvars.length =
      (recInfos.map (·.motive)).size := by
    rw [← H.motives.size]
  have hmotivesLength' : H.motives.fvars.length = recInfos.size := by
    simpa using hmotivesLength
  have HrawBase := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, Nat.add_assoc] using HthroughParams)
  have hdomainParamsStats :
      (D.type.abstractList
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractList
          H.params.fvars (recInfos.size + minorIdx) =
        D.type.abstractList
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    rw [← hmotivesLength']
    exact hdomainParams
  rw [hdomainParamsStats] at HrawBase
  have Hraw : Expr.ForallBinderAt
      (c.lctx.mkForall stats.params motiveSource)
      (H.params.fvars.length + (H.motives.fvars.length + minorIdx))
      (D.type.abstractList
        (H.params.fvars ++ (H.motives.fvars ++
          H.minors.fvars.take minorIdx))) := by
    simpa [hparamsLength, hmotivesLength, Nat.add_assoc] using
      HrawBase
  simpa [motiveSource, minorSource, minorBody, hparamsLength,
    hmotivesLength, Nat.add_assoc] using Hraw.inferImplicit 1000 false

/-- The owner-index slot of the concrete production recursor is the exact
retained index declaration closed over parameters, motives, minors, and the
strictly earlier owner indices. -/
theorem RecursorLocalSelections.indexBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c recInfos[ownerIdx]!.indices indexIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + indexIdx)
      (D.type.abstractList
        (H.params.fvars ++ (H.motives.fvars ++
          (H.minors.fvars ++ H.indices.fvars.take indexIdx)))) := by
  dsimp only
  let resultBody : Expr :=
    .app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major
  let majorSource :=
    c.lctx.mkForall #[recInfos[ownerIdx]!.major] resultBody
  let indexSource :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices majorSource
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) indexSource
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have hindexFVars : indexIdx < H.indices.fvars.length := by
    rw [← H.indices.size]
    exact D.inBounds
  have hindexTake : (H.indices.fvars.take indexIdx).length = indexIdx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindexFVars)]
  have Hindex : Expr.ForallBinderAt indexSource indexIdx
      (D.type.abstractList (H.indices.fvars.take indexIdx)) := by
    exact H.indices.forallBinderAt parts.indices D (body := majorSource)
  have hminorIndex :
      (H.minors.fvars ++ H.indices.fvars.take indexIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.minors, parts.indices.take, ?_⟩
    intro minor hminor index hindex heq
    exact parts.minors_later minor hminor index
      (List.mem_append.mpr
        (Or.inl (List.mem_of_mem_take hindex))) heq
  have HthroughMinors := H.minors.prependBinderAtClosed Hindex
    hindexTake hminorIndex
  have hminorIndexLength :
      (H.minors.fvars ++ H.indices.fvars.take indexIdx).length =
        (recInfos.flatMap (·.minors)).size + indexIdx := by
    rw [List.length_append, hindexTake, ← H.minors.size]
  have hmotiveMinorIndex :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars.take indexIdx)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.motives, hminorIndex, ?_⟩
    intro motive hmotive later hlater heq
    rcases List.mem_append.mp hlater with hminor | hindex
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inl hminor)) heq
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr
            (Or.inl (List.mem_of_mem_take hindex))))) heq
  have HthroughMotives := H.motives.prependBinderAtClosed HthroughMinors
    hminorIndexLength hmotiveMinorIndex
  have hmotiveMinorIndexLength :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars.take indexIdx)).length =
        (recInfos.map (·.motive)).size +
          ((recInfos.flatMap (·.minors)).size + indexIdx) := by
    rw [List.length_append, hminorIndexLength, ← H.motives.size]
  have hparamMotiveMinorIndex :
      (H.params.fvars ++ (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars.take indexIdx))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, hmotiveMinorIndex, ?_⟩
    intro param hparam later hlater heq
    rcases List.mem_append.mp hlater with hmotive | hlater
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inl hmotive)) heq
    · rcases List.mem_append.mp hlater with hminor | hindex
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inl hminor)))) heq
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inr
              (List.mem_append.mpr
                (Or.inl (List.mem_of_mem_take hindex))))))) heq
  have Hraw := H.params.prependBinderAtClosed HthroughMotives
    hmotiveMinorIndexLength hparamMotiveMinorIndex
  simpa [motiveSource, minorSource, indexSource, majorSource, resultBody,
    Nat.add_assoc] using Hraw.inferImplicit 1000 false

/-- The final major-premise slot is the exact retained major declaration
closed over all four preceding generated recursor groups. -/
theorem RecursorLocalSelections.majorBinderAt
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c #[recInfos[ownerIdx]!.major] 0) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size)
      (D.type.abstractList
        (H.params.fvars ++ (H.motives.fvars ++
          (H.minors.fvars ++ H.indices.fvars)))) := by
  dsimp only
  let resultBody : Expr :=
    .app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major
  let majorSource :=
    c.lctx.mkForall #[recInfos[ownerIdx]!.major] resultBody
  let indexSource :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices majorSource
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) indexSource
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have HmajorBase : Expr.ForallBinderAt majorSource 0
      (D.type.abstractList (H.major.fvars.take 0)) := by
    exact H.major.forallBinderAt parts.major D (body := resultBody)
  have Hmajor : Expr.ForallBinderAt majorSource 0 D.type := by
    simpa using HmajorBase
  have HthroughIndicesBase := H.indices.prependBinderAtClosed Hmajor
    (innerPrefix := []) (by simp) (by simpa using parts.indices)
  have HthroughIndices : Expr.ForallBinderAt indexSource
      recInfos[ownerIdx]!.indices.size
      (D.type.abstractList H.indices.fvars) := by
    simpa [indexSource] using HthroughIndicesBase
  have hminorIndices :
      (H.minors.fvars ++ H.indices.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.minors, parts.indices, ?_⟩
    intro minor hminor index hindex heq
    exact parts.minors_later minor hminor index
      (List.mem_append.mpr (Or.inl hindex)) heq
  have HthroughMinors := H.minors.prependBinderAtClosed HthroughIndices
    H.indices.size.symm hminorIndices
  have hminorIndicesLength :
      (H.minors.fvars ++ H.indices.fvars).length =
        (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size := by
    rw [List.length_append, ← H.minors.size, ← H.indices.size]
  have hmotiveMinorIndices :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.motives, hminorIndices, ?_⟩
    intro motive hmotive later hlater heq
    rcases List.mem_append.mp hlater with hminor | hindex
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inl hminor)) heq
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl hindex)))) heq
  have HthroughMotives := H.motives.prependBinderAtClosed HthroughMinors
    hminorIndicesLength hmotiveMinorIndices
  have hmotiveMinorIndicesLength :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars)).length =
        (recInfos.map (·.motive)).size +
          ((recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size) := by
    rw [List.length_append, hminorIndicesLength, ← H.motives.size]
  have hparamMotiveMinorIndices :
      (H.params.fvars ++ (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, hmotiveMinorIndices, ?_⟩
    intro param hparam later hlater heq
    rcases List.mem_append.mp hlater with hmotive | hlater
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inl hmotive)) heq
    · rcases List.mem_append.mp hlater with hminor | hindex
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inl hminor)))) heq
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inr
              (List.mem_append.mpr (Or.inl hindex)))))) heq
  have Hraw := H.params.prependBinderAtClosed HthroughMotives
    hmotiveMinorIndicesLength hparamMotiveMinorIndices
  simpa [motiveSource, minorSource, indexSource, majorSource, resultBody,
    Nat.add_assoc] using Hraw.inferImplicit 1000 false

/-- The retained executable binder selections, their global no-alias
invariant, and the independent cardinality certificate determine the exact
abstract shape of one generated recursor. -/
theorem RecursorLocalSelections.recursorShape
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : H.NoAlias)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (hdeclOwner : ownerIdx < decl.types.length)
    (recursor : VConstVal)
    (hname : recursor.name =
      decl.recursorName (decl.types[ownerIdx]'(hdeclOwner)))
    (huvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (Htr : TrExprS env Us Δ
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major))
      recursor.type) :
    Nonempty (decl.RecursorShape
      (decl.types[ownerIdx]'(hdeclOwner)) recursor) := by
  have Htel := H.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  have hresidual := H.residual_eq_concreteRecursorResult howner hnoalias
  rw [hresidual] at Htel
  rcases TrExprS.forallTelescope_shape_with_context Htel Htr with
    ⟨domains, result, hdomainsLength, htype, Hresult⟩
  have htotal : stats.params.size + (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 ≤ domains.length := by
    omega
  have hownerMotive : ownerIdx < (recInfos.map (·.motive)).size := by
    simpa using howner
  have hresultConcrete := TrExprS.concreteRecursorResult_eq
    (numParams := stats.params.size) hownerMotive htotal Hresult
  have hdomainsSpec : domains.length =
      decl.nparams + decl.types.length + decl.ownedConstructors.length +
        (decl.types[ownerIdx]'(hdeclOwner)).numIndices + 1 := by
    rw [hdomainsLength, Hcard.params, Hcard.motives, Hcard.minors,
      Hcard.indices ownerIdx howner]
  rcases List.exists_append_five_of_length_eq domains decl.nparams
      decl.types.length decl.ownedConstructors.length
      (decl.types[ownerIdx]'(hdeclOwner)).numIndices 1 hdomainsSpec with
    ⟨params, motives, minors, indices, major, hdomains,
      hparams, hmotives, hminors, hindices, hmajor⟩
  have hresult : result =
      decl.recursorResult ownerIdx minors.length
        (decl.types[ownerIdx]'(hdeclOwner)) := by
    simpa [VInductDecl.recursorResult,
      VInductDecl.recursorResultWithCounts, List.map_reverse,
      Hcard.records, Hcard.motives, Hcard.minors,
      Hcard.indices ownerIdx howner, hminors] using
        hresultConcrete
  refine ⟨VInductDecl.RecursorShape.ofWrapped hdeclOwner rfl hname huvars
    hparams hmotives hminors hindices hmajor ?_ hresult⟩
  simpa [hdomains] using htype

/-- Metadata and translation of the actual production `.recInfo` constant
discharge the remaining premises of `recursorShape`. This is the boundary
used by the outer installation loop after `inferImplicit`. -/
theorem RecursorLocalSelections.recursorShape_of_recInfo
    {indTypes : Array InductiveType}
    {envTypes envCtors : VEnv}
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : H.NoAlias)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hsourceOwner : ownerIdx < indTypes.size)
    (elimLevel : Level) (info : RecursorVal) (recursor : VConstVal)
    (Hinfo : TrConstVal safety env (.recInfo info) recursor)
    (hlevels : info.levelParams =
      AddInductive.getRecLevelParams elimLevel lparams)
    (hname : info.name =
      Lean.mkRecName (indTypes[ownerIdx]'(hsourceOwner)).name)
    (htype : info.type =
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false) :
    Nonempty (decl.RecursorShape
      (decl.types[ownerIdx]'(by simpa [Hcard.records] using howner))
      recursor) := by
  have hdeclOwner : ownerIdx < decl.types.length := by
    simpa [Hcard.records] using howner
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hdecl
    ownerIdx (by simpa using hsourceOwner) hdeclOwner
  have hinfoName : info.name = recursor.name := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hinfo.2
  have hownerName : (decl.types[ownerIdx]'(hdeclOwner)).name =
      (indTypes[ownerIdx]'(hsourceOwner)).name := by
    simpa using Howner.header.name
  have hrecName : recursor.name =
      decl.recursorName (decl.types[ownerIdx]'(hdeclOwner)) := by
    rw [← hinfoName, hname, VInductDecl.recursorName_eq_mkRecName,
      hownerName]
  have hrecUvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1 := by
    have htranslated : info.levelParams.length = recursor.uvars := by
      simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
        Hinfo.1.2.1
    have hdeclUvars : decl.uvars = lparams.length := Hdecl.uvars
    rw [hlevels] at htranslated
    rcases AddInductive.getRecLevelParams_length
        (elimLevel := elimLevel) (lparams := lparams) with hsame | hextra
    · left
      omega
    · right
      omega
  have htranslated : TrExprS env info.levelParams [] info.type
      recursor.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using Hinfo.1.2.2
  rw [htype] at htranslated
  have hpre := TrExprS.of_inferImplicit htranslated
  exact H.recursorShape howner hnoalias Hcard hdeclOwner recursor
    hrecName hrecUvars hpre

/-- The same installed `.recInfo` translation independently proves semantic
well-formedness of the generated recursor constant. -/
theorem RecursorLocalSelections.recursorWF_of_recInfo
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (info : RecursorVal) (recursor : VConstVal)
    (Hinfo : TrConstVal safety env (.recInfo info) recursor)
    (htype : info.type =
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false) :
    recursor.toVConstant.WF env := by
  have htranslated : TrExprS env info.levelParams [] info.type
      recursor.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using Hinfo.1.2.2
  rw [htype] at htranslated
  have hpre := TrExprS.of_inferImplicit htranslated
  have Htel := H.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  have hpositive : 0 < stats.params.size +
      (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 := by omega
  have hwf := TrExprS.isType_of_forallTelescope Htel hpositive hpre
  have huvars : info.levelParams.length = recursor.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hinfo.1.2.1
  rw [huvars] at hwf
  exact hwf

/-- Semantic payload still required from `mkRecInfos`: every concrete
recursor telescope translates, before the annotation-only `inferImplicit`
pass, to an abstract type in the pre-recursor environment. Keeping this
separate from operational fvar binding makes the remaining proof obligation
both explicit and independently reviewable. -/
structure RecursorTypeTranslations
    (env : VEnv) (lparams : List Name) (elimLevel : Level)
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo) : Prop where
  notPartial : c.safety ≠ .partial
  typeAt : ∀ owner (howner : owner < indTypes.size),
    ∃ type : VExpr,
      TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos c.lctx
          owner) type ∧
      env.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length [] type

/-- Soundness of the executable pre-installation validation loop.  Each
successful iteration checks the fully closed generated recursor type with the
recursor's exact universe parameters; erasing `inferImplicit` recovers the
pre-annotation telescope used by `RecursorTypeTranslations`. -/
theorem AddInductive.declareRecursors.checkRecursorTypes.translationsWF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array AddInductive.RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat) :
    (AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
      recInfos numMinors numMotives all lctx k isUnsafe lparams dIdx c).WF
      fun _ => ∀ owner, dIdx ≤ owner →
        (howner : owner < indTypes.size) →
        ∃ type : VExpr,
          TrExprS venv (AddInductive.getRecLevelParams elimLevel lparams) []
            (AddInductive.declareRecursors.recursorType stats recInfos lctx
              owner) type ∧
          venv.IsType
            (AddInductive.getRecLevelParams elimLevel lparams).length []
            type := by
  rw [AddInductive.declareRecursors.checkRecursorTypes]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    let info := AddInductive.declareRecursors.recursorInfo stats indTypes
      elimLevel recInfos numMinors numMotives all lctx k isUnsafe lparams
      dIdx []
    refine (AddInductive.declareRecursors.checkRecursorType.WF Hvalid info).bind
      fun _ ⟨type, Htype, HisType⟩ => ?_
    have Htype' : TrExprS venv
        (AddInductive.getRecLevelParams elimLevel lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos lctx
          dIdx) type := by
      apply TrExprS.of_inferImplicit
        (numParams := 1000) (considerRange := false)
      simpa [info, AddInductive.declareRecursors.recursorInfo] using Htype
    have HisType' : venv.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length [] type := by
      simpa [info, AddInductive.declareRecursors.recursorInfo] using HisType
    refine (AddInductive.declareRecursors.checkRecursorTypes.translationsWF
      Hvalid stats indTypes elimLevel recInfos numMinors numMotives all lctx k
      isUnsafe lparams (dIdx + 1)).mono fun _ Htail owner hdone howner => ?_
    by_cases heq : owner = dIdx
    · subst owner
      exact ⟨type, Htype', HisType'⟩
    · exact Htail owner (by omega) howner
  · rw [dif_neg hidx]
    exact Except.WF.pure fun owner _ howner =>
      False.elim (hidx (by omega))
termination_by indTypes.size - dIdx

/-- The complete executable validation loop supplies precisely the semantic
recursor-type certificate consumed by the installation loop.  The sole
non-computational premise excludes `.partial`, which production inductive
checking never uses and whose visibility order is incompatible with the
generated `isUnsafe` bit. -/
theorem AddInductive.declareRecursors.checkRecursorTypes.recursorTypeTranslationsWF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (hnotPartial : c.safety ≠ .partial)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array AddInductive.RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) :
    (AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
      recInfos numMinors numMotives all lctx k isUnsafe lparams 0 c).WF
      fun _ => RecursorTypeTranslations venv lparams elimLevel
        { c with lctx := lctx } stats indTypes recInfos := by
  refine (AddInductive.declareRecursors.checkRecursorTypes.translationsWF
    Hvalid stats indTypes elimLevel recInfos numMinors numMotives all lctx k
    isUnsafe lparams 0).mono fun _ Hall => ?_
  exact {
    notPartial := hnotPartial
    typeAt := fun owner howner => Hall owner (Nat.zero_le _) howner }

/-- Once the generated telescope itself is translated, all production
`RecursorVal` metadata is irrelevant to abstract constant construction.
Rules and the K flag may therefore vary without reopening the typing proof. -/
theorem RecursorTypeTranslations.recursorInfoTranslation
    (H : RecursorTypeTranslations env lparams elimLevel c stats indTypes
      recInfos)
    (k : Bool) (owner : Nat) (howner : owner < indTypes.size)
    (rules : List RecursorRule) :
    ∃ recursor : VConstVal,
      TrConstVal c.safety env
        (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
          elimLevel recInfos (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size
          (indTypes.map (·.name)).toList c.lctx k
          (c.safety != .safe) lparams owner rules)) recursor ∧
      recursor.toVConstant.WF env := by
  rcases H.typeAt owner howner with ⟨type, Htr, Hwf⟩
  let recursor : VConstVal := {
    uvars := (AddInductive.getRecLevelParams elimLevel lparams).length
    type := type
    name := Lean.mkRecName indTypes[owner]!.name }
  refine ⟨recursor, ?_, ?_⟩
  · constructor
    · refine ⟨?_, rfl, ?_⟩
      · have hsafety := H.notPartial
        cases hs : c.safety <;>
          simp_all [ConstantInfo.safety, ConstantInfo.isUnsafe,
            ConstantInfo.isPartial,
            AddInductive.declareRecursors.recursorInfo]
      · exact TrExprS.inferImplicit Htr 1000 false
    · rfl
  · exact Hwf

/-- Pointwise record emitted by one iteration of the production recursor
loop. It retains only the metadata needed to connect that iteration to the
independent shape and semantic-typing judgments. -/
structure GeneratedRecursorEntry
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (ownerIdx : Nat) (entry : ConstantInfo × VConstVal) where
  info : RecursorVal
  source_eq : entry.1 = .recInfo info
  translated : TrConstVal safety env (.recInfo info) entry.2
  levels : info.levelParams =
    AddInductive.getRecLevelParams elimLevel lparams
  name : info.name = Lean.mkRecName indTypes[ownerIdx]!.name
  /-- The production recursor pass chooses safety from the checking context.
  Retaining this exact bit is needed when an unsafe block is hidden from the
  partial and safe environment observers. -/
  isUnsafe : info.isUnsafe = (c.safety != .safe)
  type : info.type =
    (c.lctx.mkForall stats.params <|
     c.lctx.mkForall (recInfos.map (·.motive)) <|
     c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
     c.lctx.mkForall recInfos[ownerIdx]!.indices <|
     c.lctx.mkForall #[recInfos[ownerIdx]!.major]
       (.app (mkAppN recInfos[ownerIdx]!.motive
         recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
      1000 false
  rules : BoundGeneratedRecursorRules indTypes stats
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[ownerIdx]!.ctors (recursorMinorOffset indTypes ownerIdx)
    info.rules

def GeneratedRecursorEntry.ofRecursorInfo
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (numMinors numMotives : Nat) (all : List Name)
    (k isUnsafe : Bool) (ownerIdx : Nat) (rules : List RecursorRule)
    (recursor : VConstVal)
    (hunsafe : isUnsafe = (c.safety != .safe))
    (Htr : TrConstVal safety env
      (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams ownerIdx rules)) recursor)
    (Hrules : BoundGeneratedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels)
      indTypes[ownerIdx]!.ctors (recursorMinorOffset indTypes ownerIdx)
      rules) :
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos ownerIdx
      (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams ownerIdx rules), recursor) where
  info := AddInductive.declareRecursors.recursorInfo stats indTypes
    elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe lparams
    ownerIdx rules
  source_eq := rfl
  translated := Htr
  levels := rfl
  name := rfl
  isUnsafe := by
    simp [AddInductive.declareRecursors.recursorInfo, hunsafe]
  type := rfl
  rules := Hrules

/-- Reviewable output invariant for the complete production recursor loop. -/
structure GeneratedRecursors
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  length : entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

/-- Append-oriented form matching the `for dIdx in [:indTypes.size]` loop. -/
structure GeneratedRecursorsPrefix
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  covered : entries.length ≤ recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

/-- Suffix-oriented traversal invariant used by the explicit recursive
`declareRecursors.loop`. Unlike `GeneratedRecursorsPrefix`, this form can be
applied recursively at an arbitrary owner index without carrying an
accumulator through executable code. -/
structure GeneratedRecursorsRange
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (start : Nat) (entries : List (ConstantInfo × VConstVal)) where
  covered : start + entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos (start + i) entries[i]

/-- Semantic companion to `GeneratedRecursorsRange`.  The ordinary range
certificate records the source/target recursor entry and bounded rule batch;
this certificate retains, for the same owner slice, the exact field
classification and recursive-call evidence produced while constructing each
rule.  It deliberately does not duplicate the translated recursor value. -/
structure GeneratedRecursorRuleSemanticsRange
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (Horigins : RecInfoTypeOrigins semanticRoot recInfos)
    (elimLevel : Level)
    (parameterDecls : VLCtx)
    (start : Nat) (entries : List (ConstantInfo × VConstVal)) where
  covered : start + entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    ∃ info : RecursorVal,
      entries[i].1 = .recInfo info ∧
      ∃ Hrules : SemanticBoundGeneratedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) Rroot decl
          (start + i) indTypes[start + i]!.ctors
          (recursorMinorOffset indTypes (start + i)) info.rules,
        Nonempty (Hrules.ProducerMotiveEvidence recInfos elimLevel) ∧
        ∀ localIndex
            (hctor : localIndex < indTypes[start + i]!.ctors.length)
            (hrule : localIndex < info.rules.length),
          ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
              (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
              (AddInductive.getRecLevels elimLevel stats.levels)
              indTypes[start + i]!.ctors[localIndex]
              (recursorMinorOffset indTypes (start + i) + localIndex)
              info.rules[localIndex],
            ∃ S : Hrule.Semantics Rroot decl (start + i),
              Nonempty (Hrule.ProducerOriginEvidence S recInfos elimLevel
                Horigins (start + i) localIndex) ∧
              S.parameterDecls = parameterDecls

def GeneratedRecursorsRange.atZero
    (H : GeneratedRecursorsRange safety env lparams elimLevel c stats
      indTypes recInfos 0 entries)
    (hcomplete : entries.length = recInfos.size) :
    GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries where
  length := hcomplete
  entry i hi := by simpa using H.entry i hi

theorem GeneratedRecursors.nonInductive
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries) :
    ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ ConstantInfo.inductInfo inductiveValue := by
  intro info value hmem inductiveValue
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have Hentry := H.entry i hi
  rw [heq] at Hentry
  have hsource : info = .recInfo Hentry.info := by
    simpa using Hentry.source_eq
  rw [hsource]
  simp

/-- Generated recursor entries cannot introduce constructor metadata. -/
theorem GeneratedRecursors.nonConstructor
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries) :
    ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ constructorValue,
        info ≠ ConstantInfo.ctorInfo constructorValue := by
  intro info value hmem constructorValue
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have Hentry := H.entry i hi
  rw [heq] at Hentry
  have hsource : info = .recInfo Hentry.info := by
    simpa using Hentry.source_eq
  rw [hsource]
  simp

def GeneratedRecursorsPrefix.empty
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo) :
    GeneratedRecursorsPrefix safety env lparams elimLevel c stats indTypes
      recInfos [] where
  covered := Nat.zero_le _
  entry _ hi := by simp at hi

def GeneratedRecursorsPrefix.push
    (H : GeneratedRecursorsPrefix safety env lparams elimLevel c stats
      indTypes recInfos entries)
    (hnext : entries.length < recInfos.size)
    (E : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos entries.length newEntry) :
    GeneratedRecursorsPrefix safety env lparams elimLevel c stats indTypes
      recInfos (entries ++ [newEntry]) where
  covered := by simp; omega
  entry i hi := by
    by_cases hold : i < entries.length
    · simpa [List.getElem_append, hold] using H.entry i hold
    · have hieq : i = entries.length := by simp at hi; omega
      subst i
      simpa using E

def GeneratedRecursorsPrefix.complete
    (H : GeneratedRecursorsPrefix safety env lparams elimLevel c stats
      indTypes recInfos entries)
    (hcomplete : entries.length = recInfos.size) :
    GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries where
  length := hcomplete
  entry := H.entry

/-- A validated mutual-family owner index names an actually generated
recursor. This is the global half of the pointwise `RecursorsPresent`
obligation retained by generated recursive calls. -/
theorem GeneratedRecursors.recursorName_mem
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (hrecords : recInfos.size = indTypes.size)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    Lean.mkRecName indTypes[ownerIdx]!.name ∈
      (entries.map Prod.snd).map (·.name) := by
  have hentry : ownerIdx < entries.length := by
    rw [H.length, hrecords]
    exact howner
  let E := H.entry ownerIdx hentry
  have htranslatedName : E.info.name = entries[ownerIdx].2.name := by
    exact E.translated.2
  have hname : entries[ownerIdx].2.name =
      Lean.mkRecName indTypes[ownerIdx]!.name := by
    rw [← htranslatedName, E.name]
  rw [← hname]
  exact List.mem_map.mpr ⟨entries[ownerIdx].2,
    List.mem_map.mpr ⟨entries[ownerIdx], List.getElem_mem hentry, rfl⟩,
    rfl⟩

theorem GeneratedRecursors.recursorName_mem_block
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (hrecords : recInfos.size = indTypes.size)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    Lean.mkRecName indTypes[ownerIdx]!.name ∈
      block.recursors.map (·.name) := by
  rw [hrecursors]
  exact H.recursorName_mem hrecords ownerIdx howner

/-- The retained owner of a typed recursive field selects a generated
recursor in the installed block. -/
theorem GeneratedRecursors.recursiveDomainRecursor_mem_block
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (cert : RecursorRecursiveDomain domainEnv decl) :
    Lean.mkRecName indTypes[cert.ownerIdx]!.name ∈
      block.recursors.map (·.name) := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
  have hrecords : recInfos.size = indTypes.size := by
    rw [Hcard.records, htypes]
  have howner : cert.ownerIdx < indTypes.size := by
    rw [htypes]
    exact cert.owner_lt
  exact H.recursorName_mem_block block hrecords hrecursors cert.ownerIdx howner

/-- Every validated generated call selects an in-range mutual-family owner,
so its recursor is present in the installed block.  The independent field
classifier need not reproduce that owner choice: rule typing already checks
the generated sibling-recursion application, while `IotaRule` requires only
that it is guarded on a certified recursive field. -/
theorem GeneratedRecursors.recursorsPresent
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hcalls : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size) :
    Hcalls.RecursorsPresent (block.recursors.map (·.name)) := by
  intro i hi Hentry
  have hstats : Hentry.ownerIdx < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some Hentry.owner_valid).1
  have hdeclOwner : Hentry.ownerIdx < decl.types.length := by
    rwa [Hcard.families] at hstats
  have hsourceOwner : Hentry.ownerIdx < indTypes.size := by
    have htypes : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
    rwa [htypes]
  rw [Hentry.recursorName_eq_owner]
  exact H.recursorName_mem_block block (by
    rw [Hcard.records]
    simpa using
      (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl).symm)
    hrecursors Hentry.ownerIdx hsourceOwner

/-- Global recursor generation discharges the final coverage premise of the
pointwise generated-rule theorem. Every recursive call is routed through its
classifier-retained mutual owner and hence names an installed primary
recursor. -/
theorem GeneratedRecursors.iotaRule_ofTranslationCertificate
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hequation : Hrule.IotaEquationTranslationCertificate trEnv Us Δ decl
      block owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl Hrule.allArgs
      Hrule.recursiveArgs selections)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS trEnv Us
        (abstractForallContext Hequation.shape.domains Δ))
      (Hrule.recursiveArgs.map fun arg =>
        arg.abstractList Hrule.binders).toList recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hequation.shape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) := by
  have hpresent := Hgenerated.recursorsPresent block Hcard Hdecl hrecursors
    Hrule.recursive_calls
  exact Hrule.iotaRule_ofTranslationCertificate Hequation Hselection Hargs
    hfresh hctx hproj hpresent

theorem GeneratedRecursors.iotaRule_ofTranslation
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Htr : Hrule.StagedIotaRuleTranslation trEnv Us Δ semanticEnv decl
      block owner ctor rule) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) :=
  Hrule.iotaRule_ofStagedTranslation Htr

/-- Append one generated family batch to the flattened iota accumulator.
The pointwise premise now asks only for the explicit executable-to-`VDefEq`
translation payload; `IotaRule` itself is derived uniformly using the global
generated-recursor certificate. -/
theorem GeneratedRecursors.appendIotaBatch
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hbuild : IotaBuildCertificate semanticEnv decl block prior)
    (Hbatch : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (Htranslations : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length)
      (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) sourceRules[i]),
      Nonempty (Hrule.StagedIotaRuleTranslation trEnv Us Δ semanticEnv
        decl block decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate semanticEnv decl block (prior ++ abstractRules) := by
  apply Hbuild.appendBoundGeneratedRules Hbatch hlength hroom
  intro i hctor hsource habstract Hrule
  rcases Htranslations i hctor hsource habstract Hrule with ⟨Htr⟩
  exact Hgenerated.iotaRule_ofTranslation Hrule Hcard Hdecl block hrecursors
    Htr

/-- Per-owner semantic payload for the exact rule batches retained by
`GeneratedRecursors`.  The index is the number of mutual-family recursors
already consumed; the accumulated rules are therefore in the flattened
constructor order required by `IotaBuildCertificate`. -/
inductive GeneratedIotaTranslations
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (semanticEnv trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (block : VInductBlock) :
    Nat → List VDefEq → Prop
  | nil : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl
      block 0 []
  | cons
      (Hprior : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ
        decl block owner prior)
      (howner : owner < entries.length)
      (batch : List VDefEq)
      (hlength : batch.length =
        (Hgenerated.entry owner howner).info.rules.length)
      (hroom : batch.length + prior.length ≤
        decl.ownedConstructors.length)
      (translations : ∀ i
        (hctor : i < indTypes[owner]!.ctors.length)
        (hsource : i <
          (Hgenerated.entry owner howner).info.rules.length)
        (habstract : i < batch.length)
        (Hrule : BoundGeneratedRecursorRule indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[owner]!.ctors[i]
          (recursorMinorOffset indTypes owner + i)
          (Hgenerated.entry owner howner).info.rules[i]),
        (hindex : prior.length + i < decl.ownedConstructors.length) →
        Nonempty (Hrule.StagedIotaRuleTranslation trEnv Us Δ semanticEnv
          decl block (decl.ownedConstructors[prior.length + i]'hindex).1
          (decl.ownedConstructors[prior.length + i]'hindex).2 batch[i])) :
      GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl block
        (owner + 1) (prior ++ batch)

theorem GeneratedIotaTranslations.ruleLength
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (H : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl
      block owner rules)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors) :
    rules.length = recursorMinorOffset indTypes owner := by
  induction H with
  | nil => simp [recursorMinorOffset]
  | @cons actualOwner actualPrior Hprior howner batch hlength _hroom
      _translations ih =>
    let E := Hgenerated.entry _ howner
    have hsource : actualOwner < indTypes.size := by
      have hrec : actualOwner < recInfos.size := by
        simpa [Hgenerated.length] using howner
      have htypes : recInfos.size = indTypes.size := by
        rw [Hcard.records]
        simpa using
          (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl).symm
      omega
    have hrules : E.info.rules.length = indTypes[actualOwner]!.ctors.length :=
      E.rules.length
    simp only [List.length_append]
    rw [hlength, hrules, ih,
      recursorMinorOffset_step indTypes actualOwner hsource]

/-- Add one owner batch without asking the caller to prove flattened-index
room.  Batch length, source translation, and the recursor offset determine
that arithmetic fact. -/
theorem GeneratedIotaTranslations.push
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hprior : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ
      decl block owner prior)
    (howner : owner < entries.length)
    (batch : List VDefEq)
    (hlength : batch.length =
      (Hgenerated.entry owner howner).info.rules.length)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (translations : ∀ i
      (hctor : i < indTypes[owner]!.ctors.length)
      (hsource : i < (Hgenerated.entry owner howner).info.rules.length)
      (habstract : i < batch.length)
      (Hrule : BoundGeneratedRecursorRule indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (Hgenerated.entry owner howner).info.rules[i]),
      (hindex : prior.length + i < decl.ownedConstructors.length) →
      Nonempty (Hrule.StagedIotaRuleTranslation trEnv Us Δ semanticEnv
        decl block (decl.ownedConstructors[prior.length + i]'hindex).1
        (decl.ownedConstructors[prior.length + i]'hindex).2 batch[i])) :
    GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl block
      (owner + 1) (prior ++ batch) := by
  let E := Hgenerated.entry owner howner
  have hsourceOwner : owner < indTypes.size := by
    have hrec : owner < recInfos.size := by
      simpa [Hgenerated.length] using howner
    have htypes : recInfos.size = indTypes.size := by
      rw [Hcard.records]
      simpa using
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl).symm
    omega
  have hpriorLength : prior.length = recursorMinorOffset indTypes owner :=
    Hprior.ruleLength Hgenerated Hcard Hdecl
  have hbatchLength : batch.length = indTypes[owner]!.ctors.length := by
    rw [hlength, E.rules.length]
  have hconcreteRoom := recursorMinorOffset_room indTypes owner hsourceOwner
  have hownedLength :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        decl.ownedConstructors.length := by
    simpa [ownedConstructors, List.length_flatMap] using
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl
  exact .cons Hprior howner batch hlength (by
    rw [hbatchLength, hpriorLength, ← hownedLength]
    omega) translations

theorem GeneratedIotaTranslations.build
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (H : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl
      block owner rules)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hrecursors : block.recursors = entries.map Prod.snd) :
    IotaBuildCertificate semanticEnv decl block rules := by
  induction H with
  | nil => exact .empty semanticEnv decl block
  | cons Hprior howner batch hlength hroom Htranslations ih =>
    let E := Hgenerated.entry _ howner
    exact Hgenerated.appendIotaBatch Hcard Hdecl block hrecursors ih E.rules
      hlength hroom
      (fun i hctor hsource habstract Hrule =>
        Htranslations i hctor hsource habstract Hrule (by omega))

theorem GeneratedIotaTranslations.completeLength
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (H : GeneratedIotaTranslations Hgenerated semanticEnv trEnv Us Δ decl
      block owner rules)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hcomplete : owner = entries.length) :
    rules.length = decl.ownedConstructors.length := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
  have howner : owner = indTypes.size := by
    rw [hcomplete, Hgenerated.length, Hcard.records, ← htypes]
  rw [H.ruleLength Hgenerated Hcard Hdecl, howner]
  have hoffset : recursorMinorOffset indTypes indTypes.size =
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
    unfold recursorMinorOffset
    simp only [List.length_flatMap]
    have hlen : indTypes.size =
        (indTypes.toList.map (fun type => type.ctors.length)).length := by
      simp
    rw [hlen, List.map_take, List.take_length]
  rw [hoffset]
  simpa [ownedConstructors, List.length_flatMap] using
    Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl

theorem GeneratedRecursors.recursorCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors) :
    RecursorCertificate decl (entries.map Prod.snd) := by
  have hindTypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
  refine {
    length := by simp [H.length, Hcard.records]
    shapes := ?_ }
  intro i htype hrec
  have hentry : i < entries.length := by simpa using hrec
  have howner : i < recInfos.size := by simpa [H.length] using hentry
  have hsource : i < indTypes.size := by omega
  let Hlocal := Hbindings.toRecursorLocalSelections Hc Hparams i howner
  have hlocalNoAlias : Hlocal.NoAlias :=
    Hbindings.selectionNoAlias Hc Hparams hnoalias i howner
  let E := H.entry i hentry
  have hshape := Hlocal.recursorShape_of_recInfo howner hlocalNoAlias Hcard
    Hdecl hsource elimLevel E.info entries[i].2 E.translated E.levels
    (by simpa [Array.getElem!_eq_getD, Array.getD, hsource] using E.name)
    E.type
  simpa [E, Hlocal] using hshape

theorem GeneratedRecursors.recursorsWF
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    ∀ recursor ∈ entries.map Prod.snd, recursor.toVConstant.WF env := by
  intro recursor hrec
  rcases List.mem_iff_getElem.mp hrec with ⟨i, hi, heq⟩
  have hentry : i < entries.length := by simpa using hi
  have heqTarget : entries[i].2 = recursor := by simpa using heq
  subst recursor
  have howner : i < recInfos.size := by simpa [H.length] using hentry
  let Hlocal := Hbindings.toRecursorLocalSelections Hc Hparams i howner
  let E := H.entry i hentry
  have hwf := Hlocal.recursorWF_of_recInfo howner E.info entries[i].2
    E.translated E.type
  simpa using hwf

/-- Once the rule traversal and global name check are supplied, the generated
recursor-loop certificate fills the recursor component of the independent
ordinary-compilation interface. -/
theorem GeneratedRecursors.ordinaryCompilationCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (hrules : IotaCertificate envCtors decl block)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    OrdinaryCompilationCertificate sourceEnv decl block := by
  refine {
    types := htypes
    ctors := hctors
    recursors := ?_
    rules := ⟨envTypes, envCtors, by simpa [htypes] using Hdecl.typesAdded,
      by simpa [hctors] using Hdecl.ctorsAdded, hrules⟩
    names := hnames }
  rw [hrecursors]
  exact H.recursorCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl

/-- Rule-batch endpoint for ordinary compilation. Generated family batches
accumulate `IotaRule` evidence with `IotaBuildCertificate`; exact flattened
coverage turns that executable traversal invariant into the final rule
certificate consumed by `OrdinaryCompilationCertificate`. -/
theorem GeneratedRecursors.ordinaryCompilationCertificate_ofRuleBuild
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hrules : IotaBuildCertificate envCtors decl block block.rules)
    (hrulesLength : block.rules.length = decl.ownedConstructors.length)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    OrdinaryCompilationCertificate sourceEnv decl block :=
  H.ordinaryCompilationCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl
    block htypes hctors hrecursors (Hrules.completeBlock hrulesLength) hnames

/-- Nested restoration reuses the verified primary recursor traversal and
adds only the separately audited auxiliary-name/guardedness suffix. -/
def GeneratedRecursors.nestedCompilationCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock) (main : VInductiveType)
    (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (auxRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (Haux : AuxiliaryRestorationPrefix decl block main
      auxRecursors auxiliaryRules)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors =
      entries.map Prod.snd ++ auxRecursors)
    (hrules : block.rules = primaryRules ++ auxiliaryRules)
    (hprimaryRules : NestedIotaListCertificate decl block primaryRules)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    NestedCompilationCertificate sourceEnv decl block where
  main := main
  rest := rest
  types_source := htypesSource
  types := htypes
  ctors := hctors
  envTypes := envTypes
  envCtors := envCtors
  types_added := by simpa [htypes] using Hdecl.typesAdded
  ctors_added := by simpa [hctors] using Hdecl.ctorsAdded
  primaryRecursors := entries.map Prod.snd
  auxiliaryRecursors := auxRecursors
  recursors_eq := hrecursors
  primary_recursors :=
    (H.recursorCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl).toNested
  auxiliary_names := Haux.names
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  rules_eq := hrules
  primary_rules := hprimaryRules
  auxiliary_guarded := Haux.guarded
  names := hnames

end VerifyInductive
end Lean4Lean
