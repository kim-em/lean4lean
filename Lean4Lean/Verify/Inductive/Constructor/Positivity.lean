import Lean4Lean.Verify.Inductive.Header.LoopInd

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkConstructors.loopCtors

theorem result.WF
    (hidx : ¬ ctorIdx < ctors.length) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx]
  exact Except.WF.pure hQ

/-- One constructor-loop iteration up to the already verified telescope
checker. The continuation receives the closed source translation before
choosing the public `CtorShape` refinement. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  rw [if_neg (by simpa using hfresh)]
  exact (checkClosedType.WF Hc).bind fun _ hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
      ((AddInductive.checkConstructors.loopCtor stats isUnsafe
          ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
          c'.fuel.inductiveFuel >>= fun _ =>
        AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
          (foundCtors.insert ctors[ctorIdx].name)) : AddInductive.M Unit) c).WF Q
    have hread : ((read : AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine hread.bind fun c' hc' => ?_
    subst c'
    exact (Hloop _ type' checkedType' hchecked).bind fun _ hnext => hnext

/-- One constructor-loop iteration, including the production duplicate-name
guard.  A duplicate takes the executable error branch; only the successful
branch reaches the semantic constructor checker. -/
theorem stepPrefix.checkedWF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  cases hfresh : foundCtors.contains ctors[ctorIdx].name with
  | false => exact stepPrefix.WF Hc hidx hfresh Hloop
  | true =>
      rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
      simp only [hfresh, ↓reduceIte]
      exact Except.WF.throw

/-- Shape-producing constructor step. This is the interface used by the
flattened constructor-prefix accumulator; all telescope details remain local
to `Hshape`. -/
theorem stepShape.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr}
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : decl.CtorShape envTypes params target ctor' →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepPrefix.WF (stats := stats) (isUnsafe := isUnsafe)
    (targetIdx := targetIdx) (Q := Q) Hc hidx hfresh
  intro checkedType type' checkedType' hchecked
  exact (Hshape checkedType type' checkedType' hchecked).mono fun _ hshape =>
    Hnext hshape

theorem stepCertificate.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr} {done : Nat}
    (Hc : ContextWF c)
    (Hprefix : ConstructorPrefixCertificate Hc.venv decl envTypes params done)
    (hdone : done < decl.ownedConstructors.length)
    (howned : decl.ownedConstructors[done] = (target, ctor'))
    (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : ConstructorPrefixCertificate Hc.venv decl envTypes params
        (done + 1) →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepShape.WF (decl := decl) (target := target) (ctor' := ctor')
    (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
    (Q := Q) Hc hidx hfresh Hshape
  intro hshape
  have hshape' : decl.CtorShape envTypes params
      decl.ownedConstructors[done].1 decl.ownedConstructors[done].2 := by
    rw [howned]
    exact hshape
  exact Hnext (Hprefix.push hdone hshape')

/-- Complete the production constructor loop for one family.  Name-set
freshness is exposed against the exact reachable state, while semantic shape
checking is supplied one translated constructor at a time. -/
theorem refinesType
    {decl : VInductDecl} {target : VInductiveType}
    {sourceEnv envTypes : VEnv} {params : List VExpr}
    {source : InductiveType}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams source target)
    (Hprefix : ConstructorTypePrefix envTypes decl params target ctorIdx)
    (Hshape : ∀ i (hsource : i < source.ctors.length)
      (htarget : i < target.ctors.length),
      TrSourceConstRaw envTypes c.lparams source.ctors[i].name
        source.ctors[i].type target.ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        source.ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        source.ctors[i].name targetIdx source.ctors[i].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target target.ctors[i] ∧
          envTypes.IsType decl.uvars [] target.ctors[i].type)
    (Hfinish : ConstructorTypePrefix envTypes decl params target
        target.ctors.length →
      Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepPrefix.checkedWF (stats := stats) (isUnsafe := isUnsafe)
      (targetIdx := targetIdx) (Q := Q) Hc hidx
    intro checkedType type' checkedType' hchecked
    have Hchecked := Hshape ctorIdx hidx htarget Hctor checkedType type'
      checkedType' hchecked
    exact Hchecked.mono fun _ hcheckedCtor =>
      refinesType Q Hc Htarget
        (Hprefix.push htarget hcheckedCtor.1 hcheckedCtor.2)
        Hshape Hfinish
  · have heq : ctorIdx = source.ctors.length := by
      have := Hprefix.covered
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
        at this
      omega
    apply result.WF (Q := Q) hidx
    have Hcomplete : ConstructorTypePrefix envTypes decl params target
        target.ctors.length := by
      simpa [heq,
        Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget] using
          Hprefix
    exact Hfinish Hcomplete
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

theorem result.WF
    (hidx : ¬ targetIdx < indTypes.size) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx]
  exact Except.WF.pure hQ

theorem step.WF
    (hidx : targetIdx < indTypes.size)
    (Hctors :
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        indTypes[targetIdx].ctors 0 {} c).WF fun _ =>
      (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
        (targetIdx + 1) c).WF Q) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx]
  exact Hctors.bind fun _ hnext => hnext

/-- Fold the verified inner constructor traversal over every family in a
mutual block, retaining the same two-dimensional order as the source arrays. -/
theorem refinesBlock
    {decl : VInductDecl} {sourceEnv envTypes : VEnv}
    {params : List VExpr}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv envTypes c.lparams)
      indTypes.toList decl.types)
    (Hprefix : ConstructorTypesPrefix envTypes decl params targetIdx)
    (Hshape : ∀ targetIdx (hsource : targetIdx < indTypes.size)
      (htarget : targetIdx < decl.types.length)
      i (hctorSource : i < indTypes[targetIdx].ctors.length)
      (hctorTarget : i < decl.types[targetIdx].ctors.length),
      TrSourceConstRaw envTypes c.lparams indTypes[targetIdx].ctors[i].name
        indTypes[targetIdx].ctors[i].type decl.types[targetIdx].ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[targetIdx].ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[targetIdx].ctors[i].name targetIdx
        indTypes[targetIdx].ctors[i].type 0 c.fuel.inductiveFuel c).WF
        fun _ => decl.CtorShape envTypes params decl.types[targetIdx]
          decl.types[targetIdx].ctors[i] ∧
          envTypes.IsType decl.uvars [] decl.types[targetIdx].ctors[i].type)
    (Hfinish : ConstructorTypesPrefix envTypes decl params
        decl.types.length → Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.refinesType
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc Htarget
      (ConstructorTypePrefix.empty envTypes decl params decl.types[targetIdx])
    · intro i hsource htarget' Hctor checkedType type' checkedType' hchecked
      exact Hshape targetIdx hidx htarget i hsource htarget' Hctor
        checkedType type' checkedType' hchecked
    · intro Htype
      exact refinesBlock Q Hc Htypes
        (Hprefix.push htarget Htype) Hshape Hfinish
  · have heq : targetIdx = indTypes.size := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := Q) hidx
    apply Hfinish
    have hlength : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
    simpa [heq, hlength] using Hprefix
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

namespace checkConstructors.loopCtor

theorem zero.WF :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkConstructors.loopCtor] at h

/-- A constructor telescope ending in the checked target application returns
success; the separate application-refinement theorem will connect
`isValidIndAppIdx` to `VInductDecl.ValidIndAppAt`. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals exact Except.WF.pure hQ

/-- An invalid non-forall constructor target is rejected. -/
theorem invalidResult.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = false) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Common-parameter branch of a constructor telescope.  The cached parameter
type comparison is converted directly into abstract body instantiation. -/
theorem parameter.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = some param)
    (hget : (AddInductive.getType param c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx param param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 param) (body'.inst param') →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel c).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  change (AddInductive.getType param c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other
          s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel) : AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact Hrec heq hopened

/-- Safe constructor-field branch.  Successful field typing, the executable
universe bound, positivity, annotation transport, and fresh body opening are
all delivered to the recursive continuation. -/
theorem safeField.sourceWF
    {Pos : Prop}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF (fun _ => Pos))
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      Pos →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !false then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    refine Hpos.bind fun _ hpos => ?_
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound hpos body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Unsafe constructor-field branch: the same source typing, universe, and
annotation obligations apply, while positivity is intentionally skipped. -/
theorem unsafeField.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !true then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkConstructors.loopCtor

namespace checkPositivityStep

theorem hasIndOcc_eq_findAny :
    AddInductive.hasIndOcc indConsts type =
      type.findAny (fun
        | .const name _ => indConsts.any fun I => I.constName! == name
        | _ => false) := by
  unfold AddInductive.hasIndOcc
  exact Expr.find?_isSome_eq_findAny _ _

def IndConstNames (indConsts : Array Expr) (names : List Name) : Prop :=
  ∀ name, (indConsts.any fun I => I.constName! == name) = names.contains name

/-- The concrete array accumulated by header checking has exactly the abstract
mutual-family names, in declaration order.  Keeping this stronger structural
fact separate makes the weaker search correspondence above reusable by both
positivity and recursive-target validation. -/
structure IndConstArray (levels : List Level) (indConsts : Array Expr)
    (names : List Name) : Prop where
  exact : indConsts = (names.map fun name => .const name levels).toArray
  names : IndConstNames indConsts names

/-- The portion of the mutable header statistics needed to interpret a
recursive application in the independent declaration.  In particular, the
common parameters are related by expression translation rather than merely by
array position. -/
structure ValidAppStatsWF (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- The exact cached-parameter suffix supports the same application
statistics as the ambient checker context, but at independent depth zero.
This is the initial narrow invariant used before genuine recursor indices are
opened. -/
def _root_.Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.ParameterContextSuffix.narrowStats
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (Hstats : ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (hparams : stats.params.size = decl.nparams) :
    ValidAppStatsWF Hc.venv c.lparams H.parameterDecls stats decl 0 where
  levels := Hstats.levels
  uvars := Hstats.uvars
  consts := Hstats.consts
  indices := Hstats.indices
  params := by
    rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl,
      ← hparams]
    exact H.narrowParams
  paramFVars := Hstats.paramFVars

theorem forall₂_length_eq
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.mapM_some_length
    {xs : List α} {ys : List β} {f : α → Option β}
    (H : xs.mapM f = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp at H
    subst ys
    rfl
  | cons x xs ih =>
    cases hx : f x <;> simp [hx] at H
    rename_i y
    cases hxs : xs.mapM f <;> simp [hxs] at H
    rename_i ys'
    subst ys
    simp [ih hxs]

theorem forall₂_get?_eq_some
    {R : α → β → Prop} {as : List α} {bs : List β}
    {i : Nat} {a : α} {b : β}
    (H : List.Forall₂ R as bs)
    (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at ha hb
      subst a
      subst b
      exact h
    | succ i => exact ih (by simpa using ha) (by simpa using hb)

theorem ValidAppStatsWF.params_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.params.size = decl.nparams := by
  have := forall₂_length_eq H.params
  simpa [VInductDecl.paramVars] using this

theorem ValidAppStatsWF.types_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem ValidAppStatsWF.indConstAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem ValidAppStatsWF.nindicesAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem ValidAppStatsWF.paramAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env Us Δ stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlen := forall₂_length_eq H.params
      simpa using hlen ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    forall₂_get?_eq_some H.params hsource htarget⟩

theorem ValidAppStatsWF.paramFVarAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

theorem forall₂_map_right
    (H : List.Forall₂ R as bs)
    (hf : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S as (bs.map f) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

@[simp] theorem VInductDecl.paramVars_liftN
    {decl : VInductDecl} {depth : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN 1 e 0) =
      decl.paramVars (depth + 1) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  omega

@[simp] theorem VInductDecl.paramVars_liftN_many
    {decl : VInductDecl} {depth n : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN n e 0) =
      decl.paramVars (depth + n) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  congr 2
  omega

theorem ValidAppStatsWF.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsWF
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  have W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 := by
    change VLCtx.FVLift Hc.mlctx.vlctx
      ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) 0 1 0
    exact .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    H.params fun h =>
      h.weakFV Hc'.checking.tr.wf W Hc'.mlctx_wf.tr.wf
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  change List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    stats.params.toList (decl.paramVars (depth + 1))
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

/-- Extend application statistics in an independently tracked semantic scope.
Unlike `withLocalDecl`, this theorem does not require the executable context
to be that scope; the already verified target-context extension is sufficient
for weakening the cached parameter translations. -/
theorem ValidAppStatsWF.withFVar
    (H : ValidAppStatsWF env Us scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    ValidAppStatsWF env Us
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS env Us
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.ordered W hscope'
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

theorem IndConstArray.empty (levels : List Level) :
    IndConstArray levels #[] [] where
  exact := rfl
  names := by simp [IndConstNames, Array.any]

theorem IndConstArray.push
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names) (newName : Name) :
    IndConstArray levels (indConsts.push (.const newName levels))
      (names ++ [newName]) where
  exact := by rw [H.exact]; simp
  names := by
    intro name
    rw [Array.any_push, H.names name]
    change (names.contains name || (newName == name)) =
      (names ++ [newName]).contains name
    rw [List.contains_append]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.contains_cons,
      List.contains_nil, Bool.or_false]
    exact eq_comm

theorem IndConstArray.ofExact
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (h : indConsts = (names.map fun name => .const name levels).toArray) :
    IndConstArray levels indConsts names where
  exact := h
  names := by
    intro name
    apply Bool.eq_iff_iff.mpr
    simp [h]
    constructor
    · rintro ⟨source, hsource, hname⟩
      have : source = name := by
        simpa [Expr.constName!] using hname
      simpa [this] using hsource
    · intro hname
      exact ⟨name, hname, by simp [Expr.constName!]⟩

/-- Promote the exact traversal-facing statistics into the positivity-facing
application invariant. -/
def ValidAppStatsWF.ofMaterializedHeader
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us Δ stats decl depth where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.params
  paramFVars := H.paramFVars

def ValidAppStatsWF.ofMaterializedHeaderNarrow
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us H.parameterScope stats decl 0 where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.narrowParams
  paramFVars := H.paramFVars

theorem IndConstArray.updatedStats
    {stats : AddInductive.InductiveStats} {names : List Name}
    {lctx : LocalContext} {resultLevel : Level} {setResult : Bool}
    {nindices : Nat} {indName : Name}
    (H : IndConstArray stats.levels stats.indConsts names) :
    IndConstArray
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).levels
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).indConsts
      (names ++ [indName]) := by
  simpa using H.push indName

/-- Incremental form of `ValidAppStatsWF`, synchronized with the mutual-header
loop before all family members have been visited. -/
structure ValidAppStatsPrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth done : Nat) : Prop where
  covered : done ≤ decl.types.length
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    ((decl.types.take done).map (·.name))
  indices : stats.nindices.toList =
    (decl.types.take done).map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- Convert the completed first-header telescope invariant into the initial
mutual-family statistics prefix, just before the first family constant and
index count are appended. -/
def ValidAppStatsPrefix.beforeFirst
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      env Us Δ stats decl.nparams depth)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : Us.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[]) :
    ValidAppStatsPrefix env Us Δ stats decl depth 0 where
  covered := Nat.zero_le _
  levels := hlevels
  uvars := huvars
  consts := by
    simpa [hconsts] using IndConstArray.empty stats.levels
  indices := by simp [hindices]
  params := Hcache.complete
  paramFVars := Hcache.paramFVars

theorem ValidAppStatsPrefix.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsPrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsPrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) done := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList (decl.paramVars (depth + 1)) := by
    rw [← VInductDecl.paramVars_liftN]
    exact forall₂_map_right H.params fun h =>
      h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
  exact {
    covered := H.covered
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := hparams
    paramFVars := H.paramFVars }

theorem ValidAppStatsPrefix.push
    (H : ValidAppStatsPrefix env Us Δ stats decl depth done)
    (hindex : done < decl.types.length)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices) :
    ValidAppStatsPrefix env Us Δ
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName)
      decl depth (done + 1) := by
  have htake : decl.types.take (done + 1) =
      decl.types.take done ++ [decl.types[done]] :=
    List.take_succ_eq_append_getElem hindex
  refine {
    covered := by omega
    levels := by simpa using H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := by simpa using H.params
    paramFVars := by simpa using H.paramFVars }
  · rw [htake, List.map_append]
    simpa [hname] using H.consts.updatedStats (lctx := lctx)
      (resultLevel := resultLevel) (setResult := setResult)
      (nindices := nindices) (indName := indName)
  · rw [htake, List.map_append]
    simp [H.indices, hnindices]

theorem ValidAppStatsPrefix.complete
    (H : ValidAppStatsPrefix env Us Δ stats decl depth decl.types.length) :
    ValidAppStatsWF env Us Δ stats decl depth := by
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := H.params
    paramFVars := H.paramFVars }
  · simpa using H.consts
  · simpa using H.indices

/-- The two independent invariants carried across the mutual-header loop.
`headers` follows the context used to check the current family header, while
`applicationStats` remains interpreted in the parameter context captured by
the first header.  Keeping the contexts separate reflects the executable
implementation: later family headers reuse the cached parameter free
variables without retaining their temporary index contexts. -/
structure HeaderTraversalCertificate (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate env Us decl params stats done
  applicationStats : ValidAppStatsPrefix env Us Δ stats decl depth done

structure HeaderTraversalResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats) (depth : Nat) where
  headers : HeaderCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.ofMaterialized
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := H.headers
  applicationStats := ValidAppStatsWF.ofMaterializedHeader H

/-- Executable header-loop state in the actual retained reader context. -/
structure HeaderRuntimeCertificate (Hc : ContextWF c)
    (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate Hc.venv c.lparams decl params stats done
  applicationStats : ValidAppStatsPrefix Hc.venv c.lparams
    Hc.mlctx.vlctx stats decl depth done
  ambient : checkInductiveTypes.loopType.AmbientParamContext Hc params depth

def HeaderRuntimeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    HeaderRuntimeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      decl params stats (depth + 1) done where
  headers := H.headers
  applicationStats := H.applicationStats.withLocalDecl Hc htr hty
  ambient := H.ambient.withIndex htr hty hsource

def HeaderRuntimeCertificate.first
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      indices.length 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats :=
    (ValidAppStatsPrefix.beforeFirst Hcache hlevels huvars hconsts hindices).push
      hindex hname hnindices
  ambient :=
    checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctx

def HeaderRuntimeCertificate.later
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices
  ambient := H.ambient

theorem HeaderRuntimeCertificate.firstResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (params, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName)
        indices.length 1 →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes 1
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes 1 stats k)
      type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.firstResult.refinesRuntimeState
    (dIdx := 0) k Q Hc hempty htype huvars hctxEq hheader hparamsTake
      hindicesTake hlevel
  intro resultSort hofLevel _hshape _hambient
  exact Hrec resultSort hofLevel
    (HeaderRuntimeCertificate.first Hcache hlevels huvars hconsts hindices
      hindex htarget hname hnindices hofLevel
      hctxEq _hshape)

theorem HeaderRuntimeCertificate.laterResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (H : HeaderRuntimeCertificate Hc decl params stats depth dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hname : indName = decl.types[dIdx].name)
    (hnindices : nindices = decl.types[dIdx].numIndices)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName)
        depth (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.laterResult.refines k Q Hc hnonempty
    htype huvars hctxEq hheader hparamsTake hindicesTake hparams hlevel
  intro resultSort hguard hofLevel hshape
  exact Hrec resultSort hguard hofLevel
    (H.later hindex htarget hname hnindices hguard hofLevel hshape)

def HeaderRuntimeCertificate.complete
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth
      decl.types.length) :
    HeaderTraversalResult Hc.venv c.lparams Hc.mlctx.vlctx
      decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Pair the first successfully checked header with the corresponding first
statistics update.  The application-statistics premise is deliberately about
the post-telescope parameter context, which is exactly the context saved in
`stats.lctx` by the executable first-header branch. -/
def HeaderTraversalCertificate.first
    {c : AddInductive.Context}
    (Hstats : ValidAppStatsPrefix env c.lparams Δ stats decl depth 0)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      depth 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats := Hstats.push hindex hname hnindices

/-- Extend both mutual-header invariants after a later header passes the
common-universe guard. -/
def HeaderTraversalCertificate.later
    {c : AddInductive.Context}
    (H : HeaderTraversalCertificate env c.lparams Δ decl params stats
      depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices

/-- At loop completion, expose exactly the two public certificates needed by
the constructor and formation stages. -/
def HeaderTraversalCertificate.complete
    (H : HeaderTraversalCertificate env Us Δ decl params stats depth
      decl.types.length) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Joint output of header checking and the subsequent flattened constructor
traversal.  This is the formation-side payload eventually returned to
`Environment.addInductive`; application statistics remain available for
recursor and iota generation. -/
structure CheckedFormationResult (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (stats : AddInductive.InductiveStats)
    (depth : Nat) where
  formation : FormationCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.withConstructors
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConstVals decl.typeConstants = some envTypes)
    (Hctors : ConstructorPrefixCertificate env decl envTypes
      H.headers.params decl.ownedConstructors.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def HeaderTraversalResult.withConstructorTypes
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConstVals decl.typeConstants = some envTypes)
    (Hctors : ConstructorTypesPrefix envTypes decl H.headers.params
      decl.types.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def LiteralDisjoint (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal,
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

theorem forall₂_append {R : α → β → Prop}
    (H₁ : List.Forall₂ R as₁ bs₁) (H₂ : List.Forall₂ R as₂ bs₂) :
    List.Forall₂ R (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

/-- Split the right-hand list at the boundary forced by an appended
left-hand list in a `Forall₂` derivation. -/
theorem List.Forall₂.split_left
    (H : List.Forall₂ R (as ++ bs) cs) :
    ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧
      List.Forall₂ R as cs₁ ∧ List.Forall₂ R bs cs₂ := by
  induction as generalizing cs with
  | nil => exact ⟨[], cs, by simp, .nil, H⟩
  | cons a as ih =>
      cases H with
      | cons hab htail =>
        rcases ih htail with ⟨cs₁, cs₂, rfl, hleft, hright⟩
        exact ⟨_ :: cs₁, cs₂, by simp, .cons hab hleft, hright⟩

theorem List.Forall₂.drop
    (H : List.Forall₂ R as bs) (n : Nat) :
    List.Forall₂ R (as.drop n) (bs.drop n) := by
  induction H generalizing n with
  | nil => simp
  | cons hab _ ih =>
    cases n with
    | zero => exact .cons hab (ih 0)
    | succ n => exact ih n

/-- Exact inversion of a translated concrete application list.  Unlike the
typechecker-oriented `AppStack`, this retains the final abstract spine, which
is needed to split the field arguments and recursive results of an iota RHS. -/
theorem TrExprS.mkAppList_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn args) out) :
    ∃ fn' args',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) args args' ∧
      out = VExpr.mkApps fn' args' := by
  induction args generalizing fn out with
  | nil =>
      exact ⟨out, [], H, .nil, rfl⟩
  | cons arg args ih =>
      simp only [Expr.mkAppList] at H
      rcases ih H with ⟨app', args', happ, hargs, hout⟩
      cases happ with
      | app _ _ hfn harg =>
        refine ⟨_, _ :: args', hfn, .cons harg hargs, ?_⟩
        simpa [VExpr.mkApps] using hout

/-- Pointwise expression translation can be assembled into an application
spine once the independently derived abstract spine is known to be
well-typed.  Inverting that typing derivation supplies the function and
argument premises required by each `TrExprS.app` constructor. -/
theorem TrExprS.mkAppList
    (henv : VEnv.Ordered env)
    (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (hfn : TrExprS env Us Δ fn fn')
    (hargs : List.Forall₂ (TrExprS env Us Δ) args args')
    (happs : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps fn' args')) :
    TrExprS env Us Δ (Expr.mkAppList fn args)
      (VExpr.mkApps fn' args') := by
  induction hargs generalizing fn fn' with
  | nil => simpa [Expr.mkAppList, VExpr.mkApps] using hfn
  | @cons arg arg' args args' harg hargs ih =>
    have hprefix := VExpr.WF.mkApps_fn henv hctx
      (fn := .app fn' arg') (args := args') happs
    rcases hprefix.app_inv henv hctx with
      ⟨domain, body, hfnType, hargType⟩
    have happ : TrExprS env Us Δ (.app fn arg) (.app fn' arg') :=
      .app hfnType hargType hfn harg
    simpa [Expr.mkAppList, VExpr.mkApps] using
      ih (fn := .app fn arg) (fn' := .app fn' arg') happ happs

/-- Application-spine inversion with an exact split between two concrete
argument groups. -/
theorem TrExprS.mkAppList_append_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn (left ++ right)) out) :
    ∃ fn' left' right',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) left left' ∧
      List.Forall₂ (TrExprS env Us Δ) right right' ∧
      out = VExpr.mkApps fn' (left' ++ right') := by
  rcases TrExprS.mkAppList_inv H with
    ⟨fn', args', hfn, hargs, hout⟩
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.List.Forall₂.split_left
    hargs with
    ⟨left', right', rfl, hleft, hright⟩
  exact ⟨fn', left', right', hfn, hleft, hright, hout⟩

/-- Translation preserves a constant-headed application spine and the
left-to-right correspondence of all its arguments.  This is the syntax bridge
needed by both executable recursive-target checks. -/
theorem TrExprS.constAppSpine
    (H : TrExprS env Us Δ e e')
    (hhead : e.getAppFn = .const name levels) :
    ∃ levels' args',
      e'.getAppFnArgs = (.const name levels', args') ∧
      levels.mapM (VLevel.ofLevel Us) = some levels' ∧
      List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  induction e generalizing e' with
  | const _ _ =>
    cases H with
    | const _ hlevels _ =>
      cases hhead
      exact ⟨_, [], rfl, hlevels, .nil⟩
  | app fn arg ihFn _ =>
    cases H
    rename_i f' _ _ arg' _ _ hfn harg
    rcases ihFn hfn hhead with ⟨levels', args', hspine, hlevels, hargs⟩
    have hargs' := forall₂_append hargs (.cons harg .nil)
    refine ⟨levels', args' ++ [arg'], ?_, hlevels, ?_⟩
    · simp [hspine]
    · simpa only [Expr.getAppArgsList_app] using hargs'
  | bvar _ | fvar _ | sort _ | lit _ => cases hhead
  | mvar _ => cases H
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ _ => cases hhead

theorem TrExprS.eqv_fvar_target
    (H₁ : TrExprS env Us Δ (.fvar fv) e₁')
    (H₂ : TrExprS env Us Δ e₂ e₂')
    (heq : ((.fvar fv : Expr) == e₂) = true) : e₁' = e₂' := by
  cases e₂ <;> simp [(· == ·), Expr.eqv'] at heq
  have hfv : fv = _ := beq_iff_eq.mp heq
  subst_vars
  cases H₁ with
  | fvar h₁ =>
    cases H₂ with
    | fvar h₂ =>
      rw [h₁] at h₂
      cases h₂
      rfl

theorem isValidIndAppIdx.head
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    (type.getAppFn == stats.indConsts[i]!) = true := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.constHead
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels)) :
    type.getAppFn = .const name levels := by
  have hhead := isValidIndAppIdx.head hvalid
  have hget : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  rw [hget] at hhead
  exact Expr.eqv_const.mp hhead

theorem isValidIndAppIdx.arity
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    type.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.param
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hj : j < stats.params.size) :
    (stats.params[j] == type.getAppArgs[j]'(by
      have := isValidIndAppIdx.arity hvalid
      omega)) = true := by
  have hp :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    cases hparams :
        (stats.params == type.getAppArgs.extract 0 stats.params.size) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  rw [Array.beq_eq_decide] at hp
  split at hp
  · rename_i hsize
    simp only [decide_eq_true_eq] at hp
    have helem := hp j hj
    simpa only [Array.getElem_extract, Nat.zero_add] using helem
  · simp_all

theorem isValidIndAppIdx.indexNoOccurrence
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hlower : stats.params.size ≤ j) (hupper : j < type.getAppArgs.size) :
    AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
  have hall :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    have harity := isValidIndAppIdx.arity hvalid
    rw [harity]
    cases hclean :
        (type.getAppArgs.extract stats.params.size
          (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  have hk : j - stats.params.size <
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).size := by
    simp only [Array.size_extract]
    omega
  have hclean := Array.all_eq_true.mp hall (j - stats.params.size) hk
  simp only [Array.getElem_extract] at hclean
  have hj : stats.params.size + (j - stats.params.size) = j := by omega
  simp only [hj] at hclean
  cases hocc : AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] <;>
    simp_all

/-- The observable components of a valid inductive application are also
sufficient for the executable classifier.  This converse keeps later
alpha-renaming arguments independent of the implementation's nested
`unless` encoding. -/
theorem isValidIndAppIdx.intro
    (hhead : (type.getAppFn == stats.indConsts[i]!) = true)
    (harity : type.getAppArgs.size =
      stats.params.size + stats.nindices[i]!)
    (hparam : ∀ j (hj : j < stats.params.size),
      stats.params[j] = type.getAppArgs[j]'(by omega))
    (hindex : ∀ j (hlower : stats.params.size ≤ j)
      (hupper : j < type.getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false) :
    AddInductive.isValidIndAppIdx stats type i = true := by
  have hparamsEq :
      stats.params = type.getAppArgs.extract 0 stats.params.size := by
    apply Array.ext
    · simp [harity]
    · intro j hjLeft hjRight
      simpa only [Array.getElem_extract, Nat.zero_add] using hparam j hjLeft
  have hparamsBeq :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    calc
      (stats.params == type.getAppArgs.extract 0 stats.params.size) =
          (stats.params == stats.params) :=
        congrArg (fun xs => stats.params == xs) hparamsEq.symm
      _ = true := beq_self_eq_true stats.params
  have hindices :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    apply Array.all_eq_true.mpr
    intro j hj
    simp only [Array.size_extract] at hj
    simp only [Array.getElem_extract]
    have hclean := hindex (stats.params.size + j) (by omega) (by omega)
    simp [hclean]
  have hindices' :
      (type.getAppArgs.extract stats.params.size
        (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    rw [← harity]
    exact hindices
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq, hhead, harity,
    beq_self_eq_true, Bool.true_and, hparamsBeq, hindices', Bool.not_false,
    ↓reduceIte]
  rfl

theorem isValidIndAppFrom?_some
    (h : AddInductive.isValidIndAppFrom? stats type start fuel = some i) :
    start ≤ i ∧ i < start + fuel ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  induction fuel generalizing start with
  | zero => simp [AddInductive.isValidIndAppFrom?] at h
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?] at h
    by_cases hvalid : AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hvalid] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hvalid⟩
    · have hfalse : AddInductive.isValidIndAppIdx stats type start = false := by
        cases hv : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hvalid hv)
      simp [hfalse] at h
      rcases ih h with ⟨hlower, hupper, hvalid⟩
      exact ⟨by omega, by omega, hvalid⟩

/-- If any member in the scanned interval validates, the first-match scan
returns some member (possibly an earlier equivalent entry). -/
theorem isValidIndAppFrom?_exists_of_valid
    (hvalid : AddInductive.isValidIndAppIdx stats type target = true)
    (hlower : start ≤ target) (hupper : target < start + fuel) :
    ∃ owner,
      AddInductive.isValidIndAppFrom? stats type start fuel = some owner := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?]
    by_cases hstart :
        AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hstart]
      exact ⟨start, rfl⟩
    · have hstartFalse :
          AddInductive.isValidIndAppIdx stats type start = false := by
        cases h : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hstart h)
      rw [if_neg hstart]
      have hne : start ≠ target := by
        intro heq
        subst target
        exact Bool.noConfusion (hstartFalse.symm.trans hvalid)
      exact ih (start := start + 1) (by omega) (by omega)

theorem isValidIndApp?_exists_of_valid
    (hvalid : AddInductive.isValidIndAppIdx stats type target = true)
    (hconst : stats.indConsts[target]? = some value) :
    ∃ owner, AddInductive.isValidIndApp? stats type = some owner := by
  have htarget : target < stats.indConsts.size :=
    (Array.getElem?_eq_some_iff.mp hconst).1
  simpa [AddInductive.isValidIndApp?] using
    (isValidIndAppFrom?_exists_of_valid hvalid (start := 0)
      (fuel := stats.indConsts.size) (by omega) (by omega))

theorem isValidIndApp?_some
    (h : AddInductive.isValidIndApp? stats type = some i) :
    i < stats.indConsts.size ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  exact ⟨by simpa using (isValidIndAppFrom?_some h).2.1,
    (isValidIndAppFrom?_some h).2.2⟩

/-- Once the preceding validation has identified a family member,
`getIIndices` returns that same member. This isolates the partial `get!` in
the production helper. -/
theorem getIIndices.fst_eq_of_valid
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 = i := by
  simp only [AddInductive.getIIndices, h, Option.get!_eq_getD,
    Option.getD_some]

/-- The suffix returned by `getIIndices` has the declared index arity of the
selected mutual-family member. -/
theorem getIIndices.index_arity
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size = stats.nindices[i]! := by
  rw [AddInductive.getIIndices]
  change (type.getAppArgs.toSubarray stats.params.size).toArray.size = _
  rw [Subarray.size_toArray, Subarray.size_eq]
  simp only [Array.stop_toSubarray, Array.start_toSubarray]
  have hvalid := (isValidIndApp?_some h).2
  have harity := isValidIndAppIdx.arity hvalid
  omega

theorem getIIndices.family_lt
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 < decl.types.length := by
  rw [getIIndices.fst_eq_of_valid h]
  have hi := (isValidIndApp?_some h).1
  rw [H.consts.exact] at hi
  simpa using hi

/-- Together with the stats/declaration correspondence, the executable suffix
has the abstractly declared index arity. -/
theorem getIIndices.declared_index_arity
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size =
      (decl.types[i]'(by simpa [getIIndices.fst_eq_of_valid h] using
        getIIndices.family_lt H h)).numIndices := by
  rw [getIIndices.index_arity h]
  have hi : i < decl.types.length := by
    simpa [getIIndices.fst_eq_of_valid h] using getIIndices.family_lt H h
  have hlen : stats.nindices.size = decl.types.length := by
    have := congrArg List.length H.indices
    simpa using this
  have hget := congrArg (fun xs => xs[i]?) H.indices
  simpa [Array.getElem!_eq_getD, hi, hlen] using hget

namespace mkRecRules.loopU

/-- The iota RHS generator produces exactly one recursive-result term for
each field selected by `loopCtorArgs`. The contents of each term are verified
separately; this theorem fixes the cardinality and continuation boundary. -/
theorem resultCount
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (hi : i ≤ u.size) (hv : v.size = i)
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hval :
        ((AddInductive.mkRecInfos.loopUArgs u[i] (fun uiTy xs =>
          do
          let some itIdx := AddInductive.isValidIndApp? stats uiTy
            | throw (.other
              "recursive constructor field lost its inductive result type")
          let itIndices := uiTy.getAppArgs[stats.params.size:]
          let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
          let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
            motives) minors) itIndices
          return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)) c).WF
          (fun _ => True)) := by
      intro _ _
      trivial
    refine hval.bind fun val _ => ?_
    exact resultCount (indTypes := indTypes) (stats := stats)
      (motives := motives) (minors := minors) (lvls := lvls)
      (u := u) (i := i + 1) (v := v.push val) (k := k) (c := c)
      (by omega) (by simp [hv]) Hk
  · rw [dif_neg hnext]
    apply Hk
    omega
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.resultCountFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.resultCount (Nat.zero_le _) rfl Hk

namespace mkRecInfos.loopUArgs

/-- `loopUArgs` can only return through its continuation. This structural
interface lets rule generation retain the exposed recursive-field indices
without depending on typechecker correctness a second time. -/
private theorem loop_continueWith
    {α : Type} {Q : α → Prop}
    (k : Expr → Array Expr → AddInductive.M α)
    (Hk : ∀ uiTy xs c, (k uiTy xs c).WF Q) :
    ∀ fuel uiTy xs c,
      (AddInductive.mkRecInfos.loopUArgs.loop k uiTy xs fuel c).WF Q
  | 0, _, _, _ => Except.WF.throw
  | fuel + 1, uiTy, xs, c => by
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotations bi }
      unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
        AddInductive.instMonadLocalNameGeneratorM
        AddInductive.instMonadWithReaderOfLocalContextM
      change ((monadLift (TypeChecker.whnf
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
          AddInductive.M Expr) c' >>= fun normalized =>
        AddInductive.mkRecInfos.loopUArgs.loop k normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) fuel c').WF Q
      have hwhnf :
          ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c').WF (fun _ => True) := by
        intro _ _
        trivial
      exact hwhnf.bind fun normalized _ =>
        loop_continueWith k Hk fuel normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) c'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change (k _ xs c).WF Q
      exact Hk _ _ _

theorem continueWith
    {α : Type} {Q : α → Prop}
    (ui : Expr) (k : Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ uiTy xs c, (k uiTy xs c).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs ui k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopUArgs
  have hinfer :
      ((monadLift (TypeChecker.inferType ui) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hinfer.bind fun inferred _ => ?_
  have hwhnf :
      ((monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hwhnf.bind fun normalized _ => ?_
  change (AddInductive.mkRecInfos.loopUArgs.loop k normalized #[]
    c.fuel.inductiveFuel c).WF Q
  exact loop_continueWith k Hk _ _ _ _

end mkRecInfos.loopUArgs

/-- Exact concrete syntax of one recursive call generated for an argument
selected by `loopCtorArgs`. -/
def GeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (field value : Expr) : Prop :=
  ∃ (exposedType : Expr) (localArgs : Array Expr) (lctx : LocalContext),
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN
      (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices
    value = (lctx.mkLambda localArgs <|
      recursor.app (mkAppN field localArgs))

/-- Prefix invariant for `mkRecRules.loopU`: generated values correspond
pointwise to the selected recursive fields. -/
structure GeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    GeneratedRecursiveCall indTypes stats motives minors lvls u[i]
      v[i]!

def GeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) (u : Array Expr) :
    GeneratedRecursiveCalls indTypes stats motives minors lvls u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

def GeneratedRecursiveCalls.push
    (H : GeneratedRecursiveCalls indTypes stats motives minors lvls u v done)
    (hdone : done < u.size)
    (Hentry : GeneratedRecursiveCall indTypes stats motives minors lvls
      u[done] value) :
    GeneratedRecursiveCalls indTypes stats motives minors lvls u
      (v.push value) (done + 1) where
  covered := by omega
  size := by simp [H.size]
  entries i hi hiu := by
    by_cases h : i = done
    · subst i
      have hpush : done < (v.push value).size := by simp [H.size]
      have hbang : (v.push value)[done]! = value := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush]
        simpa [H.size] using (@Array.getElem_push_eq Expr v value)
      rw [hbang]
      exact Hentry
    · have hold : i < done := by omega
      have hv : i < v.size := by simpa [H.size] using hold
      have hpush : i < (v.push value).size := by
        simpa using Nat.lt_succ_of_lt hv
      have hbang : (v.push value)[i]! = v[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hv]
        exact Array.getElem_push_lt hv
      rw [hbang]
      exact H.entries i hold hiu

namespace mkRecRules.loopU

theorem generatedCalls
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hprefix : GeneratedRecursiveCalls indTypes stats motives minors lvls
      u v i)
    (Hk : ∀ v c,
      GeneratedRecursiveCalls indTypes stats motives minors lvls
        u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
        let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
          motives) minors) itIndices
        return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => GeneratedRecursiveCall indTypes stats motives minors
            lvls u[i] value) := by
      apply mkRecInfos.loopUArgs.continueWith
      intro uiTy xs c'
      unfold buildCall
      cases hvalid : AddInductive.isValidIndApp? stats uiTy with
      | none =>
        simp only [hvalid, bind, Except.bind]
        exact Except.WF.throw
      | some target =>
        simp only [hvalid, bind, Except.bind]
        refine Except.WF.pure ⟨uiTy, xs, c'.lctx, ?_⟩
        simp [AddInductive.getIIndices, hvalid]
    · exact hval.bind fun value Hvalue =>
        generatedCalls
          (Hprefix.push hnext Hvalue) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.generatedCallsFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hk : ∀ v c,
      GeneratedRecursiveCalls indTypes stats motives minors lvls
        u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.generatedCalls
    (GeneratedRecursiveCalls.empty indTypes stats motives minors lvls u) Hk

/-- Exact source-level record emitted for one constructor by `mkRecRules`.
This certificate deliberately precedes translation to `VDefEq`: it fixes the
constructor, field count, minor ordinal, recursive-call array, and complete
right-hand side built by the executable traversal. -/
def GeneratedRecursorRule
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx : Nat) (rule : RecursorRule) : Prop :=
  ∃ (bu u v : Array Expr) (lctx : LocalContext),
    u.toList.Sublist bu.toList ∧
    GeneratedRecursiveCalls indTypes stats motives minors lvls
      u v u.size ∧
    rule.ctor = ctor.name ∧
    rule.nfields = bu.size ∧
    rule.rhs =
      (lctx.mkLambda stats.params <| lctx.mkLambda motives <|
       lctx.mkLambda minors <| lctx.mkLambda bu <|
       mkAppN (mkAppN minors[minorIdx]! bu) v)

/-- Ordered source-level coverage of the constructor suffix processed by the
named `mkRecRules.loopCtors` recursion. -/
inductive GeneratedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : GeneratedRecursorRules indTypes stats motives minors lvls [] start []
  | cons :
      GeneratedRecursorRule indTypes stats motives minors lvls ctor start rule →
      GeneratedRecursorRules indTypes stats motives minors lvls
        ctors (start + 1) rules →
      GeneratedRecursorRules indTypes stats motives minors lvls
        (ctor :: ctors) start (rule :: rules)

theorem GeneratedRecursorRules.length
    (H : GeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Indexed form used by the flattened iota certificate: rule `i` belongs to
constructor `i` and its minor is the global starting ordinal plus `i`. -/
theorem GeneratedRecursorRules.entry
    (H : GeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      GeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) rules[i] := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => simpa using Hrule
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        simpa only [List.getElem_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 i] using h

/-- A validated concrete parameter argument translates to the corresponding
abstract de Bruijn parameter.  The fvar-shape invariant is what upgrades
structural `Expr` equality to exact syntax translation here. -/
theorem ValidAppStatsWF.translatedParam
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlen := forall₂_length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlen, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := forall₂_get?_eq_some hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/- Absence of a newly declared constant is preserved by syntax translation.
Literal expansion and projection translation are explicit side conditions:
literals introduce old primitive constants, while `TrProj` is still an
independent typing boundary in the existing model. -/

/-- Source-syntax absence of a set of constants.  This is deliberately an
inductive judgment rather than a Boolean fold: the literal case records the
expanded constructor syntax that `TrExprS.lit` actually translates. -/
inductive _root_.Lean.Expr.AvoidsConsts (names : List Name) : Expr → Prop
  | bvar (i) : AvoidsConsts names (.bvar i)
  | fvar (fv) : AvoidsConsts names (.fvar fv)
  | mvar (mv) : AvoidsConsts names (.mvar mv)
  | sort (u) : AvoidsConsts names (.sort u)
  | const (name levels) (fresh : name ∉ names) :
      AvoidsConsts names (.const name levels)
  | app (fn arg) : AvoidsConsts names fn → AvoidsConsts names arg →
      AvoidsConsts names (.app fn arg)
  | lam (name dom body bi) :
      AvoidsConsts names dom → AvoidsConsts names body →
      AvoidsConsts names (.lam name dom body bi)
  | forallE (name dom body bi) :
      AvoidsConsts names dom → AvoidsConsts names body →
      AvoidsConsts names (.forallE name dom body bi)
  | letE (name type value body nondep) :
      AvoidsConsts names type → AvoidsConsts names value →
      AvoidsConsts names body →
      AvoidsConsts names (.letE name type value body nondep)
  | lit (value) : AvoidsConsts names value.toConstructor →
      AvoidsConsts names (.lit value)
  | mdata (data body) : AvoidsConsts names body →
      AvoidsConsts names (.mdata data body)
  | proj (structName idx body) : AvoidsConsts names body →
      AvoidsConsts names (.proj structName idx body)

/-- Closing a free variable cannot introduce a constant name. -/
theorem _root_.Lean.Expr.AvoidsConsts.abstract1
    (H : Lean.Expr.AvoidsConsts names e) (fv : FVarId) (k : Nat := 0) :
    Lean.Expr.AvoidsConsts names (Lean.Expr.abstract1 fv e k) := by
  induction H generalizing k with
  | bvar i => exact Lean.Expr.AvoidsConsts.bvar _
  | fvar other =>
      by_cases h : fv == other
      · simpa [Expr.abstract1, h] using
          (Lean.Expr.AvoidsConsts.bvar k :
            Lean.Expr.AvoidsConsts names (.bvar k))
      · simpa [Expr.abstract1, h] using
          (Lean.Expr.AvoidsConsts.fvar other :
            Lean.Expr.AvoidsConsts names (.fvar other))
  | mvar mv => simpa [Expr.abstract1] using
      (Lean.Expr.AvoidsConsts.mvar mv :
        Lean.Expr.AvoidsConsts names (.mvar mv))
  | sort u => simpa [Expr.abstract1] using
      (Lean.Expr.AvoidsConsts.sort u :
        Lean.Expr.AvoidsConsts names (.sort u))
  | const name levels fresh =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.const name levels fresh
  | app fn arg _ _ ihFn ihArg =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.app _ _
        (ihFn k) (ihArg k)
  | lam name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.lam name _ _ bi
        (ihDom k) (ihBody (k + 1))
  | forallE name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.forallE name _ _ bi
        (ihDom k) (ihBody (k + 1))
  | letE name type value body nondep _ _ _ ihType ihValue ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.letE name _ _ _
        nondep (ihType k) (ihValue k) (ihBody (k + 1))
  | lit value expanded ih =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.lit value expanded
  | mdata data body _ ih =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.mdata data _ (ih k)
  | proj structName idx body _ ih =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.proj structName idx _ (ih k)

/-- Simultaneous abstraction likewise preserves source-level absence. -/
theorem _root_.Lean.Expr.AvoidsConsts.abstractList
    (H : Lean.Expr.AvoidsConsts names e) (fvs : List FVarId)
    (k : Nat := 0) :
    Lean.Expr.AvoidsConsts names (Lean.Expr.abstractList e fvs k) := by
  induction fvs generalizing e with
  | nil => simpa using H
  | cons fv fvs ih =>
      simp only [Expr.abstractList]
      exact ih (H.abstract1 fv k)

/-- Every argument in an application spine is a constant-avoiding
subexpression whenever the complete source expression is. -/
theorem _root_.Lean.Expr.AvoidsConsts.getAppArgsList
    (H : Lean.Expr.AvoidsConsts names e)
    (harg : arg ∈ e.getAppArgsList) :
    Lean.Expr.AvoidsConsts names arg := by
  induction H with
  | app fn value hfn hvalue ihFn ihValue =>
    rw [Expr.getAppArgsList_app] at harg
    rcases List.mem_append.mp harg with harg | harg
    · exact ihFn harg
    · simp only [List.mem_singleton] at harg
      subst arg
      exact hvalue
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit |
      mdata | proj => simp [Expr.getAppArgsList] at harg

theorem _root_.Lean.Expr.AvoidsConsts.mkAppN
    (Hfn : Lean.Expr.AvoidsConsts names fn)
    (Hargs : ∀ arg ∈ args, Lean.Expr.AvoidsConsts names arg) :
    Lean.Expr.AvoidsConsts names (Lean.mkAppN fn args) := by
  rw [Expr.mkAppN_eq_mkAppList]
  have go : ∀ (list : List Expr) (fn : Expr),
      Lean.Expr.AvoidsConsts names fn →
      (∀ arg ∈ list, Lean.Expr.AvoidsConsts names arg) →
      Lean.Expr.AvoidsConsts names (Expr.mkAppList fn list) := by
    intro list
    induction list with
    | nil => intro fn hfn _; exact hfn
    | cons arg rest ih =>
      intro fn hfn hlist
      simp only [Expr.mkAppList]
      apply ih (.app fn arg)
      · exact Lean.Expr.AvoidsConsts.app _ _ hfn
          (hlist arg (by simp))
      · intro inner hinner
        exact hlist inner (by simp [hinner])
  apply go args.toList fn Hfn
  intro arg harg
  exact Hargs arg (Array.mem_toList_iff.mp harg)

/-- A translation performed before a fresh constant is installed certifies
that the source syntax itself does not mention that constant.  Unlike
`TrExprS.noFreshConsts`, this fact remains usable when the same source
fragment is translated later in an extended environment. -/
theorem TrExprS.sourceAvoidsFresh
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (H : TrExprS env Us Δ e e') : e.AvoidsConsts names := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | sort => exact .sort _
  | @const name levels _ _ _ hlookup _ _ =>
    apply Lean.Expr.AvoidsConsts.const
    intro hmem
    rw [hfresh name hmem] at hlookup
    cases hlookup
  | app _ _ _ _ ihFn ihArg => exact .app _ _ ihFn ihArg
  | lam _ _ _ ihDom ihBody => exact .lam _ _ _ _ ihDom ihBody
  | forallE _ _ _ _ ihDom ihBody =>
    exact .forallE _ _ _ _ ihDom ihBody
  | letE _ _ _ _ ihType ihValue ihBody =>
    exact .letE _ _ _ _ _ ihType ihValue ihBody
  | lit _ _ ih => exact .lit _ ih
  | mdata _ ih => exact .mdata _ _ ih
  | proj _ _ ih => exact .proj _ _ _ ih

/-- Every ordinary local declaration type in a recursor context predating a
fresh constant set avoids those names in its concrete syntax. -/
theorem RecursorContextWF.cdeclTypeAvoids
    (R : RecursorContextWF c recLparams)
    (hfresh : ∀ name ∈ names, R.venv.constants name = none)
    (hfind : c.lctx.find? fv =
      some (.cdecl index fv userName type bi kind)) :
    type.AvoidsConsts names := by
  have hfind' : R.mlctx.lctx.find? fv =
      some (.cdecl index fv userName type bi kind) := by
    rw [R.lctx_eq]
    exact hfind
  rw [R.mlctx_wf.tr.1.find?_eq_find?_toList] at hfind'
  have hmem : (.cdecl index fv userName type bi kind) ∈
      R.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hfind'
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmem with
    ⟨valueTarget, typeTarget, hlookup, hvalueBelow, htypeBelow,
      hvalueTr, htypeTr⟩
  exact checkPositivityStep.TrExprS.sourceAvoidsFresh hfresh htypeTr

/-- Source-level absence, rather than absence from the current environment,
is sufficient to show that a translation contains no selected constants.
This is the post-installation half of the split freshness argument used by
generated iota equations. -/
theorem TrExprS.noConstsOfSourceAvoids
    (hsource : e.AvoidsConsts names)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e') :
    e'.containsAnyConst names = false := by
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | @const name levels _ _ _ _ _ _ =>
    cases hsource with
    | const _ _ hnot =>
      simp only [VExpr.containsAnyConst]
      exact Bool.eq_false_iff.mpr fun hcontains =>
        hnot (by simpa using hcontains)
  | app _ _ _ _ ihFn ihArg =>
    cases hsource with
    | app _ _ hfn harg =>
      exact Bool.or_eq_false_iff.mpr
        ⟨ihFn hfn hctx, ihArg harg hctx⟩
  | lam _ _ _ ihDom ihBody =>
    cases hsource with
    | lam _ _ _ _ hdom hbody =>
      exact Bool.or_eq_false_iff.mpr ⟨ihDom hdom hctx,
        ihBody hbody (VLCtx.NoIndConsts.cons hctx (by rfl))⟩
  | forallE _ _ _ _ ihDom ihBody =>
    cases hsource with
    | forallE _ _ _ _ hdom hbody =>
      exact Bool.or_eq_false_iff.mpr ⟨ihDom hdom hctx,
        ihBody hbody (VLCtx.NoIndConsts.cons hctx (by rfl))⟩
  | letE _ _ _ _ ihType ihValue ihBody =>
    cases hsource with
    | letE _ _ _ _ _ htype hvalue hbody =>
      exact ihBody hbody <| hctx.cons (d := .vlet _ _) (ofv := none)
        (ihValue hvalue hctx)
  | lit _ _ ih =>
    cases hsource with
    | lit _ hexpanded => exact ih hexpanded hctx
  | mdata _ ih =>
    cases hsource with
    | mdata _ _ hbody => exact ih hbody hctx
  | proj _ Hproj ih =>
    cases hsource with
    | proj _ _ _ hbody => exact hproj Hproj (ih hbody hctx)

theorem TrExprS.noFreshConsts
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e') :
    e'.containsAnyConst names = false := by
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | @const name _ _ _ _ hconst _ _ =>
    change names.contains name = false
    apply Bool.eq_false_iff.mpr
    intro hcontains
    have hmem : name ∈ names := by simpa using hcontains
    rw [hfresh name hmem] at hconst
    cases hconst
  | app _ _ _ _ ihFn ihArg =>
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx, ihArg hctx⟩
  | lam _ _ _ ihTy ihBody =>
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx, ihBody ?_⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx, ihBody ?_⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none)
      (ihValue hctx))
  | lit _ _ ih => exact ih hctx
  | mdata _ ih => exact ih hctx
  | proj _ Hproj ih => exact hproj Hproj (ih hctx)

/-- Pointwise form of `TrExprS.noFreshConsts` for a translated application
spine. -/
theorem List.Forall₂.targets_noFreshConsts
    (H : List.Forall₂ (TrExprS env Us Δ) source target)
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false) :
    ∀ arg ∈ target, arg.containsAnyConst names = false := by
  induction H with
  | nil => simp
  | cons Hhead _ ih =>
    intro arg harg
    simp only [List.mem_cons] at harg
    rcases harg with rfl | harg
    · exact checkPositivityStep.TrExprS.noFreshConsts
        hfresh hctx hproj Hhead
    · exact ih arg harg

/-- Pointwise post-installation counterpart driven by source-syntax
absence rather than environment freshness. -/
theorem List.Forall₂.targets_noConstsOfSourceAvoids
    (H : List.Forall₂ (TrExprS env Us Delta) source target)
    (hsource : ∀ arg ∈ source, arg.AvoidsConsts names)
    (hctx : VLCtx.NoIndConsts names Delta)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false) :
    ∀ arg ∈ target, arg.containsAnyConst names = false := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro arg harg
    simp only [List.mem_cons] at harg
    rcases harg with rfl | harg
    · exact checkPositivityStep.TrExprS.noConstsOfSourceAvoids
        (hsource _ (by simp)) hctx hproj Hhead
    · exact ih (fun sourceArg hmem => hsource sourceArg (by simp [hmem]))
        arg harg

theorem TrExprS.noIndOcc
    (halign : IndConstNames indConsts names)
    (hlit : LiteralDisjoint indConsts)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e')
    (hno : AddInductive.hasIndOcc indConsts e = false) :
    e'.containsAnyConst names = false := by
  rw [hasIndOcc_eq_findAny] at hno
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | const _ _ _ =>
    simp only [Expr.findAny] at hno
    change names.contains _ = false
    rw [← halign]
    exact hno
  | app _ _ _ _ ihFn ihArg =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hfn, harg⟩
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx hfn, ihArg hctx harg⟩
  | lam _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨htyValue, hbody⟩
    rcases Bool.or_eq_false_iff.mp htyValue with ⟨hty, hvalue⟩
    have hvalue' := ihValue hctx hvalue
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none) hvalue') hbody
  | lit _ _ ih =>
    apply ih hctx
    rw [← hasIndOcc_eq_findAny]
    exact hlit _
  | mdata _ ih =>
    simpa only [Expr.findAny, Bool.false_or] using ih hctx hno
  | proj _ Hproj ih =>
    simp only [Expr.findAny, Bool.false_or] at hno
    exact hproj Hproj (ih hctx hno)

theorem ValidAppStatsWF.translatedIndexNoOccurrence
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].containsAnyConst (decl.types.map (·.name)) = false := by
  have hlen := forall₂_length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlen]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := forall₂_get?_eq_some hargs hsource htarget
  have hno := isValidIndAppIdx.indexNoOccurrence hvalid hlower hjArgs
  exact TrExprS.noIndOcc H.consts.names hlit hctx hproj harg hno

theorem isValidIndAppIdx.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (htarget : target = none ∨ target = some decl.types[typeIdx].name)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt target depth type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlen := List.mapM_some_length hlevels
    have hstats := H.levels
    omega
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := forall₂_length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalid hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, htarget,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalid hargs hlit hctx hproj
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

/-- The exact indexed target recognized by the executable checker is a type,
not merely a well-typed term.  Header shape supplies the forall-to-sort
telescope; the syntax translation supplies all argument and universe typing. -/
theorem isValidIndAppIdx.isType
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (huvars : decl.types[typeIdx].uvars = decl.uvars)
    (hlookup : env.constants decl.types[typeIdx].name =
      some decl.types[typeIdx].toVConstant)
    (htargetWF : decl.types[typeIdx].toVConstant.WF env)
    (hshape : decl.TypeShape env params decl.types[typeIdx])
    (henv : env.WF) (hΔ : Δ.WF env Us.length) :
    env.IsType Us.length Δ.toCtx type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels, args, hspine, hlevels, _hargs⟩
  have hlevelsWF : ∀ level ∈ levels, level.WF Us.length :=
    VLevel.WF.of_mapM_ofLevel hlevels
  have hlevelsLength : levels.length = decl.types[typeIdx].uvars := by
    have htranslated := List.mapM_some_length hlevels
    have hstats := H.levels
    rw [huvars]
    omega
  have hargsLength : args.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := forall₂_length_eq _hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  rcases Lean4Lean.VerifyInductive.typeShape_forallAritySort
      huvars henv htargetWF hshape with
    ⟨functionType, typeLevel, hfunctionType, hfunctionShape⟩
  have hfunctionTypeInst := hfunctionType.instL hlevelsWF
  have hconstType : env.HasType Us.length Δ.toCtx
      (.const decl.types[typeIdx].name levels)
      (functionType.instL levels) := by
    have hconstBase := VEnv.HasType.const (Γ := Δ.toCtx) hlookup
      hlevelsWF hlevelsLength
    have hfunctionTypeInst' : env.IsDefEq Us.length []
        (decl.types[typeIdx].type.instL levels)
        (functionType.instL levels) (VExpr.sort (typeLevel.inst levels)) := by
      simpa [VExpr.instL] using hfunctionTypeInst
    exact (hfunctionTypeInst'.weak0 henv.ordered).defeq hconstBase
  have hrebuild := VExpr.mkApps_getAppFnArgs type'
  rw [hspine] at hrebuild
  have happWF : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps (.const decl.types[typeIdx].name levels) args) := by
    rw [hrebuild]
    exact htr.wf henv.ordered hΔ
  have hshapeInst := hfunctionShape.instL levels
  have hshapeInst' : VExpr.ForallAritySort args.length
      (functionType.instL levels) := by
    rw [hargsLength]
    exact hshapeInst
  have hresult := VEnv.HasType.mkApps_isType henv hΔ.toCtx
    hconstType hshapeInst' happWF
  rwa [hrebuild] at hresult

theorem isValidIndApp?.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt none depth type' := by
  rcases isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  exact isValidIndAppIdx.validIndAppAt H hi' htr hvalidIdx
    (Or.inl rfl) hlit hctx hproj

theorem noOccurrence.WF
    {type : Expr} {Q : Unit → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok ()).WF Q
  exact Except.WF.pure hQ

/-- The successful fast path of executable positivity establishes the
declarative nonrecursive case.  All non-syntactic correspondence assumptions
are named at the boundary: the accumulated mutual constants, local-variable
translation, literal expansion, and projection translation. -/
theorem noOccurrence.refines
    {decl : VInductDecl} {type' : VExpr} {depth : Nat} {ctx : List VExpr}
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htr : TrExprS env Us Δ type type')
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact noOccurrence.WF
    (Q := fun _ => decl.SyntacticallyPositive env ctx depth type')
    hocc (.nonrecursive <|
      checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit hctx hproj htr hocc)

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

/-- Once the application-spine refinement supplies `ValidIndAppAt`, the final
executable success branch is exactly the declarative recursive positivity
constructor. -/
theorem validApplication.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hrefines : decl.ValidIndAppAt none depth type') :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact validApplication.WF hocc hforall hvalid (.recursive hrefines)

theorem validApplication.sourceRefines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  apply validApplication.refines hocc hforall hvalid
  exact isValidIndApp?.validIndAppAt Hstats htr hvalid hlit hctx hproj

theorem invalidApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = none) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

theorem negativeDomain.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_pos hdomOcc]
  change (Except.error _).WF Q
  exact Except.WF.throw

/-- Positive higher-order branch after WHNF.  Source-domain annotation
transport is shared with header and constructor telescopes. -/
theorem forallE.sourceWF
    (Hc : ContextWF c)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_neg (by simp [hdomOcc])]
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => recur (body.instantiate1 arg))
    Hc Hdom.consumed Hdom.isType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    Hdom.consumed Hdom.isType hbody''
  exact Hrec body'' hbodyEq hopened

/-- The successful higher-order branch refines the declarative `forallE`
positivity rule.  The recursive checker runs in the consumed-annotation local
context, while its certificate is deliberately stated for the original
source-domain/body translation used by the independent specification. -/
theorem forallE.refines
    {decl : VInductDecl} {depth : Nat}
    (Hc : ContextWF c)
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (huvars : c.lparams.length = decl.uvars)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
        (fun _ => decl.Positive Hc.venv
          (consumedDom' :: Hc.mlctx.vlctx.toCtx) (depth + 1) body'')) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx depth
        (.forallE sourceDom' sourceBody')) := by
  have hdomNo := checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit
    hctx hproj Hdom.source hdomOcc
  refine forallE.sourceWF (Q := fun _ => decl.SyntacticallyPositive Hc.venv
      Hc.mlctx.vlctx.toCtx depth (.forallE sourceDom' sourceBody'))
      (recur := recur) (ctor := ctor)
      (idx := idx) Hc hocc hdomOcc Hdom hbody ?_
  intro body'' hbodyEq hopened
  exact (Hrec body'' hbodyEq hopened).mono fun _ hpositive => by
    rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
    rcases hbodyEq with ⟨bodyType, hbodyEq⟩
    exact .forallE hdomNo
      (by simpa [huvars] using hdomEq)
      (by simpa [huvars] using hbodyEq) hpositive

end checkPositivityStep

namespace checkConstructors.loopCtor

/-- The terminal constructor target check now discharges the declarative
`CtorTailWF.result` rule, rather than returning an unconstrained success. -/
theorem result.refines
    {decl : VInductDecl} {depth : Nat} {result type' exprType : VExpr}
    {ctorCtx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hdefeq : env.IsDefEq decl.uvars ctorCtx result type' exprType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF env decl.types[targetIdx]
        ctorCtx depth result) := by
  exact checkConstructors.loopCtor.result.WF
    (Q := fun _ => decl.CtorTailWF env decl.types[targetIdx]
      ctorCtx depth result)
    hforall hvalid (.result
      (checkPositivityStep.isValidIndAppIdx.validIndAppAt
        Hstats hi htr hvalid (Or.inr rfl) hlit hctx hproj)
      hdefeq)

/-- Semantic wrapper for a safe constructor field.  The low-level traversal
supplies source typing and annotation transport; this theorem packages those
facts as the declarative `CtorTailWF.field` rule. -/
theorem safeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF
      (fun _ => decl.Positive Hc.venv ctorCtx depth sourceDom'))
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.Positive Hc.venv ctorCtx depth sourceDom' →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine safeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (Pos := decl.Positive Hc.venv ctorCtx depth sourceDom')
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody Hpos ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    hpositive body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound hpositive body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inr hpositive)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

theorem unsafeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (hunsafe : decl.isUnsafe = true)
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine unsafeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inl hunsafe)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

/-- Starting after the common constructor parameters, the complete executable
constructor-tail traversal builds `CtorTailWF`.  The remaining level-order
premise is isolated explicitly until `Level.geq` is connected to `VLevel.LE`. -/
theorem tailRefines
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hpositivity : ∀ {c : AddInductive.Context} {depth posIdx : Nat}
      {type : Expr} {type' : VExpr} (Hc : ContextWF c),
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
        Hc.mlctx.vlctx stats decl depth →
      checkPositivityStep.VLCtx.NoIndConsts
        (decl.types.map (·.name)) Hc.mlctx.vlctx →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type' →
      (AddInductive.checkPositivity stats type ctor posIdx c).WF
        (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type'))
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  induction fuel generalizing c type type' depth i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htr with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        have hparamNext : stats.params[i + 1]? = none := by
          rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
          omega
        cases isUnsafe with
        | false =>
          have Hpos := hpositivity (posIdx := i) Hc Hstats hctx
            (hdom.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
          exact safeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            Hpos hbound fun _ _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
        | true =>
          exact unsafeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            (hunsafe rfl) hbound fun _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact invalidResult.WF hforall hvalid
      · rcases htr.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf with
          ⟨exprType, htype⟩
        subst target
        exact result.refines Hstats hi htr hforall hvalid hlit hctx hproj
          (by simpa [Hstats.uvars] using htype)

end checkConstructors.loopCtor

namespace checkPositivity.loop

theorem zero.WF :
    (AddInductive.checkPositivity.loop stats ctor idx type 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkPositivity.loop] at h

theorem succ.WF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.WF Hc htype).bind fun normalized hnormalized =>
    Hstep normalized hnormalized

/-- Positivity's WHNF step with the concrete free-variable preservation fact
retained for refinements whose semantic scope is narrower than the executable
local context. -/
theorem succ.scopeWF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.scopeWF Hc htype).bind
    fun normalized hnormalized => Hstep normalized hnormalized.1 hnormalized.2

/-- The complete recursive positivity traversal refines the independent
declarative judgment.  In particular, every recursive call under a higher-
order binder performs and records its own WHNF/definitional-equality step. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    refine succ.WF Hc hsource ?_
    intro normalized hnormalized
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx
              depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using hsourceExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit hctx hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        exact finish <| checkPositivityStep.forallE.refines Hc Hstats.consts
          hlit hctx hproj hocc' hdomOcc' Hdom Hstats.uvars hbody
          fun body'' hbodyEq hopened => by
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
              Hc Hdom.consumed Hdom.isType
            have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
              apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
              rfl
            exact ih Hc' Hstats' hctx'
              (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    ·
      cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit hctx hproj hocc' hforall hvalid

/-- Positivity refinement for constructor checking after mutual headers have
left ambient declarations in the executable context.  The concrete checker
runs in `Hc.mlctx.vlctx`, while every declarative judgment is constructed in
the independent `scope`; runtime WHNF results are restricted before any
positivity rule is emitted. -/
theorem refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htypeFull with ⟨sourceFull, hsourceFull, hsourceTarget⟩
    refine succ.scopeWF Hc hsourceFull ?_
    intro normalized hbelow hnormalized
    have hnormalizedFVars : FVarsIn (· ∈ scope.fvars) normalized :=
      hbelow _ Hruntime.upset htypeNarrow.fvarsIn
    rcases hnormalized with
      ⟨exposedFull, hexposedFull, hexposedTarget⟩
    have hnormalizedClosed : Closed normalized 0 := by
      have hclosed := hexposedFull.closed
      rw [Hc.mlctx.noBV] at hclosed
      exact hclosed
    have hnormalizedFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        normalized fullType :=
      ⟨exposedFull, hexposedFull,
        hexposedTarget.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
          hsourceTarget⟩
    have hinputFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        type fullType :=
      ⟨sourceFull, hsourceFull, hsourceTarget⟩
    rcases Hruntime.restrictTrExpr Hc.checking.tr.wf htypeNarrow
        hinputFull hnormalizedFull hnormalizedClosed hnormalizedFVars with
      ⟨exposed, hexposed, hexposedEq⟩
    rcases hexposedEq.symm with ⟨exprType, htypeExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv scope.toCtx depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv scope.toCtx depth narrowType) :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using htypeExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit
        (Hruntime.noIndConsts (decl.types.map (·.name))) hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hexposedFull with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          refine finish <| checkPositivityStep.forallE.sourceWF
            (Q := fun _ => decl.SyntacticallyPositive Hc.venv
              scope.toCtx depth (.forallE _ _))
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull ?_
          intro bodyFull' _hbodyFullEq hopenedFull
          let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have Hrec := ih Hc' Hruntime' Hstats' hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ hpositive => by
            rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
            rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
            change Hc.venv.IsDefEq c.lparams.length scope.toCtx
              narrowDom narrowDom (.sort domLevel) at hdomTyped
            change Hc.venv.IsDefEq c.lparams.length
              (narrowDom :: scope.toCtx) narrowBody narrowBody
              (.sort bodyLevel) at hbodyTyped
            exact .forallE
              (checkPositivityStep.TrExprS.noIndOcc Hstats.consts.names
                hlit (Hruntime.noIndConsts (decl.types.map (·.name)))
                hproj hdomNarrow hdomOcc')
              (by simpa [Hstats.uvars] using hdomTyped)
              (by simpa [Hstats.uvars] using hbodyTyped)
              hpositive
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit
            (Hruntime.noIndConsts (decl.types.map (·.name)))
            hproj hocc' hforall hvalid

end checkPositivity.loop

theorem checkPositivity.WF
    (Hloop : (AddInductive.checkPositivity.loop stats ctor idx type
      c.fuel.inductiveFuel c).WF Q) :
    (AddInductive.checkPositivity stats type ctor idx c).WF Q := by
  unfold AddInductive.checkPositivity
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact Hloop

/-- Public positivity refinement, including the production fuel lookup. -/
theorem checkPositivity.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refines Hc Hstats hconsume hlit hctx hproj htype

/-- Public narrow-scope positivity refinement, including the production fuel
lookup used by constructor checking. -/
theorem checkPositivity.refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refinesNarrow Hc Hruntime Hstats hconsume
    hlit hproj htypeNarrow htypeFull


end VerifyInductive
end Lean4Lean
