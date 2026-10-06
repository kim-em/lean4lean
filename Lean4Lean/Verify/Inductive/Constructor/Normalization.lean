import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Theory.Inductive.Normalization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The actual recursive-application test retains the whole universe spine,
not only the arity exposed by `ValidIndAppAt`. -/
theorem checkPositivityStep.isValidIndApp?.uniformNormalForm
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlevels : stats.levels.mapM (VLevel.ofLevel Us) = some levels)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ) :
    decl.UniformFieldNormalForm levels depth type' := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.indConstAt hi')
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels', _⟩
  have heq : levels' = levels := Option.some.inj (hlevels'.symm.trans hlevels)
  subst levels'
  refine .inr ⟨[], type', rfl, by simp, ?_,
    decl.types[typeIdx], List.getElem_mem hi', ?_⟩
  · simpa using checkPositivityStep.isValidIndApp?.validIndAppAt H htr hvalid hlit hctx
  · exact congrArg Prod.fst hspine

/-- Replay successful positivity in the original narrow scope, retaining every
source-free binder and the exact universe spine checked at a recursive head. -/
theorem checkPositivity.loop.uniformNormalFormNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) = some levels)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => ∃ normalized,
        Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType normalized ∧
        decl.UniformFieldNormalForm levels depth normalized) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact checkPositivity.loop.zero.WF
  | succ fuel ih =>
    rcases htypeFull with ⟨sourceFull, hsourceFull, hsourceTarget⟩
    refine checkPositivity.loop.succ.scopeWF Hc hsourceFull ?_
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
          c).WF (fun _ => ∃ result,
            Hc.venv.IsDefEqU decl.uvars scope.toCtx exposed result ∧
            decl.UniformFieldNormalForm levels depth result)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ => ∃ result,
            Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType result ∧
            decl.UniformFieldNormalForm levels depth result) :=
      Hstep.mono fun _ ⟨result, hresult, hshape⟩ =>
        ⟨result, VEnv.IsDefEqU.trans Hc.checking.tr.wf
          (by simpa [Hstats.uvars] using (Hruntime.scopeWF Hc.checking.tr.wf).toCtx)
          (by simpa [Hstats.uvars] using
            (show Hc.venv.IsDefEqU c.lparams.length scope.toCtx narrowType exposed from
              ⟨exprType, htypeExposed⟩)) hresult, hshape⟩
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · apply finish
      exact checkPositivityStep.noOccurrence.WF hocc
        ⟨exposed, (by simpa [Hstats.uvars] using
          (VEnv.IsDefEqU.refl (TrExprS.wf Hc.checking.tr.wf.ordered (Hruntime.scopeWF Hc.checking.tr.wf) hexposed))),
          .inl (checkPositivityStep.TrExprS.noIndOccAvailable Hstats.consts.names hlit
            (Hruntime.noIndConsts (decl.types.map (·.name))) hexposed hocc)⟩
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
            (Q := fun _ => ∃ result,
              Hc.venv.IsDefEqU decl.uvars scope.toCtx (.forallE narrowDom narrowBody) result ∧
              decl.UniformFieldNormalForm levels depth result)
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull ?_
          intro bodyFull' _hbodyFullEq hopenedFull
          let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          have hdeps : dom.consumeTypeAnnotationsVerified.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotationsVerified.fvarsList),
                  .vlam narrowDom) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
              hdomNarrow hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotationsVerified.fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have Hrec := ih Hc' Hruntime' Hstats' hlevels hlit hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ ⟨result, hresult, hshape⟩ => by
            obtain ⟨domLevel, hdomTyped⟩ := hdomNarrowType
            obtain ⟨bodyLevel, hbodyTyped⟩ := hbodyNarrowType
            have hdomTyped' : Hc.venv.HasType decl.uvars scope.toCtx narrowDom (.sort domLevel) := by
              simpa [Hstats.uvars] using hdomTyped
            have hbodyTyped' : Hc.venv.HasType decl.uvars
                (narrowDom :: scope.toCtx) narrowBody (.sort bodyLevel) := by
              simpa [Hstats.uvars] using hbodyTyped
            have hbodyctx : OnCtx (narrowDom :: scope.toCtx)
                (Hc.venv.IsType decl.uvars) := by
              refine ⟨?_, _, hdomTyped'⟩
              simpa [Hstats.uvars] using (Hruntime.scopeWF Hc.checking.tr.wf).toCtx
            have hresult' : Hc.venv.IsDefEqU decl.uvars
                (narrowDom :: scope.toCtx) narrowBody result := hresult
            exact ⟨.forallE narrowDom result,
              ⟨_, .forallEDF hdomTyped'
                (hresult'.of_l Hc.checking.tr.wf hbodyctx hbodyTyped')⟩,
              hshape.forallE
                (checkPositivityStep.TrExprS.noIndOccAvailable Hstats.consts.names
                  hlit (Hruntime.noIndConsts (decl.types.map (·.name))) hdomNarrow hdomOcc')⟩
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        apply finish
        exact checkPositivityStep.validApplication.WF hocc' hforall hvalid
          ⟨exposed, (by simpa [Hstats.uvars] using
            (VEnv.IsDefEqU.refl (TrExprS.wf Hc.checking.tr.wf.ordered (Hruntime.scopeWF Hc.checking.tr.wf) hexposed))),
            checkPositivityStep.isValidIndApp?.uniformNormalForm Hstats hexposed
              hvalid hlevels hlit (Hruntime.noIndConsts (decl.types.map (·.name)))⟩

/-- Source-boundary form of the production positivity check. The levels
premise is obtained from `MaterializedHeaderResult.levelParamsTranslation`;
it is preserved while recursive binders are opened. -/
theorem checkPositivity.uniformNormalFormNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) = some levels)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => ∃ normalized,
        Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType normalized ∧
        decl.UniformFieldNormalForm levels depth normalized) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.uniformNormalFormNarrow Hc Hruntime Hstats
    hlevels hconsume hlit htypeNarrow htypeFull

/-- The successful constructor traversal retains normalized field data at
the exact original source domains, with the complete checked universe spine. -/
theorem checkConstructors.loopCtor.uniformTailWF
    {decl : VInductDecl} {target : VInductiveType} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) = some levels)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF (fun _ =>
        decl.UniformCtorTail Hc.venv target levels scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi, type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, _⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with ⟨consumedDom, Hdom⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : dom.consumeTypeAnnotationsVerified.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          let Hruntime' : checkInductiveTypes.loopType.NarrowRuntimeScope
              Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotationsVerified.fvarsList),
                .vlam narrowDom) :: scope) Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom hdomNarrow hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotationsVerified.fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have finish
              (hfield : decl.isUnsafe = true ∨ ∃ normalized,
                Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowDom normalized ∧
                decl.UniformFieldNormalForm levels depth normalized)
              {bodyFull' : VExpr}
              (hopenedFull : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) bodyFull') :
              (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
                { c with
                  ngen := c.ngen.next
                  lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
                    dom.consumeTypeAnnotationsVerified bi
                  checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
                    dom.consumeTypeAnnotationsVerified bi }).WF (fun _ =>
                  decl.UniformCtorTail Hc.venv target levels scope.toCtx depth
                    (.forallE narrowDom narrowBody)) := by
            have Htail := ih Hc' Hruntime' Hstats' hparamNext hlit hlevels hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => .field
              (by simpa [Hstats.uvars] using hdomNarrowType) hfield htail
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.uniformNormalFormNarrow
              (ctor := ctor) (idx := i) Hc Hruntime Hstats hlevels
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              Hc hparamAt Hdom hbodyFull Hpos ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound hpositive bodyFull' _hbodyFullEq hopenedFull
            exact finish (.inr hpositive) hopenedFull
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              Hc hparamAt Hdom hbodyFull ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound bodyFull' _hbodyFullEq hopenedFull
            exact finish (.inl (hunsafe rfl)) hopenedFull
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · have hvalidAt := checkPositivityStep.isValidIndAppIdx.validIndAppAt
          Hstats hi htrNarrow hvalid (.inr rfl) hlit
          (Hruntime.noIndConsts (decl.types.map (·.name)))
        have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalid
          (Hstats.indConstAt hi)
        rcases checkPositivityStep.TrExprS.constAppSpine htrNarrow hhead with
          ⟨levels', args', hspine, hlevels', _⟩
        have heq : levels' = levels := Option.some.inj (hlevels'.symm.trans hlevels)
        subst levels'
        subst target
        exact checkConstructors.loopCtor.result.WF hforall hvalid
          (.result hvalidAt (congrArg Prod.fst hspine))

end VerifyInductive
end Lean4Lean
