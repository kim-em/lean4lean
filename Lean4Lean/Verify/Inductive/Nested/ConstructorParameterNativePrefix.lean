import Lean4Lean.Verify.Inductive.Nested.ParameterOpening
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterRawShape

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The source parameter opening retained by nested lowering determines an
exact semantic metacontext with the same concrete local context. -/
theorem NestedParamOpening.toMLCtx
    (henv : env.WF)
    (Hopen : NestedParamOpening lctx params type n outLctx tail outParams)
    (houtWF : outLctx.WF)
    (mlctx : TypeChecker.MLCtx)
    (hmlctx : mlctx.lctx = lctx)
    (hmlctxWF : mlctx.WF env Us)
    (Htype : TrExprS env Us mlctx.vlctx type target) :
    ∃ outMLCtx : TypeChecker.MLCtx, ∃ targetTail,
      outMLCtx.lctx = outLctx ∧
      outMLCtx.WF env Us ∧
      TrExprS env Us outMLCtx.vlctx tail targetTail := by
  induction Hopen generalizing mlctx target with
  | done =>
    exact ⟨mlctx, target, hmlctx, hmlctxWF, Htype⟩
  | step Hnext ih =>
    rename_i n' outLctx' tail' outParams' lctx' params' id name dom body bi
    cases Htype with
    | forallE HdomainType HbodyType Hdomain Hbody =>
      rename_i domainTarget bodyTarget
      have hcurrentWF : lctx'.WF := hmlctx ▸ hmlctxWF.tr.1
      have hidFresh : lctx'.find? id = none := by
        rcases Hnext.context_extension with
          ⟨decls, hlctx, _hparams, _hlength⟩
        have hnodup := houtWF.nodup
        rw [hlctx, List.map_append] at hnodup
        simp only [LocalContext.mkLocalDecl_toList, List.map_cons,
          LocalDecl.fvarId] at hnodup
        have hidNotMem : id ∉ lctx'.toList.map (fun d => d.fvarId) := by
          exact (List.nodup_cons.mp
            (List.nodup_append.mp hnodup).2.1).1
        rw [hcurrentWF.find?_eq_find?_toList]
        exact List.find?_eq_none.mpr (by
          intro decl hdecl hmatch
          have hfv : decl.fvarId = id := (LawfulBEq.eq_of_beq hmatch).symm
          exact hidNotMem (List.mem_map.mpr ⟨decl, hdecl, hfv⟩))
      let nextMLCtx := TypeChecker.MLCtx.vlam id name dom domainTarget bi mlctx
      have hnextWF : nextMLCtx.WF env Us :=
        ⟨hmlctxWF, by simpa [nextMLCtx, hmlctx] using hidFresh,
          Hdomain, HdomainType⟩
      have Hbody' : TrExprS env Us nextMLCtx.vlctx
          (body.instantiate1 (.fvar id)) bodyTarget := by
        rw [Expr.instantiate1_eq]
        exact Hbody.inst_fvar henv.ordered hnextWF.tr.wf
      apply ih houtWF nextMLCtx
      · simp [nextMLCtx, TypeChecker.MLCtx.lctx, hmlctx]
      · exact hnextWF
      · exact Hbody'

/-- Successful native restored-parameter validation refines the same exact
checked-prefix judgment used by the independent constructor formation proof.
The `stats` value is only a carrier for the validator's actual parameter
array; no production replay or environment-locality premise is involved. -/
theorem NestedParamOpening.validateRestoredConstructorPrefix
    (stats : AddInductive.InductiveStats)
    (Hopen : NestedParamOpening lctx opened familyType n
      fullLCtx familyTail fullParams)
    (hvalid : CheckingEnv.Valid safety prodEnv env)
    (hfullWF : fullLCtx.WF)
    (hfullFresh : ∀ fv ∈ fullLCtx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (mlctx : TypeChecker.MLCtx)
    (hmlctx : mlctx.lctx = lctx)
    (hmlctxWF : mlctx.WF env Us)
    (hcurrentFresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (Hfamily : TrExprS env Us mlctx.vlctx familyType familyTarget)
    (Hctor : TrExprS env Us mlctx.vlctx ctorType ctorTarget)
    (Hprefix : CheckedConstructorParameterPrefix env Us
      { stats with params := fullParams } original opened.size ctorType
        mlctx.vlctx sourceDomains)
    (hrun : Lean4Lean.validateRestoredConstructorParameters.loop prodEnv Us
      safety typeCheckerFuel fullLCtx lctx ctorName fullParams ctorType
      opened.size loopFuel = .ok ()) :
    ∃ finalMLCtx : TypeChecker.MLCtx, ∃ ctorTail finalDomains
        familyDomains familyTargetTail,
      finalMLCtx.lctx = fullLCtx ∧
      finalMLCtx.WF env Us ∧
      familyTarget = VExpr.wrapForalls familyDomains familyTargetTail ∧
      familyDomains.length = n ∧
      finalMLCtx.vlctx.toCtx =
        familyDomains.reverse ++ mlctx.vlctx.toCtx ∧
      CheckedConstructorParameterPrefix env Us
        { stats with params := fullParams } original (opened.size + n)
        ctorTail finalMLCtx.vlctx finalDomains := by
  induction Hopen generalizing mlctx ctorType ctorTarget familyTarget
      sourceDomains loopFuel with
  | done =>
    exact ⟨mlctx, ctorType, sourceDomains, [], familyTarget, hmlctx, hmlctxWF,
      by simp [VExpr.wrapForalls], rfl, by simp, Hprefix⟩
  | step Hnext ih =>
    rename_i n' fullLCtx' familyTail' fullParams' lctx' opened' id name dom
      body bi
    cases loopFuel with
    | zero => simp [Lean4Lean.validateRestoredConstructorParameters.loop] at hrun
    | succ loopFuel =>
      cases Hfamily with
      | forallE HfamilyDomainType _HfamilyBodyType HfamilyDomain HfamilyBody =>
        rename_i familyDomainTarget familyBodyTarget
        have hi : opened'.size < fullParams'.size := by
          have hsize := Hnext.params_size
          simp only [Array.size_push] at hsize
          omega
        have hparam : fullParams'[opened'.size]? = some (.fvar id) := by
          rw [← Array.getElem?_toList]
          rcases Hnext.params_extension with ⟨suffix, heq, _hlength⟩
          rw [heq]
          simp
        have hparamGet : fullParams'[opened'.size] = .fvar id :=
          Option.some.inj ((Array.getElem?_eq_getElem hi).symm.trans hparam)
        have hfind : fullLCtx'.find? id = some
            (.cdecl lctx'.decls.size id name dom bi .default) := by
          apply LocalContextWF_find?_eq_some_of_mem hfullWF
            (d := .cdecl lctx'.decls.size id name dom bi .default)
          rcases Hnext.context_extension with
            ⟨decls, hlctx, _hparams, _hlength⟩
          rw [hlctx]
          simp [LocalContext.mkLocalDecl_toList]
        have hlocal : fullLCtx'.get! id =
            .cdecl lctx'.decls.size id name dom bi .default := by
          simp [LocalContext.get!, hfind]
        cases ctorType with
          | forallE ctorName' ctorDom ctorBody ctorBi =>
            cases Hctor with
            | @forallE ctorDomainTarget ctorBodyTarget _ _ _ _ _
                HctorDomainType _HctorBodyType HctorDomain HctorBody =>
              cases hcheck : TypeChecker.M.run prodEnv safety lctx' Us
                  typeCheckerFuel (TypeChecker.isDefEq ctorDom dom) with
              | error err =>
                simp [Lean4Lean.validateRestoredConstructorParameters.loop, hi,
                  hparamGet, Expr.fvarId!, hlocal, hcheck] at hrun
                simp only [bind, Except.bind] at hrun
                cases hrun
              | ok matched =>
                cases matched with
                | false =>
                  simp [Lean4Lean.validateRestoredConstructorParameters.loop,
                    hi, hparamGet, Expr.fvarId!, hlocal, hcheck] at hrun
                  simp only [bind, Except.bind] at hrun
                  simp at hrun
                | true =>
                  have hcompare : env.IsDefEqU Us.length mlctx.vlctx.toCtx
                      ctorDomainTarget familyDomainTarget := by
                    have Hcheck := TypeChecker.M.WF.runCheckingValidMLC
                      (fuel := typeCheckerFuel) (wf := hvalid)
                      (mlctx_wf := hmlctxWF) hcurrentFresh
                      (TypeChecker.isDefEq.WF HctorDomain HfamilyDomain)
                    exact Hcheck true (by simpa [hmlctx] using hcheck) rfl
                  let nextMLCtx := TypeChecker.MLCtx.vlam id name dom
                    familyDomainTarget bi mlctx
                  have hnextWF : nextMLCtx.WF env Us := by
                    refine ⟨hmlctxWF, ?_, HfamilyDomain, HfamilyDomainType⟩
                    have hcurrentWF : lctx'.WF := hmlctx ▸ hmlctxWF.tr.1
                    have hidFresh : lctx'.find? id = none := by
                      have hfinalNodup := hfullWF.nodup
                      rcases Hnext.context_extension with
                        ⟨decls, hlctx, _hparams, _hlength⟩
                      rw [hlctx, List.map_append] at hfinalNodup
                      simp only [LocalContext.mkLocalDecl_toList, List.map_cons,
                        LocalDecl.fvarId] at hfinalNodup
                      have hidNotMem : id ∉
                          lctx'.toList.map (fun d => d.fvarId) := by
                        exact (List.nodup_cons.mp
                          (List.nodup_append.mp hfinalNodup).2.1).1
                      rw [hcurrentWF.find?_eq_find?_toList]
                      exact List.find?_eq_none.mpr (by
                        intro decl hdecl hmatch
                        have hfv : decl.fvarId = id :=
                          (LawfulBEq.eq_of_beq hmatch).symm
                        exact hidNotMem
                          (List.mem_map.mpr ⟨decl, hdecl, hfv⟩))
                    simpa [nextMLCtx, hmlctx] using hidFresh
                  have HfamilyNext : TrExprS env Us nextMLCtx.vlctx
                      (body.instantiate1 (.fvar id)) familyBodyTarget := by
                    rw [Expr.instantiate1_eq]
                    exact HfamilyBody.inst_fvar hvalid.tr.wf.ordered
                      hnextWF.tr.wf
                  have hcompareAtSort := hcompare.of_l hvalid.tr.wf
                    hmlctxWF.tr.wf (Classical.choose_spec HctorDomainType)
                  let Hcontexts : VLCtx.IsDefEq env Us.length
                      ((none, .vlam ctorDomainTarget) :: mlctx.vlctx)
                      ((none, .vlam familyDomainTarget) :: mlctx.vlctx) :=
                    .cons (.refl hvalid.tr.wf hmlctxWF.tr.wf) nofun
                      (.vlam hcompareAtSort)
                  rcases HctorBody.defeqDFC hvalid.tr.wf Hcontexts with
                    ⟨nextCtorTarget, HctorBody'⟩
                  have HctorNext : TrExprS env Us nextMLCtx.vlctx
                      (Expr.instantiate1 ctorBody (.fvar id)) nextCtorTarget := by
                    rw [Expr.instantiate1_eq]
                    exact HctorBody'.inst_fvar hvalid.tr.wf.ordered
                      hnextWF.tr.wf
                  have HprefixNext : CheckedConstructorParameterPrefix env Us
                      { stats with params := fullParams' } original
                      (opened'.push (.fvar id)).size
                      (ctorBody.instantiate1 (.fvar id)) nextMLCtx.vlctx
                      (sourceDomains ++ [ctorDomainTarget]) := by
                    simpa [nextMLCtx] using CheckedConstructorParameterPrefix.step
                      Hprefix hparam rfl HctorDomain HctorDomainType hcompare
                  have hnextFresh : ∀ fv ∈ nextMLCtx.vlctx.fvars,
                      ({} : TypeChecker.State).ngen.Reserves fv := by
                    intro fv hfv
                    simp only [nextMLCtx, TypeChecker.MLCtx.vlctx,
                      VLCtx.fvars, List.filterMap_cons, Option.map_some,
                      List.mem_cons] at hfv
                    rcases hfv with hfv | hfv
                    · subst fv
                      apply hfullFresh id
                      rw [LocalContext.fvars]
                      rcases Hnext.context_extension with
                        ⟨decls, hlctx, _hparams, _hlength⟩
                      rw [hlctx]
                      exact List.mem_map.mpr ⟨.cdecl lctx'.decls.size id name dom
                        bi .default, by
                          apply List.mem_append_right
                          simp [LocalContext.mkLocalDecl_toList], rfl⟩
                    · exact hcurrentFresh fv hfv
                  have hrunNext :
                      Lean4Lean.validateRestoredConstructorParameters.loop
                        prodEnv Us safety typeCheckerFuel fullLCtx'
                        (lctx'.mkLocalDecl id name dom bi) ctorName fullParams'
                        (ctorBody.instantiate1 (.fvar id))
                        (opened'.push (.fvar id)).size loopFuel = .ok () := by
                    simpa [Lean4Lean.validateRestoredConstructorParameters.loop,
                      hi, hparamGet, Expr.fvarId!, hlocal, hcheck, bind,
                      Except.bind] using hrun
                  rcases ih hfullWF hfullFresh nextMLCtx
                      (by
                        change mlctx.lctx.mkLocalDecl id name dom bi =
                          lctx'.mkLocalDecl id name dom bi
                        rw [hmlctx])
                      hnextWF hnextFresh
                      HfamilyNext HctorNext HprefixNext hrunNext with
                    ⟨finalMLCtx, finalCtorTail, finalDomains, familyDomains,
                      finalFamilyTail, hfinalLCtx, hfinalWF, hfamilyTarget,
                      hfamilyLength, hfinalContext, HfinalPrefix⟩
                  refine ⟨finalMLCtx, finalCtorTail, finalDomains,
                    familyDomainTarget :: familyDomains, finalFamilyTail,
                    hfinalLCtx, hfinalWF, ?_, ?_, ?_, ?_⟩
                  · simp [VExpr.wrapForalls, hfamilyTarget]
                  · simp [hfamilyLength]
                  · simpa [nextMLCtx, VLCtx.toCtx, List.append_assoc] using
                      hfinalContext
                  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using HfinalPrefix
          | bvar | fvar | mvar | sort | const | app | lam | letE | lit
              | mdata | proj =>
            simp [Lean4Lean.validateRestoredConstructorParameters.loop, hi]
              at hrun

end VerifyInductive
end Lean4Lean
