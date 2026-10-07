import Lean4Lean.Theory.Typing.ProjectionCornerIndexedCase
import Lean4Lean.Theory.Typing.ProjectionCornerIndexedTele

/-! # The case type of a registered indexed structure is a type

The index-general form of `caseView_recursorType_isType`. The parameter part of the family
telescope is related to the registered constructor's parameters as in the non-indexed case.
The index part is related to the declared family type by an explicit header-agreement
hypothesis: the declared type of the family is definitionally the normalized family type
`∀ params indices, Sort r`. The certified compilation data does not provide this agreement
(`InductiveSignature.FamilyTypesWF` only types the family application under all the index
binders). -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

/-- The recursor type into `Prop` of the case view of a registered indexed structure is a type,
given that the view's constructor type is the registered constructor type and that the declared
family type is the normalized one. Also returns the constructor's field count. -/
theorem caseViewI_recursorType_isType (henv : env.WF)
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {uvars : Nat} {isUnsafe : Bool} {fam : Family} {RP RF RCI : List VExpr}
    (hfam : fam.name = S) (huv : uvars = info.uvars)
    (hnp : RP.length = info.nparams) (hCIlen : RCI.length = fam.indices.length)
    (hdef : env.IsDefEqU info.uvars []
      ((caseViewI uvars isUnsafe fam info.ctorName RP RF RCI).constructorType
        ⟨info.ctorName, ⟨0, by simp [caseViewI]⟩, RF.map Field.external, RCI⟩) info.ctorType)
    (hhdr : ∃ tc, env.constants S = some tc ∧ env.IsDefEqU info.uvars [] tc.type
      (VExpr.wrapForalls (RP ++ fam.indices) (.sort fam.resultLevel))) :
    env.IsType U []
      ((⟨U, ls, .zero, fun _ => default⟩ : Instance (caseViewI uvars isUnsafe fam info.ctorName
        RP RF RCI)).recursorType ⟨0, by simp [caseViewI]⟩) ∧
    info.nparams + RF.length = info.ctorType.forallArity := by
  let sv := caseViewI uvars isUnsafe fam info.ctorName RP RF RCI
  let gp : Instance sv := ⟨U, ls, .zero, fun _ => default⟩
  let c' : Constructor sv.families.size :=
    ⟨info.ctorName, ⟨0, by simp [sv, caseViewI]⟩, RF.map Field.external, RCI⟩
  have hrec := gp.recursorType_shape rfl rfl ⟨0, by simp [sv, caseViewI]⟩
    ⟨0, by simp [sv, caseViewI]⟩
  have hc0 : sv.constructors[(⟨0, by simp [sv, caseViewI]⟩ : Fin sv.constructors.size)] = c' :=
    rfl
  rw [hc0, gp.motive_shape _ rfl, gp.minor_shape rfl c' rfl, gp.major_lift,
    gp.constructorApp_shape] at hrec
  have hsH : gp.sHyps c' = [] := by
    unfold Instance.sHyps; rw [caseViewI_recursiveFields]; rfl
  simp only [hsH, List.append_nil, List.length_nil, Nat.add_zero, VExpr.liftN_zero] at hrec
  change env.IsType U [] (gp.recursorType ⟨0, by simp [sv, caseViewI]⟩) ∧ _
  rw [hrec]
  -- notation
  have hF : sv.fieldTypes c' = RF := fieldTypes_external _ rfl
  have hsF : gp.sFields c' = RF.map (·.instL ls) := by simp only [Instance.sFields, hF]; rfl
  have hP : gp.params = RP.map (·.instL ls) := rfl
  have hsI : gp.sIndices ⟨0, by simp [sv, caseViewI]⟩ = fam.indices.map (·.instL ls) := rfl
  have hsCI : gp.sCtorIndices c' = RCI.map (·.instL ls) := rfl
  have hlsU : ls.length = uvars := hlslen.trans huv.symm
  rw [hsF, hP, hsI, hsCI]
  generalize hPdef : RP.map (·.instL ls) = P
  generalize hFdef : RF.map (·.instL ls) = F
  generalize hIdef : fam.indices.map (·.instL ls) = I
  generalize hCIdef : RCI.map (·.instL ls) = CI
  have hPl : P.length = info.nparams := by rw [← hPdef]; simp [hnp]
  have hFl : F.length = RF.length := by rw [← hFdef]; simp
  have hIl : I.length = fam.indices.length := by rw [← hIdef]; simp
  have hCIl : CI.length = I.length := by rw [← hCIdef, hIl]; simp [hCIlen]
  -- the view's constructor type at `ls`
  let R := VExpr.mkApps (.const S ls) (vars P.length F.length ++ CI)
  have hC : (sv.constructorType c').instL ls = VExpr.wrapForalls (P ++ F) R := by
    simp only [InductiveSignature.constructorType, hF, InductiveSignature.familyApp,
      VExpr.instL_wrapForalls, List.map_append, VExpr.instL_mkApps, VExpr.instL, R,
      ← hPdef, ← hFdef, ← hCIdef]
    simp only [sv, caseViewI, hfam, VLevel.inst_map_id hlsU]
    congr 2
    · exact congrArg (VExpr.const · ls) hfam
    · simp [c', InductiveSignature.Instance.instL_vars, vars, VExpr.instL]
      intro a _; exact List.length_map ..
  -- the registered constructor
  obtain ⟨decl, type, ctor, -, -, htname, -, hdu, hdn, -, -, -, hctorType, -, hwf, -, Hraw, -⟩ :=
    Ordered.projectionShape henv.ordered hinfo
  have hctorT : env.IsType U [] (info.ctorType.instL ls) := by
    have h := hwf.instL (ls := ls) hls
    rw [hctorType] at h
    simpa using h
  have hdefL : env.IsDefEqU U [] (VExpr.wrapForalls (P ++ F) R) (info.ctorType.instL ls) := by
    have h := hdef.instL hls
    rw [hC] at h
    simpa using h
  have hCT : env.IsType U [] (VExpr.wrapForalls (P ++ F) R) :=
    IsType.defeqU_l henv trivial hdefL.symm hctorT
  have hPF := IsType.wrapForalls_inv henv (Γ := []) trivial hCT
  simp only [List.append_nil] at hPF
  obtain ⟨hctxPF, hRT⟩ := hPF
  have hRT' := hRT
  have hctxP : OnCtx P.reverse (env.IsType U) := by
    have h := hctxPF
    rw [List.reverse_append] at h
    exact OnCtx.of_append h
  -- the declared family type is the normalized one
  obtain ⟨uR, huR⟩ := hRT
  obtain ⟨_, hRhd⟩ := VExpr.WF.of_mkApps henv.ordered hctxPF (f := .const S ls) ⟨_, huR⟩
  obtain ⟨tc, hlook, hhdr⟩ := hhdr
  obtain ⟨ci, hci, _, hlen⟩ := HasType.const_inv henv.ordered hctxPF hRhd
  rw [hlook] at hci
  cases Option.some.inj hci
  have hhdrL : env.IsDefEqU U [] (tc.type.instL ls)
      (VExpr.wrapForalls (P ++ I) (.sort (fam.resultLevel.inst ls))) := by
    have h := hhdr.instL hls
    simpa [VExpr.instL_wrapForalls, List.map_append, ← hPdef, ← hIdef, VExpr.instL] using h
  have hconstH : ∀ {Γ}, OnCtx Γ (env.IsType U) → env.HasType U Γ (.const S ls)
      (VExpr.wrapForalls (P ++ I) (.sort (fam.resultLevel.inst ls))) := fun hΓ =>
    (HasType.const hlook hls hlen).defeqU_r henv hΓ (hhdrL.weak0 henv.ordered)
  have hNT : env.IsType U [] (VExpr.wrapForalls (P ++ I) (.sort (fam.resultLevel.inst ls))) :=
    IsType.defeqU_l henv trivial hhdrL ((henv.ordered.constWF hlook).instL hls)
  have hPI := IsType.wrapForalls_inv henv (Γ := []) trivial hNT
  simp only [List.append_nil] at hPI
  obtain ⟨hctxPI, -⟩ := hPI
  -- the major domain
  have hsM : gp.sMajor ⟨0, by simp [sv, caseViewI]⟩ =
      VExpr.mkApps (.const S ls) (bvarRange (P.length + I.length) (P.length + I.length)) := by
    simp only [Instance.sMajor]
    have e2 : (sv.families[(⟨0, by simp [sv, caseViewI]⟩ : Fin sv.families.size)]).name = S := hfam
    rw [e2]
    have hPv : sv.params.length = P.length := by rw [← hPdef]; simp [sv, caseViewI]
    have hIv : (sv.families[(⟨0, by simp [sv, caseViewI]⟩ : Fin sv.families.size)]).indices.length =
        I.length := hIl.symm
    rw [hPv, hIv, vars_eq_bvarRange, vars_eq_bvarRange, Nat.add_zero, ← CastSpec.bvarRange_split]
  rw [hsM]
  have hPIcl := OnCtx.closed_reverse henv.ordered hctxPI
  have hTPI := TelInst.ident (env := env) (U := U) [] hPIcl
  simp only [List.append_nil] at hTPI
  have hMaj : env.HasType U (P ++ I).reverse
      (VExpr.mkApps (.const S ls) (bvarRange (P.length + I.length) (P.length + I.length)))
      (.sort (fam.resultLevel.inst ls)) := by
    have := HasType.mkApps_of_tel henv hctxPI (hconstH hctxPI) hTPI
    simpa using this
  have hidx : OnCtx (P ++ I ++ [VExpr.mkApps (.const S ls)
      (bvarRange (P.length + I.length) (P.length + I.length))]).reverse (env.IsType U) := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact ⟨by simpa [List.reverse_append] using hctxPI, _, by simpa [List.reverse_append] using hMaj⟩
  generalize hMajdef : VExpr.mkApps (.const S ls)
    (bvarRange (P.length + I.length) (P.length + I.length)) = Maj at hidx hMaj
  -- the constructor at the parameter and field variables
  have hctorC := Ordered.projectionConstructor henv.ordered hinfo
  let Ctor := VExpr.mkApps (.const info.ctorName ls)
    (bvarRange (P.length + F.length) (P.length + F.length))
  have hCtor : env.HasType U (P ++ F).reverse Ctor R := by
    have h1 : env.HasType U (P ++ F).reverse (.const info.ctorName ls) (info.ctorType.instL ls) :=
      .const hctorC hls hlslen
    have h2 := h1.defeqU_r henv hctxPF (hdefL.symm.weak0 henv.ordered)
    have hPFcl := OnCtx.closed_reverse henv.ordered hctxPF
    have hT := TelInst.ident (env := env) (U := U) [] hPFcl
    simp only [List.append_nil, List.length_append] at hT
    have h3 := HasType.mkApps_of_tel henv hctxPF h2 hT
    have hRcl : R.ClosedN (P.length + F.length) := by
      obtain ⟨_, h⟩ := hRT'
      have := h.closedN henv.ordered (CtxWF.closed henv.ordered hctxPF)
      simpa [Nat.add_comm] using this
    rw [VExpr.instOuter_range_bvar' _ _ _ hRcl (Nat.le_refl _), Nat.sub_self,
      VExpr.liftN_zero] at h3
    exact h3
  have harity : info.nparams + RF.length = info.ctorType.forallArity := by
    obtain ⟨doms, result, hshape0, -, -, hhead0, harity0⟩ := Hraw.forallArity
    rw [hctorType] at hshape0 harity0
    rw [harity0]
    have h1 : env.HasType U (P ++ F).reverse (.const info.ctorName ls)
        (info.ctorType.instL ls) := .const hctorC hls hlslen
    have hh : (VExpr.getAppFnArgs.go result []).1 =
        .const type.name (VLevel.params decl.uvars) := hhead0
    rw [hshape0, VExpr.instL_wrapForalls, ← VExpr.mkApps_getAppFnArgs_eq result, hh,
      htname, VExpr.instL_mkApps, VExpr.instL] at h1
    have h := VEnv.HasType.mkApps_rigid_arity henv hctxPF (henv.projectionRigid hinfo) h1 hCtor
    simp only [bvarRange_length, List.length_map] at h
    rw [← h]; simp [hPl, hFl]
  refine ⟨?_, harity⟩
  -- the constructor's indices and the constructor along the family telescope
  have hlenR : (vars P.length F.length ++ CI).length = (P ++ I).length := by
    simp [vars, hCIl]
  obtain ⟨hargs, -⟩ := HasType.mkApps_wrapForalls henv hctxPF (hconstH hctxPF) ⟨_, huR⟩ hlenR
  have hRargs : TelInst env U (P ++ F).reverse (P ++ I) (vars P.length F.length ++ CI) :=
    ⟨hlenR, hargs⟩
  have hCtorMaj : env.HasType U (P ++ F).reverse Ctor
      (Maj.instOuter (vars P.length F.length ++ CI)) := by
    rw [← hMajdef, show P.length + I.length = (vars P.length F.length ++ CI).length by
      rw [hlenR]; simp, instOuter_bvarRange_apps (f := .const S ls) trivial]
    exact hCtor
  have hTF := TelInst.append_one hRargs hCtorMaj
  have hclPIM := OnCtx.closed_reverse henv.ordered hidx
  have hW := insertBinders_ctxLiftN F [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] P.reverse 1
    rfl F.length (Nat.le_refl _)
  rw [List.take_length, List.take_of_length_le (by simp)]
    at hW
  have hW' : Ctx.LiftN 1 F.length (P ++ F).reverse
      ((insertBinders F 1).reverse ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++
        P.reverse) := by simpa [List.reverse_append] using hW
  have hT := TelInst.weakAt henv.ordered hclPIM hW' hTF
  simp only [List.map_append, vars_eq_bvarRange] at hT
  rw [bvarRange_map_liftN_hi _ _ _ _ (by omega)] at hT
  have hT' : TelInst env U ((insertBinders F 1).reverse ++
      [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (P ++ (I ++ [Maj]))
      (bvarRange P.length (P.length + (F.length + 1)) ++
        ((CI ++ [Ctor]).map (·.liftN 1 F.length))) := by
    rw [← Nat.add_assoc]
    simpa [List.append_assoc] using hT
  have hDcl : ∀ j (h : j < (I ++ [Maj]).length), ((I ++ [Maj])[j]).ClosedN (P.length + j) := by
    intro j h
    have := hclPIM (P.length + j) (by simp at h ⊢; omega)
    simpa [List.append_assoc, List.getElem_append_right] using this
  have hU := TelInst.unlift hDcl rfl hT'
  -- the motive variable in the minor premise's context
  have hlook := Lookup.reverse_append
    (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ insertBinders F 1) [] P.length
    (by simp)
  have hctxEq : (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++
      insertBinders F 1).reverse ++ [] =
      (insertBinders F 1).reverse ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++
        P.reverse := by simp
  rw [hctxEq] at hlook
  rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)] at hlook
  simp only [List.length_append, List.length_singleton, Instance.length_insertBinders,
    Nat.sub_self, List.getElem_singleton] at hlook
  have hmot : env.HasType U ((insertBinders F 1).reverse ++
      [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (.bvar F.length)
      (VExpr.wrapForalls ((I ++ [Maj]).mapIdx fun l d => d.liftN (F.length + 1) l)
        (.sort .zero)) := by
    have h := HasType.bvar (env := env) (U := U) hlook
    rw [show P.length + 1 + F.length - 1 - P.length = F.length by omega,
      show P.length + 1 + F.length - P.length = F.length + 1 by omega,
      liftN_wrapForalls] at h
    simpa [VExpr.liftN] using h
  have hMotT : env.IsType U P.reverse (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)) :=
    IsType.wrapForalls_of (by simpa [List.reverse_append, List.append_assoc] using hidx)
      ⟨_, HasType.sort (by trivial)⟩
  have hCm := OnCtx.insert_binders henv.ordered (F := F)
    (X := [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)]) (Γ := P.reverse)
    (by simpa [List.reverse_append] using hctxPF) ⟨hctxP, hMotT⟩
  have hCm' : OnCtx ((insertBinders F 1).reverse ++
      [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (env.IsType U) := hCm
  have hbody := HasType.mkApps_of_tel henv hCm' hmot hU
  have hsC : gp.sCtorApp c' = Ctor := by
    simp only [Instance.sCtorApp, hsF, ← hFdef]
    simp [sv, caseViewI, c', gp, Ctor, ← hPdef, hFl]
  rw [hsC]
  refine IsType.recursorShape henv hidx (IsType.wrapForalls_of
    (by simpa [List.reverse_append, List.append_assoc] using hCm') ⟨.zero, ?_⟩)
  simpa [List.map_append, List.reverse_append, List.append_assoc] using hbody

end VEnv
end Lean4Lean
