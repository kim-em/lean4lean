import Lean4Lean.Theory.Typing.ProjectionCornerIndexedSubst

/-! # The projection-walk corner at an indexed structure, from a typed eliminator of its view

For the one-constructor view `caseView` of a registered structure, possibly indexed: a closed term `h` typed at the view's recursor type into `Prop`
inhabits the projection-walk binder. The motive is the constant `fun idx _ => Nonempty X`;
the major's index arguments are typed along the view's index telescope by the header-agreement
hypothesis. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

theorem corner_inhabit_view (henv : env.WF) (hch : env.HasCanonicalChoice)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {T₀ : VExpr} (hT₀ : VExpr.LEquiv U T₀ (info.ctorType.instL ls))
    {ps idx : List VExpr} (hpl : ps.length = info.nparams)
    {e' : VExpr} (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx)))
    {j : Nat} {D body' : VExpr}
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (ps ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : env.IsType U Δ D)
    (hguard : ∀ u, env.HasType U Δ D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    {uvars : Nat} {isUnsafe : Bool} {fam : Family} {RP RF RCI : List VExpr}
    (hfam : fam.name = S) (huv : uvars = info.uvars)
    (hnp : RP.length = info.nparams) (hCIlen : RCI.length = fam.indices.length)
    (hIlen : fam.indices.length = info.nindices)
    (hdef : env.IsDefEqU info.uvars []
      ((caseView uvars isUnsafe fam info.ctorName RP RF RCI).constructorType
        ⟨info.ctorName, ⟨0, by simp [caseView]⟩, RF.map Field.external, RCI⟩) info.ctorType)
    (hhdr : ∃ tc, env.constants S = some tc ∧ env.IsDefEqU info.uvars [] tc.type
      (VExpr.wrapForalls (RP ++ fam.indices) (.sort fam.resultLevel)))
    {h : VExpr}
    (hhead : env.HasType U [] h
      ((⟨U, ls, .zero, fun _ => default⟩ : Instance (caseView uvars isUnsafe fam info.ctorName
        RP RF RCI)).recursorType ⟨0, by simp [caseView]⟩)) :
    ∃ d, env.HasType U Δ d D := by
  let sv := caseView uvars isUnsafe fam info.ctorName RP RF RCI
  let gp : Instance sv := ⟨U, ls, .zero, fun _ => default⟩
  let c' : Constructor sv.families.size :=
    ⟨info.ctorName, ⟨0, by simp [sv, caseView]⟩, RF.map Field.external, RCI⟩
  have hrec := gp.recursorType_shape rfl rfl ⟨0, by simp [sv, caseView]⟩
    ⟨0, by simp [sv, caseView]⟩
  have hc0 : sv.constructors[(⟨0, by simp [sv, caseView]⟩ : Fin sv.constructors.size)] = c' :=
    rfl
  rw [hc0, gp.motive_shape _ rfl, gp.minor_shape rfl c' rfl, gp.major_lift,
    gp.constructorApp_shape] at hrec
  have hsH : gp.sHyps c' = [] := by
    unfold Instance.sHyps; rw [caseView_recursiveFields]; rfl
  simp only [hsH, List.append_nil, List.length_nil, Nat.add_zero, VExpr.liftN_zero] at hrec
  -- notation
  have hF : sv.fieldTypes c' = RF := fieldTypes_external _ rfl
  have hsF : gp.sFields c' = RF.map (·.instL ls) := by simp only [Instance.sFields, hF]; rfl
  have hP : gp.params = RP.map (·.instL ls) := rfl
  have hsI : gp.sIndices ⟨0, by simp [sv, caseView]⟩ = fam.indices.map (·.instL ls) := rfl
  have hsCI : gp.sCtorIndices c' = RCI.map (·.instL ls) := rfl
  have hlsU : ls.length = uvars := hlslen.trans huv.symm
  rw [hsF, hP, hsI, hsCI] at hrec
  generalize hPdef : RP.map (·.instL ls) = P at hrec
  generalize hFdef : RF.map (·.instL ls) = F at hrec
  generalize hIdef : fam.indices.map (·.instL ls) = I at hrec
  generalize hCIdef : RCI.map (·.instL ls) = CI at hrec
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
    simp only [sv, caseView, hfam, VLevel.inst_map_id hlsU]
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
  have hsM : gp.sMajor ⟨0, by simp [sv, caseView]⟩ =
      VExpr.mkApps (.const S ls) (bvarRange (P.length + I.length) (P.length + I.length)) := by
    simp only [Instance.sMajor]
    have e2 : (sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)]).name = S := hfam
    rw [e2]
    have hPv : sv.params.length = P.length := by rw [← hPdef]; simp [sv, caseView]
    have hIv : (sv.families[(⟨0, by simp [sv, caseView]⟩ : Fin sv.families.size)]).indices.length =
        I.length := hIl.symm
    rw [hPv, hIv, vars_eq_bvarRange, vars_eq_bvarRange, Nat.add_zero, ← CastSpec.bvarRange_split]
  rw [hsM] at hrec
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
    (bvarRange (P.length + I.length) (P.length + I.length)) = Maj at hidx hMaj hrec
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
  have hsC : gp.sCtorApp c' = Ctor := by
    simp only [Instance.sCtorApp, hsF, ← hFdef]
    simp [sv, caseView, c', gp, Ctor, ← hPdef, hFl]
  rw [hsC] at hrec
  generalize hMindef : VExpr.wrapForalls (insertBinders F 1) (VExpr.mkApps (.bvar F.length)
    (CI.map (fun e => e.liftN 1 F.length) ++ [Ctor.liftN 1 F.length])) = Min at hrec
  -- the eliminator's telescope
  have HR : env.IsType U [] (gp.recursorType ⟨0, by simp [sv, caseView]⟩) :=
    hhead.isType henv.ordered trivial
  rw [hrec] at HR
  have hpeel := (IsType.wrapForalls_inv henv (Γ := []) trivial HR).1
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_nil, List.singleton_append, List.cons_append] at hpeel
  obtain ⟨hpre, -⟩ := hpeel
  obtain ⟨⟨-, hMotT⟩, hMinT⟩ := OnCtx.of_append hpre
  have hctxPIM := OnCtx.closed_reverse henv.ordered hidx
  -- the parameters and indices of the major along the family telescope
  obtain ⟨v, hTy⟩ := he'.isType henv.ordered hΔ
  have hlenA := HasType.mkApps_sort_arity henv hΔ (hconstH hΔ) hTy
  obtain ⟨hargsA, -⟩ := HasType.mkApps_wrapForalls henv hΔ (hconstH hΔ) ⟨_, hTy⟩ hlenA
  have hTelPI : TelInst env U Δ (P ++ I) (ps ++ idx) := ⟨hlenA, hargsA⟩
  have hidxl : idx.length = I.length := by simp [hpl, hPl] at hlenA; omega
  have he'' : env.HasType U Δ e' (Maj.instOuter (ps ++ idx)) := by
    rw [← hMajdef, show P.length + I.length = (ps ++ idx).length by simp [hpl, hPl, hidxl],
      instOuter_bvarRange_apps (f := .const S ls) trivial]
    exact he'
  have hTelPIM := TelInst.append_one hTelPI he''
  have hTelP : TelInst env U Δ P ps := by
    have := hTelPI.take (doms := P) (more := I)
    rwa [List.take_left' (by rw [hpl, hPl])] at this
  -- the binder reached by the walk
  obtain ⟨doms, result, hshape0, hle0, hvalid0, hhead0, harity0⟩ := Hraw.forallArity
  rw [hctorType] at hshape0 harity0
  rw [htname] at hvalid0 hhead0
  have hT₀' : VExpr.LEquiv U T₀
      (VExpr.wrapForalls (doms.map (·.instL ls)) (result.instL ls)) := by
    rw [hshape0, VExpr.instL_wrapForalls] at hT₀; exact hT₀
  have hr : (result.instL ls).AppOrConst := (VExpr.AppOrConst.of_getAppFnArgs hhead0).instL ls
  obtain ⟨hn, hDX⟩ := VExpr.walk_binder hT₀' hr hwalk
  have hargsl : (ps ++ (List.range j).map fun k => VExpr.proj S k e').length =
      info.nparams + j := by simp [hpl]
  have hmd : info.nparams + j < doms.length := by simpa [hargsl] using hn
  have hDX' : VExpr.LEquiv U D (((doms[info.nparams + j]'hmd).instL ls).instOuter
      (ps ++ (List.range j).map fun k => VExpr.proj S k e')) := by
    simpa [hargsl] using hDX
  obtain ⟨u0, hu0⟩ := hD
  have hDXd := VExpr.LEquiv.defeq henv hΔ hDX' ⟨_, hu0⟩
  obtain ⟨u, hXu⟩ := IsType.defeqU_l henv hΔ hDXd ⟨_, hu0⟩
  have hu : u.WF U := (hXu.isType henv.ordered hΔ).sort_inv henv.ordered
  have hnz : ¬ (info.resultLevel.inst ls).IsNeverZero := fun h => hguard u0 hu0 (.inl h)
  generalize hXdef : ((doms[info.nparams + j]'hmd).instL ls).instOuter
    (ps ++ (List.range j).map fun k => VExpr.proj S k e') = X at hXu hDXd
  have hNe : env.HasType U Δ (.const ``Nonempty [u]) (.forallE (.sort u) (.sort .zero)) := by
    have := HasType.const (env := env) (Γ := Δ) (ls := [u]) hch.1 (by simpa using hu) rfl
    simpa [canonicalNonemptyType, VExpr.instL, VLevel.inst] using this
  have hY : env.HasType U Δ (.app (.const ``Nonempty [u]) X) (.sort .zero) := by
    simpa [VExpr.inst] using HasType.app hNe hXu
  -- the motive `fun idx _ => Nonempty X`
  have hMotI : env.IsType U Δ ((VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).instOuter ps) := by
    obtain ⟨w, hw⟩ := hMotT
    have hP' : OnCtx P.reverse (env.IsType U) := hctxP
    have := IsDefEq.closed_instOuter_congr henv hΔ hP' hw hTelP.1 hTelP.1
      (fun j hj _ hd => hTelP.2 j hj hd)
    rw [VExpr.instOuter_sort] at this
    exact ⟨w, this⟩
  rw [VExpr.motive_instOuter] at hMotI
  generalize hDdef : (I ++ [Maj]).mapIdx (fun k d => d.subst ((Subst.ofList ps).liftN k)) = Doms'
    at hMotI
  have hDl : Doms'.length = I.length + 1 := by rw [← hDdef]; simp
  obtain ⟨hctxM, -⟩ := IsType.wrapForalls_inv henv hΔ hMotI
  have hYM := hY.weakN henv.ordered (n := Doms'.length)
    (Ctx.LiftN.zero Doms'.reverse (Γ := Δ) (by simp))
  have hM : env.HasType U Δ (VExpr.wrapLams Doms' ((VExpr.app (.const ``Nonempty [u]) X).liftN
      Doms'.length)) (VExpr.wrapForalls Doms' (.sort .zero)) :=
    HasType.wrapLams_of hctxM (by simpa [VExpr.liftN] using hYM)
  generalize hMdef : VExpr.wrapLams Doms' ((VExpr.app (.const ``Nonempty [u]) X).liftN
      Doms'.length) = M at hM
  have hM' : env.HasType U Δ M ((VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).instOuter ps) := by
    rw [VExpr.motive_instOuter, hDdef]; exact hM
  -- the instantiated minor premise and its fields
  have hTelPMot := TelInst.append_one hTelP hM'
  obtain ⟨w, hMinw⟩ := hMinT
  have hMinI := IsDefEq.closed_instOuter_congr henv hΔ
    (doms := P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)])
    (by simpa using (show OnCtx (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero) :: P.reverse)
      (env.IsType U) from ⟨hctxP, hMotT⟩))
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append]; exact hMinw) hTelPMot.1 hTelPMot.1
    (fun j hj _ hd => hTelPMot.2 j hj hd)
  simp only [VExpr.instOuter_sort] at hMinI
  rw [← hMindef, VExpr.minor_instOuter] at hMinI
  generalize hF'def : F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i)) = F' at hMinI
  have hF'l : F'.length = F.length := by rw [← hF'def]; simp
  obtain ⟨hFctx, hBody⟩ := IsType.wrapForalls_inv henv hΔ ⟨_, hMinI⟩
  -- the constructor applied to the parameters and the field variables
  have hPps : P.length = ps.length := by rw [hPl, hpl]
  have hPFcl := OnCtx.closed_reverse henv.ordered hctxPF
  have hPcl := OnCtx.closed_reverse henv.ordered hctxP
  have hFcl : ∀ k (hk : k < F.length), (F[k]).ClosedN (P.length + k) := by
    intro k hk
    have := hPFcl (P.length + k) (by simp; omega)
    simpa [List.getElem_append_right] using this
  have hTelPF : TelInst env U (F'.reverse ++ Δ) (P ++ F)
      (ps.map (·.liftN F.length) ++ bvarRange F.length F.length) := by
    subst hF'def
    have hW := TelInst.weak henv.ordered
      (F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i))).reverse hPcl hTelP
    simp only [List.length_reverse, List.length_mapIdx] at hW
    refine TelInst.append hW (by simp) fun k hk => ?_
    rw [getD_of_lt (by simpa using hk), getD_of_lt hk, bvarRange_getElem _ _ _ hk,
      bvarRange_take _ _ _ (Nat.le_of_lt hk),
      VExpr.instOuter_params_bvarRange (by rw [← hPps]; exact hFcl k hk) (Nat.le_of_lt hk)]
    have hlk := Lookup.reverse_append (F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i)))
      Δ k (by simpa using hk)
    simp only [List.length_mapIdx, List.getElem_mapIdx] at hlk
    exact .bvar hlk
  have hdoms : P.length + F.length = doms.length := by
    rw [hPl, hFl, harity, harity0]
  have hctxD : IsDefEqCtx env U [] (P ++ F).reverse (doms.map (·.instL ls)).reverse := by
    have hdef' := hdefL
    rw [hshape0, VExpr.instL_wrapForalls] at hdef'
    have h := IsDefEqU.wrapForalls_context' henv (Γ₀ := []) trivial .zero
      (by simp [hdoms]) hdef'
    simpa using h
  have hTelD := TelInst.of_ctxDefEq henv hFctx hTelPF hctxD
  have hconst : env.HasType U (F'.reverse ++ Δ) (.const info.ctorName ls)
      (VExpr.wrapForalls (doms.map (·.instL ls)) (result.instL ls)) := by
    have := HasType.const (env := env) (U := U) (Γ := F'.reverse ++ Δ) hctorC hls hlslen
    rwa [hshape0, VExpr.instL_wrapForalls] at this
  have hc' := HasType.mkApps_of_tel henv hFctx hconst hTelD
  -- the field variable inhabits the binder (every projection the binder uses is a proof)
  have hwf' : env.IsType info.uvars [] info.ctorType := by
    rw [← hctorType, ← hdu]; exact hwf
  have hle : info.nparams ≤ doms.length := hdn ▸ hle0
  have hlenA' : (ps.map (·.liftN F.length) ++ bvarRange F.length F.length).length =
      doms.length := by simp [← hdoms, hPps]
  have hΓ'len : F'.reverse.length = F.length := by simp [hF'l]
  have hPA : List.Forall₂ (env.IsDefEqU U (F'.reverse ++ Δ))
      (ps.map (·.liftN F.length))
      ((ps.map (·.liftN F.length) ++ bvarRange F.length F.length).take info.nparams) := by
    rw [List.take_left' (by simp [hpl])]
    have hW := TelInst.weak henv.ordered F'.reverse hPcl hTelP
    rw [hΓ'len] at hW
    have key : ∀ (l : List VExpr), (∀ k (hk : k < l.length), env.IsDefEqU U
        (F'.reverse ++ Δ) l[k] l[k]) → List.Forall₂ (env.IsDefEqU U (F'.reverse ++ Δ)) l l := by
      intro l
      induction l with
      | nil => intro _; exact .nil
      | cons a as ih =>
        intro h
        exact .cons (h 0 (by simp)) (ih fun k hk => h (k + 1) (by simp; omega))
    exact key _ fun k hk => ⟨_, hW.2 k hk (by simp at hk; rw [hPps]; omega)⟩
  have he'L : env.HasType U (F'.reverse ++ Δ) (e'.liftN F.length)
      (VExpr.mkApps (.const S ls) (ps.map (·.liftN F.length) ++ idx.map (·.liftN F.length))) := by
    have := he'.weakN henv.ordered (Ctx.LiftN.zero F'.reverse (Γ := Δ) hΓ'len)
    simpa [VExpr.liftN_mkApps, VExpr.liftN] using this
  have hIA : (idx.map (·.liftN F.length)).length = info.nindices := by
    simp [hidxl, hIl, hIlen]
  have hdcl : ((doms[info.nparams + j]'hmd).instL ls).ClosedN (info.nparams + j) := by
    have := wrapForalls_closed_dom (n := 0)
      (by rw [← hshape0]; obtain ⟨_, h⟩ := hwf'; exact h.closedN henv.ordered trivial)
      (info.nparams + j) hmd
    simpa using this.instL
  have hXlift : X.liftN F.length =
      ((doms[info.nparams + j]'hmd).instL ls).instOuter
        (ps.map (·.liftN F.length) ++
          (List.range j).map fun k => VExpr.proj S k (e'.liftN F.length)) := by
    rw [← hXdef, VExpr.liftN_instOuter _ _ (by simpa [hpl] using hdcl)]
    simp [List.map_append, VExpr.liftN, Function.comp_def]
  have hXuL := hXu.weakN henv.ordered (Ctx.LiftN.zero F'.reverse (Γ := Δ) hΓ'len)
  have hlsE : List.Forall₂ (· ≈ ·) ls ls := VLevel.forall₂_equiv_refl ls
  have hfield := VProjectionInfo.field_of_walk (decl := decl) henv hinfo hwf' hctorC hshape0
    hvalid0 hhead0 hdn hdu hle hFctx hc' hlenA' hls hlsE hnz hPA hIA he'L hmd
    (by rw [← hXlift]; exact ⟨_, hXuL⟩)
  rw [← hXlift, List.getElem_append_right (by simp [hpl])] at hfield
  simp only [List.length_map, hpl, Nat.add_sub_cancel_left] at hfield
  have hjF : j < F.length := by omega
  rw [bvarRange_getElem _ _ _ hjF] at hfield
  -- the branch `Nonempty.intro field`
  have hIntro : env.HasType U (F'.reverse ++ Δ) (.const ``Nonempty.intro [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1)))) := by
    have := HasType.const (env := env) (U := U) (Γ := F'.reverse ++ Δ)
      (ls := [u]) hch.2.1 (by simpa using hu) rfl
    simpa [canonicalNonemptyIntroType, VExpr.instL, VLevel.inst] using this
  have hb1 := HasType.app hIntro hXuL
  simp [VExpr.inst, VExpr.instVar] at hb1
  have hbY := HasType.app hb1 hfield
  simp [VExpr.inst, VExpr.instVar] at hbY
  rw [VExpr.inst_liftN] at hbY
  -- `fun idx _ => Nonempty X` at the constructor's indices and application
  have hMF : env.HasType U (F'.reverse ++ Δ)
      (VExpr.wrapLams (Doms'.mapIdx fun l d => d.liftN F.length l)
        (((VExpr.app (.const ``Nonempty [u]) X).liftN Doms'.length).liftN F.length Doms'.length))
      (VExpr.wrapForalls (Doms'.mapIdx fun l d => d.liftN F.length l) (.sort .zero)) := by
    have := hM.weakN henv.ordered (Ctx.LiftN.zero F'.reverse (Γ := Δ) hΓ'len)
    rw [← hMdef, liftN_wrapLams, liftN_wrapForalls] at this
    simpa [VExpr.liftN] using this
  obtain ⟨_, hBody'⟩ := hBody
  have hMeq : M.liftN F.length = VExpr.wrapLams (Doms'.mapIdx fun l d => d.liftN F.length l)
      (((VExpr.app (.const ``Nonempty [u]) X).liftN Doms'.length).liftN F.length Doms'.length) := by
    rw [← hMdef, liftN_wrapLams]
  rw [hMeq] at hBody'
  have hlenM : (CI.map (fun e => e.subst ((Subst.ofList ps).liftN F.length)) ++
      [Ctor.subst ((Subst.ofList ps).liftN F.length)]).length =
      (Doms'.mapIdx fun l d => d.liftN F.length l).length := by
    simp [hDl, hCIl]
  obtain ⟨hargsM, -⟩ := HasType.mkApps_wrapForalls henv hFctx hMF ⟨_, hBody'⟩ hlenM
  have hβ := IsDefEq.mkApps_wrapLams henv hFctx hMF hlenM hargsM
  have hval : (((VExpr.app (.const ``Nonempty [u]) X).liftN Doms'.length).liftN F.length
      Doms'.length).instOuter (CI.map (fun e => e.subst ((Subst.ofList ps).liftN F.length)) ++
        [Ctor.subst ((Subst.ofList ps).liftN F.length)]) =
      .app (.const ``Nonempty [u]) (X.liftN F.length) := by
    have hc := VExpr.liftN'_comm (VExpr.app (.const ``Nonempty [u]) X) F.length Doms'.length 0 0
      (Nat.le_refl _)
    simp only [Nat.add_zero] at hc
    rw [← hc, show Doms'.length = (CI.map (fun e => e.subst ((Subst.ofList ps).liftN F.length)) ++
      [Ctor.subst ((Subst.ofList ps).liftN F.length)]).length by rw [hlenM]; simp,
      VExpr.instOuter_liftN]
    rfl
  rw [hval, VExpr.instOuter_sort] at hβ
  have hbM : env.HasType U (F'.reverse ++ Δ)
      (.app (.app (.const ``Nonempty.intro [u]) (X.liftN F.length)) (.bvar (F.length - 1 - j)))
      (VExpr.mkApps (M.liftN F.length) (CI.map (fun e => e.subst ((Subst.ofList ps).liftN F.length)) ++
        [Ctor.subst ((Subst.ofList ps).liftN F.length)])) := by
    rw [hMeq]
    exact .defeqDF hβ.symm hbY
  -- the minor premise
  have hm : env.HasType U Δ
      (VExpr.wrapLams F' (.app (.app (.const ``Nonempty.intro [u]) (X.liftN F.length))
        (.bvar (F.length - 1 - j))))
      (Min.instOuter (ps ++ [M])) := by
    rw [← hMindef, VExpr.minor_instOuter, hF'def]
    exact HasType.wrapLams_of hFctx hbM
  generalize hmdef : VExpr.wrapLams F' (.app (.app (.const ``Nonempty.intro [u])
    (X.liftN F.length)) (.bvar (F.length - 1 - j))) = mm at hm
  -- the eliminator applied to the parameters, the motive, the minor, the indices and the major
  have hTelPIM' : TelInst env U Δ (P ++ (I ++ [Maj])) (ps ++ (idx ++ [e'])) := by
    simpa [List.append_assoc] using hTelPIM
  have hBcl : ∀ k (hk : k < (I ++ [Maj]).length), ((I ++ [Maj])[k]).ClosedN (P.length + k) := by
    intro k hk
    have := hctxPIM (P.length + k) (by simp at hk ⊢; omega)
    simpa [List.append_assoc, List.getElem_append_right] using this
  have htel := TelInst.insert2 hTelPIM' hPps.symm hBcl hM' hm
  have hins : (I ++ [Maj]).mapIdx (fun k d => d.liftN 2 k) =
      insertBinders I 2 ++ [Maj.liftN 2 I.length] := by
    rw [← VEnv.insertBinders_eq_mapIdx]; simp [insertBinders, List.zipIdx_append]
  rw [hins, ← List.append_assoc] at htel
  have hheadΔ := HasType.weak0 henv.ordered (Γ := Δ) hhead
  rw [hrec] at hheadΔ
  have hNE := HasType.mkApps_of_tel henv hΔ hheadΔ htel
  have hv : vars I.length 1 ++ [VExpr.bvar 0] = bvarRange (I.length + 1) (I.length + 1) := by
    rw [vars_eq_bvarRange, CastSpec.bvarRange_append I.length 1 _ (by omega)]
    simp [bvarRange]
  have hargsl : (ps ++ [M] ++ [mm] ++ (idx ++ [e'])).length = P.length + I.length + 3 := by
    simp [hPps, hidxl]; omega
  rw [hv, VExpr.instOuter_mkApps, VExpr.instOuter_bvar _ (by rw [hargsl]; omega),
    instOuter_bvarRange _ _ _ (Nat.le_refl _) (by rw [hargsl]; omega)] at hNE
  have hhd : ∀ hb, (ps ++ [M] ++ [mm] ++ (idx ++ [e']))[
      (ps ++ [M] ++ [mm] ++ (idx ++ [e'])).length - 1 - (I.length + 2)]'hb = M := by
    intro hb
    simp only [hargsl, show P.length + I.length + 3 - 1 - (I.length + 2) = ps.length by omega]
    simp
  have htl : ((ps ++ [M] ++ [mm] ++ (idx ++ [e'])).drop
        ((ps ++ [M] ++ [mm] ++ (idx ++ [e'])).length - (I.length + 1))).take (I.length + 1) =
        idx ++ [e'] := by
    rw [hargsl, show P.length + I.length + 3 - (I.length + 1) = (ps ++ [M] ++ [mm]).length by
      simp [hPps]; omega, List.drop_left]
    exact List.take_of_length_le (by simp [hidxl])
  simp only [hhd, htl] at hNE
  -- `M idx e'` reduces to `Nonempty X`
  have hlenD : (idx ++ [e']).length = Doms'.length := by simp [hidxl, hDl]
  have hargsD : ∀ k (hk : k < (idx ++ [e']).length) (hk' : k < Doms'.length),
      env.HasType U Δ (idx ++ [e'])[k] (Doms'[k].instOuter ((idx ++ [e']).take k)) := by
    intro k hk hk'
    subst hDdef
    have hk2 : k < (I ++ [Maj]).length := by simpa using hk'
    have hk3 : k < (idx ++ [e']).length := hk
    have hT := hTelPIM'.2 (ps.length + k) (by simp at hk ⊢; omega) (by simp at hk ⊢; omega)
    have e1 : (ps ++ (idx ++ [e']))[ps.length + k]'(by simp at hk ⊢; omega) =
        (idx ++ [e'])[k] := by
      rw [List.getElem_append_right (by omega)]; congr 1; omega
    have e2 : (P ++ (I ++ [Maj]))[ps.length + k]'(by simp at hk ⊢; omega) =
        (I ++ [Maj])[k] := by
      rw [List.getElem_append_right (by omega)]; congr 1; omega
    have e3 : (ps ++ (idx ++ [e'])).take (ps.length + k) = ps ++ (idx ++ [e']).take k := by
      rw [List.take_append, List.take_of_length_le (by omega)]; simp
    rw [e1, e2, e3] at hT
    rw [List.getElem_mapIdx]
    have hcl := hBcl k hk2
    rw [hPps] at hcl
    have htk : ((idx ++ [e']).take k).length = k := by simp; omega
    have heq := VExpr.subst_liftN_instOuter (ps := ps) (bs := (idx ++ [e']).take k)
      (by rw [htk]; exact hcl)
    rw [htk] at heq
    rw [heq]; exact hT
  have hMfull := hM
  rw [← hMdef] at hMfull
  have hβ2 := IsDefEq.mkApps_wrapLams henv hΔ hMfull hlenD hargsD
  rw [← hlenD, VExpr.instOuter_liftN, VExpr.instOuter_sort, hlenD, hMdef] at hβ2
  have hNE' := IsDefEq.defeqDF hβ2 hNE
  -- `Classical.choice`
  have hCh : env.HasType U Δ (.const ``Classical.choice [u])
      (.forallE (.sort u) (.forallE (.app (.const ``Nonempty [u]) (.bvar 0)) (.bvar 1))) := by
    have := HasType.const (env := env) (Γ := Δ) (ls := [u]) hch.2.2 (by simpa using hu) rfl
    simpa [canonicalChoiceType, VExpr.instL, VLevel.inst] using this
  have hd1 := HasType.app hCh hXu
  simp [VExpr.inst, VExpr.instVar] at hd1
  have hd := HasType.app hd1 hNE'
  rw [VExpr.inst_liftN] at hd
  exact ⟨_, hd.defeqU_r henv hΔ hDXd.symm⟩

end VEnv
end Lean4Lean
