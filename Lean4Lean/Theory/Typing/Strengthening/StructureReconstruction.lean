import Lean4Lean.Theory.Typing.UnitLikeConstructor
import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Reconstructing a structure from its dependent projections

The reconstruction must type every field along the actual constructor telescope.
Projection admissibility is kept explicit: a merely nonzero universe expression
is not necessarily never zero, and non-proof fields of a Prop structure cannot
be projected. No strengthening theorem is used.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Prefixes of the parameter-and-projection spine stop at the corresponding field. -/
theorem projection_args_take (hp : params.length = nparams) (hi : index ≤ fields) :
    (params ++ (List.range fields).map (fun j => VExpr.proj family j major)).take (nparams + index) =
      params ++ (List.range index).map (fun j => VExpr.proj family j major) := by
  rw [List.take_append]
  simp [hp, List.take_of_length_le (show params.length ≤ nparams + index by omega),
    ← List.map_take, List.take_range, Nat.min_eq_left hi]

/-- All arguments of a reconstructed constructor are typed in their dependent
positions. The field guard is checked at the type reconstructed from earlier fields. -/
theorem projection_args_typed (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hlevels : ∀ l ∈ levels, l.WF U)
    (hlevelCount : levels.length = info.uvars)
    (hshape : info.ctorType = wrapForalls doms result)
    (hdomlen : doms.length = info.nparams + info.numFields)
    (hmajor : env.HasType U Γ major (mkApps (.const family levels) params))
    (hparams : ∀ k (hk : k < params.length) (hk' : k < doms.length),
      env.HasType U Γ params[k] ((doms[k].instL levels).instOuter (params.take k)))
    (hguard : ∀ index F u, index < info.numFields →
      info.fieldType family levels params index major = some F → env.HasType U Γ F (.sort u) →
      (info.resultLevel.inst levels).IsNeverZero ∨ u ≈ .zero) :
    ∀ j (hj : j < (params ++ (List.range info.numFields).map (fun i => VExpr.proj family i major)).length)
      (hj' : j < doms.length),
      env.HasType U Γ (params ++ (List.range info.numFields).map (fun i => VExpr.proj family i major))[j]
        ((doms[j].instL levels).instOuter
          ((params ++ (List.range info.numFields).map (fun i => VExpr.proj family i major)).take j)) := by
  let args := params ++ (List.range info.numFields).map (fun i => VExpr.proj family i major)
  have hargsLen : args.length = doms.length := by simp [args, hp, hdomlen]
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hinfo) hlevels hlevelCount
  rw [hshape, instL_wrapForalls] at hctor
  have hctx := (IsType.wrapForalls_inv henv hΓ (hctor.isType henv.ordered hΓ)).1
  have hclosed : info.ctorType.Closed := by
    obtain ⟨_, ht⟩ := henv.ordered.constWF (henv.ordered.projectionConstructor hinfo)
    exact ht.closedN henv.ordered (by trivial)
  intro j
  induction j using Nat.strongRecOn with
  | ind j ihj =>
    intro hj hj'
    by_cases hjp : j < params.length
    · have ht := hparams j hjp hj'
      simpa only [List.getElem_append_left hjp, List.take_append_of_le_length (Nat.le_of_lt hjp)] using ht
    · have hji : j - info.nparams < info.numFields := by omega
      have hdom := hctx.reverse_getElem j (by simpa using hj')
      have hF := hdom.instOuter_telescope henv (args := args.take j)
        (by simp [hargsLen]) (by
          intro k hk hk'
          simp only [List.length_take] at hk hk'
          have ht := ihj k (by omega) (by change k < args.length; omega) (by omega)
          simpa only [List.getElem_take, List.getElem_map, List.take_take,
            Nat.min_eq_left (show k ≤ j by omega)] using ht)
      obtain ⟨u, hF⟩ := hF
      simp only [List.getElem_map] at hF
      have htake : args.take j = params ++ (List.range (j - info.nparams)).map
          (fun i => VExpr.proj family i major) := by
        have := projection_args_take (family := family) (major := major) hp (Nat.le_of_lt hji)
        simpa only [Nat.add_sub_of_le (show info.nparams ≤ j by omega)] using this
      have hfield := info.fieldType_eq_instOuter (typeName := family) (major := major)
        hshape hlevelCount hp (index := j - info.nparams) (by omega)
      simp only [Nat.add_sub_of_le (show info.nparams ≤ j by omega), ← htake] at hfield
      have hm : env.HasType U Γ major (mkApps (.const family levels) (params ++ [])) := by
        simpa only [List.append_nil] using hmajor
      have ht : env.HasType U Γ (.proj family (j - info.nparams) major)
          ((doms[j].instL levels).instOuter (args.take j)) :=
        .projDF hinfo hlevels hlevelCount hp (by simpa using hi.symm) hfield hF hm hm hclosed
          (hguard _ _ _ hji hfield hF)
      simpa only [List.getElem_append_right (as := params) (i := j) (by omega), hp, List.getElem_map,
        List.getElem_range] using ht

/-- Reconstruct a registered structure at its actual parameter instance whenever
its dependent projections satisfy the projection guard. Parameter agreement is
recovered from the declaration, extending `HasType.unitLike_constructor`. -/
theorem structure_constructor (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0)
    (H : env.HasType U Γ major (mkApps (.const name levels) params))
    (hguard : ∀ index F u, index < info.numFields →
      info.fieldType name levels params index major = some F → env.HasType U Γ F (.sort u) →
      (info.resultLevel.inst levels).IsNeverZero ∨ u ≈ .zero) :
    env.HasType U Γ (structExpand name info levels params major)
      (mkApps (.const name levels) params) := by
  obtain ⟨decl, family, ctor, hfamily, hctorMem, hname, hctorUvars, huvars,
    hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
    ⟨common, Hshape, Hparams⟩, Hraw, hnodup⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  have hdomle : info.nparams ≤ doms.length := by omega
  have hdomlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hresultWF := hwf
  rw [hshape] at hresultWF
  obtain ⟨hdomctx, _, hresult⟩ := IsType.wrapForalls_inv henv (by trivial) hresultWF
  have hresultShape : result = mkApps (.const family.name (VLevel.params decl.uvars))
      result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (VExpr.mkApps_getAppFnArgs_eq result).symm
  have hresult' := hresult
  rw [hresultShape] at hresult'
  obtain ⟨_, hfamilyHead⟩ := VExpr.WF.of_mkApps henv hdomctx ⟨_, hresult'⟩
  obtain ⟨ci, hci, _, hcount⟩ := HasType.const_inv henv hdomctx hfamilyHead
  rw [hname, hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : family.uvars = decl.uvars := by simpa using hcount.symm
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType,
    hnorm, hown, hidx, HownP, hres⟩ := Hshape
  obtain ⟨ctorParams, tail, hctorParams, HctorP⟩ := Hparams
  have hownLen : ownParams.length = info.nparams :=
    (VExpr.takeForalls_domains_length hown).trans hnparams
  have hidxLen : indices.length = 0 :=
    (VExpr.takeForalls_domains_length hidx).trans (hindices.trans hi)
  have hidxNil : indices = [] := List.eq_nil_of_length_eq_zero hidxLen
  subst indices
  have hnormEq : normalized = wrapForalls ownParams result' := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown,
      VExpr.eq_wrapForalls_of_takeForalls hidx]
    rfl
  have hctorParamsEq : ctorParams = doms.take info.nparams := by
    have h1 := VExpr.takeForalls_wrapForalls (doms.take info.nparams)
      (wrapForalls (doms.drop info.nparams) result)
    have hsplit : wrapForalls doms result = wrapForalls (doms.take info.nparams)
        (wrapForalls (doms.drop info.nparams) result) := by
      rw [← wrapForalls_append, List.take_append_drop]
    have h2 := hctorParams
    rw [hshape, hnparams, hsplit] at h2
    simp only [List.length_take, Nat.min_eq_left hdomle] at h1
    exact (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).1
  have hctx : env.IsDefEqCtx decl.uvars [] ownParams.reverse (doms.take info.nparams).reverse := by
    rw [← hctorParamsEq]
    exact IsDefEqCtx.trans_empty henv (HownP.symm henv.ordered) HctorP
  have htypeWF : env.IsType decl.uvars [] family.type := by
    have ht := henv.ordered.constWF hlookup
    change env.IsType family.uvars [] family.type at ht
    rwa [hfamilyUvars] at ht
  have hnormWF : env.IsType decl.uvars [] normalized :=
    let ⟨u, h⟩ := htypeWF
    ⟨u, h.defeqU_l henv (by trivial) ⟨_, hnorm⟩⟩
  rw [hnormEq] at hnormWF
  have hΓtel := (IsType.wrapForalls_inv henv (by trivial) hnormWF).1
  simp only [List.append_nil] at hΓtel
  obtain ⟨u, hsort⟩ := H.isType henv.ordered hΓ
  obtain ⟨_, hcw⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsort⟩
  obtain ⟨ci', hci', hlsw, hlen'⟩ := HasType.const_inv henv hΓ hcw
  rw [hlookup] at hci'
  cases Option.some.inj hci'
  have hlevels : levels.length = info.uvars := by
    exact hlen'.trans (hfamilyUvars.trans huvars)
  have hc := HasType.const (Γ := Γ) hlookup hlsw hlen'
  have hdef : env.IsDefEqU U Γ (family.type.instL levels) (normalized.instL levels) :=
    ⟨_, (hnorm.instL hlsw).weak0 henv.ordered⟩
  have hc' := hc.defeqU_r henv hΓ hdef
  rw [hnormEq, instL_wrapForalls] at hc'
  obtain ⟨hargsT, _⟩ := HasType.mkApps_wrapForalls henv hΓ hc' ⟨_, hsort⟩
    (by simp only [List.length_map]; omega)
  have hparams : ∀ k (hk : k < params.length) (hk' : k < doms.length),
      env.HasType U Γ params[k] ((doms[k].instL levels).instOuter (params.take k)) := by
    intro k hk hk'
    have hkown : k < ownParams.length := by omega
    obtain ⟨u, hdk⟩ := hctx.reverse_getElem k hkown (by simp; omega)
    simp only [List.getElem_take] at hdk
    have hΔ₀ : OnCtx (ownParams.take k).reverse (env.IsType decl.uvars) := by
      have he : ownParams.reverse = (ownParams.drop k).reverse ++ (ownParams.take k).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      rw [he] at hΓtel
      exact hΓtel.of_append
    have hconv := IsDefEqU.closed_telescope_instOuter henv hΔ₀ ⟨_, hdk⟩ hlsw
      (args := params.take k) (by simp; omega) (by
        intro j hj hj'
        simp only [List.length_take] at hj
        have ht := hargsT j (by omega) (by simp; omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take,
          List.take_take, Nat.min_eq_left (Nat.le_of_lt (show j < k by omega))] at ht ⊢
        exact ht)
    have harg := hargsT k hk (by simpa using hkown)
    simp only [List.getElem_map] at harg
    exact harg.defeqU_r henv hΓ hconv
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hinfo) hlsw hlevels
  rw [← hctorType, hshape, instL_wrapForalls] at hctor
  let args := params ++ (List.range info.numFields).map (fun i => VExpr.proj name i major)
  have hargsLen : args.length = doms.length := by simp [args, hp, hdomlen]
  have hargs := projection_args_typed henv hΓ hinfo hp hi hlsw hlevels
    (hctorType ▸ hshape) hdomlen H hparams hguard
  have hvalue := HasType.mkApps_of_telescope (args := args) hctor
    (by simp only [List.length_map]; exact hargsLen)
    (by simpa only [List.getElem_map, List.length_map] using hargs)
  have hhead' : (result.instL levels).getAppFnArgs.1 = .const name levels := by
    rw [VExpr.getAppFnArgs_instL]
    change result.getAppFnArgs.1.instL levels = _
    rw [hhead, hname]
    simp [VExpr.instL, VLevel.params_map_inst levels (hlevels.trans huvars.symm)]
  obtain ⟨idx, hresEq, family', hfamily', hname', hidxCount⟩ :=
    (hvalid.instL levels).instOuter (by simpa only [hname] using hhead') args (by omega)
  have hsame : family' = family := List.eq_of_mem_of_nodup_map
    (VInductDecl.typeNames_nodup hnodup) hfamily' hfamily (by simpa only [hname] using hname')
  have hidxEmpty : idx = [] := List.eq_nil_of_length_eq_zero (by rw [hidxCount, hsame, hindices, hi])
  rw [hresEq, hidxEmpty, List.append_nil, hname] at hvalue
  have htake : args.take decl.nparams = params := by
    rw [hnparams, ← hp]
    exact List.take_append_length
  rw [htake] at hvalue
  exact hvalue


/-- Every registered unindexed structure in a never-zero source universe can
be reconstructed from its projections, using source typing alone. -/
theorem structure_constructor_neverZero (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hz : (info.resultLevel.inst levels).IsNeverZero)
    (H : env.HasType U Γ major (mkApps (.const name levels) params)) :
    env.HasType U Γ (structExpand name info levels params major)
      (mkApps (.const name levels) params) :=
  structure_constructor henv hΓ hinfo hp hi H (fun _ _ _ _ _ _ => .inl hz)

/-- The newly reconstructed constructor licenses an actual typed eta equation;
no typing of the expanded endpoint is assumed. -/
theorem structure_eta_neverZero (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hz : (info.resultLevel.inst levels).IsNeverZero)
    (H : env.HasType U Γ major (mkApps (.const name levels) params)) :
    env.IsDefEq U Γ major (structExpand name info levels params major)
      (mkApps (.const name levels) params) :=
  (IsDefEq.structEta hinfo hp hi H (structure_constructor_neverZero henv hΓ hinfo hp hi hz H)).symm

end Lean4Lean.VEnv.Strengthening.StructureReplay
