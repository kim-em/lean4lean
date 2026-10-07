import Lean4Lean.Theory.Typing.ProjectionCornerNonempty
import Lean4Lean.Theory.Typing.ProjectionCornerSubst

/-! # The recursor of an ordinary structure applied in an arbitrary context -/

namespace Lean4Lean
open VExpr

namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s)

/-- The recursor type of an ordinary declaration with one constructor and no indices,
eliminating into `Prop`. -/
theorem ordinary_recursorType (hfam : s.families.size = 1) (hcs : s.constructors.size = 1)
    (owner : Fin s.families.size) (index : Fin s.constructors.size)
    {c : Constructor s.families.size} (hc : s.constructors[index] = c) (hown : c.owner = owner)
    (htarget : g.targetLevel = .zero) (hI : s.families[owner].indices = [])
    (hCI : c.indices = []) :
    g.recursorType owner =
      VExpr.wrapForalls (g.params ++ [.forallE (g.sMajor owner) (.sort .zero)] ++
          [VExpr.wrapForalls (insertBinders (g.sFields c) 1 ++ g.sHyps c)
            (VExpr.mkApps (.bvar ((g.sFields c).length + (g.sHyps c).length))
              [((g.sCtorApp c).liftN (g.sHyps c).length).liftN 1
                ((g.sFields c).length + (g.sHyps c).length)])] ++
          [(g.sMajor owner).liftN 2])
        (.app (.bvar 2) (.bvar 0)) := by
  have hown0 : c.owner.val = 0 := by
    have := c.owner.isLt; omega
  have hrec := g.recursorType_shape hfam hcs owner index
  rw [hc] at hrec
  rw [g.motive_shape owner htarget, g.minor_shape hfam _ hown0, g.major_lift owner,
    g.constructorApp_shape] at hrec
  rw [hrec]
  have hI' : g.sIndices owner = [] := by
    unfold sIndices; rw [hI]; rfl
  have hCI' : g.sCtorIndices c = [] := by simp [sCtorIndices, hCI]
  simp only [hI', hCI', insertBinders, List.zipIdx_nil, List.map_nil, List.append_nil,
    List.nil_append, List.length_nil, Nat.zero_add, vars, List.range_zero, List.reverse_nil]
  rfl

end InductiveSignature.Instance

namespace InductiveSignature.NativeRecursorData

/-- A registered native recursor's constructors carry their family's index count. -/
theorem NativeRecursorRegistered.ctor_indices_length {env : VEnv} {data : NativeRecursorData}
    (H : VEnv.NativeRecursorRegistered env data) :
    ∀ c ∈ data.schema.signature.constructors.toList,
      c.indices.length = data.schema.signature.families[c.owner].indices.length := by
  obtain ⟨_, _, _, _, _, _, _, _, hdata, _⟩ := H
  exact hdata.model.constructorArity

end InductiveSignature.NativeRecursorData

namespace VEnv
open InductiveSignature
variable {env : VEnv} {U : Nat}

/-- The elimination into `Prop` of a registered structure `S` used by the projection-walk corner:
`S` is the single family of an ordinary (one-family, one-constructor) native declaration
without indices, whose recursor is registered; its constructor is the projection metadata's
constructor with the declaration's field count; and the recursor can be instantiated with
motive universe zero at universe levels whose family levels are equivalent to `ls`. -/
def StructurePropRecursor (env : VEnv) (U : Nat) (S : Name) (info : VProjectionInfo)
    (ls : List VLevel) : Prop :=
  ∃ (data : NativeRecursorData) (ls0 : List VLevel)
    (i : Fin data.schema.signature.constructors.size),
    NativeRecursorRegistered env data ∧
    data.schema.signature.families.size = 1 ∧ data.schema.signature.constructors.size = 1 ∧
    data.schema.signature.families[data.owner].name = S ∧
    data.schema.signature.families[data.owner].indices = [] ∧
    data.schema.signature.constructors[i].name = info.ctorName ∧
    data.schema.signature.params.length = info.nparams ∧
    info.nparams + data.schema.signature.constructors[i].fields.length =
      info.ctorType.forallArity ∧
    (∀ l ∈ ls0, l.WF U) ∧ ls0.length = data.uvars ∧ data.target.inst ls0 = .zero ∧
    List.Forall₂ (· ≈ ·) (data.levels.map (·.inst ls0)) ls

theorem forall₂_map_map {f g : VExpr → VExpr} {R : VExpr → VExpr → Prop} :
    ∀ {l : List VExpr}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (.head _)) (forall₂_map_map fun x hx => h x (.tail _ hx))

theorem LEquiv.mkApps_fn {f f' : VExpr} (H : VExpr.LEquiv U f f') :
    ∀ (args : List VExpr), VExpr.LEquiv U (VExpr.mkApps f args) (VExpr.mkApps f' args)
  | [] => H
  | _ :: as => LEquiv.mkApps_fn (.app H .refl) as

theorem instOuterAt_sort (u : VLevel) :
    ∀ (args : List VExpr) (k : Nat), (VExpr.sort u).instOuterAt args k = .sort u
  | [], _ => rfl
  | _ :: as, k => instOuterAt_sort u as k

theorem forall₂_equiv_symm :
    ∀ {l l' : List VLevel}, List.Forall₂ (· ≈ ·) l l' → List.Forall₂ (· ≈ ·) l' l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (Eq.symm h) (forall₂_equiv_symm t)

theorem corner_inhabit (henv : env.WF) (hch : env.HasCanonicalChoice)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {T₀ : VExpr} (hT₀ : VExpr.LEquiv U T₀ (info.ctorType.instL ls))
    {ps idx : List VExpr} (hpl : ps.length = info.nparams) (hni : info.nindices = 0)
    {e' : VExpr} (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx)))
    {j : Nat} {D body' : VExpr}
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (ps ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : env.IsType U Δ D)
    (hguard : ∀ u, env.HasType U Δ D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    (hrec : StructurePropRecursor env U S info ls) :
    ∃ d, env.HasType U Δ d D := by
  obtain ⟨data, ls0, i, H, hfam, hcs, hSname, hI, hcname, hnp, harity, hls0, hls0len, htgt,
    hlev⟩ := hrec
  -- the structure's constructor
  obtain ⟨decl, type, ctor, -, -, hname, -, hdu, hdn, -, -, -, hctorType, -, hwf, -, Hraw, -⟩ :=
    Ordered.projectionShape henv.ordered hinfo
  obtain ⟨doms, result, hshape0, hle0, hvalid0, hhead0, harity0⟩ := Hraw.forallArity
  rw [hctorType] at hshape0 harity0
  rw [hname] at hvalid0 hhead0
  have hctorC := Ordered.projectionConstructor henv.ordered hinfo
  obtain ⟨hrecC, hcu, envTypes, hET, hdef0⟩ := NativeRecursorData.NativeRecursorRegistered.ordinary H hfam hcs i hcname hctorC
  have hdef : env.IsDefEqU data.schema.signature.uvars []
      (data.schema.signature.constructorType data.schema.signature.constructors[i])
      info.ctorType := hdef0.mono hET
  have hdoms : info.nparams + data.schema.signature.constructors[i].fields.length =
      doms.length := by rw [harity, harity0]
  -- the recursor at motive universe zero
  let gp := data.nativeInstance.specialize U ls0
  have htarget : gp.targetLevel = .zero := htgt
  have hgpl : gp.levels = data.levels.map (·.inst ls0) := rfl
  have hgpwf : ∀ l ∈ gp.levels, l.WF U := by
    intro l hl
    rw [hgpl, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact VLevel.WF.inst hls0
  have hhead : env.HasType U [] (.const data.name ls0) (gp.recursorType data.owner) := by
    have := HasType.const (env := env) (Γ := []) hrecC hls0 (by simp [hls0len])
    rwa [Instance.recursorType_specialize _ U] at this
  obtain ⟨c, hc⟩ : ∃ c, data.schema.signature.constructors[i] = c := ⟨_, rfl⟩
  have hown : c.owner = data.owner := by
    ext; have := c.owner.isLt; have := data.owner.isLt; omega
  have hCI : c.indices = [] := by
    have := NativeRecursorData.NativeRecursorRegistered.ctor_indices_length H c
      (hc ▸ Array.getElem_mem_toList ..)
    simp only [hown] at this
    have h0 : data.schema.signature.families[data.owner].indices.length = 0 := by rw [hI]; rfl
    exact List.eq_nil_of_length_eq_zero (this.trans h0)
  have hR := gp.ordinary_recursorType hfam hcs data.owner i hc hown htarget hI hCI
  -- the recursor's telescope
  have HR : env.IsType U [] (gp.recursorType data.owner) := hhead.isType henv.ordered trivial
  rw [hR] at HR
  have hpeel := (IsType.wrapForalls_inv henv (Γ := []) trivial HR).1
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_nil, List.singleton_append, List.cons_append] at hpeel
  obtain ⟨⟨⟨hP, hMotT⟩, hMinT⟩, -⟩ := hpeel
  have hMajT := (IsType.forallE_inv henv.ordered hMotT).1
  have hMotCtx : OnCtx (VExpr.forallE (gp.sMajor data.owner) (.sort .zero) :: gp.params.reverse)
      (env.IsType U) := ⟨hP, hMotT⟩
  have hMinInv := IsType.wrapForalls_inv henv hMotCtx hMinT
  have hall : OnCtx (gp.params ++ [VExpr.forallE (gp.sMajor data.owner) (.sort .zero)] ++
      insertBinders (gp.sFields c) 1 ++ gp.sHyps c).reverse (env.IsType U) := by
    simpa [List.append_assoc] using hMinInv.1
  have hallcl := OnCtx.closed_reverse henv.ordered hall
  have hFcl : ∀ k (hk : k < (gp.sFields c).length),
      ((gp.sFields c)[k]).ClosedN (gp.params.length + k) := by
    intro k hk
    have := hallcl (gp.params.length + 1 + k) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
      getElem_insertBinders (by simp; omega)] at this
    simp only [List.length_append, List.length_singleton,
      show gp.params.length + 1 + k - (gp.params.length + 1) = k by omega] at this
    exact VExpr.ClosedN.of_liftN (k := gp.params.length + k)
      (by simpa [Nat.add_right_comm] using this) (by omega)
  have hPcl := OnCtx.closed_reverse henv.ordered hP
  have hPlen : gp.params.length = info.nparams := by
    simp [Instance.params, hnp]
  -- the parameters along the recursor's parameter telescope
  obtain ⟨hidx, ctorParams, tail, hctorP, hTel⟩ :=
    HasType.structure_params henv hΔ hinfo hls hni hpl he'
  subst hidx
  rw [← hnp] at hctorP
  have hTel2 := TelInst.signature_params henv hΔ hls hctorP hdef hTel
  have hlsE : List.Forall₂ (· ≈ ·) ls gp.levels := forall₂_equiv_symm hlev
  have hTelP : TelInst env U Δ gp.params ps :=
    TelInst.of_lequiv henv hΔ hTel2 (forall₂_map_map fun x _ =>
      VExpr.LEquiv.instL_expr x hls hgpwf hlsE)
  -- the major premise
  have hMajEq : gp.sMajor data.owner =
      VExpr.mkApps (.const S gp.levels) (bvarRange ps.length ps.length) := by
    have hv := vars_eq_bvarRange data.schema.signature.params.length 0
    simp only [Nat.add_zero] at hv
    simp only [Instance.sMajor]
    rw [hSname, hI]
    simp only [List.length_nil, vars, List.range_zero, List.reverse_nil, List.map_nil,
      List.append_nil]
    have hv' := vars_eq_bvarRange data.schema.signature.params.length 0
    simp only [vars, Nat.add_zero] at hv'
    rw [hv', hpl, hnp]
  have he'' : env.HasType U Δ e' ((gp.sMajor data.owner).instOuter ps) := by
    rw [hMajEq, instOuter_bvarRange_apps (f := .const S gp.levels) trivial]
    rw [List.append_nil] at he'
    obtain ⟨_, hTy⟩ := he'.isType henv.ordered hΔ
    exact he'.defeqU_r henv hΔ (VExpr.LEquiv.defeq henv hΔ
      (LEquiv.mkApps_fn (.const hlsE hgpwf) ps) ⟨_, hTy⟩)
  have hTelPM := TelInst.append_one hTelP he''
  -- the binder reached by the walk
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
  -- the motive `fun _ => Nonempty X`
  have hNe : env.HasType U Δ (.const ``Nonempty [u]) (.forallE (.sort u) (.sort .zero)) := by
    have := HasType.const (env := env) (Γ := Δ) (ls := [u]) hch.1 (by simpa using hu) rfl
    simpa [canonicalNonemptyType, VExpr.instL, VLevel.inst] using this
  have hY : env.HasType U Δ (.app (.const ``Nonempty [u]) X) (.sort .zero) := by
    simpa [VExpr.inst] using HasType.app hNe hXu
  obtain ⟨v, hA⟩ := he''.isType henv.ordered hΔ
  have hAeq : (gp.sMajor data.owner).instOuter ps = VExpr.mkApps (.const S gp.levels) ps := by
    rw [hMajEq, instOuter_bvarRange_apps (f := .const S gp.levels) trivial]
  rw [hAeq] at hA he''
  have hM : env.HasType U Δ
      (.lam (VExpr.mkApps (.const S gp.levels) ps) (VExpr.app (.const ``Nonempty [u]) X).lift)
      ((VExpr.forallE (gp.sMajor data.owner) (.sort .zero)).instOuter ps) := by
    rw [VExpr.instOuter_forallE, hAeq]
    have := HasType.lam hA (hY.weak henv.ordered (B := VExpr.mkApps (.const S gp.levels) ps))
    simpa [instOuterAt_sort, VExpr.liftN] using this
  -- the instantiated minor premise and its fields
  have hTelPMot := TelInst.append_one hTelP hM
  obtain ⟨w, hMinw⟩ := hMinT
  have hMinI := IsDefEq.closed_instOuter_congr henv hΔ
    (doms := gp.params ++ [VExpr.forallE (gp.sMajor data.owner) (.sort .zero)])
    (by simpa using hMotCtx)
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append]; exact hMinw) hTelPMot.1 hTelPMot.1
    (fun j hj _ hd => hTelPMot.2 j hj hd)
  simp only [VExpr.instOuter_sort] at hMinI
  rw [VExpr.minor_instOuter] at hMinI
  have hFHctx := (IsType.wrapForalls_inv henv hΔ ⟨_, hMinI⟩).1
  rw [List.reverse_append, List.append_assoc] at hFHctx
  have hFctx := OnCtx.of_append hFHctx
  -- the constructor applied to the parameters and the field variables
  have hnF : (gp.sFields c).length = c.fields.length := by
    simp [Instance.sFields, InductiveSignature.fieldTypes]
  have hPps : gp.params.length = ps.length := by rw [hPlen, hpl]
  have hTelPF : TelInst env U
      (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (gp.params ++ gp.sFields c)
      (ps.map (·.liftN (gp.sFields c).length) ++
        bvarRange (gp.sFields c).length (gp.sFields c).length) := by
    have hW := TelInst.weak henv.ordered
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse
      hPcl hTelP
    simp only [List.length_reverse, List.length_mapIdx] at hW
    refine TelInst.append hW (by simp) fun k hk => ?_
    rw [getD_of_lt (by simpa using hk), getD_of_lt hk, bvarRange_getElem _ _ _ hk,
      bvarRange_take _ _ _ (Nat.le_of_lt hk),
      VExpr.instOuter_params_bvarRange (by rw [← hPps]; exact hFcl k hk) (Nat.le_of_lt hk)]
    have hlk := Lookup.reverse_append
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)) Δ k
      (by simpa using hk)
    simp only [List.length_mapIdx, List.getElem_mapIdx] at hlk
    exact .bvar hlk
  -- along the constructor's own telescope
  have hlenPF : (data.schema.signature.params ++ data.schema.signature.fieldTypes c).length =
      doms.length := by
    have hdoms' : info.nparams + c.fields.length = doms.length := hc ▸ hdoms
    simp [InductiveSignature.fieldTypes, ← hdoms', hnp]
  have hctxD : IsDefEqCtx env U [] (gp.params ++ gp.sFields c).reverse
      (doms.map (·.instL gp.levels)).reverse := by
    have hdef' := hdef
    rw [hc, InductiveSignature.constructorType, hshape0] at hdef'
    have h := IsDefEqU.wrapForalls_context' henv (Γ₀ := []) trivial .zero hlenPF hdef'
    simp only [List.append_nil] at h
    have h' := IsDefEqCtx.instL hgpwf h
    simpa [List.map_reverse, Instance.params, Instance.sFields] using h'
  have hTelD := TelInst.of_ctxDefEq henv hFctx hTelPF hctxD
  have hgplen : gp.levels.length = info.uvars := by
    rw [← List.Forall₂.length_eq hlsE, hlslen]
  have hconst : env.HasType U
      (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (.const info.ctorName gp.levels)
      (VExpr.wrapForalls (doms.map (·.instL gp.levels)) (result.instL gp.levels)) := by
    have := HasType.const (env := env) (U := U)
      (Γ := ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      hctorC hgpwf hgplen
    rwa [hshape0, VExpr.instL_wrapForalls] at this
  have hc' := HasType.mkApps_of_tel henv hFctx hconst hTelD
  -- the field variable inhabits the binder (every projection the binder uses is a proof)
  have hwf' : env.IsType info.uvars [] info.ctorType := by
    rw [← hctorType, ← hdu]; exact hwf
  have hle : info.nparams ≤ doms.length := hdn ▸ hle0
  have hlenA : (ps.map (·.liftN (gp.sFields c).length) ++
      bvarRange (gp.sFields c).length (gp.sFields c).length).length = doms.length := by
    have hdoms' : info.nparams + c.fields.length = doms.length := hc ▸ hdoms
    simp [hpl, hnF, ← hdoms']
  have hΓ'len : (((gp.sFields c).mapIdx fun i d =>
      d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse).length = (gp.sFields c).length := by
    simp
  have hPA : List.Forall₂ (env.IsDefEqU U
        (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ))
      (ps.map (·.liftN (gp.sFields c).length))
      ((ps.map (·.liftN (gp.sFields c).length) ++
        bvarRange (gp.sFields c).length (gp.sFields c).length).take info.nparams) := by
    rw [List.take_left' (by simp [hpl])]
    have hW := TelInst.weak henv.ordered
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse
      hPcl hTelP
    rw [hΓ'len] at hW
    have key : ∀ (l : List VExpr), (∀ k (hk : k < l.length), env.IsDefEqU U
        (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
        l[k] l[k]) → List.Forall₂ (env.IsDefEqU U
        (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ))
        l l := by
      intro l
      induction l with
      | nil => intro _; exact .nil
      | cons a as ih =>
        intro h
        exact .cons (h 0 (by simp)) (ih fun k hk => h (k + 1) (by simp; omega))
    exact key _ fun k hk => ⟨_, hW.2 k hk (by simp at hk; rw [hPps]; omega)⟩
  have he'L : env.HasType U
      (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (e'.liftN (gp.sFields c).length)
      (VExpr.mkApps (.const S ls) (ps.map (·.liftN (gp.sFields c).length))) := by
    rw [List.append_nil] at he'
    have := he'.weakN henv.ordered (Ctx.LiftN.zero
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse
      (Γ := Δ) hΓ'len)
    simpa [VExpr.liftN_mkApps, VExpr.liftN] using this
  have hdcl : ((doms[info.nparams + j]'hmd).instL ls).ClosedN (info.nparams + j) := by
    have := wrapForalls_closed_dom (n := 0)
      (by rw [← hshape0]; obtain ⟨_, h⟩ := hwf'; exact h.closedN henv.ordered trivial)
      (info.nparams + j) hmd
    simpa using this.instL
  have hXlift : X.liftN (gp.sFields c).length =
      ((doms[info.nparams + j]'hmd).instL ls).instOuter
        (ps.map (·.liftN (gp.sFields c).length) ++
          (List.range j).map fun k => VExpr.proj S k (e'.liftN (gp.sFields c).length)) := by
    rw [← hXdef, VExpr.liftN_instOuter _ _ (by simpa [hpl] using hdcl)]
    simp [List.map_append, VExpr.liftN, Function.comp_def]
  have hXuL := hXu.weakN henv.ordered (Ctx.LiftN.zero
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse
      (Γ := Δ) hΓ'len)
  have hfield := VProjectionInfo.field_of_walk (decl := decl) henv hinfo hwf' hctorC hshape0
    hvalid0 hhead0 hdn hdu hle hni hFctx hc' hlenA hls hlsE hnz hPA he'L hmd
    (by rw [← hXlift]; exact ⟨_, hXuL⟩)
  rw [← hXlift, List.getElem_append_right (by simp [hpl])] at hfield
  simp only [List.length_map, hpl, Nat.add_sub_cancel_left] at hfield
  have hjF : j < (gp.sFields c).length := by
    have hdoms' : info.nparams + c.fields.length = doms.length := hc ▸ hdoms
    rw [hnF]; omega
  rw [bvarRange_getElem _ _ _ hjF] at hfield
  -- the branch `Nonempty.intro field`
  have hIntro : env.HasType U
      (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (.const ``Nonempty.intro [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1)))) := by
    have := HasType.const (env := env) (U := U)
      (Γ := ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (ls := [u]) hch.2.1 (by simpa using hu) rfl
    simpa [canonicalNonemptyIntroType, VExpr.instL, VLevel.inst] using this
  have hb1 := HasType.app hIntro hXuL
  simp [VExpr.inst, VExpr.instVar] at hb1
  have hbY := HasType.app hb1 hfield
  simp [VExpr.inst, VExpr.instVar] at hbY
  rw [VExpr.inst_liftN] at hbY
  -- the constructor application
  have hCcl : (gp.sCtorApp c).ClosedN (ps.length + (gp.sFields c).length) := by
    apply ClosedN.mkApps_closed (show (VExpr.const c.name gp.levels).ClosedN _ from trivial)
    intro a ha
    simp only [bvarRange, List.mem_map, List.mem_range] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show _ < _
    rw [← hPps]; simp [Instance.params] at hk ⊢; omega
  have hC' : (gp.sCtorApp c).subst ((VExpr.Subst.ofList ps).liftN (gp.sFields c).length) =
      VExpr.mkApps (.const info.ctorName gp.levels)
        (ps.map (·.liftN (gp.sFields c).length) ++
          bvarRange (gp.sFields c).length (gp.sFields c).length) := by
    have h := VExpr.instOuter_params_bvarRange hCcl (Nat.le_refl (gp.sFields c).length)
    rw [Nat.sub_self, VExpr.liftN_zero] at h
    rw [← h]
    have hl : (ps.map (·.liftN (gp.sFields c).length) ++
        bvarRange (gp.sFields c).length (gp.sFields c).length).length =
        data.schema.signature.params.length + (gp.sFields c).length := by simp [hpl, hnp]
    simp only [Instance.sCtorApp]
    rw [← hl, instOuter_bvarRange_apps (f := .const c.name gp.levels) trivial, ← hc, hcname]
  obtain ⟨-, -, -, -, idx', hCT⟩ := VProjectionInfo.ctorApp_typing henv hFctx hctorC hshape0
    hvalid0 hhead0 hdn hdu hle hc' hlenA
  rw [List.take_left' (by simp [hpl])] at hCT
  obtain ⟨rfl, -⟩ := HasType.structure_params henv hFctx hinfo hgpwf hni (by simp [hpl]) hCT
  rw [List.append_nil, ← hC'] at hCT
  -- `fun _ => Nonempty X` applied to the constructor application
  have hYL := hY.weakN henv.ordered (Ctx.LiftN.zero
      ((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse
      (Γ := Δ) hΓ'len)
  have hβ := IsDefEq.beta (hYL.weak henv.ordered) hCT
  rw [VExpr.inst_lift] at hβ
  have hbM : env.HasType U
      (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)).reverse ++ Δ)
      (.app (.app (.const ``Nonempty.intro [u]) (X.liftN (gp.sFields c).length))
        (.bvar ((gp.sFields c).length - 1 - j)))
      (.app ((VExpr.lam (VExpr.mkApps (.const S gp.levels) ps)
          (VExpr.app (.const ``Nonempty [u]) X).lift).liftN (gp.sFields c).length)
        ((gp.sCtorApp c).subst ((VExpr.Subst.ofList ps).liftN (gp.sFields c).length))) := by
    have e : (VExpr.lam (VExpr.mkApps (.const S gp.levels) ps)
        (VExpr.app (.const ``Nonempty [u]) X).lift).liftN (gp.sFields c).length =
        .lam (VExpr.mkApps (.const S gp.levels) (ps.map (·.liftN (gp.sFields c).length)))
          ((VExpr.app (.const ``Nonempty [u]) X).liftN (gp.sFields c).length).lift := by
      simp only [VExpr.liftN, VExpr.liftN_mkApps, VExpr.lift_liftN']
    rw [e]
    refine .defeqDF (.symm hβ) ?_
    exact hbY
  -- the minor premise
  have hHlen : ((gp.sHyps c).mapIdx fun k d =>
      d.subst ((VExpr.Subst.ofList (ps ++ [VExpr.lam (VExpr.mkApps (.const S gp.levels) ps)
        (VExpr.app (.const ``Nonempty [u]) X).lift])).liftN
          ((gp.sFields c).length + k))).reverse.length = (gp.sHyps c).length := by simp
  have hm : env.HasType U Δ
      (VExpr.wrapLams
        (((gp.sFields c).mapIdx fun i d => d.subst ((VExpr.Subst.ofList ps).liftN i)) ++
          ((gp.sHyps c).mapIdx fun k d =>
            d.subst ((VExpr.Subst.ofList (ps ++ [VExpr.lam (VExpr.mkApps (.const S gp.levels) ps)
              (VExpr.app (.const ``Nonempty [u]) X).lift])).liftN
                ((gp.sFields c).length + k))))
        ((VExpr.app (.app (.const ``Nonempty.intro [u]) (X.liftN (gp.sFields c).length))
          (.bvar ((gp.sFields c).length - 1 - j))).liftN (gp.sHyps c).length))
      ((VExpr.wrapForalls (insertBinders (gp.sFields c) 1 ++ gp.sHyps c)
        (VExpr.mkApps (.bvar ((gp.sFields c).length + (gp.sHyps c).length))
          [((gp.sCtorApp c).liftN (gp.sHyps c).length).liftN 1
            ((gp.sFields c).length + (gp.sHyps c).length)])).instOuter
        (ps ++ [VExpr.lam (VExpr.mkApps (.const S gp.levels) ps)
          (VExpr.app (.const ``Nonempty [u]) X).lift])) := by
    rw [VExpr.minor_instOuter]
    apply HasType.wrapLams_of (by rw [List.reverse_append, List.append_assoc]; exact hFHctx)
    rw [List.reverse_append, List.append_assoc]
    exact hbM.weakN henv.ordered (Ctx.LiftN.zero _ hHlen)
  -- the recursor applied to the parameters, the motive, the minor premise and the major
  have hMajcl : (gp.sMajor data.owner).ClosedN gp.params.length := by
    obtain ⟨_, h⟩ := hMajT
    simpa using h.closedN henv.ordered (CtxWF.closed henv.ordered hP)
  have htel := TelInst.insert2 hTelPM hPps.symm
    (fun k hk => by
      simp only [List.length_singleton] at hk
      obtain rfl : k = 0 := by omega
      simpa using hMajcl) hM hm
  simp only [List.mapIdx_cons, List.mapIdx_nil, Nat.zero_add] at htel
  have hhead' := HasType.weak0 henv.ordered (Γ := Δ) hhead
  rw [hR] at hhead'
  have hNE := HasType.mkApps_of_tel henv hΔ hhead' htel
  rw [VExpr.instOuter_app_bvar2_bvar0] at hNE
  -- `Nonempty X`, then `Classical.choice`
  have hβ2 := IsDefEq.beta (hY.weak henv.ordered) he''
  rw [VExpr.inst_lift] at hβ2
  have hNE' := IsDefEq.defeqDF hβ2 hNE
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
