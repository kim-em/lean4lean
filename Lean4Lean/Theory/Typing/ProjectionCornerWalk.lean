import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas

/-!
# Projections of an arbitrary major as constructor fields, up to proof irrelevance

Let `c args'` be a typed application of the constructor of a registered structure `S`, and `M`
an arbitrary major of type `S PA`, where `PA` agrees with the parameters of `args'` and `S` is not
a type at every universe instantiation. Then every projection of `M` that occurs in a well-formed
term is a proof, and it is definitionally equal to the corresponding field argument of `c args'`
by proof irrelevance. This is how the data-free part of a projection walk over `M` is transported
to the fields of a generic constructor application, without context strengthening.
-/

namespace Lean4Lean.VEnv
open VExpr

variable {env : VEnv} {U : Nat}

theorem forall₂_weakU {Γ Γ' : List VExpr} (W : Ctx.LiftN n 0 Γ Γ') (henv : env.Ordered) :
    ∀ {l l' : List VExpr}, List.Forall₂ (env.IsDefEqU U Γ) l l' →
      List.Forall₂ (env.IsDefEqU U Γ') (l.map (·.liftN n)) (l'.map (·.liftN n))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (h.weakN henv W) (forall₂_weakU W henv t)

theorem forall₂_transU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {a b c : List VExpr}, List.Forall₂ (env.IsDefEqU U Γ) a b →
      List.Forall₂ (env.IsDefEqU U Γ) b c → List.Forall₂ (env.IsDefEqU U Γ) a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (h.trans henv hΓ h') (forall₂_transU henv hΓ t t')

theorem forall₂_equiv_trans :
    ∀ {a b c : List VLevel}, List.Forall₂ (· ≈ ·) a b → List.Forall₂ (· ≈ ·) b c →
      List.Forall₂ (· ≈ ·) a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (Eq.trans h h') (forall₂_equiv_trans t t')

theorem wrapForalls_closed_dom : ∀ {doms : List VExpr} {body : VExpr} {n : Nat},
    (VExpr.wrapForalls doms body).ClosedN n → ∀ i (h : i < doms.length), (doms[i]).ClosedN (n + i)
  | [], _, _, _, i, h => by simp at h
  | d :: ds, body, n, h, i, hi => by
    obtain ⟨hd, hb⟩ := h
    cases i with
    | zero => simpa using hd
    | succ i =>
      have := wrapForalls_closed_dom (doms := ds) (n := n + 1) hb i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- **Projections of a major as proof fields.** If a projection of (a term convertible to) the
major `M`, lifted over binders `Δ`, is well formed, then for every extension `Δ₂` the projection
of a term convertible to `M` is definitionally equal to the corresponding field argument of the
constructor application `c args'`. -/
theorem VProjectionInfo.proofField_transfer {decl : VInductDecl}
    (henv : VEnv.WF env)
    (hinfo : env.projections S info)
    (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hvalid : decl.RawIndAppAt (some S) (doms.length - decl.nparams) result)
    (hhead : result.getAppFnArgs.1 = .const S (VLevel.params decl.uvars))
    (hdn : decl.nparams = info.nparams) (hdu : decl.uvars = info.uvars)
    (hle : info.nparams ≤ doms.length) (hni : info.nindices = 0)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {ls' : List VLevel} {args' : List VExpr} {T : VExpr}
    (hc' : env.HasType U Γ (VExpr.mkApps (.const info.ctorName ls') args') T)
    (hlen : args'.length = doms.length)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlsE : List.Forall₂ (· ≈ ·) ls ls')
    (hnz : ¬ (info.resultLevel.inst ls).IsNeverZero)
    {PA : List VExpr} (hPA : List.Forall₂ (env.IsDefEqU U Γ) PA (args'.take info.nparams))
    {M : VExpr} (hM : env.HasType U Γ M (VExpr.mkApps (.const S ls) PA)) (index : Nat) :
    ∀ (Δ : List VExpr) {X : VExpr}, OnCtx (Δ ++ Γ) (env.IsType U) →
      (hmd : info.nparams + index < doms.length) →
      env.IsDefEqU U (Δ ++ Γ) X (M.liftN Δ.length) →
      VExpr.WF env U (Δ ++ Γ) (.proj S index X) →
      ∀ (Δ₂ : List VExpr) {Y : VExpr}, OnCtx (Δ₂ ++ Γ) (env.IsType U) →
        env.IsDefEqU U (Δ₂ ++ Γ) Y (M.liftN Δ₂.length) →
        env.IsDefEqU U (Δ₂ ++ Γ) (.proj S index Y)
          ((args'[info.nparams + index]'(by omega)).liftN Δ₂.length) := by
  induction index using WellFounded.induction Nat.lt_wfRel.2 with
  | _ index IH =>
  intro Δ X hΓΔ hmd hX hwfX
  have hclosedT : info.ctorType.ClosedN 0 := by
    obtain ⟨_, h⟩ := hwf
    simpa using h.closedN henv.ordered trivial
  have hdomcl : ∀ i (h : i < doms.length), (doms[i]).ClosedN i := by
    intro i h
    have := wrapForalls_closed_dom (n := 0) (by rw [← hshape]; exact hclosedT) i h
    simpa using this
  obtain ⟨hls', hlen', hargsTy, -, idx', hres⟩ :=
    VProjectionInfo.ctorApp_typing henv hΓ hctor hshape hvalid hhead hdn hdu hle hc' hlen
  have hlsl : ls.length = info.uvars := (List.Forall₂.length_eq hlsE).trans hlen'
  have hPAl : PA.length = info.nparams := by
    rw [List.Forall₂.length_eq hPA, List.length_take]; omega
  have hCty := hargsTy (info.nparams + index) (by omega)
  have ⟨u, hCu⟩ := hCty.isType henv.ordered hΓ
  -- the field type at the constructor's arguments, lifted over any binders
  have hVlift : ∀ (Δ₂ : List VExpr),
      (((doms[info.nparams + index]'hmd).instL ls').instOuter
        (args'.take (info.nparams + index))).liftN Δ₂.length =
      ((doms[info.nparams + index]'hmd).instL ls').instOuter
        ((args'.map (·.liftN Δ₂.length)).take (info.nparams + index)) := by
    intro Δ₂
    rw [VExpr.liftN_instOuter _ _ (by
      have := (hdomcl _ hmd).instL (ls := ls')
      simpa [Nat.min_eq_left (show info.nparams + index ≤ args'.length by omega)] using this)]
    simp [List.map_take]
  -- the source of the occurrence
  obtain ⟨_, hpX⟩ := hwfX
  obtain ⟨info', L, P, I, N, Fs, fl, hinfo', hL, hLlen, hP, hI, hfield, hFty, hN, hclosed,
    hguard⟩ := HasType.proj_inv henv.ordered hΓΔ hpX
  obtain rfl := henv.ordered.projections_unique hinfo hinfo'
  have WΔ : Ctx.LiftN Δ.length 0 Γ (Δ ++ Γ) := .zero Δ rfl
  have hMΔ := hM.weakN henv.ordered WΔ
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at hMΔ
  have hNM : env.IsDefEqU U (Δ ++ Γ) N (M.liftN Δ.length) := (IsDefEq.toU hN).trans henv hΓΔ hX
  have hNS := (hNM.of_r henv hΓΔ hMΔ).hasType.1
  have ⟨u₀, hu₀⟩ := IsDefEq.isType henv.ordered hΓΔ hN
  have ⟨hLE, hargsE⟩ :=
    IsDefEqU.structApp_inv henv hΓΔ hinfo (hN.hasType.1.uniqU henv hΓΔ hNS) hu₀
  have hIe : I = [] := List.eq_nil_of_length_eq_zero (hI.trans hni)
  subst hIe
  simp only [List.append_nil] at hargsE hN hNS hu₀
  have hLls : List.Forall₂ (· ≈ ·) L ls := hLE
  have hfl : fl ≈ .zero := by
    rcases hguard with h | h
    · exact absurd (h.of_equiv (VLevel.inst_congr (VLevel.equiv_def'.2 rfl) hLls)) hnz
    · exact h
  -- every projection used by the field type is equal to the field argument, in every extension
  have hEq : ∀ k (hk : k < index),
      ¬ ((doms[info.nparams + index]'hmd).instL L).Skips 1 (index - 1 - k) →
      ∀ (Δ₂ : List VExpr) {Y : VExpr}, OnCtx (Δ₂ ++ Γ) (env.IsType U) →
        env.IsDefEqU U (Δ₂ ++ Γ) Y (M.liftN Δ₂.length) →
        env.IsDefEqU U (Δ₂ ++ Γ) (.proj S k Y)
          ((args'[info.nparams + k]'(by omega)).liftN Δ₂.length) := by
    intro k hk hsk
    have hocc' : VExpr.Occurs (.bvar (index - 1 - k))
        ((doms[info.nparams + index]'hmd).instL L) 0 :=
      VExpr.Occurs.of_not_skips' _ 0 (by simpa [← VExpr.skips_iff] using hsk)
    have hFs := VProjectionInfo.fieldType_eq_instOuter info hshape hLlen hP hmd
      (typeName := S) (major := N)
    rw [hfield] at hFs
    cases Option.some.inj hFs
    have hocc'' := hocc'.instOuter (P ++ (List.range index).map fun j => VExpr.proj S j N)
    have hb : (VExpr.bvar (index - 1 - k)).instOuter
        (P ++ (List.range index).map fun j => VExpr.proj S j N) = .proj S k N := by
      rw [VExpr.instOuter_bvar _ (by simp [hP]; omega)]
      apply (List.getElem_eq_iff _).2
      have hidx : (P ++ (List.range index).map fun j => VExpr.proj S j N).length - 1 -
          (index - 1 - k) = info.nparams + k := by
        simp [hP]; omega
      rw [hidx, List.getElem?_append_right (by omega), hP, Nat.add_sub_cancel_left]
      simp [List.getElem?_range hk]
    rw [hb] at hocc''
    obtain ⟨Δ', hΓΔ', hwfΔ'⟩ := VExpr.WF.of_occurs_lift henv [] hocc'' hΓΔ ⟨_, hFty⟩
    have hX' : env.IsDefEqU U ((Δ' ++ Δ) ++ Γ) (N.liftN Δ'.length)
        (M.liftN (Δ' ++ Δ).length) := by
      have := hNM.weakN henv.ordered (Ctx.LiftN.zero (Γ := Δ ++ Γ) Δ' rfl)
      rw [List.append_assoc]
      simpa [VExpr.liftN_liftN, Nat.add_comm] using this
    exact (IH k hk) (Δ' ++ Δ) (by rwa [List.append_assoc]) (by omega) hX'
      (by rw [List.append_assoc]; simpa [VExpr.liftN] using hwfΔ')
  have hFs := VProjectionInfo.fieldType_eq_instOuter info hshape hLlen hP hmd
    (typeName := S) (major := N)
  rw [hfield] at hFs
  cases Option.some.inj hFs
  -- the occurring field is a proof field
  have hc'Δ := hc'.weakN henv.ordered WΔ
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at hc'Δ
  have hPΔ : List.Forall₂ (env.IsDefEqU U (Δ ++ Γ)) P
      ((args'.map (·.liftN Δ.length)).take info.nparams) := by
    rw [← List.map_take]
    exact forall₂_transU henv hΓΔ hargsE (forall₂_weakU WΔ henv.ordered hPA)
  have hWΔ := VProjectionInfo.field_walk henv hΓΔ hwf hctor hshape hvalid hhead hdn hdu hle hc'Δ
    (by simp [hlen]) hL (forall₂_equiv_trans hLls hlsE) hPΔ hmd
    (qs := (List.range index).map fun j => .proj S j N) (by simp)
    fun k hk => by
      by_cases hsk : ((doms[info.nparams + index]'hmd).instL L).Skips 1 (index - 1 - k)
      · exact .inl hsk
      refine .inr ?_
      have := hEq k hk hsk Δ hΓΔ hNM
      simpa [List.getElem_map] using this
  rw [← hVlift Δ] at hWΔ
  have hCuΔ := hCu.weakN henv.ordered WΔ
  have hFsu := hCuΔ.defeqU_l henv hΓΔ hWΔ.symm
  have hufl : u ≈ fl := IsDefEqU.sort_inv henv hΓΔ
    (by simpa [VExpr.liftN] using hFsu.uniqU henv hΓΔ hFty)
  have hu0 : u ≈ .zero := Eq.trans hufl hfl
  -- the projection of any convertible major is that proof field
  intro Δ₂ Y hΓΔ₂ hY
  have W₂ : Ctx.LiftN Δ₂.length 0 Γ (Δ₂ ++ Γ) := .zero Δ₂ rfl
  have hc'₂ := hc'.weakN henv.ordered W₂
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at hc'₂
  have hM₂ := hM.weakN henv.ordered W₂
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at hM₂
  have hY₂ := (hY.of_r henv hΓΔ₂ hM₂).hasType.1
  have hPA₂ : List.Forall₂ (env.IsDefEqU U (Δ₂ ++ Γ)) (PA.map (·.liftN Δ₂.length))
      ((args'.map (·.liftN Δ₂.length)).take info.nparams) := by
    rw [← List.map_take]
    exact forall₂_weakU W₂ henv.ordered hPA
  have hW₂ := VProjectionInfo.field_walk henv hΓΔ₂ hwf hctor hshape hvalid hhead hdn hdu hle hc'₂
    (by simp [hlen]) hls hlsE hPA₂ hmd
    (qs := (List.range index).map fun j => .proj S j Y) (by simp)
    fun k hk => by
      by_cases hsk : ((doms[info.nparams + index]'hmd).instL ls).Skips 1 (index - 1 - k)
      · exact .inl hsk
      refine .inr ?_
      have hsk' : ¬ ((doms[info.nparams + index]'hmd).instL L).Skips 1 (index - 1 - k) :=
        fun h => hsk h.of_instL.instL
      have := hEq k hk hsk' Δ₂ hΓΔ₂ hY
      simpa [List.getElem_map] using this
  rw [← hVlift Δ₂] at hW₂
  have hCu₂ := hCu.weakN henv.ordered W₂
  have hFY := hCu₂.defeqU_l henv hΓΔ₂ hW₂.symm
  have hfieldY := VProjectionInfo.fieldType_eq_instOuter info hshape hlsl
    (params := PA.map (·.liftN Δ₂.length)) (by simp [hPAl]) hmd (typeName := S) (major := Y)
  have hY₂' : env.IsDefEq U (Δ₂ ++ Γ) Y Y
      (VExpr.mkApps (.const S ls) (PA.map (·.liftN Δ₂.length) ++ [])) := by
    rw [List.append_nil]; exact hY₂
  have hproj := IsDefEq.projDF hinfo hls hlsl (by simp [hPAl]) (by simp [hni]) hfieldY hFY
    hY₂' hY₂' hclosed (.inr hu0)
  have hargΔ₂ := (hCty.weakN henv.ordered W₂).defeqU_r henv hΓΔ₂ hW₂.symm
  have huwf : u.WF U := (hFY.isType henv.ordered hΓΔ₂).sort_inv henv.ordered
  have hFY0 : env.HasType U (Δ₂ ++ Γ) _ (.sort .zero) :=
    .defeqDF (.sortDF huwf (by simp [VLevel.WF]) hu0) hFY
  exact ⟨_, .proofIrrel hFY0 hproj hargΔ₂⟩

end Lean4Lean.VEnv
