import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NativeSem

/-! # Soundness of eliminator rules (stage E)

The analogue of `Model/RuleSound.lean` for generic case equations, whose left-hand sides are
headed by an abstract eliminator `.elim b o ls`: `sound_pat_elim` (mode AB; mode C is excluded
by a hypothesis) and `sound_pat_elim_empty` (a right-hand side without observations). The
head's type is the schema's generic type; its semantic typing derivation lives in the
derivation's context (`HTS.elim`), so the family indicator is read at a typed valuation of
that context (`major_indicator_gen`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The family indicator at the major domain of a closed head type typed in a context with a
typed valuation. -/
theorem major_indicator_gen {Th : VExpr} {ls : List VLevel} {uH : VLevel} {Γ0 : List VExpr}
    {σ0 : VExpr.Subst} {S0 : ObSets} {dsH : List VExpr} {RH : VExpr} {k : Nat} {I : Name}
    {lsI : List VLevel} {iargs : List VExpr} {τ₀ : List Ob} {o : Ob}
    (hTcl : Th.ClosedN) (hT : HTS env U Δ Γ0 Th (.sort uH))
    (W0 : Ctx.SubstEq env U Δ σ0 σ0 Γ0) (tv0 : TV env U Δ Γ0 σ0 S0)
    (eT : Th = .wrapForalls (dsH.map (·.instL ls)) (RH.instL ls)) (hlen : dsH.length = k + 1)
    (hk : dsH[k]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    {keys : List Key} (hkeys : keys.length = k + 1)
    (hτ₀ : ∀ τ ∈ τ₀, Obs' .id .empty Th τ)
    (hty : TypedOb env U Δ (wrap keys o) τ₀) :
    ∃ u : VLevel, Obs' .id .empty Th (piCodChain (keys.take k)
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval))) := by
  have hk' : k < dsH.length := by omega
  have hsplit : dsH.map (·.instL ls) =
      (dsH.take k).map (·.instL ls) ++ [(VExpr.mkApps (.const I lsI) iargs).instL ls] := by
    conv => lhs; rw [← List.take_append_drop k dsH]
    rw [List.map_append]; congr 1
    rw [List.drop_eq_getElem_cons hk', List.drop_eq_nil_of_le (by omega)]
    simp only [List.map_cons, List.map_nil]
    rw [List.getElem?_eq_getElem hk'] at hk; injection hk with hk; rw [hk]
  have hτ₀' : ∀ τ ∈ τ₀, Obs' σ0 S0 Th τ := fun τ hτ => (Obs.closed_iff_id hTcl).2 (hτ₀ τ hτ)
  rw [eT] at hT hτ₀' hTcl ⊢
  have hpi := hT.piSD
  obtain ⟨σH, SH, hkH, -⟩ := tele_unwind henv hΔ hpi W0 tv0
    (by simp [hkeys, hlen]) hty hτ₀'
  rw [hsplit] at hkH hT
  have hkeys' : keys = keys.take k ++ keys.drop k := (List.take_append_drop k keys).symm
  rw [hkeys'] at hkH
  obtain ⟨σ₁, S₁, hk1, -⟩ := hkH.split (by simp; omega)
  have hpi' := hT.piSD
  obtain ⟨W₁, tv₁⟩ := hk1.typed' henv hΔ (DomsSD.left hpi'.doms) W0 tv0
  obtain ⟨u, hA, -⟩ := HTS.tele_dom (pre := (dsH.take k).map (·.instL ls)) (post := [])
    (by simpa using hT)
  simp only [VExpr.instL] at hA W₁ tv₁
  have hr := spine_rigid_obs henv hΔ hA W₁ tv₁ hIrig
  simp only [List.length_map] at hr
  have hd : Obs' σ₁ S₁ (.wrapForalls [(VExpr.mkApps (.const I lsI) iargs).instL ls] (RH.instL ls))
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval)) := by
    simp only [VExpr.wrapForalls, List.foldr_cons, List.foldr_nil, VExpr.instL_mkApps,
      VExpr.instL]
    exact Obs.piDomOb hr
  have := tele_obs hk1 hd
  refine ⟨u, ?_⟩
  rw [hsplit, wrapForalls_append] at hTcl ⊢
  exact (Obs.closed_iff_id hTcl).1 this

omit henv hΔ in
theorem HeadTy.elim_eq {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {Th type : VExpr}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (h : HeadTy env U (.elim b owner.val ls) Th) (hb : env.eliminators b schema)
    (htype : schema.genericType owner = some type) : Th = type.instL ls := by
  rcases h with ⟨_, _, _, e, -⟩ | ⟨b', ls', schema', owner', type', e, hb', ht', -, -, rfl⟩
  · cases e
  · injection e with e1 e2 e3
    subst e1 e3
    cases hEu _ _ _ hb hb'
    cases Fin.ext e2
    cases htype.symm.trans ht'
    rfl

omit henv hΔ in
theorem pat_instL_elim {df : VDefEq} {fs : List Nat}
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b o lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body) (hlsP : lsP.map (·.inst ls) = ls) :
    df.lhs.instL ls = .wrapLams (doms.map (·.instL ls)) (.mkApps (.elim b o ls)
      (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
        (ms.map (·.instL ls) ++ fs.map .bvar)])) ∧
    df.rhs.instL ls = .wrapLams (doms.map (·.instL ls)) (body.instL ls) := by
  refine ⟨?_, by rw [hr, instL_wrapLams']⟩
  rw [hl, instL_wrapLams']
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, hlsP]

/-- **Right to left** for an eliminator rule. -/
theorem pat_rhs_sub_elim {df : VDefEq} {b : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {type : VExpr} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hb : env.eliminators b schema) (hrules : schema.genericEquations b owner = some rules)
    (hmem : df ∈ rules)
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b owner.val lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls)
    {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (htype : schema.genericType owner = some type) (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      False)
    (hL : HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.rhs.instL ls)) (Obs' σ S (df.lhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL_elim hl hr hlsP
  intro o ho
  refine ⟨o, ?_, .refl⟩
  obtain ⟨τs, hτs, hty⟩ := (hR σ σ S W tv tv).2.2.1 o ho
  rw [eR] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eL] at hL ⊢
  obtain ⟨T', hX, hdoms, τc, hτc, hpty⟩ := hL.lamSpine henv hΔ rfl W tv hk hτs hty
  obtain ⟨Wv, tvv⟩ := hk.typed' henv hΔ hdoms W tv
  have hinner := hk.inner
  obtain ⟨Lx, hLx⟩ : ∃ Lx : Nat → List Ob, ∀ x < doms.length, vS x = listSet (Lx x) :=
    ⟨fun x => if h : x < doms.length then Classical.choose (hinner x (by simpa using h))
      else [], fun x hx => by
        simp only [hx, dite_true]; exact Classical.choose_spec (hinner x (by simpa using hx))⟩
  -- the first pass of the head spine
  have hKs := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
    (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
      (ms.map (·.instL ls) ++ fs.map .bvar)])
  rw [List.map_append] at hKs
  obtain ⟨Th, info, hTh, hThcl, hTT, hinfo, hKsi, P1, -, dP2⟩ :=
    hX.spineH henv hΔ rfl (.inr ⟨_, _, _, rfl⟩) Wv tvv _ hKs τc hτc
  obtain rfl := HeadTy.elim_eq hEu hTh hb htype
  obtain ⟨Γ0, σ0, S0, uH, hHT, W0, tv0⟩ : ∃ Γ0 σ0 S0 uH, HTS env U Δ Γ0 (type.instL ls) (.sort uH) ∧
      Ctx.SubstEq env U Δ σ0 σ0 Γ0 ∧ TV env U Δ Γ0 σ0 S0 := by
    rcases hTT with ⟨uH, hHT, -⟩ | ⟨-, uH, hHT, -⟩
    · exact ⟨[], .id, .empty, uH, hHT, .nil, TV.empty⟩
    · exact ⟨_, v, vS, uH, hHT, Wv, tvv⟩
  obtain ⟨infoL, kaM, rfl, hinfoL, hkaM⟩ := forall₂_split hinfo
  obtain ⟨KsL, KsM, eKs, hKsiL, -⟩ := forall₂_split' hKsi
  obtain ⟨rfl, -⟩ := List.append_inj' eKs rfl
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 p hpty
  have hlenL : infoL.length = lead.length := by
    have := List.Forall₂.length_eq hinfoL; simpa using this
  obtain ⟨u, hind⟩ := major_indicator_gen (dsH := dsH) (RH := RH) henv hΔ hThcl hHT W0 tv0
    (by rw [eH, instL_wrapForalls'']) hlenH hkH hIrig
    (keys := (infoL ++ [kaM]).map (·.1)) (by simp [hlenL]) hτ₀ hty₀
  rw [show ((infoL ++ [kaM]).map (·.1)).take lead.length = infoL.map (·.1) by
    simp [List.map_append, hlenL]] at hind
  obtain ⟨xr, hxr, lr⟩ := dP2 infoL kaM [] rfl _ hind
  rw [lr.rigid_inv] at hxr
  have firstOcc : ∀ x : Nat, (∃ i : Nat, lead[i]? = some (VExpr.bvar x)) →
      ∃ i : Nat, lead[i]? = some (VExpr.bvar x) ∧ ∀ j < i, lead[j]? ≠ some (VExpr.bvar x) := by
    intro x ⟨i₀, hi₀⟩
    have hmem : VExpr.bvar x ∈ lead := List.mem_of_getElem? hi₀
    obtain ⟨i, hi⟩ : ∃ i, lead.idxOf? (VExpr.bvar x) = some i := by
      cases h : lead.idxOf? (VExpr.bvar x) with
      | none => exact absurd hmem (by simpa using h)
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hil, h1, h2⟩ := List.idxOf?_eq_some_iff.1 hi
    refine ⟨i, List.getElem?_eq_some_iff.2 ⟨hil, h1⟩, fun j hj e => ?_⟩
    obtain ⟨hjl, e⟩ := List.getElem?_eq_some_iff.1 e
    exact h2 j hj e
  have fieldIdx : ∀ x : Nat, x ∈ fs → ∃ j : Nat, fs[j]? = some x := fun x hx => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    exact ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, e⟩⟩
  -- the common conclusion from a rule clause instance
  have finish : ∀ (infoL' : List (Key × VExpr)) (kaM' : Key × VExpr) (S' : ObSets)
      (τ₀' : List Ob),
      List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS)
        (infoL' ++ [kaM']) (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]) →
      (∀ τ ∈ τ₀', Obs' .id .empty (type.instL ls) τ) →
      TypedOb env U Δ (wrap ((infoL' ++ [kaM']).map (·.1)) p) τ₀' →
      (∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ kaM'.1.2.2) →
      RuleBind env U Δ doms ls lead ms.length fs false (infoL'.map (·.1)) kaM'.1.2.2 v S' →
      (∀ x o, vS x o → S' x o) →
      Obs' σ S (.wrapLams (doms.map (·.instL ls)) (.mkApps (.elim b owner.val ls)
        (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]))) (wrap lk p) := by
    intro infoL' kaM' S' τ₀' hinfo' hτ₀' hty₀' hhd hbind hS'
    have hlen' : infoL'.length = lead.length := by
      have := List.Forall₂.length_eq hinfo'; simpa using this
    have hc := Obs.elimRule (σ := v) (S := vS) (Dm := kaM'.1.1) (cm := kaM'.1.2.1)
      (Km := kaM'.1.2.2) (lkeys := infoL'.map (·.1)) hb hrules hmem hl hr htype hτ₀'
      (by simpa using hty₀') (by simp [hlen']) hhd hbind (hp.mono hS')
    have hXo := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo') (by simpa using hc)
    exact Obs.wrapLams_iff.2 ⟨lk, v, vS, p, hk, rfl, hXo⟩
  by_cases hm : u.eval = fun _ => 0
  · rw [hm] at hind
    exact (hC _ (by simp [hlenL]) hind).elim
  · -- mode AB: the major's constructor observations
    obtain ⟨-, -, -, hHTSm, -⟩ := hkaM
    have hKc := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
      (ms.map (·.instL ls) ++ fs.map .bvar)
    obtain ⟨cc, cinfo, hcc, -, -, hcinfo, hcKs, cP1, -, -⟩ :=
      hHTSm.spine henv hΔ rfl Wv tvv _ hKc
        [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval]
        (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hxr)
    have hCT : CtorTyped env ctor
        [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval] :=
      ⟨I, _, _, _, List.mem_singleton_self _, hcf, hm⟩
    have hcobs : ∀ r ∈ ctorObs ctor ((lsC.map (·.inst ls)).map (·.eval)) (cinfo.map (·.1)),
        Obs' v vS (.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)) r := by
      intro r hr
      have hend := ctorObs_end hr
      have hrty : TypedOb env U Δ r
          [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval] := by
        rcases hend with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
        · exact .ctorHead hCT
        · exact .ctorArg hCT
        · exact .ctorArgOb hCT
      obtain ⟨τ₀c, h1, h2⟩ := cP1 r hrty
      exact obs_mkApps_of_wrap (KeyData.forall₂_keys hcinfo) (.ctor hcis hcc h1 h2 hend)
    have hKs2 := forall₂_append_single' (argDemand_ok (env := env) (U := U) (Δ := Δ)
      (nd := doms.length) hLx v (lead.map (·.instL ls))) hcobs
    obtain ⟨Th2, info2, hTh2, -, -, hinfo2, hKsi2, P12, -, -⟩ :=
      hX.spineH henv hΔ rfl (.inr ⟨_, _, _, rfl⟩) Wv tvv _ hKs2 τc hτc
    obtain rfl := HeadTy.elim_eq hEu hTh2 hb htype
    obtain ⟨infoL2, kaM2, rfl, hinfoL2, -⟩ := forall₂_split hinfo2
    obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := forall₂_split' hKsi2
    obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
    cases e2
    obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 p hpty
    have hclen : (cinfo.map (·.1)).length = ms.length + fs.length := by
      have := List.Forall₂.length_eq hcinfo; simp at this ⊢; omega
    have hmarg : ∀ j x, fs[j]? = some x →
        (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms.length + j]? = some (.bvar x) := by
      intro j x hj
      rw [List.getElem?_append_right (by simp)]
      simp [hj]
    classical
    let S' : ObSets := fun x =>
      if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ fs then
        fun k => ∃ pre, .ctorArgOb (ms.length + fs.idxOf x) pre k ∈ kaM2.1.2.2
      else vS x
    have hfsj : ∀ x, x ∈ fs → fs[fs.idxOf x]? = some x := fun x hx =>
      List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_of_mem hx, List.getElem_idxOf _⟩
    refine finish infoL2 kaM2 S' τ₀2 hinfo2 hτ₀2 hty₀2
      ⟨_, hKsM2 _ (hclen ▸ mem_ctorObs_head)⟩ ?_ ?_
    · intro x hx
      by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
      · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL2 hKsiL2 hi
        have : S' x = vS x := by
          simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
        exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, this.trans hk4⟩
      · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
        have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
          obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
          exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
        obtain ⟨cl, hcl, hcty, hcm, -⟩ := bind_field (c := ctor)
          (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
          (hmarg _ _ (hfsj x hxf))
        refine .inr ⟨hnb, fs.idxOf x, hfsj x hxf, .inl ⟨rfl, cl, hKsM2 _ hcl, hcty, hcm, ?_⟩⟩
        simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
    · intro x o ho
      simp only [S']
      split
      · rename_i hMF
        obtain ⟨hx, hnb, hxf⟩ := hMF
        obtain ⟨_, -, -, -, hall⟩ := bind_field (c := ctor)
          (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
          (hmarg _ _ (hfsj x hxf))
        rw [hLx x hx] at ho
        exact ⟨_, hKsM2 _ (hall o ho)⟩
      · exact ho

end

end Model
end VEnv
end Lean4Lean
