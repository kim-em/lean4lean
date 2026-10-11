import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleSound
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.MajorRel
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaGeneric

/-! # Soundness of an instance of an ι rule

An instance of a registered ι rule is a redex `e = rec m1 (recArgs ++ [ctor lsC ctorArgs])`
with arbitrary terms at the index and constructor-parameter holes, and its reduct
`red = (rhs.instL m1) argsR` with `argsR = recArgs.take k ++ ctorArgs.drop cnp` (the
parameters, motives, minors and fields). The two directions of its soundness are read at the
*argument valuation* `v = argSubst (argsR σ)`, `vS = argSets σ S argsR` of the reduct
template's binders:

* left to right (`iota_lhs_sub_inst`): an observation of the redex comes from the `pat` clause
  of the recursor, whose binding `τ` of the template's variables is definitionally equal to
  `v` (a leading argument by the key class, an index-bound field by the relation of the index
  argument to the field, `hlead`; a constructor field by the constructor class of the major;
  a projection field by the eta anchor; a proof field by proof irrelevance), so the body
  observation transfers to `v` and the β-spine (`beta_spine_sub`) makes it one of the reduct.

The typing of the arguments along the template (`Wv`, `tvv`) and the relation of the index
arguments to the fields they bind (`hlead`) are hypotheses here; `Model/IotaRel.lean` derives
them for the rules of ordinary blocks. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem iotaFs_getElem? {nf j x : Nat} (h : (iotaFs nf)[j]? = some x) : j < nf ∧ x = nf - 1 - j := by
  simp only [iotaFs, List.getElem?_eq_some_iff, List.length_reverse,
    List.length_range] at h
  obtain ⟨hj, e⟩ := h
  simp only [List.getElem_reverse, List.getElem_range, List.length_range] at e
  exact ⟨hj, e.symm⟩

/-- The argument of the reduct at a field variable. -/
theorem argsR_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat}
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    argsR.length = k + nf ∧ ∃ h : argsR.length - 1 - (nf - 1 - j) < argsR.length,
      argsR[argsR.length - 1 - (nf - 1 - j)] = ctorArgs[cnp + j]'(by omega) := by
  subst hargs
  have hl : (recArgs.take k ++ ctorArgs.drop cnp).length = k + nf := by simp; omega
  refine ⟨hl, by omega, ?_⟩
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.getElem_drop, List.length_take]
  congr 1; simp; omega

theorem argSubst_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat} {σ : VExpr.Subst}
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    VExpr.argSubst (argsR.map (·.subst σ)) (nf - 1 - j) =
      (ctorArgs[cnp + j]'(by omega)).subst σ := by
  obtain ⟨hl, h, e⟩ := argsR_field (j := j) hargs hrA hcA hj
  rw [VExpr.argSubst_lt _ (by simp; omega)]
  simp only [List.getElem_map, List.length_map]
  rw [e]

theorem argSets_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat} {σ : VExpr.Subst}
    {S : ObSets} (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    argSets env U Δ σ S argsR (nf - 1 - j) = Obs' σ S (ctorArgs[cnp + j]'(by omega)) := by
  obtain ⟨hl, h, e⟩ := argsR_field (j := j) hargs hrA hcA hj
  simp only [argSets, show nf - 1 - j < argsR.length by omega, dite_true]
  rw [e]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Left to right** for an instance of an ι rule. -/
theorem iota_lhs_sub_inst {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (huniq : PatUniq env n ctor k nind cnp nf rhs)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (hfam : MajorFamEntry env I ctor)
    {m1 lsC : List VLevel} {recArgs ctorArgs argsR : List VExpr}
    (hrA : recArgs.length = k + nind) (hcA : ctorArgs.length = cnp + nf)
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp)
    {T : VExpr} (hRH : HTS env U Δ [] (rhs.instL m1) T)
    (hRS : SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T)
    {σ v : VExpr.Subst} {S vS : ObSets}
    (hv : v = VExpr.argSubst (argsR.map (·.subst σ))) (hvS : vS = argSets env U Δ σ S argsR)
    (Wv : Ctx.SubstEq env U Δ v v (doms.map (·.instL m1)).reverse)
    (tvv : TV env U Δ (doms.map (·.instL m1)).reverse v vS)
    (hlead : ∀ (i x : Nat), lead[i]? = some (VExpr.bvar x) → x < doms.length →
      (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∃ a : VExpr, recArgs[i]? = some a ∧
        (∃ X, TyCls env U Δ ((binderTy doms m1 x).subst v) X ∧
          env.IsDefEq U Δ (a.subst σ) (v x) X) ∧ Ob.Sub (Obs' σ S a) (vS x)) :
    Ob.Sub (Obs' σ S (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])))
      (Obs' σ S (.mkApps (rhs.instL m1) argsR)) := by
  have hrcl : rhs.ClosedN := hc
  have hleadl : lead.length = k + nind := hstat.lead_length
  obtain ⟨hdl, eH, hlenH0, hkH0, -⟩ := hstat
  have hlenH : dsH.length = lead.length + 1 := by rw [hleadl]; exact hlenH0
  have hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs) := by rw [hleadl]; exact hkH0
  have hal : argsR.length = doms.length := by subst hargs; simp; omega
  -- the reduct template
  have eR : rhs.instL m1 = .wrapLams (doms.map (·.instL m1)) (body.instL m1) := by
    rw [hr, instL_wrapLams]
  have hbcl : (body.instL m1).ClosedN doms.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms.length), (doms[i]).ClosedN i := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).2
    simpa using this
  rw [eR] at hRH hRS
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hRS
  rw [List.append_nil] at hBs
  intro o ho
  obtain ⟨keys, hkeys, hc'⟩ := wrap_of_obs_mkApps_le ho
  have hnrig : ¬ env.Rigid n := fun hrig => hrig.pats _ _ hp (SimplePattern.iota_headConst ..)
  rcases Obs.const_iff.1 hc' with ⟨_, _, _, _, _, hrig, _⟩ | ⟨df', _, _, hdf', hlhs', _⟩ |
    ⟨_, _, _, _, _, hcn, _⟩ |
    ⟨df', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf', hl', _⟩ |
    ⟨k'', nind'', ctor'', cnp'', nf'', rhs'', hc'', doms'', body'', ci', τs, lkeys, Dm, cm, Km,
      p'', mC, τ, S'', I', ℓsI', mI', dsH', RH', lsI', iargs', lead'', e, hp'', hr'', hstatic,
      hci'', -, -, hlen'', hsingle, -, hhd, hbind, -, hbody⟩ |
    ⟨fam, info, _, _, _, _, _, hpi, hcn, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrig, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hrig, _⟩
  · exact absurd hrig hnrig
  · exact absurd (by rw [hlhs']; rfl) (hnodf df' hdf' _)
  · exact absurd (hctor n hcn) hnrig
  · exact absurd (by rw [hl']; exact VExpr.stripLams_wrapLams_mkApps_head) (hnodf df' hdf' _)
  rotate_left
  · exact absurd (hpctor n ⟨fam, info, hpi, hcn⟩) hnrig
  · exact absurd hrig hnrig
  · exact absurd hrig hnrig
  obtain ⟨hleadlen, huq⟩ := huniq _ _ _ _ _ _ _ hp''
  have hklen : keys.length = lead.length + 1 := by
    have := List.Forall₂.length_eq hkeys; simp at this; omega
  obtain ⟨ekeys, rfl⟩ := wrap_inj_len (by simp [hklen, hlen'', hleadlen, hleadl]) e
  subst ekeys
  obtain ⟨lkeys', mk, ekl, hkeysL, hkM⟩ := List.forall₂_snoc_right hkeys
  obtain ⟨rfl, emk⟩ := List.append_inj' ekl (by simp)
  cases emk
  obtain ⟨hcmM, hKmcov⟩ := hkM
  cases hci.symm.trans hci''
  -- the clause's constructor is the rule's
  have hctor_eq : ctor'' = ctor := by
    cases mC with
    | true =>
      obtain ⟨h, -⟩ := hsingle rfl _ _ hp (SimplePattern.iota_headConst ..)
      exact (iota_toPattern_inj h).2.2.1.symm
    | false =>
      rcases hhd rfl with ⟨ℓs, hmem⟩ | hEH
      · obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        rw [ly.ctorHead_inv] at hy
        obtain ⟨_, _, hend⟩ := ctor_spine_inv hcrig hy (.inl ⟨_, _, _, rfl⟩)
        rcases hend with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩
        · injection h
        · cases h
        · cases h
      · have hll : lkeys.length = lead.length := by rw [hlen'', hleadlen, hleadl]
        obtain ⟨rfl, info', hpi', hcn'⟩ :=
          hEH.fam eH (by rw [hll]; exact hlenH) (by rw [hll]; exact hkH)
        rcases hfam with ⟨hnp, -⟩ | ⟨info, hpi, hcn⟩
        · exact absurd hpi' (hnp _)
        · cases henv.ordered.projections_unique hpi hpi'
          exact hcn'.symm.trans hcn
  subst ctor''
  obtain ⟨hk1, hk2, hk3, hk4, hrhs⟩ := huq rfl
  subst k'' nind'' cnp'' nf''
  subst hrhs
  have hdl'' : doms''.length = doms.length := by rw [hstatic.1, hdl]
  obtain ⟨hd1, hd2⟩ := wrapLams_inj_len hdl'' (hr''.symm.trans hr)
  subst doms'' body''
  have hlead_eq : lead'' = lead := hleadU _ _ _ _ _ _ _ hstatic
  subst lead''
  -- the fields of the major
  have hkr : k ≤ recArgs.length := by omega
  have hvF : ∀ j x, (iotaFs nf)[j]? = some x → ∃ h : cnp + j < ctorArgs.length,
      v x = (ctorArgs[cnp + j]'h).subst σ ∧ vS x = Obs' σ S (ctorArgs[cnp + j]'h) := by
    intro j x hj
    obtain ⟨hjn, rfl⟩ := iotaFs_getElem? hj
    refine ⟨by omega, ?_, ?_⟩
    · rw [hv]; exact argSubst_field hargs hkr hcA hjn
    · rw [hvS]; exact argSets_field hargs hkr hcA hjn
  have argOf : ∀ j x cl, (iotaFs nf)[j]? = some x → .ctorArg (cnp + j) cl ∈ Km → cl (v x) := by
    intro j x cl hj hcl
    obtain ⟨y, hy, ly⟩ := hKmcov _ hcl
    rw [ly.ctorArg_inv] at hy
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inl ⟨_, _, rfl⟩))
    rcases hend with h | ⟨i, hi, h⟩ | ⟨_, _, _, _, h⟩
    · cases h
    · injection h with e1 e2; subst e1; subst e2
      obtain ⟨hil, hvx, -⟩ := hvF j x hj
      obtain ⟨_, hci', -⟩ := List.forall₂_getElem_exists hck _ hi
      rw [hci', hvx]; exact ElCls.self
    · cases h
  have argObOf : ∀ j x pre k, (iotaFs nf)[j]? = some x →
      .ctorArgOb (cnp + j) pre k ∈ Km → ∃ k', vS x k' ∧ k' ≼ k := by
    intro j x pre k hj hk
    obtain ⟨y, hy, ly⟩ := hKmcov _ hk
    obtain ⟨k₀, rfl, l₀⟩ := ly.ctorArgOb_inv
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inr ⟨_, _, _, rfl⟩))
    rcases hend with h | ⟨_, _, h⟩ | ⟨i, hi, k', hk', h⟩
    · cases h
    · cases h
    · injection h with e1 e2 e3; subst e1
      obtain ⟨hil, -, hvS'⟩ := hvF j x hj
      obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hck _ hi
      obtain ⟨k₁, hk₁, l₁⟩ := hcov k' hk'
      exact ⟨k₁, by rw [hvS']; exact hk₁, l₁.trans (e3 ▸ l₀)⟩
  -- the binding, restricted to the rule's variables
  classical
  let τ' : VExpr.Subst := fun x => if x < doms.length then τ x else v x
  let S' : ObSets := fun x => if x < doms.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body.instL m1) o :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms.length
    · simp only [S', hx, if_true] at ho
      rcases hbind.2 x hx with ⟨i, k, hi, hfirst, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, hS⟩ | ⟨-, info', hpi', -, hle', -, -, -, hS⟩⟩
      · obtain ⟨o₀, ho₀, l₀⟩ := hkS o ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨a, ha, -, hsub⟩ := hlead i x hi hx hfirst
        obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hkeysL i hil
        have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
        rw [hk] at hcov
        obtain ⟨o₁, ho₁, l₁⟩ := hcov o₀ ho₀
        have ha' : recArgs[i]'(by have := List.Forall₂.length_eq hkeysL; omega) = a :=
          (List.getElem?_eq_some_iff.1 ha).2
        rw [ha'] at ho₁
        obtain ⟨o₂, ho₂, l₂⟩ := hsub o₁ ho₁
        exact ⟨o₂, ho₂, l₂.trans (l₁.trans l₀)⟩
      · rw [hS] at ho
        obtain ⟨pre, hpre⟩ := ho
        exact argObOf j x pre o hj hpre
      · rw [hS] at ho; cases ho
      · -- eta: a field observation of the major key
        rw [hS] at ho
        obtain ⟨L, hmem⟩ := ho
        obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        obtain ⟨L', y₀, rfl, l₀⟩ := ly.fieldOb_inv
        obtain ⟨info'', hpi'', -, a, ha, k', hk', l'⟩ := projctor_spine_inv hcrig hy
        cases henv.ordered.projections_unique hpi' hpi''
        obtain ⟨hil, -, hvS'⟩ := hvF j x hj
        rw [show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          List.getElem?_eq_getElem hil] at ha
        cases ha
        exact ⟨k', by rw [hvS']; exact hk', l'.trans l₀⟩
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the argument valuation
  have hL := fun x (hx : x < doms.length) => lookup_binderTy (Γ := []) (ls := m1) hx
  have hbcl' : ∀ x, x < doms.length →
      (binderTy doms m1 x).subst τ = (binderTy doms m1 x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have Wv' : Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) := by
    simpa using Wv
  have W' : Ctx.SubstEq env U Δ τ' v ((doms.map (·.instL m1)).reverse ++ []) := by
    refine SubstEq.of_heads_ind Wv' (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv'.lookup (hL x hx')).hasType.1
    have hD := SubstEq.entry_typed Wv' hx
    obtain ⟨uD, hDt⟩ := hD
    have hDD := hDt.substDF henv hW.wf hΔ hW
    have eA : (binderTy doms m1 x) =
        ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
          (lookup_append _ x hx)
    have e1 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx) τ' x
    have e2 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx) v x
    rw [← eA] at e1 e2
    -- the type conversion between the two substitutions
    have hconv : ∀ {a b : VExpr}, env.IsDefEq U Δ a b ((binderTy doms m1 x).subst v) →
        env.IsDefEq U Δ a b ((binderTy doms m1 x).subst τ) := by
      intro a b h
      rw [hbcl' x hx', e1]; rw [e2] at h; exact hDD.symm.defeqDF h
    have hvx' : env.HasType U Δ (v x) ((binderTy doms m1 x).subst τ) := hconv hvx
    rcases hbind.2 x hx' with ⟨i, k, hi, hfirst, hki, hkt, hkm, -⟩ |
      ⟨-, j, hj, ⟨-, cl, hcl, hct, hcm, -⟩ | ⟨⟨X, hX, hτX⟩, ⟨P, hP, hPs⟩, -⟩ |
        ⟨-, info', hpi', hcn', hle', -, hTE, hpc, -⟩⟩
    · have hil : i < lkeys.length := by
        have := List.Forall₂.length_eq hkeysL
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
      obtain ⟨a, ha, ⟨X, hX, hav⟩, -⟩ := hlead i x hi hx' hfirst
      obtain ⟨_, hcls, -⟩ := List.forall₂_getElem_exists hkeysL i hil
      have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
      have ha' : recArgs[i]'(by have := List.Forall₂.length_eq hkeysL; omega) = a :=
        (List.getElem?_eq_some_iff.1 ha).2
      rw [hk, ha'] at hcls
      have hka : k.2.1 (a.subst σ) := by rw [hcls]; exact ElCls.self
      have h1 := hkt.defeq henv hΔ hkm hka
      exact h1.trans (hconv (TyCls.defeq henv hΔ hX hav))
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- proof binding: both are proofs of the proposition `P`
      have hτx : env.HasType U Δ (τ x) ((binderTy doms m1 x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq_rev henv hΔ hP hτx
      have h2 := TyCls.defeq_rev henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
    · -- eta binding: the anchor is a projection of the major, whose field is `v x`
      obtain ⟨hil, hvx, -⟩ := hvF j x hj
      refine eta_anchor_defeq henv hΔ hpi' hTE hpc (lsc := lsC)
        (margs := ctorArgs.map (·.subst σ)) (a := v x) ?_ ?_ hvx'
      · rw [show cm = (Dm, cm, Km).2.1 from rfl, hcmM]
        simp only [VExpr.subst_mkApps, VExpr.subst]
        rw [hcn']; exact ElCls.self
      · rw [List.getElem?_map,
          show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          List.getElem?_eq_getElem hil, hvx]
        rfl
  have hctx := DomsSD.ctxSD (L := []) (Γ := []) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvv' : TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS := by simpa using tvv
  have tvτ := TV.transfer henv hΔ (by simpa using hctx) W' (fun x hx => hτ'2 x (by simpa using hx))
    tvv'
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS (by simpa using W') (by simpa using tvτ) tvv).1 p₁ hp₁
  -- the β-spine of the reduct
  have hRcl : (VExpr.wrapLams (doms.map (·.instL m1)) (body.instL m1)).ClosedN := by
    rw [← eR]; exact hrcl.instL
  have hal' : argsR.length = (doms.map (·.instL m1)).length := by simp [hal]
  rw [hv] at Wv; rw [hv, hvS] at tvv
  have hβ := (beta_spine_sub henv hΔ hRcl hRH hRS hal' Wv tvv).2 p₂
    ((Obs.subst_argSubst (by rw [hal]; exact hbcl)).2 (by rw [← hv, ← hvS]; exact hp₂))
  exact ⟨p₂, by rw [eR]; exact hβ, l₂.trans l₁⟩

end

end Model
end VEnv
end Lean4Lean
