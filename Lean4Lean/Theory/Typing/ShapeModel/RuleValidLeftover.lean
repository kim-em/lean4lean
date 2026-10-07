import Lean4Lean.Theory.Typing.ShapeModel.RuleValidSpine
import Lean4Lean.Theory.Typing.ShapeModel.RuleValidSig

/-!
# Leftover parameters of structure constructors read from indices

A rule whose major is the constructor `c` of a registered structure `s` with `np` parameters may
supply fewer than `np` parameter arguments: its first fields then sit in parameter positions of
the structure's view, which constructor shapes do not store. The signature reads such a field
from the rule's index argument at the same position of the major's type (`fieldIndexOf`,
`EnvSigSyntax.lean`). This file proves that the read is semantically the field
(`leftover_reads`): the type of the major is both the structure applied to the major's first
`np` arguments (its constructor's codomain) and the head's major domain, the family applied to the
parameters and the indices; rigid shapes approximating one approximate the other, and their
arguments approximate the arguments of both applications (`Interp.rigid_inv`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

section abstract
variable [SemSig] [SemSig.Coherent]

/-- A rigid shape approximating an application of a rigid former is a shape of that former, and
its arguments approximate the arguments of the application. -/
theorem Interp.rigid_inv (hnc : SemSig.ctor F = none) (hnr : ∀ r, SemSig.rules r → r.head ≠ .const F)
    {as : List (WShape n)} {cts : List (Name × WShape n)}
    (H : Interp env ρ (WShape.rigid s ls' as cts).T (VExpr.mkApps (.const F lv) args)) :
    s = F ∧ List.Forall₂ (fun a A => Interp env ρ a.T A) as args := by
  rcases Interp.fam_inv hnc hnr H with h | ⟨_, _, h⟩ | ⟨n', rargs, cts', -, -, hle, hargs⟩
  · exact absurd h TShape.rigid_not_le_bot
  · exact absurd h TShape.rigid_not_le_lam'
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂), WShape.lift_rigid le₁,
    WShape.lift_rigid le₂, WShape.rigid_le_rigid] at hle
  obtain ⟨rfl, -, hl, -⟩ := hle
  refine ⟨rfl, forall₂_interp_of_le ?_ hargs⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hl
  exact hl.imp fun x y h => (TShape.LE.def le₁ le₂).2 h

/-- The codomain of a structure constructor's telescope, under typed keys along it, is
approximated by a rigid shape of the structure (typed) whose parameter arguments are above the
parameter keys. -/
theorem struct_codomain_realize (hcl : ConstClosed env) (hF : SemSig.StructFacts env s info)
    (W : Valuation.Fits env Γ₀ Γ σ) {Dsc idxs : List VExpr}
    (hct : info.ctorType = Dsc.foldr .forallE (VExpr.mkApps (.const s (VLevel.params info.uvars))
      ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
        idxs)))
    (hDsc : Dsc.length = info.nparams + info.numFields) (hlv : lv.length = info.uvars)
    (hTyc : StrongSound env Γ (info.ctorType.instL lv) (.sort u))
    {ps : List (TShape × TShape)} (htel : TelInterp env σ (Dsc.map (·.instL lv)) ps)
    (hpt : TelTyped ps) :
    ∃ N, ∃ as : List (WShape N), ∃ cts : List (Name × WShape N),
      as.length = info.nparams + idxs.length ∧
      (∀ j (hj : j < info.nparams) (hj' : j < ps.length) (hja : j < as.length),
        ps[j].2 ≤ as[j].T) ∧
      Interp env (σ.pushes (ps.map (·.2))) (WShape.rigid s (lv.map (·.eval)) as cts).T
        (VExpr.mkApps (.const s lv)
          ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
            idxs.map (·.instL lv))) ∧
      (WShape.rigid s (lv.map (·.eval)) as cts).T.HasType TShape.type := by
  have hctl : info.ctorType.instL lv = (Dsc.map (·.instL lv)).foldr .forallE
      (VExpr.mkApps (.const s lv)
        ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
          idxs.map (·.instL lv))) := by
    rw [hct, VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
    simp only [VExpr.instL, VLevel.inst_map_id hlv, List.map_append, List.map_map,
      Function.comp_def]
  rw [hctl] at hTyc
  obtain ⟨Γ', v, W', hB⟩ := Tel.fits W hTyc htel hpt
  have hlps : ps.length = info.nparams + info.numFields := by
    rw [← htel.length_eq, List.length_map, hDsc]
  obtain ⟨cisF, DsF, hscF, huvF, hDsF, hfamT⟩ := hF.famTypeSem
  have hsem : FamSem env s info.resultLevel (info.nparams + info.nindices) :=
    ⟨cisF, DsF, hscF, hDsF, fun ls hls m => hfamT ls (hls.trans huvF) m⟩
  obtain ⟨K, hK⟩ := depth_bound (ps.map (·.2))
  have hkey : ∀ p ∈ ps, p.2.1 ≤ K := fun p hp => hK _ (List.mem_map_of_mem hp)
  obtain ⟨asP, hasP⟩ : ∃ asP : List (WShape K),
      asP = (ps.take info.nparams).map (fun p => p.2.2.lift K) := ⟨_, rfl⟩
  have hasPl : asP.length = info.nparams := by rw [hasP]; simp [hlps]
  have hasPe : ∀ j (hj : j < asP.length) (hj' : j < ps.length), asP[j] = ps[j].2.2.lift K := by
    intro j hj hj'; subst hasP; simp
  obtain ⟨cts, hcts₀⟩ : ∃ cts : List (Name × WShape K),
      cts = (SemSig.famCtors s).map fun c' => (c', WShape.bot) := ⟨_, rfl⟩
  have hpbv : List.Forall₂ (fun x A => Interp env (σ.pushes (ps.map (·.2))) (WShape.T x) A) asP
      ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j))) := by
    refine List.forall₂_of_getElem (by simp [hasPl]) fun j h1 h2 => ?_
    have hj' : j < ps.length := by omega
    rw [hasPe j h1 hj', List.getElem_map, List.getElem_range]
    refine .bvar ((TShape.lift_eqv (hkey _ (List.getElem_mem hj'))).1.trans ?_)
    have e : info.nparams + info.numFields - 1 - j = (ps.map (·.2)).length - 1 - j := by
      simp [hlps]
    rw [e, Valuation.pushes_getElem σ (ps.map (·.2)) j (by simp; omega), List.getElem_map]
    exact TShape.LE.rfl
  have hargs : List.Forall₂ (fun x A => Interp env (σ.pushes (ps.map (·.2))) (WShape.T x) A)
      (asP ++ idxs.map (fun _ => WShape.bot))
      ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
        idxs.map (·.instL lv)) := by
    refine (List.Forall₂.append_of_left (by simp [hasPl])).2 ⟨hpbv, ?_⟩
    refine List.forall₂_of_getElem (by simp) fun j _ _ => ?_
    simp only [List.getElem_map]; exact .bot
  have hent : ∀ p ∈ cts, CtorEntry env (Interp env) lv
      ((asP ++ idxs.map (fun _ => WShape.bot)).map (fun x : WShape K => x.T)) p := by
    intro p hp
    rw [hcts₀] at hp
    simp only [List.mem_map, hF.famCtors, List.mem_singleton] at hp
    obtain ⟨c', rfl, rfl⟩ := hp
    exact ⟨_, _, TShape.bot, hF.ctorConst, hF.ctor, .bot, TShape.bot_le'⟩
  have hcts : WShape.CtsTypes cts := by
    intro p hp
    rw [hcts₀] at hp
    simp only [List.mem_map] at hp
    obtain ⟨c', -, rfl⟩ := hp
    exact .bot' .sort_type
  obtain ⟨-, hI, hty⟩ := Rigid.realize hcl W' hF.famNotCtor hF.famNoRule hF.famLevel hsem hB
    hargs (by rw [hcts₀]; simp [List.map_map, Function.comp_def]) hent hcts
  refine ⟨K, asP ++ idxs.map (fun _ => WShape.bot), cts, by simp [hasPl],
    fun j hj hj' hja => ?_, hI, hty.toType⟩
  rw [List.getElem_append_left (by omega), hasPe j (by omega) hj']
  exact (TShape.lift_eqv (hkey _ (List.getElem_mem hj'))).2

/-- A rigid family applied to parameter expressions and index variables, typed at a sort, is
approximated by a typed rigid shape whose index arguments are above the keys of the index
variables. -/
theorem fam_dom_realize (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (hnc : SemSig.ctor F = none) (hnr : ∀ r, SemSig.rules r → r.head ≠ .const F)
    (hl : SemSig.famLevel F = some lF) (hsem : FamSem env F lF n)
    (hfc : ∀ c' ∈ SemSig.famCtors F, ∃ ci k, env.constants c' = some ci ∧ SemSig.ctor c' = some k)
    (hD : StrongSound env Γ (VExpr.mkApps (.const F lvF) (pargs ++ vars nidx 0)) (.sort u)) :
    ∃ N, ∃ as : List (WShape N), ∃ cts : List (Name × WShape N),
      as.length = pargs.length + nidx ∧
      (∀ j (hj : j < nidx) (hja : pargs.length + j < as.length),
        ρ (nidx - 1 - j) ≤ as[pargs.length + j].T) ∧
      Interp env ρ (WShape.rigid F (lvF.map (·.eval)) as cts).T
        (VExpr.mkApps (.const F lvF) (pargs ++ vars nidx 0)) ∧
      (WShape.rigid F (lvF.map (·.eval)) as cts).T.HasType TShape.type := by
  obtain ⟨K, hK⟩ := depth_bound ((List.range nidx).map fun j => ρ (nidx - 1 - j))
  obtain ⟨asI, hasI⟩ : ∃ asI : List (WShape K),
      asI = (List.range nidx).map (fun j => (ρ (nidx - 1 - j)).2.lift K) := ⟨_, rfl⟩
  have hkey : ∀ j < nidx, (ρ (nidx - 1 - j)).1 ≤ K := fun j hj =>
    hK _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  obtain ⟨cts, hcts₀⟩ : ∃ cts : List (Name × WShape K),
      cts = (SemSig.famCtors F).map fun c' => (c', WShape.bot) := ⟨_, rfl⟩
  have hargs : List.Forall₂ (fun x A => Interp env ρ (WShape.T x) A)
      (pargs.map (fun _ => WShape.bot) ++ asI) (pargs ++ vars nidx 0) := by
    refine (List.Forall₂.append_of_left (by simp)).2 ⟨?_, ?_⟩
    · refine List.forall₂_of_getElem (by simp) fun j _ _ => ?_
      simp only [List.getElem_map]; exact .bot
    · refine List.forall₂_of_getElem (by simp [hasI, vars_length']) fun j h1 h2 => ?_
      have hj : j < nidx := by simpa [hasI] using h1
      rw [vars_getElem]
      subst hasI
      have e : ((List.range nidx).map (fun j => (ρ (nidx - 1 - j)).2.lift K))[j]'(by simpa using hj)
          = (ρ (nidx - 1 - j)).2.lift K := by simp only [List.getElem_map]; rw [List.getElem_range]
      rw [e]
      refine .bvar ((TShape.lift_eqv (hkey j hj)).1.trans ?_)
      rw [show 0 + (nidx - 1 - j) = nidx - 1 - j by omega]; exact TShape.LE.rfl
  have hent : ∀ p ∈ cts, CtorEntry env (Interp env) lvF
      ((pargs.map (fun _ => WShape.bot) ++ asI).map (fun x : WShape K => x.T)) p := by
    intro p hp
    rw [hcts₀] at hp
    simp only [List.mem_map] at hp
    obtain ⟨c', hc', rfl⟩ := hp
    obtain ⟨ci, k, h1, h2⟩ := hfc c' hc'
    exact ⟨ci, k, TShape.bot, h1, h2, .bot, TShape.bot_le'⟩
  have hcts : WShape.CtsTypes cts := by
    intro p hp
    rw [hcts₀] at hp
    simp only [List.mem_map] at hp
    obtain ⟨c', -, rfl⟩ := hp
    exact .bot' .sort_type
  obtain ⟨-, hI, hty⟩ := Rigid.realize hcl W hnc hnr hl hsem hD hargs
    (by rw [hcts₀]; simp [List.map_map, Function.comp_def]) hent hcts
  subst hasI
  refine ⟨K, _, cts, by simp, fun j hj hja => ?_, hI, hty.toType⟩
  rw [List.getElem_append_right (by simp)]
  have e : ((List.range nidx).map (fun j => (ρ (nidx - 1 - j)).2.lift K))[pargs.length + j -
      (pargs.map (fun _ => (WShape.bot : WShape K))).length]'(by simp; omega) =
      (ρ (nidx - 1 - j)).2.lift K := by
    simp only [List.getElem_map, List.length_map, Nat.add_sub_cancel_left]; rw [List.getElem_range]
  rw [e]
  exact (TShape.lift_eqv (hkey j hj)).2

/-- The leftover parameter fields of a structure constructor major are read from the index
arguments of the rule: the index argument at the position of the field in the major's type has
exactly the approximations of the field. -/
theorem leftover_reads (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ σ) {h : Head}
    {pre₀ idx ps pargs doms₀ : List VExpr} {TbH : VExpr}
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls)
      (pre₀ ++ idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])) B)
    (hTh : HeadType env h ls Th)
    (hThs : Th = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const F lvF)
      (pargs ++ vars idx.length 0)]) TbH)
    (hlen0 : doms₀.length = pre₀.length + idx.length)
    (hncF : SemSig.ctor F = none) (hnrF : ∀ r, SemSig.rules r → r.head ≠ .const F)
    (hF : SemSig.StructFacts env s info) (hcn : info.ctorName = c)
    (hpl : ps.length = pargs.length) (halign : ps.length + nf = info.nparams + info.numFields)
    (hi : ps.length + i < info.nparams) (hif : i < nf) :
    ∃ hidx : i < idx.length, ∀ t, Interp env σ t idx[i] ↔ t ≤ σ (nf - 1 - i) := by
  subst hcn
  obtain ⟨A, Bf, hf, hM⟩ := StrongSound.app_last hTy
  obtain ⟨Dsc, idxs, hDsc, hidxs, hct⟩ := hF.ctorType
  have hcv := hF.ctorConst
  have hM' : StrongSound env Γ (VExpr.mkApps (.const info.ctorName lv)
      (ps ++ vars nf 0).reverse.reverse) A := by rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hlv, hTyc⟩ := Spine.constInfo hM'
  cases hci.symm.trans hcv
  have hlv' : lv.length = info.uvars := hlv
  let pbv : List VExpr :=
    (List.range info.nparams).map fun j => .bvar (info.nparams + info.numFields - 1 - j)
  have hctl : info.ctorType.instL lv = VExpr.wrapForalls (Dsc.map (·.instL lv))
      (VExpr.mkApps (.const s lv) (pbv ++ idxs.map (·.instL lv))) := by
    rw [hct]
    show VExpr.instL lv (Dsc.foldr .forallE _) = _
    rw [VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
    simp only [VExpr.instL, VLevel.inst_map_id hlv', List.map_append, List.map_map,
      Function.comp_def, pbv]
    rfl
  have hmlen : (ps ++ vars nf 0).length = info.nparams + info.numFields := by
    simp [vars_length']; omega
  have hDl : (Dsc.map (·.instL lv)).length = (ps ++ vars nf 0).length := by
    rw [List.length_map, hDsc, hmlen]
  have hk : ps.length + i < (ps ++ vars nf 0).length := by rw [hmlen]; omega
  have hmk : (ps ++ vars nf 0)[ps.length + i] = .bvar (nf - 1 - i) := by
    rw [List.getElem_append_right (by omega), vars_getElem]; congr 1; simp
  -- ⊇: the field's key approximates the index
  let xs : List TShape := ps.map (fun _ => TShape.bot) ++ (List.range nf).reverse.map (fun j => σ j)
  have hxs : List.Forall₂ (fun x A => Interp env σ x A) xs (ps ++ vars nf 0) := by
    refine (List.Forall₂.append_of_left (by simp)).2 ⟨?_, ?_⟩
    · refine List.forall₂_of_getElem (by simp) fun j _ _ => ?_
      simp only [List.getElem_map]; exact .bot
    · refine List.forall₂_of_getElem (by simp [vars_length']) fun j h1 h2 => ?_
      rw [vars_getElem]
      have hj : j < nf := by simpa using h1
      have e : ((List.range nf).reverse.map (fun j => σ j))[j]'(by simpa using hj) =
          σ (nf - 1 - j) := by simp [List.getElem_reverse]
      rw [e, show 0 + (nf - 1 - j) = nf - 1 - j by omega]; exact .bvar'
  have hxk : xs[ps.length + i]'(by simp [xs]; omega) = σ (nf - 1 - i) := by
    simp only [xs]
    rw [List.getElem_append_right (by simp)]
    simp [List.getElem_reverse]
  obtain ⟨psc, hpsc1, hpsc2, hpsct, hpsctel, -⟩ :=
    ctor_body_of_type W hM hcv hctl hDl hxs (t := TShape.bot) .bot
  obtain ⟨N, as, cts, has, haskey, hR1, hR1t⟩ :=
    struct_codomain_realize hcl hF W hct hDsc hlv' hTyc hpsctel hpsct
  have hR1A : Interp env σ (WShape.rigid s (lv.map (·.eval)) as cts).T A :=
    ctor_type_of_body W hM hcv hctl hpsc2 hpsct hpsctel hR1
  obtain ⟨psh, -, hpsh2, hpsht, hpshtel, hD⟩ := head_dom_of_type W hf hTh hThs
    (by rw [hlen0]; simp) (xs := (pre₀ ++ idx).map fun _ => TShape.bot)
    (List.forall₂_of_getElem (by simp) fun j _ _ => by simp only [List.getElem_map]; exact .bot)
    hR1A hR1t
  obtain ⟨rfl, hasD⟩ := Interp.rigid_inv hncF hnrF hD
  have hlens := hasD.length_eq
  simp only [List.length_append, vars_length'] at hlens
  have hidx : i < idx.length := by omega
  refine ⟨hidx, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  rotate_left
  · -- ⊇
    have hkas : pargs.length + i < as.length := by omega
    have h1 : σ (nf - 1 - i) ≤ as[pargs.length + i].T := by
      have := forall₂_getElem hpsc1 (i := ps.length + i) (by simp [xs]; omega)
      rw [hxk] at this
      have h' := haskey _ hi (by rw [hpsc2.length_eq]; exact hk) (by omega)
      simp only [hpl] at this h'
      exact this.trans h'
    have h2 := forall₂_getElem hasD (i := pargs.length + i) hkas
    rw [List.getElem_append_right (by omega), vars_getElem] at h2
    have h3 := Interp.bvar_iff.1 h2
    have hpl' : (psh.map (·.2)).length = pre₀.length + idx.length := by
      simp [hpsh2.length_eq]
    have e : 0 + (idx.length - 1 - (pargs.length + i - pargs.length)) =
        (psh.map (·.2)).length - 1 - (pre₀.length + i) := by rw [hpl']; omega
    rw [e, Valuation.pushes_getElem σ (psh.map (·.2)) _ (by rw [hpl']; omega),
      List.getElem_map] at h3
    have h4 := forall₂_getElem hpsh2 (i := pre₀.length + i) (by rw [hpsh2.length_eq]; simp; omega)
    rw [List.getElem_append_right (by simp)] at h4
    simp only [Nat.add_sub_cancel_left] at h4
    exact h4.mono (ht.trans (h1.trans h3))
  · -- ⊆
    let xh : List TShape := pre₀.map (fun _ => TShape.bot) ++
      (List.range idx.length).map (fun j => if j = i then t else TShape.bot)
    have hxh : List.Forall₂ (fun x A => Interp env σ x A) xh (pre₀ ++ idx) := by
      refine (List.Forall₂.append_of_left (by simp)).2 ⟨?_, ?_⟩
      · refine List.forall₂_of_getElem (by simp) fun j _ _ => ?_
        simp only [List.getElem_map]; exact .bot
      · refine List.forall₂_of_getElem (by simp) fun j h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        split
        · rename_i hj; subst hj; exact ht
        · exact .bot
    have hxhk : xh[pre₀.length + i]'(by simp [xh]; omega) = t := by
      simp only [xh]
      rw [List.getElem_append_right (by simp)]
      simp
    have hf' : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) (pre₀ ++ idx).reverse.reverse)
        (.forallE A Bf) := by rwa [List.reverse_reverse]
    obtain ⟨qsh, hqh1, hqh2, hqh3, hqh4⟩ := Spine.typed_head W hf' hTh
      (List.Forall₂.reverse.2 hxh) (R := TShape.piBot) Interp.piBot
    rw [hThs] at hqh4
    have hqh4' : Interp env σ (nestPi qsh.reverse TShape.piBot)
        (doms₀.foldr .forallE (.forallE (VExpr.mkApps (.const s lvF) (pargs ++ vars idx.length 0))
          TbH)) := by
      simpa only [VExpr.wrapForalls, List.foldr_append, List.foldr_cons, List.foldr_nil] using hqh4
    obtain ⟨htelh, -⟩ := Interp.nest_inv (by
      rw [List.length_reverse, hqh2.length_eq]; simp [hlen0]; omega) hqh4'
    have hpth : TelTyped qsh.reverse := fun p hp => hqh3 p (List.mem_reverse.1 hp)
    have hpsh2' : List.Forall₂ (fun p A => Interp env σ p.2 A) qsh.reverse (pre₀ ++ idx) := by
      have := List.Forall₂.reverse.2 hqh2; rwa [List.reverse_reverse] at this
    have hxh' : List.Forall₂ (fun x p => x ≤ p.2) xh qsh.reverse := by
      have := List.Forall₂.reverse.2 hqh1; rwa [List.reverse_reverse] at this
    obtain ⟨Th', uh, hTh', hThr⟩ := Spine.headInfo hf'
    cases HeadType.unique hTh hTh'
    rw [hThs] at hThr
    have hThr' : StrongSound env Γ (doms₀.foldr .forallE
        (.forallE (VExpr.mkApps (.const s lvF) (pargs ++ vars idx.length 0)) TbH)) (.sort uh) := by
      simpa only [VExpr.wrapForalls, List.foldr_append, List.foldr_cons, List.foldr_nil] using hThr
    obtain ⟨Γh, vh, Wh, hBh⟩ := Tel.fits W hThr' htelh hpth
    obtain ⟨uD, -, hDr, -⟩ := hBh.forallE_inv
    obtain ⟨cisF, DsF, hscF, huvF, hDsF, hfamT⟩ := hF.famTypeSem
    have hsemS : FamSem env s info.resultLevel (info.nparams + info.nindices) :=
      ⟨cisF, DsF, hscF, hDsF, fun ls hls m => hfamT ls (hls.trans huvF) m⟩
    have hfcS : ∀ c' ∈ SemSig.famCtors s, ∃ ci k, env.constants c' = some ci ∧
        SemSig.ctor c' = some k := by
      intro c' hc'
      rw [hF.famCtors, List.mem_singleton] at hc'
      subst hc'
      exact ⟨_, _, hF.ctorConst, hF.ctor⟩
    obtain ⟨N₂, as₂, cts₂, has₂, hkey₂, hR2, hR2t⟩ := fam_dom_realize hcl Wh hF.famNotCtor
      hF.famNoRule hF.famLevel hsemS hfcS hDr
    have hR2A := head_type_of_dom W hf hTh hThs hpsh2' hpth htelh hR2 hR2t
    obtain ⟨psc₂, -, hpsc₂2, -, -, hb⟩ := ctor_body_of_type W hM hcv hctl hDl
      (xs := (ps ++ vars nf 0).map fun _ => TShape.bot)
      (List.forall₂_of_getElem (by simp) fun j _ _ => by simp only [List.getElem_map]; exact .bot)
      hR2A
    obtain ⟨-, hasB⟩ := Interp.rigid_inv hF.famNotCtor hF.famNoRule hb
    have hk2 : pargs.length + i < as₂.length := by omega
    -- the argument of the rigid shape at the leftover position is below the field's key
    have g1 := forall₂_getElem hasB (i := pargs.length + i) hk2
    have hpb : pargs.length + i < ((List.range info.nparams).map
        (fun j => VExpr.bvar (info.nparams + info.numFields - 1 - j))).length := by
      simp only [List.length_map, List.length_range]; omega
    rw [List.getElem_append_left hpb, List.getElem_map, List.getElem_range] at g1
    have g2 := Interp.bvar_iff.1 g1
    have hlc : (psc₂.map (·.2)).length = info.nparams + info.numFields := by
      simp [hpsc₂2.length_eq, hmlen]
    rw [show info.nparams + info.numFields - 1 - (pargs.length + i) =
        (psc₂.map (·.2)).length - 1 - (pargs.length + i) by rw [hlc],
      Valuation.pushes_getElem σ (psc₂.map (·.2)) _ (by rw [hlc]; omega), List.getElem_map] at g2
    have g3 := forall₂_getElem hpsc₂2 (i := pargs.length + i)
      (by rw [hpsc₂2.length_eq]; simp [vars_length']; omega)
    have hmk2 : (ps ++ vars nf 0)[pargs.length + i]'(by simp [vars_length']; omega) =
        .bvar (nf - 1 - i) := by
      rw [List.getElem_append_right (by omega), vars_getElem]; congr 1; omega
    rw [hmk2] at g3
    have g4 := Interp.bvar_iff.1 g3
    -- the key of the index position is below the argument
    have g5 := hkey₂ i hidx hk2
    have hlh : (qsh.reverse.map (·.2)).length = pre₀.length + idx.length := by
      rw [List.length_map, hpsh2'.length_eq]; simp
    rw [show idx.length - 1 - i = (qsh.reverse.map (·.2)).length - 1 - (pre₀.length + i) by
        rw [hlh]; omega,
      Valuation.pushes_getElem σ (qsh.reverse.map (·.2)) _ (by rw [hlh]; omega),
      List.getElem_map] at g5
    have g6 := forall₂_getElem hxh' (i := pre₀.length + i) (by simp [xh]; omega)
    rw [hxhk] at g6
    exact g6.trans (g5.trans (g2.trans g4))

end abstract

end

end Lean4Lean.ShapeModel
