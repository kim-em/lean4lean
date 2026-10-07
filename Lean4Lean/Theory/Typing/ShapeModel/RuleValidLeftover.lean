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

end abstract

end

end Lean4Lean.ShapeModel
