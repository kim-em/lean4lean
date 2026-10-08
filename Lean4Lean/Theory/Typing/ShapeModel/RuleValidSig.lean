import Lean4Lean.Theory.Typing.ShapeModel.RuleValidGood
import Lean4Lean.Theory.Typing.ShapeModel.RuleValidDef

/-!
# Families and constructors of the semantic signature of a well-formed environment

Helpers for the validity of the rules of `envSig env`: the semantic header of the quotient, the
exclusion of families that are also constructors (`fam_not_ctor`, semantically: a constructor's
type ends in an application of a rigid family, a family's in a sort), and the realization of a
constructor application of the signature (`realize_sig`, for structure constructors through
`Ctor.realize` and for the other constructors through `Ctor.realize0`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem quot_famSem (hq : QuotInstalled env) :
    letI := envSig env; FamSem env ``Quot (.param 0) 2 := by
  letI := envSig env
  refine ⟨_, [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))], hq.quot,
    rfl, fun ls _ m => ?_⟩
  exact Iff.rfl

/-- The structure facts of a registered projection follow from the semantic header of its
recorded family. -/
theorem famTypeSem_of_famSem (H : env.WF) (hp : env.projections s info)
    (hsem : letI := envSig env; FamSem env s info.resultLevel (info.nparams + info.nindices)) :
    FamTypeSem env s info := by
  letI := envSig env
  obtain ⟨ci, Ds, hci, hlen, hiff⟩ := hsem
  obtain ⟨ci', hci', huv, -⟩ := famOf_shape H (famOf_projection H hp)
  cases hci.symm.trans hci'
  exact ⟨ci, Ds, hci, huv, hlen, fun ls hls m => hiff ls (by rw [hls, huv]) m⟩

/-- A family with a semantic header is not a constructor of the signature. -/
theorem fam_not_ctor (H : env.WF)
    (hsem : letI := envSig env; FamSem env I l n) (hk : sigCtor env I = some k) : False := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  obtain ⟨hc, cv, hcv, hF, -⟩ := sigCtor_spec hk
  obtain ⟨k', cv', doms, idx, hcv', -, ht, -⟩ := hc.shape H
  cases hcv.symm.trans hcv'
  rw [ht, familyOfType_shape, Option.some.injEq] at hF
  have hnr : ∀ r, SemSig.rules r → r.head ≠ .const k'.family := fun r hr =>
    EnvRule.head_not_rigid H (hF ▸ sigCtor_family_rigid H hk) hr
  obtain ⟨ci, Ds, hci, -, hiff⟩ := hsem
  cases hci.symm.trans hcv
  let ls := VLevel.params cv.uvars
  have hb := Interp.nestPi_bots_sort (env := env) (ρ := .nil) (Ds.map (·.instL ls)) (l.inst ls)
  have hb' : Interp env .nil (nestPi ((Ds.map (·.instL ls)).map fun _ => (TShape.bot, TShape.bot))
      (TShape.sort (l.inst ls).eval)) (VExpr.instL ls (Ds.foldr .forallE (.sort l))) := by
    rw [VExpr.instL_foldr_forallE]; exact hb
  have := (hiff ls (by simp [ls]) _).2 hb'
  rw [ht] at this
  change Interp env .nil _ (VExpr.instL ls (doms.foldr .forallE _)) at this
  rw [VExpr.instL_foldr_forallE, VExpr.instL_mkApps] at this
  exact Interp.nestPi_fam_absurd hnr this

/-- The realization of a constructor application of the signature: if the constructor's family
is not a proposition at the levels, a constructor shape whose stored fields are above the
approximations of the stored arguments approximates the application. -/
theorem realize_sig (H : env.WF) (W : letI := envSig env; Valuation.Fits env Γ₀ Γ ρ)
    (hci : sigCtor env c = some ci)
    (hfamd : famOf env ci.family = some d)
    (hsem : letI := envSig env; FamSem env ci.family d.resultLevel n)
    (hstr : ∀ {s info}, env.projections s info → info.ctorName = c → FamTypeSem env s info)
    (hTy : letI := envSig env; StrongSound env Γ (VExpr.mkApps (.const c ls) args) T)
    (hlen : args.length = ci.nparams + ci.nfields)
    (hxs : letI := envSig env; List.Forall₂ (fun x A => Interp env ρ x A) xs args)
    (hfp : letI := envSig env; SemSig.famProp ci.family (ls.map (·.eval)) = false) :
    letI := envSig env
    ∃ n, ∃ fs : List (WShape n), fs.length = ci.nfields ∧
      Interp env ρ (WShape.ctor' c fs).T (VExpr.mkApps (.const c ls) args) ∧
      List.Forall₂ (fun x f => x ≤ f.T) (xs.drop ci.nparams) fs := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  have hcl : ConstClosed env := fun h => H.ordered.closedC h
  obtain ⟨hic, cv, hcv, hF, hnp, hnf⟩ := sigCtor_spec hci
  rcases structNp_eq H c with h0 | ⟨s, info, hp, hcn, hnpi⟩
  · have hnp0 : ci.nparams = 0 := hnp.trans h0
    obtain ⟨k', cv', doms, idx, hcv', huv, ht, hdl⟩ := hic.shape H
    cases hcv.symm.trans hcv'
    rw [ht, familyOfType_shape, Option.some.injEq] at hF
    have hnf' : ci.nfields = doms.length := by
      rw [hnf, h0, ht, forallArity_shape]; rfl
    have hci' : SemSig.ctor c = some ⟨ci.family, 0, ci.nfields⟩ := by
      show sigCtor env c = _
      rw [hci]; cases ci; simp only at hnp0; subst hnp0; rfl
    have hnc : SemSig.ctor ci.family = none := by
      show sigCtor env ci.family = none
      cases h : sigCtor env ci.family with
      | none => rfl
      | some k => exact (fam_not_ctor H hsem h).elim
    have hnr : ∀ r, SemSig.rules r → r.head ≠ .const ci.family := fun r hr =>
      (envSig_ctorType H hci hcv).1 r hr
    have hl : SemSig.famLevel ci.family = some d.resultLevel := by
      show sigFamLevel env ci.family = _; simp [sigFamLevel, hfamd]
    have hmem : c ∈ SemSig.famCtors ci.family := (mem_sigFamCtors H).2 ⟨ci, hci, rfl⟩
    have hfc : ∀ c' ∈ SemSig.famCtors ci.family, ∃ ci k, env.constants c' = some ci ∧
        SemSig.ctor c' = some k := by
      intro c' hc'
      obtain ⟨k, hk, -⟩ := (mem_sigFamCtors H).1 hc'
      obtain ⟨-, cv'', hcv'', -⟩ := sigCtor_spec hk
      exact ⟨cv'', k, hcv'', hk⟩
    have ht' : cv.type = VExpr.wrapForalls doms
        (VExpr.mkApps (.const ci.family (VLevel.params cv.uvars)) (vars k'.nparams k'.nfields ++ idx)) := by
      rw [ht, huv, hF]
    obtain ⟨n', fs, hfl, hI, hfx⟩ := Ctor.realize0 hcl W hci' hcv ht' hnf'.symm hnc hnr hl hsem
      hmem hfc hTy (by rw [hlen, hnp0]; simp) hxs hfp
    exact ⟨n', fs, hfl, hI, by rw [hnp0, List.drop_zero]; exact hfx⟩
  · subst hcn
    have hF' := envSig_structFacts_of_wf H hp (hstr hp rfl)
    have hcis := sig_ctor_proj (env := env) (s := s) (info := info) H hp
    rw [hci, Option.some.injEq] at hcis
    subst hcis
    obtain ⟨-, h2⟩ := Ctor.realize hcl hF' W hTy hlen hxs
    obtain ⟨n', fs, hI, hfx⟩ := h2 hfp
    refine ⟨n', fs, ?_, hI, hfx⟩
    rw [← hfx.length_eq, List.length_drop, (hxs.length_eq), hlen]; simp

end

end Lean4Lean.ShapeModel
