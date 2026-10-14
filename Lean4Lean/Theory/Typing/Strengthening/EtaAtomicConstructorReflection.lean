import Lean4Lean.Theory.Typing.Strengthening.NormalHeadBetaExposure
import Lean4Lean.Theory.Typing.Strengthening.EtaNormalHeadReflection

/-! # Atomic constructor arguments reflect through terminal eta

At a non-propositional family type, terminal eta/normal comparison to a
constructor of non-proof, non-function variables forces the original constant
spine to have those same arguments. A newly eta-created constructor has a
projected first field, which cannot become such a variable.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Reflection of every argument from a constructor whose arguments are atomic
variables. The constructor must have at least one field; zero-field eta would
provide no projected field with which to exclude a newly created head. -/
theorem EtaNormal.atomic_constructor_args
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hfields : 0 < info.numFields)
    (hnp : ¬ env.HasType univs Γ (mkApps (.const family familyLevels) params) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const c ls) args)
      (mkApps (.const family familyLevels) params))
    (hvars : ∀ e ∈ targetArgs, ∃ i, e = .bvar i ∧ ¬ IsProof Γ (.bvar i) ∧
      ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (H : EtaNormal Γ (mkApps (.const c ls) args)
      (mkApps (.const info.ctorName targetLevels) targetArgs)) : args = targetArgs := by
  obtain ⟨mid, RE, n, HN⟩ := H
  have htMid := (RE.simAt hΓ _ ht).hasType.2
  rcases normal_spine_expose_headBeta hΓ .const n HN (bs := []) .nil htMid with
    hproof | ⟨head, midArgs, hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, ha, hf⟩
  · exact (hnp hproof).elim
  · simp only [mkApps_nil] at RB
    simp only [List.append_nil] at HA
    cases hh with
    | const hls =>
      have RE' := eta_constant_headBeta hΓ RE ht RB
      rcases RE'.constructor_exposure hΓ ht with ⟨args0, he, HE⟩ | HE
      · have hargs := congrArg getAppArgs he
        simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at hargs
        cases hargs
        apply List.ext_getElem (HE.length_eq.trans HA.length_eq)
        intro j hj hj'
        have hjm : j < midArgs.length := by rw [← HE.length_eq]; exact hj
        have E := HE.getElem_of j hj hjm
        have N := HA.getElem_of j hjm hj'
        obtain ⟨i, hi, hnp, hnf⟩ := hvars _ (List.getElem_mem hj')
        rw [hi] at N
        exact (EtaNormal.bvar_right hΓ hnp hnf ⟨_, E, N⟩).trans hi.symm
      · obtain ⟨family', info', ps, hi', hc, hp, hx, hm, hz, hlen, HF⟩ := HE
        obtain ⟨hfamily, hinfo⟩ := henv.ordered.projectionConstructor_family hi' hi hc
        cases hinfo
        cases hfamily
        have hj : info.nparams < midArgs.length := by omega
        have hj' : info.nparams < targetArgs.length := by rw [← HA.length_eq]; exact hj
        have E := HF.getElem_of 0 (by simpa using hfields) (by simp; omega)
        simp only [List.getElem_map, List.getElem_range, List.getElem_drop, Nat.add_zero] at E
        have N := HA.getElem_of info.nparams hj hj'
        obtain ⟨i, hi, hnp, hnf⟩ := hvars _ (List.getElem_mem hj')
        rw [hi] at N
        have he := EtaNormal.bvar_right hΓ hnp hnf ⟨_, E, N⟩
        cases he
  · have htLam := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htMid).hasType.2
    obtain ⟨_, hY, _⟩ := htLam.lam_inv_forallE henv hΓ
    obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
    exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily hY.symm).elim
  · have htZ := (RB.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htMid).hasType.2
    obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
    exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily
      (htZ.uniqU henv hΓ hz)).elim

end Lean4Lean.VEnv.Strengthening.PureObservation
