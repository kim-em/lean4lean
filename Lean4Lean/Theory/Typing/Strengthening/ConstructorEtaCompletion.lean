import Lean4Lean.Theory.Typing.Strengthening.ProjectionPathSpecialization
import Lean4Lean.Theory.Typing.Strengthening.CompletedEtaPhase

/-! # Completing finite computation after constructor eta

An existing saturated constructor supplies each projected field independently.
Every finite prefix-computation path from its eta expansion therefore joins an
actual computation of the original constructor. No normalization or confluence
assumption is used, and its parameters and fields may be arbitrary expressions.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Assemble independent finite joins into one list of common endpoints. -/
theorem forall₂_common_targets {R : α → γ → Prop} {S : β → γ → Prop}
    {xs : List α} {ys : List β} (hlen : xs.length = ys.length)
    (H : ∀ i (hx : i < xs.length) (hy : i < ys.length), ∃ z, R xs[i] z ∧ S ys[i] z) :
    ∃ zs, List.Forall₂ R xs zs ∧ List.Forall₂ S ys zs := by
  classical
  let pick (i : Fin xs.length) := Classical.choose (H i i.isLt (by omega))
  have hpick (i : Fin xs.length) : R xs[i] (pick i) ∧ S ys[i] (pick i) :=
    Classical.choose_spec (H i i.isLt (by omega))
  refine ⟨List.ofFn pick, ?_, ?_⟩
  · apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simpa using (hpick ⟨i, hi⟩).1
  · apply List.forall₂_of_getElem (by simpa using hlen.symm)
    intro i hi hi'
    simpa using (hpick ⟨i, by omega⟩).2

variable [Params] {D : Definitions}

/-- Compute a function and every argument along a finite application spine. -/
theorem PrefixCompute.mkApps_paths (R : PrefixCompute D Γ f f')
    (HA : List.Forall₂ (PrefixCompute D Γ) args args') :
    PrefixCompute D Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact R
  | cons H _ ih => exact ih (.app R H)

/-- Finite computation after expanding an existing saturated constructor has
an exact computational join with the original constructor. The expansion uses
its original parameter prefix and universe instance. Computation inside every
copy of every field is unrestricted. -/
theorem constructor_eta_compute_join
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hf : fields.length = info.numFields)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (R : PrefixCompute D Γ
      (structExpand family info levels params
        (VExpr.mkApps (.const info.ctorName levels) (params ++ fields))) out) :
    ∃ result, PrefixCompute D Γ
        (VExpr.mkApps (.const info.ctorName levels) (params ++ fields)) result ∧
      PrefixCompute D Γ out result := by
  obtain ⟨outArgs, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi) hn
  have hlen : (params ++ fields).length = outArgs.length := by
    simpa [hf] using HA.length_eq
  have htarget : ∀ j (hj : j < (params ++ fields).length) (ho : j < outArgs.length),
      ∃ z, PrefixCompute D Γ (params ++ fields)[j] z ∧ PrefixCompute D Γ outArgs[j] z := by
    intro j hj ho
    have hsrc : j < (params ++ (List.range info.numFields).map
        (fun k => VExpr.proj family k (VExpr.mkApps (.const info.ctorName levels) (params ++ fields)))).length := by
      simpa [hf] using hj
    have H := HA.getElem_of j hsrc ho
    by_cases hjp : j < params.length
    · simp only [List.getElem_append_left hjp] at H ⊢
      exact ⟨_, H, .refl⟩
    · simp only [List.getElem_append_right (by omega : params.length ≤ j),
        List.getElem_map, List.getElem_range] at H
      apply H.projection_complete hi hn (by simp [hp, hf])
      have hk : info.nparams + (j - params.length) = j := by omega
      simp [hk]
  obtain ⟨targets, HS, HO⟩ := forall₂_common_targets hlen htarget
  exact ⟨_, PrefixCompute.mkApps_paths .refl HS, PrefixCompute.mkApps_paths .refl HO⟩

/-- The join gives a completed phase representation for the whole eta-root
followed by arbitrary finite computation. Source typing supplies the final
normal identity; no typing of separate duplicated copies is assumed. -/
theorem constructor_eta_completed_phase
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hf : fields.length = info.numFields)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (ht : env.HasType univs Γ
      (VExpr.mkApps (.const info.ctorName levels) (params ++ fields)) T)
    (R : PrefixCompute D Γ
      (structExpand family info levels params
        (VExpr.mkApps (.const info.ctorName levels) (params ++ fields))) out) :
    CompletedEtaPhase D Γ
      (VExpr.mkApps (.const info.ctorName levels) (params ++ fields)) out := by
  obtain ⟨result, RS, RO⟩ := constructor_eta_compute_join hi hp hf hn R
  exact ⟨result, RO, PrefixEtaNormal.compute hs hΓ RS ht⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
