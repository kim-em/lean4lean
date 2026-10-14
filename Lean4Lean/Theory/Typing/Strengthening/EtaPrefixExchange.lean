import Lean4Lean.Theory.Typing.Strengthening.EtaExpansionHeads
import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Moving argument eta expansions past actual prefixes

An actual prefix checked after its arguments expand can be checked before those
expansions. The earlier output then expands by eta to a term normally
equal to the later output. This root exchange retains every original check and
requires neither canonical Eq nor a proposition-front hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Pointwise eta expansion gives typed argument conversion from source
well-formedness. The intermediate argument types need not be supplied separately. -/
theorem TypedEtaExpansion.spine_defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (ht : env.HasType univs Γ (mkApps f args) T) :
    List.Forall₂ (env.IsDefEqU univs Γ) args args' := by
  apply List.forall₂_of_getElem H.length_eq
  intro i hi hi'
  obtain ⟨_, ha⟩ := mkApps_arg_type hΓ ht (List.getElem_mem hi)
  exact ⟨_, (H.getElem_of i hi hi').simAt hΓ _ ha⟩

/-- Singleton prefix contraction commutes to before compatible function and structure
expansions of its supplied arguments. Residual domain changes stay in NormalEq. -/
theorem singleton_prefix_eta_exchange (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T)
    (R : PrefixUnfold env univs recursorData Γ name levels args' rhs') :
    ∃ rhs mid, PrefixUnfold env univs recursorData Γ name levels args rhs ∧
      TypedEtaExpansion Γ rhs mid ∧ NormalEq Γ mid rhs' := by
  have HE := TypedEtaExpansion.spine_defeq hΓ H ht
  obtain ⟨rhs, RR⟩ := R.congr_defeq hΓ (HE.flip.imp (fun _ _ (h : env.IsDefEqU univs Γ _ _) => h.symm))
  obtain ⟨out, mid, R', HS, HN⟩ := RR.congr_red
    typedEtaExpansion_congrRel typedEtaExpansion_argRel hΓ H
  have he := PrefixUnfold.unique R R'
  subst out
  obtain ⟨n, HN⟩ := HN
  exact ⟨rhs, mid, RR, HS, n, HN.toTrue⟩

/-- The same root exchange holds for every actual quotient prefix. -/
theorem quotient_prefix_eta_exchange (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (R : QuotPrefixUnfold env univs Γ levels args' rhs') :
    ∃ rhs mid, QuotPrefixUnfold env univs Γ levels args rhs ∧
      TypedEtaExpansion Γ rhs mid ∧ NormalEq Γ mid rhs' := by
  have HE := TypedEtaExpansion.spine_defeq hΓ H ht
  obtain ⟨rhs, RR⟩ := R.congr_defeq hΓ (HE.flip.imp (fun _ _ (h : env.IsDefEqU univs Γ _ _) => h.symm))
  obtain ⟨out, mid, R', HS, HN⟩ := RR.congr_red
    typedEtaExpansion_congrRel typedEtaExpansion_argRel hΓ H
  have he := QuotPrefixUnfold.unique R R'
  subst out
  obtain ⟨n, HN⟩ := HN
  exact ⟨rhs, mid, RR, HS, n, HN.toTrue⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
