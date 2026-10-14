import Lean4Lean.Theory.Typing.Strengthening.EtaNormal
import Lean4Lean.Theory.Typing.Strengthening.EtaDuplicationBoundary
import Lean4Lean.Theory.Typing.Strengthening.PrefixStructureBoundary
import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Atomic head reflection through the terminal eta/normal phase

Non-proof, non-function variables cannot be reached from different syntax by
the terminal phase. At sort-typed endpoints a projection head likewise must
already exist. These are necessary field constraints for the selective
projection test, not a constructor-spine inversion theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A term whose type is a sort cannot also be a proof. -/
theorem sortTyped_not_isProof (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.sort u)) : ¬ IsProof Γ e := by
  rintro ⟨P, he, hP⟩
  exact HasType.sort_not_proof hΓ ht
    (hP.defeqU_l henv hΓ (ht.uniqU henv hΓ he).symm)

/-- A non-proof, non-function variable on the right fixes the original source,
even through an arbitrary finite eta phase and normal comparison. -/
theorem EtaNormal.bvar_right (hΓ : OnCtx Γ (env.IsType univs))
    (hna : ¬ IsProof Γ (.bvar i))
    (hnf : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (H : EtaNormal Γ e (.bvar i)) : e = .bvar i := by
  obtain ⟨mid, R, N⟩ := H
  have he := normal_bvar_eq_of_nonfunction hna hnf (N.symm hΓ)
  subst mid
  exact R.bvar_source

/-- Normal comparison to a projection that is neither a proof nor a function
has a projection at the same family and index on its other side. -/
theorem normal_proj_right_of_nonfunction
    (hna : ¬ IsProof Γ (.proj family index major))
    (hnf : ∀ A B, ¬ env.HasType univs Γ (.proj family index major) (.forallE A B))
    (H : NormalEq Γ e (.proj family index major)) :
    ∃ major', e = .proj family index major' := by
  obtain ⟨n, H⟩ := H
  generalize hout : VExpr.proj family index major = target at H
  cases H with
  | refl => exact ⟨major, hout.symm⟩
  | projDF => cases hout; exact ⟨_, rfl⟩
  | etaL hf _ => cases hout; exact (hnf _ _ hf).elim
  | etaBoth _ hf _ => cases hout; exact (hnf _ _ hf).elim
  | proofIrrel hp _ ht => cases hout; exact (hna ⟨_, ht, hp⟩).elim
  | sortDF | constDF | appDF | lamDF | forallEDF | etaR => cases hout

/-- At a sort-typed right endpoint, the terminal phase cannot create a
projection head. The original source need not have its own supplied typing. -/
theorem EtaNormal.sort_proj_source (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj family index major) (.sort u))
    (H : EtaNormal Γ e (.proj family index major)) :
    ∃ major', e = .proj family index major' := by
  obtain ⟨mid, R, N⟩ := H
  obtain ⟨major', rfl⟩ := normal_proj_right_of_nonfunction
    (sortTyped_not_isProof hΓ ht)
    (fun A B hf => (ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ) N
  exact R.proj_source

/-- Sort typing prevents both root eta forms at a variable, so every finite
compatible expansion of that variable is the identity. -/
theorem TypedEtaExpansion.sort_bvar_eq (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.bvar i) (.sort u))
    (R : TypedEtaExpansion Γ (.bvar i) out) : out = .bvar i := by
  have aux {Γ e out} (R : TypedEtaExpansion Γ e out) :
      ∀ {i u}, e = .bvar i → OnCtx Γ (env.IsType univs) →
        env.HasType univs Γ e (.sort u) → out = .bvar i := by
    induction R with
    | refl => exact fun h _ _ => h
    | structEta hi _ _ hm _ =>
      intro i u _ hΓ ht
      exact (structure_source_not_sort_or_pi hΓ hi hm (.inl ⟨u, ht⟩)).elim
    | funEta hf =>
      intro i u _ hΓ ht
      exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
    | trans R1 _ ih1 ih2 =>
      intro i u h hΓ ht
      exact ih2 (ih1 h hΓ ht) hΓ (R1.simAt hΓ _ ht).hasType.2
    | app | lam | forallE | proj => exact fun h _ _ => by cases h
  exact aux R rfl hΓ ht

/-- A sort-typed variable is fixed on either side of the terminal phase. -/
theorem EtaNormal.sort_bvar_eq (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.bvar i) (.sort u)) (H : EtaNormal Γ (.bvar i) out) :
    out = .bvar i := by
  obtain ⟨mid, R, N⟩ := H
  cases R.sort_bvar_eq hΓ ht
  exact normal_bvar_eq_of_nonfunction (sortTyped_not_isProof hΓ ht)
    (fun A B hf => (ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ) N

/-- Sort typing also prevents eta from changing an existing projection head.
Its major may still undergo an arbitrary finite expansion. -/
theorem TypedEtaExpansion.sort_proj_out (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj family index major) (.sort u))
    (R : TypedEtaExpansion Γ (.proj family index major) out) :
    ∃ major', out = .proj family index major' := by
  generalize hsrc : VExpr.proj family index major = source at R ht
  induction R generalizing major u with
  | refl => exact ⟨major, hsrc.symm⟩
  | structEta hi _ _ hm _ =>
    exact (structure_source_not_sort_or_pi hΓ hi hm (.inl ⟨u, ht⟩)).elim
  | funEta hf => exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  | trans R1 _ ih1 ih2 =>
    obtain ⟨major', he⟩ := ih1 hΓ hsrc ht
    exact ih2 hΓ he.symm (R1.simAt hΓ _ ht).hasType.2
  | proj => cases hsrc; exact ⟨_, rfl⟩
  | app | lam | forallE => cases hsrc

end Lean4Lean.VEnv.Strengthening.PureObservation
