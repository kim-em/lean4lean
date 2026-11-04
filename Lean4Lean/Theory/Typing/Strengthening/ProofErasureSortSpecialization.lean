import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking

/-! # Images admitting an actual specialization to a type

An existential typed substitution can certify that an image cannot currently
be a function or a structure major. The witness may change the context and
retains actual image typing; no inhabitation or recovery law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A typed interpretation of the context makes this expression a type.
This certificate is deliberately not claimed stable under arbitrary substitution. -/
def SortSpecialization (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ Γ₀ σ u, OnCtx Γ₀ (env.IsType univs) ∧ Ctx.SubstEq env univs Γ₀ σ σ Γ ∧
    env.HasType univs Γ₀ (e.subst σ) (.sort u)

/-- An actual type admits the identity specialization. -/
theorem SortSpecialization.of_type (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.sort u)) : SortSpecialization Γ e :=
  ⟨Γ, VExpr.Subst.id, u, hΓ, Ctx.SubstEq.id henv.ordered hΓ, by simpa using he⟩

/-- Ordinary equality preserves the existence of a typed specialization. -/
theorem SortSpecialization.back (H : SortSpecialization Γ e')
    (HE : env.IsDefEq univs Γ e e' T) : SortSpecialization Γ e := by
  obtain ⟨Γ₀, σ, u, hΓ₀, W, ht⟩ := H
  have HE' := HE.subst henv.orderedStrong W hΓ₀
  exact ⟨Γ₀, σ, u, hΓ₀, W, (HE'.toU.of_r henv hΓ₀ ht).hasType.1⟩

/-- A new local binder can be interpreted over the same specializing context. -/
theorem SortSpecialization.weak (H : SortSpecialization Γ e)
    (hA : env.HasType univs Γ A (.sort u)) : SortSpecialization (A :: Γ) e.lift := by
  obtain ⟨Γ₀, σ, v, hΓ₀, W, ht⟩ := H
  have hA' := hA.subst henv.orderedStrong W hΓ₀
  refine ⟨A.subst σ :: Γ₀, σ.lift, v, ⟨hΓ₀, _, hA'⟩, W.lift henv.ordered hA, ?_⟩
  simpa only [VExpr.lift_subst_lift, VExpr.lift, VExpr.liftN] using (ht.weak henv).hasType.1

/-- A proof cannot specialize to a type under an actual typed substitution. -/
theorem SortSpecialization.not_isProof (H : SortSpecialization Γ e) : ¬ IsProof Γ e := by
  obtain ⟨Γ₀, σ, _, hΓ₀, W, ht⟩ := H
  intro hp
  obtain ⟨P, he, hP⟩ := hp
  exact not_isProof_of_sort hΓ₀ ht ((isProof_subst hΓ₀ W he).2 ⟨P, he, hP⟩)

/-- A currently function-typed term cannot specialize to a type: substitution
retains its Pi type, contradicting uniqueness against the witnessed sort. -/
theorem SortSpecialization.not_function (H : SortSpecialization Γ e)
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  obtain ⟨Γ₀, σ, _, hΓ₀, W, ht⟩ := H
  exact (ht.uniqU henv hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)).sort_forallE_inv henv hΓ₀

/-- A structure-typed term likewise cannot specialize to a type. -/
theorem SortSpecialization.not_structure (H : SortSpecialization Γ e)
    (hi : env.projections family info)
    (he : env.HasType univs Γ e (VExpr.mkApps (.const family ls) ps)) : False := by
  obtain ⟨Γ₀, σ, _, hΓ₀, W, ht⟩ := H
  have he' := he.subst henv.orderedStrong W hΓ₀
  simp only [VExpr.subst_mkApps, VExpr.subst_const] at he'
  exact HasType.sortTele_not_rigid (as := []) (doms := []) hΓ₀ (henv.projectionRigid hi) ht he'

/-- Every value of a generic successor-universe type parameter specializes to
a type by replacing that parameter with its predecessor universe. Arbitrary
local binders above the parameter remain in the interpreted context. -/
theorem SortSpecialization.type_parameter
    (W : Ctx.InstN Γ₀ (.sort u) (.sort (.succ u)) k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (he : env.HasType univs Γ e (.bvar k)) : SortSpecialization Γ e := by
  have hp : env.HasType univs Γ₀ (.sort u) (.sort (.succ u)) := .sort hu
  have hΓ' := (W.wf henv.ordered hp hΓ).2
  refine ⟨Γ', (VExpr.Subst.one (.sort u)).liftN k, u, hΓ', W.substEq hΓ hp, ?_⟩
  have he' := he.instN henv.ordered W hp
  simpa only [← VExpr.instN_eq, VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte,
    Nat.sub_self, VExpr.liftN] using he'

/-- Beta substitution preserves a type test when the body's test is the lift
of the surrounding interpretation. This is the coherent local law required
by a recovery path; arbitrary existential test witnesses do not suffice. -/
theorem SortSpecialization.inst_of_lifted_test {b : VExpr}
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs (A.subst σ :: Γ₀) (b.subst σ.lift) (.sort u)) :
    SortSpecialization Γ (b.inst a) := by
  refine ⟨Γ₀, σ, u, hΓ₀, W, ?_⟩
  rw [VExpr.subst_inst]
  exact hb.instN henv.ordered .zero (ha.subst henv.orderedStrong W hΓ₀)

end Lean4Lean.VEnv.Strengthening
