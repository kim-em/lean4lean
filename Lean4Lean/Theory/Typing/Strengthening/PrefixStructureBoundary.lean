import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixFactorization
import Lean4Lean.Theory.Typing.Strengthening.StructureReconstruction

/-! # Structure eta needs a richer terminal comparison

A non-proof variable at a registered structure type admits an actual structure
eta step, but no PrefixCompute path followed by ordinary NormalEq can perform
that expansion. This refutes extending the current factorization unchanged to
FullReduction; it is not a strengthening counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Ordinary normal comparison fixes a variable whose type is neither a
proposition nor a Pi. Structure eta is not among its constructors. -/
theorem normal_bvar_eq_of_nonfunction
    (hna : ¬ IsProof Γ (.bvar i))
    (hnf : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (H : NormalEq Γ (.bvar i) out) : out = .bvar i := by
  obtain ⟨n, H⟩ := H
  generalize hsrc : VExpr.bvar i = source at H
  cases H with
  | refl => cases hsrc; rfl
  | sortDF | constDF | appDF | projDF | lamDF | forallEDF | etaL => cases hsrc
  | etaR hf _ => cases hsrc; exact (hnf _ _ hf).elim
  | etaBoth hf _ _ => cases hsrc; exact (hnf _ _ hf).elim
  | proofIrrel hp ha _ => cases hsrc; exact (hna ⟨_, ha, hp⟩).elim

/-- Prefix computation and ordinary normal comparison together still fix such
variables, regardless of the supplied collection of closed equations. -/
theorem PrefixNormal.bvar_eq_of_nonfunction
    (hna : ¬ IsProof Γ (.bvar i))
    (hnf : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (H : PrefixNormal D Γ (.bvar i) out) : out = .bvar i := by
  obtain ⟨mid, R, H⟩ := H
  cases R.bvar_eq
  exact normal_bvar_eq_of_nonfunction hna hnf H

/-- An actual structure eta step at a non-proof variable cannot have the current
computation/normal factorization. All declaration and endpoint typing premises
are retained, so no untyped structure expansion is being used. -/
theorem structure_eta_not_prefixNormal (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (ht : env.HasType univs Γ (.bvar i) (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun j => .proj family j (.bvar i)))
      (mkApps (.const family levels) params))
    (hna : ¬ IsProof Γ (.bvar i)) :
    FullStep Γ (.bvar i)
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun j => .proj family j (.bvar i))) ∧
    ¬ PrefixNormal D Γ (.bvar i)
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun j => .proj family j (.bvar i))) := by
  refine ⟨.structEta hi hp hx ht hc, ?_⟩
  intro H
  have hnf : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B) := by
    intro A B hf
    obtain ⟨_, hsort⟩ := ht.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hsort
      (ht.uniqU henv hΓ hf)
  have he := H.bvar_eq_of_nonfunction hna hnf
  have he := congrArg VExpr.getAppFn he
  simp only [getAppFn_mkApps, getAppFn] at he
  cases he

/-- A never-zero structure universe supplies both the expanded typing and the
non-proof condition. Only the original variable typing is assumed. -/
theorem structure_eta_neverZero_not_prefixNormal (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hl : levels.length = info.uvars)
    (hp : params.length = info.nparams) (hx : info.nindices = 0)
    (hz : (info.resultLevel.inst levels).IsNeverZero)
    (ht : env.HasType univs Γ (.bvar i) (mkApps (.const family levels) params)) :
    FullStep Γ (.bvar i) (structExpand family info levels params (.bvar i)) ∧
    ¬ PrefixNormal D Γ (.bvar i) (structExpand family info levels params (.bvar i)) := by
  have hc := StructureReplay.structure_constructor_neverZero henv hΓ hi hp hx hz ht
  apply structure_eta_not_prefixNormal hΓ hi hp hx ht hc
  rintro ⟨P, htP, hP⟩
  have hAP := ht.uniqU henv hΓ htP
  have hA0 := hP.defeqU_l henv hΓ hAP.symm
  have hAu := HasType.projectionFamily_sort henv hΓ hi hl hp
    (indexArgs := []) (by simpa using hx.symm) (by
      simpa only [List.append_nil] using (ht.isType henv hΓ).elim (fun _ h => ⟨_, h⟩))
  simp only [List.append_nil] at hAu
  have he := (hAu.uniqU henv hΓ hA0).sort_inv henv hΓ
  exact (hz.of_equiv he) [] rfl

/-- Every well-formed unindexed structure family at a never-zero universe gives
a concrete obstruction in its fresh-variable context. No inhabitant below the
new binder or typing of the expanded endpoint is required. -/
theorem fresh_structure_eta_not_prefixNormal (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hl : levels.length = info.uvars)
    (hp : params.length = info.nparams) (hx : info.nindices = 0)
    (hz : (info.resultLevel.inst levels).IsNeverZero)
    (hA : env.HasType univs Γ (mkApps (.const family levels) params) (.sort u)) :
    let Δ := mkApps (.const family levels) params :: Γ
    FullStep Δ (.bvar 0) (structExpand family info levels (params.map VExpr.lift) (.bvar 0)) ∧
    ¬ PrefixNormal D Δ (.bvar 0)
      (structExpand family info levels (params.map VExpr.lift) (.bvar 0)) := by
  apply structure_eta_neverZero_not_prefixNormal (Γ := _ :: Γ) ⟨hΓ, _, hA⟩ hi hl
    (by simpa only [List.length_map] using hp) hx hz
  simpa only [lift, liftN_mkApps, liftN, Nat.zero_add] using
    (HasType.bvar (env := env) (U := univs)
      (Lookup.zero (Γ := Γ) (ty := mkApps (.const family levels) params)))

end Lean4Lean.VEnv.Strengthening.PureObservation
