import Lean4Lean.Theory.Typing.Strengthening.CompletedEtaPhase
import Lean4Lean.Theory.Typing.Strengthening.EtaAtomicConstructorReflection

/-! # Reparameterized eta obstructs computational completion

An eta root may use a family parameter convertible to the constructor's original
parameter. After projecting its field, this can replace a constructor-headed
parameter by a variable. A completed computation/eta/normal phase cannot make
that replacement when its target consists of atomic variables.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- The nested-parameter obstruction is repaired by eta expansion on the
right. Its direction is essential: further computation of that target alone
is insufficient. This identifies a requirement on any symmetric join model. -/
theorem constructor_parameter_reverse_eta
    (hi : env.projections innerFamily innerInfo)
    (hp : innerInfo.nparams = 0) (hx : innerInfo.nindices = 0)
    (hv : env.HasType univs Γ (.bvar i) (.const innerFamily innerLevels))
    (hc : env.HasType univs Γ (structExpand innerFamily innerInfo innerLevels [] (.bvar i))
      (.const innerFamily innerLevels)) :
    TypedEtaExpansion Γ (mkApps (.const outer levels) [.bvar i, field])
      (mkApps (.const outer levels)
        [structExpand innerFamily innerInfo innerLevels [] (.bvar i), field]) :=
  .app (.app .refl (.structEta hi hp.symm hx hv hc)) .refl

/-- A constructor-headed parameter cannot disappear into an atomic variable
through the completed phase. The target constructor is computationally fixed,
and terminal reflection forces its variable arguments before eta as well. -/
theorem constructor_parameter_not_completed
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hf : 0 < info.numFields)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hr : env.Rigid inner) (hnInner : ∀ levels rhs, ¬ D.unfolds inner levels rhs)
    (hnp : ¬ env.HasType univs Γ (mkApps (.const family levels) [.bvar i]) (.sort .zero))
    (ht : env.HasType univs Γ
      (mkApps (.const info.ctorName levels) [mkApps (.const inner innerLevels) innerArgs, .bvar j])
      (mkApps (.const family levels) [.bvar i]))
    (hvi : ¬ IsProof Γ (.bvar i))
    (hfi : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (hvj : env.HasType univs Γ (.bvar j) (.sort u)) :
    ¬ CompletedEtaPhase D Γ
      (mkApps (.const info.ctorName levels) [mkApps (.const inner innerLevels) innerArgs, .bvar j])
      (mkApps (.const info.ctorName levels) [.bvar i, .bvar j]) := by
  rintro ⟨out, RR, HP⟩
  obtain ⟨middle, RC, HE⟩ := PrefixEtaNormal.terminal_iff.1 HP
  have hfix := RR.constructor_bvar_spine_fixed hi hn (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩)
  cases hfix
  obtain ⟨midArgs, rfl, HA⟩ := RC.rigid_spine_paths (henv.projectionCtorRigid hi) hn
  have hm := (RC.simAt hs hΓ _ ht).hasType.2
  have hvars : ∀ e ∈ ([.bvar i, .bvar j] : List VExpr), ∃ k, e = .bvar k ∧
      ¬ IsProof Γ (.bvar k) ∧ ∀ A B, ¬ env.HasType univs Γ (.bvar k) (.forallE A B) := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨i, rfl, hvi, hfi⟩
    · exact ⟨j, rfl, sortTyped_not_isProof hΓ hvj,
        fun A B h => (hvj.uniqU henv hΓ h).sort_forallE_inv henv hΓ⟩
  have hargs := HE.atomic_constructor_args hΓ hi hf hnp hm hvars
  cases hargs
  have H0 := HA.getElem_of 0 (by simp) (by simp)
  simp only [List.getElem_cons_zero] at H0
  obtain ⟨args', he, _⟩ := H0.rigid_spine hr hnInner
  have hh := congrArg getAppFn he
  simp only [getAppFn_mkApps, getAppFn] at hh
  cases hh

/-- A genuine structure-eta root using a converted family parameter, followed
by one field projection, reaches the atomic target excluded above. Both actual
root typings are retained; no parameter-change reduction is invented. -/
theorem reparameterized_eta_completion_boundary
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hr : env.Rigid inner) (hnInner : ∀ levels rhs, ¬ D.unfolds inner levels rhs)
    (hnp : ¬ env.HasType univs Γ (mkApps (.const family levels) [.bvar i]) (.sort .zero))
    (ht : env.HasType univs Γ
      (mkApps (.const info.ctorName levels) [mkApps (.const inner innerLevels) innerArgs, .bvar j])
      (mkApps (.const family levels) [.bvar i]))
    (hc : env.HasType univs Γ
      (structExpand family info levels [.bvar i]
        (mkApps (.const info.ctorName levels) [mkApps (.const inner innerLevels) innerArgs, .bvar j]))
      (mkApps (.const family levels) [.bvar i]))
    (hvi : ¬ IsProof Γ (.bvar i))
    (hfi : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B))
    (hvj : env.HasType univs Γ (.bvar j) (.sort u)) :
    let source := mkApps (.const info.ctorName levels)
      [mkApps (.const inner innerLevels) innerArgs, .bvar j]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .bvar j]
    FullReduction Γ source target ∧ ¬ CompletedEtaPhase D Γ source target := by
  intro source target
  refine ⟨?_, constructor_parameter_not_completed hs hΓ hi (by omega) hn hr hnInner hnp ht hvi hfi hvj⟩
  have RE : FullReduction Γ source (structExpand family info levels [.bvar i] source) :=
    .tail .rfl (.structEta hi (by simpa using hp.symm) hx ht hc)
  have he : structExpand family info levels [.bvar i] source =
      mkApps (.const info.ctorName levels) [.bvar i, .proj family 0 source] := by
    simp [structExpand, hf, List.range_succ]
  rw [he] at RE hc
  obtain ⟨F, hproj⟩ := mkApps_arg_type hΓ hc (arg := .proj family 0 source) (by simp)
  have hg : ([mkApps (.const inner innerLevels) innerArgs, .bvar j] : List VExpr)[info.nparams + 0]? =
      some (.bvar j) := by simp [hp]
  have hlen : ([mkApps (.const inner innerLevels) innerArgs, .bvar j] : List VExpr).length =
      info.nparams + info.numFields := by simp [hp, hf]
  have RF : FullReduction Γ (.proj family 0 source) (.bvar j) :=
    .tail .rfl (.projIota hi hproj hg (HasType.projIota_field hΓ hi hproj hlen hg))
  exact RE.trans (FullReduction.app .rfl RF)


private theorem family_neverZero_not_prop
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hl : levels.length = info.uvars) (hp : params.length = info.nparams)
    (hx : info.nindices = 0) (hz : (info.resultLevel.inst levels).IsNeverZero)
    (ht : VExpr.WF env univs Γ (mkApps (.const family levels) params)) :
    ¬ env.HasType univs Γ (mkApps (.const family levels) params) (.sort .zero) := by
  intro hzero
  have hf := HasType.projectionFamily_sort henv hΓ hi hl hp
    (indexArgs := []) (by simpa using hx.symm) (by simpa using ht)
  simp only [List.append_nil] at hf
  exact (hz.of_equiv ((hf.uniqU henv hΓ hzero).sort_inv henv hΓ)) [] rfl

/-- Ordinary nested structure eta supplies the converted parameter needed by
the obstruction. The source is assumed only at its canonical constructor
family. Never-zero universes derive both eta-root typings and non-proofness.
This remains conditional on the displayed registered structures and typings;
it does not construct a canonical-Eq environment or refute strengthening. -/
theorem nested_structure_eta_completion_boundary
    (hΓ : OnCtx Γ (env.IsType univs))
    (hiInner : env.projections innerFamily innerInfo)
    (hpInner : innerInfo.nparams = 0) (hxInner : innerInfo.nindices = 0)
    (hlInner : innerLevels.length = innerInfo.uvars)
    (hzInner : (innerInfo.resultLevel.inst innerLevels).IsNeverZero)
    (hi : env.projections family info)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : levels.length = info.uvars)
    (hz : (info.resultLevel.inst levels).IsNeverZero)
    (hvi : env.HasType univs Γ (.bvar i) (.const innerFamily innerLevels))
    (hvj : env.HasType univs Γ (.bvar j) (.sort u))
    (ht : env.HasType univs Γ
      (mkApps (.const info.ctorName levels)
        [structExpand innerFamily innerInfo innerLevels [] (.bvar i), .bvar j])
      (mkApps (.const family levels)
        [structExpand innerFamily innerInfo innerLevels [] (.bvar i)])) :
    let source := mkApps (.const info.ctorName levels)
      [structExpand innerFamily innerInfo innerLevels [] (.bvar i), .bvar j]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .bvar j]
    FullReduction Γ source target ∧
      ¬ CompletedEtaPhase (Definitions.ofEnv env univs henv) Γ source target := by
  intro source target
  have hcInner := StructureReplay.structure_constructor_neverZero henv hΓ hiInner
    (params := []) hpInner.symm hxInner hzInner hvi
  have HEInner := IsDefEq.structEta hiInner (params := []) hpInner.symm hxInner hvi hcInner
  obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
  obtain ⟨A, B, hhead, hparam⟩ := hfamily.app_inv henv hΓ
  have HEFamily := IsDefEq.appDF hhead (HEInner.toU.of_l henv hΓ hparam)
  have ht' := ht.defeqU_r henv hΓ HEFamily.toU
  have hc := StructureReplay.structure_constructor_neverZero henv hΓ hi
    (params := [.bvar i]) (by simpa using hp.symm) hx hz ht'
  have hnp := family_neverZero_not_prop hΓ hi hl (params := [.bvar i])
    (by simpa using hp.symm) hx hz ((ht'.isType henv hΓ).elim (fun _ h => ⟨_, h⟩))
  have hnpInner := family_neverZero_not_prop hΓ hiInner hlInner (params := [])
    hpInner.symm hxInner hzInner ((hvi.isType henv hΓ).elim (fun _ h => ⟨_, h⟩))
  have hviNotProof : ¬ IsProof Γ (.bvar i) := by
    rintro ⟨P, hterm, hP⟩
    exact hnpInner (hP.defeqU_l henv hΓ (hvi.uniqU henv hΓ hterm).symm)
  have hviNotFunction : ∀ A B, ¬ env.HasType univs Γ (.bvar i) (.forallE A B) := by
    intro A B hfun
    obtain ⟨_, hinner⟩ := hvi.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hiInner)
      (args := []) hinner (hvi.uniqU henv hΓ hfun)
  exact reparameterized_eta_completion_boundary (Definitions.ofEnv_sound henv) hΓ hi hp hx hf
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hi))
    (henv.projectionCtorRigid hiInner)
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hiInner))
    hnp ht' hc hviNotProof hviNotFunction hvj

end Lean4Lean.VEnv.Strengthening.PureObservation
