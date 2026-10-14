import Lean4Lean.Theory.Typing.Strengthening.EtaDuplicationNormalBoundary
import Lean4Lean.Theory.Typing.Strengthening.PrefixConstructorFixed
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaCompatibility

/-! # Selective projection obstructs computation/eta/normal factorization

A registered two-field constructor with sort-typed variable fields is fixed by
the initial computational phase. Structure eta followed by selective projection
contraction nevertheless reaches a target outside the eta/normal terminal phase.
All registration, source typing and eta-root typing premises remain explicit.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Completing the other projection returns the obstructing mixed target to
the original constructor. Thus this example does not refute factorization up
to a further computational join. No typing premise is needed for this path. -/
theorem selective_projection_computes_back
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    PrefixCompute D Γ
      (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) source := by
  intro source
  apply PrefixCompute.app .refl
  apply PrefixCompute.base (PatternCompute.base (ProjectionCompute.projIota hi _ _))
  · simp [hp, hf]
  · simp [hp]

/-- No initial computation can repair the selective-projection obstruction
when the declaration collection preserves the constructor's rigidity. -/
theorem selective_projection_not_prefixEtaNormal
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hproj : env.HasType univs Γ (.proj family 0
      (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])) (.sort v)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    ¬ PrefixEtaNormal D Γ source
      (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) := by
  intro source H
  obtain ⟨mid, RC, HE⟩ := PrefixEtaNormal.terminal_iff.1 H
  have he := RC.constructor_bvar_spine_fixed hi hn (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha
    exact ⟨i, ha⟩)
  cases he
  exact selective_projection_not_etaNormal hΓ hi hp hf hnp ht hv hproj HE

/-- An actual finite FullReduction lies outside the proposed three-phase
representation. Sort typing of the first projection is derived from the eta
root's expanded typing and projection iota, rather than assumed separately. -/
theorem selective_projection_phase_boundary
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hc : env.HasType univs Γ
      (structExpand family info levels [] (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]))
      (.const family levels)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]
    FullReduction Γ source target ∧ ¬ PrefixEtaNormal D Γ source target := by
  intro source target
  refine ⟨selective_projection_full hΓ hi hp hx hf ht hc, ?_⟩
  have hc' : env.HasType univs Γ
      (mkApps (.const info.ctorName levels) [.proj family 0 source, .proj family 1 source])
      (.const family levels) := by
    simpa [source, structExpand, hf, List.range_succ] using hc
  obtain ⟨F, hproj⟩ := mkApps_arg_type hΓ hc' (arg := .proj family 0 source) (by simp)
  have hlen : ([.bvar i, .bvar i] : List VExpr).length = info.nparams + info.numFields := by
    simp [hp, hf]
  have hg : ([.bvar i, .bvar i] : List VExpr)[info.nparams + 0]? = some (.bvar i) := by
    simp [hp]
  have HE : env.IsDefEq univs Γ (.proj family 0 source) (.bvar i) F :=
    .projIota hi hproj hg (HasType.projIota_field hΓ hi hproj hlen hg)
  have hprojSort := (HE.toU.of_r henv hΓ hv).hasType.1
  exact selective_projection_not_prefixEtaNormal hΓ hi hn hp hf hnp ht hv hprojSort

/-- The obstruction applies to the environment's actual stored declarations;
their inability to unfold the registered constructor is automatic. -/
theorem selective_projection_env_phase_boundary
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hc : env.HasType univs Γ
      (structExpand family info levels [] (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]))
      (.const family levels)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]
    FullReduction Γ source target ∧
      ¬ PrefixEtaNormal (Definitions.ofEnv env univs henv) Γ source target :=
  selective_projection_phase_boundary hΓ hi
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hi))
    hp hx hf hnp ht hv hc

/-- A never-zero family universe supplies non-propositionality and the eta
root's expanded typing. The only expression typings assumed are the source
constructor and its repeated variable field. -/
theorem selective_projection_neverZero_phase_boundary
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hl : levels.length = info.uvars)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hz : (info.resultLevel.inst levels).IsNeverZero)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]
    FullReduction Γ source target ∧
      ¬ PrefixEtaNormal (Definitions.ofEnv env univs henv) Γ source target := by
  have hc := StructureReplay.structure_constructor_neverZero henv hΓ hi
    (params := []) hp.symm hx hz ht
  apply selective_projection_env_phase_boundary hΓ hi hp hx hf _ ht hv hc
  intro hzero
  have hfamily := HasType.projectionFamily_sort henv hΓ hi hl (params := []) hp.symm
    (indexArgs := []) (by simpa using hx.symm)
    ((ht.isType henv hΓ).elim (fun _ h => ⟨_, h⟩))
  have he := (hfamily.uniqU henv hΓ hzero).sort_inv henv hΓ
  exact (hz.of_equiv he) [] rfl

/-- The obstructing path consists of two individually representable phases
with a commonly typed middle. Thus typed transitivity of PrefixEtaNormal is
already false under these explicit structure and typing assumptions. -/
theorem selective_projection_phase_nontransitive
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hc : env.HasType univs Γ
      (structExpand family info levels [] (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]))
      (.const family levels)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    let target := mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]
    ∃ middle, env.HasType univs Γ middle (.const family levels) ∧
      PrefixEtaNormal D Γ source middle ∧ PrefixEtaNormal D Γ middle target ∧
      ¬ PrefixEtaNormal D Γ source target := by
  intro source target
  obtain ⟨RF, hno⟩ := selective_projection_phase_boundary hΓ hi hn hp hx hf hnp ht hv hc
  have RE : TypedEtaExpansion Γ source (structExpand family info levels [] source) :=
    .structEta hi hp.symm hx ht hc
  have RC : PrefixCompute D Γ (structExpand family info levels [] source) target := by
    have he : structExpand family info levels [] source =
        mkApps (.const info.ctorName levels) [.proj family 0 source, .proj family 1 source] := by
      simp [structExpand, hf, List.range_succ]
    rw [he]
    apply PrefixCompute.app (PrefixCompute.app .refl _) .refl
    apply PrefixCompute.base (PatternCompute.base (ProjectionCompute.projIota hi _ _))
    · simp [hp, hf]
    · simp [hp]
  have htTarget := (RF.defeq hΓ ht).hasType.2
  exact ⟨_, hc, PrefixEtaNormal.of_terminal (EtaNormal.expansion hΓ RE ht),
    PrefixEtaNormal.terminal_iff.2 ⟨_, RC, EtaNormal.normal (.refl htTarget)⟩, hno⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
