import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerFamilyShape
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Every enriched root primitive preserves constructor control observations

Data demands read their registered family from the lower type history. A
structure expansion therefore creates a new payload even inside a control
body whose fields mention temporary variables. Function demands preserve eta
and exclude structure guards. Compatible constructor-prefix evolution remains
the separate missing case for a full computation-preservation induction.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorControlObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private const_spine_inj from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : PureObservation.Definitions}

/-- A primitive head in an observed program is the payload's constructor.
Arbitrary fields cannot change the head demanded by the control program. -/
theorem Obs.primitive_head (H : Obs D Γ r info origin n Δ S e o) (HH : PrimitiveHead e) :
    e.constHead = some info.ctorName := by
  induction H with
  | var | lam => cases HH
  | payload HP => exact HP.head
  | app _ _ ih _ => exact ih HH

/-- A sort is not a constructor control program. -/
theorem Obs.not_sort (H : Obs D Γ r info origin n Δ S (.sort u) o) : False := by
  cases H with
  | payload HP => have E := HP.head; cases E

/-- A bare constant is not a saturated one-parameter constructor payload. -/
theorem Obs.not_const (H : Obs D Γ r info origin n Δ S (.const c ls) o) : False := by
  cases H with
  | payload HP =>
    obtain ⟨p, fields, E, _, _⟩ := HP
    have E := (const_spine_inj (ps := []) E).2.2
    cases E

omit [Params] in
private theorem primitive_const_spine (args : List ProofShape) :
    PrimitiveHead (ProofShape.mkApps (.const c ls) args) := by
  have H {f : ProofShape} (h : PrimitiveHead f) : PrimitiveHead (ProofShape.mkApps f args) := by
    induction args generalizing f with
    | nil => exact h
    | cons a args ih => exact ih h
  exact H trivial

/-- A rigid-family origin excludes eta at data demands; function demands
retain their recursive annotation histories through ordinary functional eta. -/
theorem Obs.native_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (hO : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (H : Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S)
    (R : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S out o := by
  cases o with
  | app keys result => exact H.native_function_eta heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS R
  | sort =>
    cases R with
    | intro RN _ =>
      have HN := H.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS RN
      simp only [LowerTypeDemand, NativeGroundDemand] at HN
  | pi =>
    cases R with
    | intro RN _ =>
      have HN := H.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS RN
      simp only [LowerTypeDemand, NativeGroundDemand] at HN
      exact (HN.family_not_pi heq hs hΓ (henv.projectionRigid hi) hO hΓ' W).elim

/-- Structure expansion of any observed data control term, including a fresh
control variable, creates a valid constructor payload. Its field dependencies
are unrestricted and its selected parameter history follows from the guard. -/
theorem Obs.native_structure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (hO : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (H : Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S)
    (R : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S out o := by
  cases R with
  | @intro r' info' ls _ ps hi' hx' ha hps RN =>
    have HN := H.native heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS RN
    cases o with
    | sort => simp only [LowerTypeDemand, NativeGroundDemand] at HN
    | app keys result => exact (HN.function_not_primitiveHead (primitive_const_spine _)).elim
    | pi =>
      simp only [LowerTypeDemand, NativeGroundDemand] at HN
      obtain ⟨rfl, rfl⟩ := HN.family_shape heq hs hΓ (henv.projectionRigid hi) hO hi' hΓ' W
      cases henv.ordered.projections_unique hi hi'
      have hps' : ps.length = 1 := hps.trans hp
      cases ps with
      | nil => simp at hps'
      | cons p ps =>
        have E : ps = [] := by cases ps <;> simp_all
        subst ps
        exact .payload ⟨p, (List.range info.numFields).map (nativeStructureField r info [] raw),
          rfl, by simp, HN⟩

/-- All primitive roots of the full staged language preserve the observer.
No whole-computation or constructor-prefix closure premise is used here. The
constructor unfolding exclusion is automatic for EnvironmentCore definitions. -/
theorem Obs.stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hO : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u)) :
    ∀ stage {n Δ S raw out o Γ' e T}, ErasedStaticStructureEtaExpansionStage D stage Δ raw out →
      Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S raw o →
      OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' → env.HasType univs Γ' e T →
      proofEraseCtx Γ' = Δ → proofErase Γ' e = raw →
      Valuation D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S →
      Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S out o := by
  intro stage
  have hc := henv.projectionCtorRigid hi
  induction stage with
  | zero =>
    intro n Δ S raw out o Γ' e T R H hΓ' W ht EΓ Ee HS
    rcases R with (R | R) | R
    · exact (erased_iota_primitive_no_rigid hc hD R
        (H.primitive_head (erased_iota_primitive_head R))).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact H.not_const.elim
    · cases R
      exact H.constant_expansion ⟨Γ', .sort (.succ .zero), hΓ', EΓ,
        HasType.sort (by trivial), if_neg (not_isProof_of_sort hΓ' (HasType.sort (by trivial)))⟩
  | succ stage ih =>
    intro n Δ S raw out o Γ' e T R H hΓ' W ht EΓ Ee HS
    rcases R with R | R | R | R | R | R
    · exact ih R H hΓ' W ht EΓ Ee HS
    · have hh := H.primitive_head R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact (V.not_rigid (hn ▸ hc)).elim
    · have hh := H.primitive_head R.head
      cases R with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact (hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)).elim
    · exact H.native_identity heq hs hΓ hi hp hx HH hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))
    · exact H.native_eta heq hs hΓ hi hp hx HH hO hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))
    · exact H.native_structure heq hs hΓ hi hp hx HH hO hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))

end Lean4Lean.VEnv.Strengthening.ConstructorControlObservation
