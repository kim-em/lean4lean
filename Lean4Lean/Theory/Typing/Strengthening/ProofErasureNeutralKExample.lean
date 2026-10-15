import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitPrefixExample
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierFiniteStrength
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary

/-! # Neutral unit indices obstruct old compared-K Pi exposure

A typed positive-universe Eq recursor equals a Pi, but every old-stage
computation is fixed by its retained neutral indices. New unit computation
exposes the Pi at stage one. Consequently, the old recovery family cannot
satisfy finite joint re-synthesis, even with arbitrarily growing comparisons.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

private def Good (D : PureObservation.Definitions) (e : ProofShape) : Prop :=
  ProofShape.NormalSyntax (ErasedIotaPrimitive D) e ∧ e.NeutralKGuards

private theorem good_proof : Good D .proof :=
  ⟨⟨fun _ H => erased_iota_primitive_head H, trivial⟩, by simp [ProofShape.NeutralKGuards, ProofShape.eqRec]⟩

private theorem good_var (i : Nat) : Good D (.bvar i) :=
  ⟨⟨fun _ H => erased_iota_primitive_head H, trivial⟩, by simp [ProofShape.NeutralKGuards, ProofShape.eqRec]⟩

private theorem good_sort (u : VLevel) : Good D (.sort u) :=
  ⟨⟨fun _ H => erased_iota_primitive_head H, trivial⟩, by simp [ProofShape.NeutralKGuards, ProofShape.eqRec]⟩

private theorem good_lam (hA : Good D A) (hb : Good D b) : Good D (.lam A b) :=
  ⟨⟨fun _ H => erased_iota_primitive_head H, hA.1, hb.1⟩,
    by simpa [ProofShape.NeutralKGuards, ProofShape.eqRec] using And.intro hA.2 hb.2⟩

private theorem good_forall (hA : Good D A) (hb : Good D b) : Good D (.forallE A b) :=
  ⟨⟨fun _ H => erased_iota_primitive_head H, hA.1, hb.1⟩,
    by simpa [ProofShape.NeutralKGuards, ProofShape.eqRec] using And.intro hA.2 hb.2⟩

private theorem good_spine (hc : env.Rigid c) (hne : c ≠ ``Eq.rec)
    (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hargs : ∀ a ∈ args, Good D a) : Good D (ProofShape.mkApps (.const c levels) args) := by
  refine ⟨ProofShape.NormalSyntax.mkApps (fun _ _ _ H =>
    erased_iota_primitive_no_rigid hc hD H (ProofShape.constHead_mkApps _ _))
    (fun a ha => (hargs a ha).1), ?_⟩
  induction args using List.snoc_induction with
  | nil => simp [ProofShape.mkApps, ProofShape.NeutralKGuards, ProofShape.eqRec]
  | snoc args a ih =>
    rw [ProofShape.mkApps_snoc]
    refine ⟨?_, ih (fun a ha => hargs a (List.mem_append_left _ ha)), (hargs a (by simp)).2⟩
    intro v w α x M m y p E
    have H := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead, ProofShape.constHead_mkApps, ProofShape.eqRec] at H
    exact (hne (Option.some.inj H)).elim

private theorem good_erase_var (Γ : List VExpr) (i : Nat) : Good D (proofErase Γ (.bvar i)) := by
  unfold proofErase
  split
  · exact good_proof
  · exact good_var i

private theorem good_erase_sort (Γ : List VExpr) (u : VLevel) : Good D (proofErase Γ (.sort u)) := by
  unfold proofErase
  split
  · exact good_proof
  · exact good_sort u

private theorem good_erase_spine (hc : env.Rigid c) (hne : c ≠ ``Eq.rec)
    (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (mkApps (.const c levels) args) T)
    (hargs : ∀ a ∈ args, Good D (proofErase Γ a)) : Good D (proofErase Γ (mkApps (.const c levels) args)) := by
  by_cases hp : IsProof Γ (mkApps (.const c levels) args)
  · rw [proofErase_eq_proof.2 hp]; exact good_proof
  · rw [proofErase_const_spine hΓ ht hp]
    apply good_spine hc hne hD
    intro a ha
    obtain ⟨b, hb, hab⟩ := List.mem_map.1 ha
    cases hab
    exact hargs b hb

private theorem rigid_ne_eqRec (heq : env.HasCanonicalEq) (hc : env.Rigid c) : c ≠ ``Eq.rec := by
  intro E
  subst c
  obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
  exact hc.pats _ _ hp rfl

private theorem good_erase_motive (heq : env.HasCanonicalEq)
    (hi : env.projections family info)
    (hD : ∀ c ∈ [family, ``Eq], ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family levels) (.sort w))
    (ha : env.HasType univs Γ (.bvar i) (.const family levels)) (hw : w.WF univs) :
    Good D (proofErase Γ (constantEqMotive w (.const family levels) (.bvar i) (.sort u))) := by
  have GS (Δ : List VExpr) : Good D (proofErase Δ (.const family levels)) := by
    unfold proofErase
    split
    · exact good_proof
    · exact good_spine (args := []) (henv.projectionRigid hi)
        (rigid_ne_eqRec heq (henv.projectionRigid hi)) (hD family (by simp)) (by simp)
  have hΓS : OnCtx (.const family levels :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hE := HasType.eqApp heq hw (hS.weak henv) (ha.weak henv)
    (show env.HasType univs (.const family levels :: Γ) (.bvar 0) (.const family levels) from .bvar .zero)
  have GE : Good D (proofErase (.const family levels :: Γ)
      (eqApp w (.const family levels) (.bvar (i+1)) (.bvar 0))) := by
    apply good_erase_spine (args := [.const family levels, .bvar (i+1), .bvar 0])
      (heq.rigid henv) (by decide) (hD ``Eq (by simp)) hΓS
      (by simpa [VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm, eqApp, mkApps] using hE)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact GS _
    · exact good_erase_var _ _
    · exact good_erase_var _ _
  simp only [constantEqMotive, VExpr.lift, VExpr.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm]
  unfold proofErase
  split
  · exact good_proof
  · apply good_lam (GS _)
    change Good D (proofErase _ (.lam _ (.sort u)))
    unfold proofErase
    split
    · exact good_proof
    · exact good_lam GE (good_erase_sort _ _)

/-- An actual positive-universe type equal to a Pi has no Pi exposure at any
old compared-K stage. The same source computes to that Pi at new unit stage one.
The explicit equation collection need only leave the three rigid/recursor heads
used by this finite source unopened. -/
theorem unit_neutral_pi_exposure_separation
    (heq : env.HasCanonicalEq) (hreg : recursorData ``Eq.rec = some data)
    (hoff : data.majorOffset = 5)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family levels) (.sort (.succ u)))
    (hD : ∀ c ∈ [family, ``Eq, ``Eq.rec], ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ e (.sort (.succ (.succ .zero))) ∧
      env.IsDefEq univs Γ e (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
        (.sort (.succ (.succ .zero))) ∧
      ProofShape.ScopedCompute (ErasedUnitSingletonStage D 1) (proofEraseCtx Γ)
        (proofErase Γ e) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ∀ stage A B, ¬ ProofShape.Compute (ErasedComparedKStage D stage)
        (proofErase Γ e) (.forallE A B) := by
  let S := VExpr.const family levels
  let Γ := [S, S]
  let X := VExpr.sort (.succ (.succ .zero))
  let F := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hS' : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have ha : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hb : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have Hab := IsDefEq.unitLike hi (params := []) hp.symm hx hf ha hb
  have hw := hS'.sort_r henv hΓ
  let q := eqReflApp (.succ u) S (.bvar 0)
  have hq : env.HasType univs Γ q (eqApp (.succ u) S (.bvar 0) (.bvar 1)) :=
    (IsDefEq.eqApp_r heq hw hS' ha Hab).defeq (HasType.eqReflApp heq hw hS' ha)
  have hF : env.HasType univs Γ F X :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  let M := constantEqMotive (.succ u) S (.bvar 0) X
  let e := eqRecApp (.succ (.succ (.succ .zero))) (.succ u) S (.bvar 0) M F (.bvar 1) q
  have he : env.HasType univs Γ e X := constant_eqRec_typed henv heq (by trivial) hw hΓ hS' ha
    (HasType.sort (by trivial)) hF hb hq
  have HE : env.IsDefEq univs Γ e F X := eqRecApp_simAt henv heq hΓ ⟨_, Hab⟩ _ he
  have EF : proofErase Γ F = .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ (.sort (.succ .zero)))
      (proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero))) from
        if_neg (not_isProof_of_sort hΓ hF)]
    have hΓT : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
      ⟨hΓ, _, HasType.sort (by trivial)⟩
    rw [show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
      show proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
      if_neg (not_isProof_of_sort hΓT (HasType.sort (by trivial)))]
  have Rnew := proofErase_unit_singleton_full_forward (D := D) heq hΓ hi hx hf (ps := []) hp.symm he
  rw [EF] at Rnew
  refine ⟨Γ, e, hΓ, he, HE, Rnew, ?_⟩
  have Ea : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hS' ha)
  have Eb : proofErase Γ (.bvar 1) = .bvar 1 := if_neg (not_proof_at_positive_type hΓ hS' hb)
  have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq hw hS' ha hb⟩
  have EE := proofErase_const_spine hΓ (args := [S, .bvar 0, M, F, .bvar 1, q]) he
    (not_isProof_of_sort hΓ he)
  change proofErase Γ e = _ at EE
  simp only [List.map_cons, List.map_nil, Ea, Eb, Eq] at EE
  have GS : Good D (proofErase Γ S) := good_erase_spine (args := []) (henv.projectionRigid hi)
    (rigid_ne_eqRec heq (henv.projectionRigid hi)) (hD family (by simp)) hΓ hS' (by simp)
  have GM : Good D (proofErase Γ M) := good_erase_motive heq hi
    (fun c hc => hD c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      exact hc.elim Or.inl (fun h => .inr (.inl h))))
    hΓ hS' ha hw
  have GF : Good D (proofErase Γ F) := by rw [EF]; exact good_forall (good_sort _) (good_sort _)
  intro stage A B R
  rw [EE] at R
  have E := eqRec_distinct_variables_fixed hreg hoff (hD ``Eq.rec (by simp))
    GS.1 GM.1 GF.1 GS.2 GM.2 GF.2 (by decide : 0 ≠ 1) R
  cases E

private theorem core_no_rigid (hc : env.Rigid c) :
    ¬ ErasedCore.definitions.unfolds c levels rhs := by
  rintro (H | H)
  · exact PureObservation.Definitions.ofEnv_no_rigid henv hc H
  · cases H.closedStructure with
    | intro _ _ _ _ _ _ hp _ =>
      exact hc.not_patternHeadsStoredRule (pat_storedRule hp)
        (by simp [ClosedStructure.pattern, Pattern.constHead_eq, Pattern.headConst, Pattern.headConst_varN])

private theorem core_no_eqRec (heq : env.HasCanonicalEq) :
    ¬ ErasedCore.definitions.unfolds ``Eq.rec levels rhs := by
  rintro (H | H)
  · exact ConstructorObservation.eqRec_no_stored_unfold henv heq H
  · have H' := H.closedStructure
    generalize hn : ``Eq.rec = name at H'
    cases H' with
    | intro hr _ _ hi hz _ _ _ =>
      rw [hr.eqRec_family heq hn.symm] at hi
      exact heq.projection_indexed henv hi hz

omit [Params] in
/-- With a positive closed empty structure, the actual old compared-K recovery
family fails finite joint re-synthesis, regardless of how its comparison stages
grow. This uses every stored definition and selected structure equation in the
core; the counterexample is not caused by choosing an empty equation collection. -/
theorem not_finite_carrier_domain_resynthesis_comparedK {env : VEnv} (henv : env.WF)
    (U : Nat) (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType U [] (.const family levels) (.sort (.succ u)))
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) :
    letI := henv.params U
    ¬ FiniteCarrierDomainResynthesis (ErasedComparedKStage ErasedCore.definitions) Stages := by
  letI := henv.params U
  intro H
  obtain ⟨data, hreg, _, _, hoff, _⟩ := heq.recursorRegistration henv
  have hD : ∀ c ∈ [family, ``Eq, ``Eq.rec], ∀ levels rhs,
      ¬ ErasedCore.definitions.unfolds c levels rhs := by
    intro c hc levels rhs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact core_no_rigid (henv.projectionRigid hi)
    · exact core_no_rigid (heq.rigid henv)
    · exact core_no_eqRec heq
  obtain ⟨Γ, e, hΓ, he, HE, _, HN⟩ := unit_neutral_pi_exposure_separation
    heq hreg hoff hi hp hx hf hS hD
  obtain ⟨stage, A, B, R⟩ := H.positive_pi_exposure
    (by intro stage a b σ HR; exact erased_compared_K_stage_subst stage HR)
    hΓ he ⟨_, HE⟩
  exact HN stage A B R

end Lean4Lean.VEnv.Strengthening
