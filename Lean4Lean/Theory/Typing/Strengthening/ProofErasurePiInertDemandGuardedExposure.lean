import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandExposureBoundary

/-! # Guarded selected carriers retain an explicit demand interface

A value retains its assigned selected carrier, a hereditary guarded computation
to an interface, and its full finite demand at that interface. Ground readout
returns to the selected carrier; applications use the retained interface.
This does not assert that bare demands transport along arbitrary guarded paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Retained guarded type computation transports an actual assignment to its
output interface. Its common output has a core tail, so typed reflection can
align actual representatives without claiming a core join of the inputs. -/
theorem ProofShape.TypedAt.world_computation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedAt Δ e T) (R : PiInertWorldComputation D n Δ T U) : TypedAt Δ e U := by
  obtain ⟨Γ, a, A, hΓ, rfl, ha, Ea, EA⟩ := H
  obtain ⟨V, HV⟩ := R.base.1.assigned
  obtain ⟨B, C, hB, EB, _⟩ := HV.realize hΓ
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  obtain ⟨out, RA, RB⟩ := R.base.2 .refl
  obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize
    (fun hΓ hΓ' W ht S => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed S)) hΓ hA rfl EA RA
  obtain ⟨B', HB, EB'⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hB rfl EB (RB.scoped (fun S => .base S))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ HA.hasType.2 HB.hasType.2 (EA'.trans EB'.symm)).2
    (not_isProof_of_sort hΓ HA.hasType.2)
  have HAB := (HA.toU.trans henv hΓ (HE.defeq hΓ)).trans henv hΓ HB.toU.symm
  exact ⟨Γ, a, B, hΓ, rfl, ha.defeqU_r henv hΓ HAB, Ea, EB⟩

/-- A selected carrier keeps both actual operand assignments and a full
finite demand at an explicitly retained interface. The exposure computation
and demand may use different finite stages; future worlds remain core worlds. -/
structure PiInertGuardedDemand (D : Definitions) (Δ : List ProofShape)
    (p : PiInertDemand) (a b T U : ProofShape) : Prop where
  left : TypedAt Δ a T
  right : TypedAt Δ b T
  exposure : ∃ n, PiInertWorldComputation D n Δ T U
  value : PiInertDemandValue p D Δ a b U

/-- Every ordinarily assigned demand is a guarded demand at its own interface. -/
theorem PiInertGuardedDemand.of_value
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b T) (H : PiInertDemandValue p D Δ a b T) :
    PiInertGuardedDemand D Δ p a b T T :=
  ⟨HA, HB, ⟨0, (PiInertEvidence.of_core_join hc HA.sources.2 HA.sources.2 .refl).world_computation⟩, H⟩

/-- Both selected assignments, the exposure and the action move together. -/
theorem PiInertGuardedDemand.move (H : PiInertGuardedDemand D Δ p a b T U)
    (W : PiInertCoreWorld D Δ Λ σ) :
    PiInertGuardedDemand D Λ p (a.subst σ) (b.subst σ) (T.subst σ) (U.subst σ) := by
  obtain ⟨n, R⟩ := H.exposure
  exact ⟨H.left.subst W.typed, H.right.subst W.typed, ⟨n, R.move W⟩, H.value.move W⟩

/-- Ground readout returns to the selected carrier by the actual guarded
computation. The interface's higher-order action remains stored separately. -/
theorem PiInertGuardedDemand.base (H : PiInertGuardedDemand D Δ p a b T U) :
    PiInertDemandBase D Δ a b T := by
  obtain ⟨n, R⟩ := H.exposure
  obtain ⟨m, HM⟩ := H.value.base.history
  exact ⟨H.left.sources.1, H.right.sources.1, H.left.sources.2, max n m,
    (HM.raise (Nat.le_max_right n m)).carrier_prefix (R.raise (Nat.le_max_left n m))⟩

/-- The explicit interface also carries the actual assignments needed by
recursive typed calls. No source typing is inferred from raw action alone. -/
theorem PiInertGuardedDemand.interface_assignments
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertGuardedDemand D Δ p a b T U) : TypedAt Δ a U ∧ TypedAt Δ b U := by
  obtain ⟨n, R⟩ := H.exposure
  exact ⟨H.left.world_computation heq hs R, H.right.world_computation heq hs R⟩

/-- A further guarded selected-type prefix preserves the same interface and
all its action. The caller supplies the new original endpoint assignments. -/
theorem PiInertGuardedDemand.prefix
    (H : PiInertGuardedDemand D Δ p a b T U)
    (HA : TypedAt Δ a C) (HB : TypedAt Δ b C)
    (R : PiInertWorldComputation D n Δ C T) : PiInertGuardedDemand D Δ p a b C U := by
  obtain ⟨m, S⟩ := H.exposure
  exact ⟨HA, HB, ⟨max n m,
    (R.raise (Nat.le_max_left n m)).trans (S.raise (Nat.le_max_right n m))⟩, H.value⟩

/-- Core changes of the interface retain action, unlike arbitrary guarded
interface changes. The selected-to-interface computation is composed explicitly. -/
theorem PiInertGuardedDemand.interface_core_join
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedDemand D Δ p a b T U) (HV : TypedSource Δ V)
    (J : ComputeJoin (ErasedLevelCore D) U V) : PiInertGuardedDemand D Δ p a b T V := by
  obtain ⟨n, R⟩ := H.exposure
  have S : PiInertWorldComputation D n Δ U V :=
    (PiInertEvidence.of_core_join hc H.value.base.typeSource HV J).world_computation
  exact ⟨H.left, H.right, ⟨n, R.trans S⟩, H.value.core_join hs hc HV J⟩

/-- Application consumes the retained interface demand even if the selected
carrier cannot expose any Pi by ordinary core. Actual interface assignments
construct the dependent result source, and the full result demand is returned. -/
theorem PiInertGuardedDemand.app
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedDemand D Δ (.arrow p q) f g T (.forallE A B))
    (HX : PiInertDemandValue p D Δ x y A)
    (HL : TypedSource Δ (.app f x)) (HR : TypedSource Δ (.app g y)) :
    PiInertDemandValue q D Δ (.app f x) (.app g y) (B.inst x) := by
  have HF := (H.interface_assignments heq hs).1
  exact H.value.app heq hc HX HL HR (HF.app_parts HL).2.sources.2

/-- A native variable constructs every interface demand after retained guarded
type computation. Its neutral recovery composes with that computation before
finite action is built; no source demand at the alias is assumed sufficient. -/
theorem PiInertGuardedDemand.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (lookup : Lookup Γ i T)
    (hn : ¬ IsProof Γ (.bvar i))
    (R : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ T) U) :
    PiInertGuardedDemand D (proofEraseCtx Γ) p
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i)) (proofErase Γ T) U := by
  have hf : env.HasType univs Γ (.bvar i) T := .bvar lookup
  have TF := TypedAt.of_typed hΓ hf
  have EV : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ lookup]
  have HV : TypedSource (proofEraseCtx Γ) (.bvar i) := ⟨Γ, .bvar i, T, hΓ, rfl, hf, EV⟩
  have HN : PiInertWorldValue D 0 (proofEraseCtx Γ) (.bvar i) (.bvar i) (proofErase Γ T) := by
    rw [← EO]
    exact pi_inert_native_variable_world_neutral.value HV HV
  refine ⟨TF, TF, ⟨n, R⟩, ?_⟩
  rw [EV]
  exact (PiInertCarrierValue.neutral ((HN.raise (Nat.zero_le n)).convert R)).demand
    heq hs hc hRigid R.base.1

omit [Params] in
/-- A native function declared at the free-major reflexive Pi cast retains
every finite interface demand, although no ordinary-core arrow exposure
certificate exists for its selected type. The guarded path is constructed
at stage one; no demand or exposure is assumed for the function. -/
theorem EnvironmentCore.native_cast_guarded_demand
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u v Γ j i A B}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar j) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.HasType U Γ (.forallE A B) (.sort v) →
      Lookup Γ i (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A B)) →
      ¬ IsProof Γ (.bvar i) →
      (∀ p, PiInertGuardedDemand definitions (proofEraseCtx Γ) p
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i))
        (proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A B)))
        (proofErase Γ (.forallE A B))) ∧
      (∀ p q, ¬ PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) (.arrow p q)
        (proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A B)))) := by
  letI := henv.params U
  intro u v Γ j i A B heq hu hΓ hX hq hPi lookup hni
  have hs : definitions.Sound env U := EnvironmentCore.sound
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    EnvironmentCore.typed_level_core_confluence hcon
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  have RX := PiInertEvidence.core (stage := 0) hs hc hΓ hX (.refl)
  have HX : PiInertEvidence definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (.sort v)) (proofErase Γ (.sort v)) := RX.join hc RX
  have ht : env.HasType U (.sort v :: Γ) (.bvar 0) (VExpr.sort v).lift := .bvar .zero
  have RC := HX.castConsumer heq hs (EnvironmentCore.levelCompatible hcon) hcon hc
    hreg (hr.eqRec_target heq hn).2.1 (EnvironmentCore.no_eqRec heq)
    hu hΓ hX hX hq hPi ht
  have R : PiInertWorldComputation definitions 1 (proofEraseCtx Γ)
      (proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A B)))
      (proofErase Γ (.forallE A B)) := by
    simpa only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, VExpr.liftN_zero]
      using RC.world_computation
  constructor
  · intro p
    exact PiInertGuardedDemand.native heq hs hc (fun h => EnvironmentCore.no_rigid h)
      hΓ lookup hni R
  · intro p q
    exact reflexive_cast_no_core_type_carrier henv U heq hu hΓ hX hq hPi

/-- Finite reference-tree conversion changes the retained interface while
keeping the selected carrier. Both interface assignments are recovered from
their guarded exposures; the target exposure remains explicit. -/
theorem PiInertGuardedDemand.convert_interface
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedDemand D Δ p a b T U)
    (HR : PiInertTypeInterface p R)
    (HU : PiInertCoreTypeCarrier D Δ p U) (HV : PiInertCoreTypeCarrier D Δ p V)
    (HA : TypedAt Δ a R) (HB : TypedAt Δ b R)
    (RV : PiInertWorldComputation D n Δ T V) : PiInertGuardedDemand D Δ p a b T V := by
  have old := (H.interface_assignments heq hs).1
  have leftNew := H.left.world_computation heq hs RV
  have rightNew := H.right.world_computation heq hs RV
  exact ⟨H.left, H.right, ⟨n, RV⟩,
    HR.convert_core_exposed heq hs hc hRigid HU HV old leftNew rightNew HA HB H.value⟩

/-- An original strong conversion parent retains the old interface and its
action when the new selected carrier has a guarded path to the old one.
The path is a separate certificate, not inferred from the type child. -/
theorem StrongBounded.guarded_demand_convert
    (typeChild : StrongBounded env univs k Γ T C (.sort u))
    (termChild : StrongBounded env univs k Γ a b T)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PiInertGuardedDemand D (proofEraseCtx Γ) p
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) U)
    (R : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ C) (proofErase Γ T)) :
    PiInertGuardedDemand D (proofEraseCtx Γ) p
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ C) U := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.prefix (TypedAt.of_typed hΓ (HE.defeq HT.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.2)) R

/-- Application returns another assigned guarded value at its dependent
result interface. Retained argument equality assigns the right result at the
left result carrier, so higher-order results can continue through this API. -/
theorem PiInertGuardedDemand.app_guarded
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedDemand D Δ (.arrow p q) f g T (.forallE A B))
    (HX : PiInertDemandValue p D Δ x y A)
    (HL : TypedSource Δ (.app f x)) (HR : TypedSource Δ (.app g y)) :
    PiInertGuardedDemand D Δ q (.app f x) (.app g y) (B.inst x) (B.inst x) := by
  obtain ⟨HF, HG⟩ := H.interface_assignments heq hs
  obtain ⟨TX, TL⟩ := HF.app_parts HL
  have TR := HG.app_result_left heq hs TX HX HR
  exact .of_value hc TL TR (H.app heq hs hc HX HL HR)

end Lean4Lean.VEnv.Strengthening
