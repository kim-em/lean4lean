import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRecursiveInterfaceConversion

/-! # Original ground conversion coverage already contains the proposition front

One original strong conversion rule, with an independently constructed ground
term-child interpreter, suffices for the hidden-unit test. Its output need only
be one finite base carrier guard. Thus unrestricted conversion coverage cannot
be presented as a smaller frontier merely because recursive Pi transport and
type-certificate composition have been proved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Missing coverage for one original strong conversion rule. Both original
children share a finite rank bound; its source interpreter is supplied under
arbitrary paired typed substitutions with empty image requirements. Only one
finite base guard is requested. This law is not proved or claimed smaller
than PropositionFront; the lower bound below applies already to this form. -/
def FinitePiInertOriginalGroundConversion (D : Definitions) : Prop :=
  ∀ {Γ k A B u f g}, OnCtx Γ (env.IsType univs) →
    StrongBounded env univs k Γ A B (.sort u) →
    StrongBounded env univs k Γ f g A →
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A)
      (.plain .ground) (.plain .ground) →
    ∃ n, ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ f) (proofErase Γ g)

/-- Missing construction of ground-tree transports from all original strong
type children. The rank is unrestricted and the resulting certificate has no
uniform stage bound. The lower bound is about this actual current contract,
not about an older exposure or substitution invariant. -/
def PiInertStrongGroundTreeCoverage (D : Definitions) : Prop :=
  ∀ {Γ k A B u}, OnCtx Γ (env.IsType univs) →
    StrongBounded env univs k Γ A B (.sort u) →
    PiInertTreeTransport D (proofEraseCtx Γ)
      (.plain .ground) (proofErase Γ A) (.plain .ground) (proofErase Γ B)

/-- Missing construction of the earlier bidirectional carrier certificate
from every original strong type child. It is stronger than the ground-tree
coverage used in the lower bound, since its raw endpoints need not be typed. -/
def PiInertStrongCarrierCoverage (D : Definitions) : Prop :=
  ∀ {Γ k A B u}, OnCtx Γ (env.IsType univs) →
    StrongBounded env univs k Γ A B (.sort u) →
    PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B)

/-- Carrier coverage constructs the exact ground-tree certificate consumed
by recursive conversion. No term composition is involved. -/
theorem PiInertStrongCarrierCoverage.ground_trees (H : PiInertStrongCarrierCoverage D) :
    PiInertStrongGroundTreeCoverage D := by
  intro Γ k A B u hΓ HE Λ σ W a b X HA HB
  exact PiInertTreeTransport.ground (H hΓ HE) W X HA HB

/-- Ground-tree coverage closes the original conversion consumer and hence
its weaker base-only readout. The source interpreter supplies its own identity
environment; the type child supplies actual converted assignments. -/
theorem PiInertStrongGroundTreeCoverage.original_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (H : PiInertStrongGroundTreeCoverage D) :
    FinitePiInertOriginalGroundConversion D := by
  intro Γ k A B u f g hΓ typeChild termChild source
  have converted := StrongBounded.paired_convert_interfaces heq hs hΓ typeChild termChild
    (H hΓ typeChild) (H hΓ typeChild) source
  have W := PiInertCoreWorld.identity_source (D := D) heq hc converted.left.sources.1
  have result := converted.run W.typed W.typed (fun _ _ h => nomatch h)
  obtain ⟨n, history⟩ := result.forward.base.ground.history
  exact ⟨n, by simpa only [ProofShape.subst_id] using history.base .refl .refl .refl⟩

/-- A single converted unit equality exposes a hidden type probe and descends
its original proposition indices. Both strong children are constructed and
raised to a common finite bound. The term interpreter comes from the native
unit rule, with no semantic proposition-index evidence or composition premise. -/
theorem FinitePiInertOriginalGroundConversion.unit_probe_descend
    (Hconv : FinitePiInertOriginalGroundConversion D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN count) (Q.liftN count)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have hPw := hP.weakN henv W
  have hQw := hQ.weakN henv W
  let T := eqTypeProbe (.succ u) (.const family ls) (P.liftN count) (Q.liftN count) q
  have HE : env.IsDefEq univs Γ' T (.const family ls) (.sort (.succ u)) :=
    eqTypeProbe_defeq heq hΓ' hSw hPw hQw hq HPQ
  have HU : env.IsDefEq univs Γ' (.bvar i) (.bvar j) (.const family ls) :=
    .unitLike hi (params := []) hp.symm hx hf hiT hjT
  obtain ⟨n, typeChild⟩ := strong_has_bound (HE.symm.strong henv.orderedStrong hΓ')
  obtain ⟨m, termChild⟩ := strong_has_bound (HU.strong henv.orderedStrong hΓ')
  have ES : proofErase Γ' (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ' hSw)
  have source : PiInertGuardedPairInterpretation D (proofEraseCtx Γ') []
      (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j))
      (proofErase Γ' (.const family ls)) (proofErase Γ' (.const family ls))
      (.plain .ground) (.plain .ground) := by
    rw [ES]
    exact PiInertGuardedPairInterpretation.unit_ground hi hp hx hf hD
      (ES ▸ TypedAt.of_typed hΓ' hiT) (ES ▸ TypedAt.of_typed hΓ' hjT)
  obtain ⟨k, H⟩ := Hconv hΓ' (typeChild.mono (Nat.le_max_left n m))
    (termChild.mono (Nat.le_max_right n m)) source
  rw [show proofErase Γ' (.bvar i) = .bvar i from
      if_neg (not_proof_at_positive_type hΓ' hSw hiT),
    show proofErase Γ' (.bvar j) = .bvar j from
      if_neg (not_proof_at_positive_type hΓ' hSw hjT)] at H
  rcases H.checked_or_exposed with HC | ⟨out, R, HX, _⟩
  · exact (hne HC.pi_inert_bvar_injective).elim
  · exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HX

/-- Even base-only coverage of one original ground conversion implies the
whole proposition front when a closed positive unit exists. No law composing
term interpreters is assumed. This is a lower bound, not a counterexample or
an equivalence, and does not refute induction on the original strong children. -/
theorem FinitePiInertOriginalGroundConversion.propositionFront_of_closed_unit
    (Hconv : FinitePiInertOriginalGroundConversion D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family ls
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hSA : env.HasType univs (A :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hSA⟩
  have hΓSS : OnCtx (S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓS, _, hSA.weak henv⟩
  have W3 : Ctx.LiftN 3 0 Γ (S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
  have hP3 := hP.weakN henv W3
  have hQ3 := hQ.weakN henv W3
  let E := eqApp (.succ .zero) (.sort .zero) (P.liftN 3) (Q.liftN 3)
  have hE : env.HasType univs (S :: S :: A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP3 hQ3
  have hΓE : OnCtx (E :: S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓSS, _, hE⟩
  have W4 : Ctx.LiftN 4 0 Γ (E :: S :: S :: A :: Γ) := W3.cons0
  have hq : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    have h := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using h
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    have H := HT.weakN henv WX
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using H⟩
  exact Hconv.unit_probe_descend heq hs hreg hoff hRec hi hp hx hf hD hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

omit [Params] in
/-- The exact ground-tree coverage contract already implies PropositionFront
for the full actual environment core with a closed positive empty structure.
Canonical Eq and the declaration discharge all technical core assumptions. -/
theorem EnvironmentCore.ground_tree_coverage_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls u}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      env.HasType U [] (.const family ls) (.sort (.succ u)) →
      PiInertStrongGroundTreeCoverage definitions → PropositionFront := by
  letI := henv.params U
  intro family info ls u heq hi hp hx hf hS H
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  exact FinitePiInertOriginalGroundConversion.propositionFront_of_closed_unit
    (H.original_conversion heq sound (typed_level_core_confluence (fun H => H)))
    heq sound hreg (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
    hi hp hx hf (no_rigid (henv.projectionRigid hi)) hS

omit [Params] in
/-- The earlier carrier-transport coverage promise has the same lower bound.
The result requires neither recursive call profiles nor term composition. -/
theorem EnvironmentCore.carrier_coverage_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls u}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      env.HasType U [] (.const family ls) (.sort (.succ u)) →
      PiInertStrongCarrierCoverage definitions → PropositionFront := by
  letI := henv.params U
  intro family info ls u heq hi hp hx hf hS H
  exact ground_tree_coverage_propositionFront henv U heq hi hp hx hf hS H.ground_trees

end Lean4Lean.VEnv.Strengthening
