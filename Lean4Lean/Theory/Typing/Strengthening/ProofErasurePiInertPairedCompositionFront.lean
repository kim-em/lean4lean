import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedPairs

/-! # Paired ordinary-demand composition still contains the proposition front

The inputs below retain actual common typing, both comparison directions,
every ordinary finite demand, and interpretation under arbitrary paired typed
substitutions with no variable-image requirements. Even a composition
law returning only one finite base carrier guard descends arbitrary proposition
equality, conditional on a closed positive empty structure. The obstruction is
to treating composition as a smaller missing lemma, not a refutation of it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

omit [Params] in
/-- Ordinary leaves and their finite intersections have no explicit guarded
call node. The ordinary demand inside a leaf may itself contain arrows. -/
def PiInertGuardedTree.Ordinary : PiInertGuardedTree → Prop
  | .plain _ => True
  | .both p q => p.Ordinary ∧ q.Ordinary
  | .call _ _ _ _ => False

/-- A positive structure inhabitant cannot carry an explicit guarded call
profile at any selected type. A supplied Pi exposure would actually assign
that same inhabitant a Pi type, contradicting rigid structure-head inversion.
Thus adding guarded function profiles cannot strengthen the unit bridge used
below: every realizable tree there contains only ordinary leaves/intersections. -/
theorem PiInertGuardedTreeValue.ordinary_of_structure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (ha : env.HasType univs Γ a (.const family ls))
    (H : PiInertGuardedTreeValue p ρ D (proofEraseCtx Γ) (proofErase Γ a) b T) :
    p.Ordinary := by
  induction p with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1, ihq H.2⟩
  | call A B p q =>
    obtain ⟨n, R⟩ := H.2.1
    have HT := H.1.left.world_computation heq hs R
    have hn : proofErase Γ a ≠ .proof :=
      fun E => not_proof_at_positive_type hΓ hS ha (proofErase_eq_proof.1 E)
    obtain ⟨P, hP, EP⟩ := HT.realize_term hΓ ha rfl hn
    obtain ⟨A₀, B₀, rfl, _, _, _⟩ := erase_forallE_inv EP
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi)
      (args := []) hS (ha.uniqU henv hΓ hP)

/-- A checked common comparison at an Eq-headed assigned carrier supplies
both directions of every ordinary finite demand. The common comparison retains
all typed-substitution futures; ordinary arrow tests at this carrier are empty.
This theorem does not supply any explicit guarded call interface. -/
theorem PiInertEvidence.eq_head_ordinary_pairs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : PiInertEvidence D n (.compare true) Δ a b)
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b T) (HH : T.constHead = some ``Eq.rec) :
    ∀ p q, PiInertGuardedPair D Δ (.plain p) (.plain q)
      ProofShape.Subst.id ProofShape.Subst.id a b T T := by
  intro p q
  have HL : PiInertDemandBase D Δ a b T :=
    ⟨HA.sources.1, HB.sources.1, HA.sources.2, n, H.carrier_history.world_history⟩
  have HR : PiInertDemandBase D Δ b a T :=
    ⟨HB.sources.1, HA.sources.1, HB.sources.2, n, H.symm.carrier_history.world_history⟩
  exact ⟨⟨HA, HB, HL.eq_head_demand heq hs hreg hoff hRec HH⟩,
    ⟨HB, HA, HR.eq_head_demand heq hs hreg hoff hRec HH⟩⟩

/-- At an Eq-headed assigned carrier, the empty-structure constructor gives
a paired interpreter with no image requirements for every ordinary profile.
Its invariant constructor can be assigned both substituted carriers; type
uniqueness transfers the other endpoint's assignment between them. This is
ordinary typing transport only. Histories come from constructor comparison,
not from semantic interpretation of the hidden type conversion. -/
theorem PiInertGuardedPairInterpretation.unit_constructor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HM : TypedAt Δ (.const info.ctorName ls) T) (HA : TypedAt Δ a T)
    (HH : T.constHead = some ``Eq.rec) :
    ∀ p q, PiInertGuardedPairInterpretation D Δ [] (.const info.ctorName ls) a T T
      (.plain p) (.plain q) := by
  intro p q
  refine ⟨HM, HA, ?_⟩
  intro Λ σ τ WL WR _
  have ML := HM.subst WL
  have MR := HM.subst WR
  simp only [ProofShape.subst] at ML MR
  have AR := HA.subst WR
  have AL := MR.transfer ML AR (by intro h; cases h)
  have HC : PiInertEvidence D 0 (.compare true) Λ (.const info.ctorName ls) (a.subst τ) :=
    pi_inert_unit_constructor_evidence hi hp hx hf hCtor
  have L := HC.eq_head_ordinary_pairs heq hs hreg hoff hRec ML AL
    (ProofShape.const_head_subst HH) p q
  have R := HC.eq_head_ordinary_pairs heq hs hreg hoff hRec MR AR
    (ProofShape.const_head_subst HH) p q
  exact ⟨L.forward, R.backward⟩

/-- Missing composition for two actually commonly typed links interpreted
under arbitrary paired typed substitutions with empty image requirements,
retaining both directions and every ordinary finite demand. The conclusion is only
a base carrier guard at some finite stage, not a paired value or future action.
This is not proved and is not claimed strictly smaller than PropositionFront. -/
def FinitePiInertOrdinaryPairComposition (D : Definitions) : Prop :=
  ∀ {Γ a m b T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ m T → env.HasType univs Γ b T →
    (∀ p q, PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ m) (proofErase Γ T) (proofErase Γ T) (.plain p) (.plain q)) →
    (∀ p q, PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ m) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T) (.plain p) (.plain q)) →
    ∃ n, ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ a) (proofErase Γ b)

/-- The empty-structure constructor constructs both complete interpreter families
at a type-valued Eq probe. The proposition equation is used only for actual
typing conversion. No semantic interpretation of that equation is a premise
of either input. Thus composition must recover information absent from the
retained comparison histories even after retaining both directions. -/
theorem FinitePiInertOrdinaryPairComposition.unit_probe_descend
    (Hcomp : FinitePiInertOrdinaryPairComposition D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
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
  have hm : env.HasType univs Γ' (.const info.ctorName ls) (.const family ls) :=
    hiT.unitLike_constructor henv hΓ' hi (params := []) hp.symm hx hf
  have Em : proofErase Γ' (.const info.ctorName ls) = .const info.ctorName ls :=
    if_neg (not_proof_at_positive_type hΓ' hSw hm)
  have HH : (proofErase Γ' T).constHead = some ``Eq.rec := by
    rw [eqTypeProbe_erase heq hΓ' hSw hPw hQw hq]
    exact constHead_mkApps _ _
  have HA := TypedAt.of_typed hΓ' (HE.symm.defeq hiT)
  have HM := TypedAt.of_typed hΓ' (HE.symm.defeq hm)
  have HB := TypedAt.of_typed hΓ' (HE.symm.defeq hjT)
  have HMc : TypedAt (proofEraseCtx Γ') (.const info.ctorName ls) (proofErase Γ' T) := Em ▸ HM
  have IL := PiInertGuardedPairInterpretation.unit_constructor heq hs hreg hoff hRec
    hi hp hx hf hCtor HMc HA HH
  have IR := PiInertGuardedPairInterpretation.unit_constructor heq hs hreg hoff hRec
    hi hp hx hf hCtor HMc HB HH
  obtain ⟨n, H⟩ := Hcomp hΓ' (HE.symm.defeq hiT) (HE.symm.defeq hm) (HE.symm.defeq hjT)
    (by intro p q; rw [Em]; exact (IL q p).symm)
    (by intro p q; rw [Em]; exact IR p q)
  rw [show proofErase Γ' (.bvar i) = .bvar i from
    if_neg (not_proof_at_positive_type hΓ' hSw hiT),
    show proofErase Γ' (.bvar j) = .bvar j from
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)] at H
  rcases H.checked_or_exposed with HC | ⟨out, R, HEout, _⟩
  · exact (hne HC.pi_inert_bvar_injective).elim
  · exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HEout

/-- Even composition supplied with every ordinary-demand pair implies the
full proposition front when a closed positive empty structure is present.
The output stage is unrestricted. This is a lower bound on the missing law,
not a proof of it, a converse, or a counterexample to strengthening. -/
theorem FinitePiInertOrdinaryPairComposition.propositionFront_of_closed_unit
    (Hcomp : FinitePiInertOrdinaryPairComposition D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
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
  exact Hcomp.unit_probe_descend heq hs hreg hoff hRec hi hp hx hf hCtor hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

omit [Params] in
/-- The lower bound applies to the full stock environment core: canonical Eq
and the actual empty-structure declaration discharge the technical core
premises. Only the proposed composition law and closed positive unit remain
as additional hypotheses; no bespoke weak core is used. -/
theorem EnvironmentCore.ordinary_pair_composition_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls u}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      env.HasType U [] (.const family ls) (.sort (.succ u)) →
      FinitePiInertOrdinaryPairComposition definitions → PropositionFront := by
  letI := henv.params U
  intro family info ls u heq hi hp hx hf hS Hcomp
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  exact Hcomp.propositionFront_of_closed_unit heq sound hreg (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hi hp hx hf (no_rigid (henv.projectionCtorRigid hi)) hS

end Lean4Lean.VEnv.Strengthening
