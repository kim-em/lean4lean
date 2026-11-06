import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaBodyCut

/-! # Classifying the later retained-eta body root

The later body's joint minimum and its actual instantiation frame exclude
identity and constant expansions at the same selected root. On a short Eq
prefix, only the two singleton forms and native function eta remain. Reading
the singleton guards through the original target specialization is separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- The selected body root is neither administrative wrapper form. This
records exclusions derived from the actual body/continuation minimum. -/
def EtaBodyNonWrapperRoot (_ : Nat) (Δ : List ProofShape) (source target : ProofShape) : Prop :=
  ¬ ConstantExpansion source target ∧
    ∀ Recovery, ¬ NativeIdentityExpansion Recovery Δ source target

/-- Refine the existing counted root using its joint minimum and typed
endpoint substitution. Both wrapper bypasses preserve the exposed final
output and save the root's unit count. All selected witnesses are retained. -/
theorem CountedNonlevelSpineRoot.no_wrappers
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedNonlevelSpineRoot D m Δ c ls args body' cb)
    (W : ContextSubstitution Δ Ω τ)
    (RS : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (body'.subst τ) pending) out)
    (hmin : ∀ later suffixStage j k endpoint,
      ScopedComputeCount (PiInertStage D later) j Δ
        (ProofShape.mkApps (.const c ls) args) endpoint →
      ScopedComputeCount (PiInertStage D suffixStage) k Ω
        (ProofShape.mkApps (endpoint.subst τ) pending) out → cb+cs ≤ j+k)
    (HE : CarrierExposure out) :
    CountedNonlevelSpineRoot D m Δ c ls args body' cb EtaBodyNonWrapperRoot := by
  obtain ⟨ls', pre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT, _⟩ := H
  have RP' : ScopedComputeCount (PiInertStage D m) cp Δ
      (ProofShape.mkApps (.const c ls) args)
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls') pre) rest) := by
    simpa only [ProofShape.mkApps_append] using RP
  have HC := pi_inert_continuation_minimum_no_constant heq hs HT W RP' RT RS hc hmin HE
  have HI := pi_inert_continuation_minimum_no_identity RP' RT RS hc hmin HE
  exact ⟨ls', pre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT, HC, HI⟩

/-- The later body cut already contains the minimum, root typing and actual
argument interpretation required by wrapper elimination. No extra source or
substitution premise is added, and the same body/root decomposition survives. -/
theorem CountedLaterEtaBodyCut.no_wrappers
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedLaterEtaBodyCut D n Δ A f u args out ct cost)
    (HE : CarrierExposure out) :
    CountedLaterEtaBodyCut D n Δ A f u args out ct cost EtaBodyNonWrapperRoot := by
  obtain ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
    RD, RB, RX, RS, HT, WI, HM, HR⟩ := H
  refine ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
    RD, RB, RX, RS, HT, WI, HM, ?_⟩
  intro c ls pre Ef
  apply (HR c ls pre Ef).no_wrappers heq hs WI
    (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) ?_ HE
  intro later suffixStage j k endpoint RJ RK
  apply HM later suffixStage j k endpoint
  · simpa only [Ef, ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RJ
  · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RK

/-- A counted short Eq root with the wrappers excluded has only singleton
or native function-eta guards. Component ancestry bounds the selected prefix;
the count, root typing and both surrounding paths are unchanged. -/
theorem CountedNonlevelSpineRoot.eq_guarded
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CountedNonlevelSpineRoot D n Δ ``Eq.rec ls args body' cb EtaBodyNonWrapperRoot)
    (hlen : args.length ≤ 5) :
    CountedNonlevelSpineRoot D n Δ ``Eq.rec ls args body' cb (EqEtaGuardedRoot D) := by
  obtain ⟨ls', pre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT, HC, HI⟩ := H
  have hargs := HA.length_eq
  simp only [List.length_append] at hargs
  exact ⟨ls', pre, rest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT, HT,
    pi_inert_eq_short_guarded_root heq hs hreg hoff hRec HT (by omega) HR HN HC HI⟩

/-- Classify the actual later body cut of an Eq prefix with at most four
arguments. Its fresh-slot body has at most five, so core iota and structure
eta are excluded as well as the two wrappers. The result retains all earlier
counts, paths, typed instantiation and joint minimality; singleton readout
and elimination of another native eta remain to be proved. -/
theorem CountedLaterEtaBodyCut.eq_guarded
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CountedLaterEtaBodyCut D n Δ A (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      u args out ct cost)
    (hshort : pre.length ≤ 4) (HE : CarrierExposure out) :
    CountedLaterEtaBodyCut D n Δ A (ProofShape.mkApps (.const ``Eq.rec ls) pre)
      u args out ct cost (EqEtaGuardedRoot D) := by
  obtain ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
    RD, RB, RX, RS, HT, WI, HM, HR⟩ := H.no_wrappers heq hs HE
  refine ⟨A', body', x', xs', cd, cb, ca, cs, m, hc, hsmall,
    RD, RB, RX, RS, HT, WI, HM, ?_⟩
  intro c ls' pre' Ef
  obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj Ef
  apply (HR _ _ _ rfl).eq_guarded heq hs hreg hoff hRec
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

end Lean4Lean.VEnv.Strengthening
