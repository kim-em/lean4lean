import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredPiTrace
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePairedIdentityExposure

/-! # Pi exposure from comparison at the expansion base

Inferred checking follows an ignored Pi trace through function positions and
lambda bodies. Argument guards need no transport. Constant expansion preserves
the trace even though it does not preserve the source's literal head.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem inferred_trace_pair
    (hctx : ∀ {Δ Δ' a b}, Step Δ a b → Step Δ' a b)
    (htrace : ∀ {Δ a b n}, Step Δ a b → IgnoredPiTrace a n → IgnoredPiTrace b n)
    (H : ComputedJointCheck Step Δ kind a b) (hk : kind = .compare false) :
    (∀ n, IgnoredPiTrace a n → ∃ out, ScopedCompute Step Δ b out ∧ IgnoredPiTrace out n) ∧
    (∀ n, IgnoredPiTrace b n → ∃ out, ScopedCompute Step Δ a out ∧ IgnoredPiTrace out n) := by
  induction H with
  | leaf H =>
    cases hk
    cases H with
    | refl => constructor <;> intro n HT <;> exact ⟨_, .refl, HT⟩
    | sort | const => constructor <;> intro n HT <;> cases HT
  | app HF HX ihF _ | appCarrier _ HF HX ihF _ | appComputed _ HF HX ihF _ =>
    constructor
    · intro n HT
      cases HT with
      | app HT =>
        obtain ⟨out, R, HO⟩ := (ihF rfl).1 _ HT
        exact ⟨_, .app R .refl, .app HO⟩
    · intro n HT
      cases HT with
      | app HT =>
        obtain ⟨out, R, HO⟩ := (ihF rfl).2 _ HT
        exact ⟨_, .app R .refl, .app HO⟩
  | proj => constructor <;> intro n HT <;> cases HT
  | lam HA HB _ ihB | lamSorted _ _ HA HB _ ihB =>
    cases hk
    constructor
    · intro n HT
      cases HT with
      | lam HT =>
        obtain ⟨out, R, HO⟩ := (ihB rfl).1 _ HT
        exact ⟨_, .lam .refl (R.recontext_independent hctx), .lam HO⟩
    · intro n HT
      cases HT with
      | lam HT =>
        obtain ⟨out, R, HO⟩ := (ihB rfl).2 _ HT
        exact ⟨_, .lam .refl R, .lam HO⟩
  | forallE | forallSorted =>
    constructor <;> intro n HT <;> cases HT <;> exact ⟨_, .refl, .pi⟩
  | etaLams _ HE =>
    constructor
    · intro n HT
      cases n with
      | zero => cases HT
      | succ n =>
        rcases HE with HE | HE
        · exact ⟨_, .refl, (IgnoredPiTrace.eta_iff HE).1 HT⟩
        · exact ⟨_, .refl, (IgnoredPiTrace.eta_iff HE).2 HT⟩
    · intro n HT
      cases n with
      | zero => cases HT
      | succ n =>
        rcases HE with HE | HE
        · exact ⟨_, .refl, (IgnoredPiTrace.eta_iff HE).2 HT⟩
        · exact ⟨_, .refl, (IgnoredPiTrace.eta_iff HE).1 HT⟩
  | compute RA RB _ ih =>
    constructor
    · intro n HT
      obtain ⟨out, R, HO⟩ := (ih hk).1 _ (HT.compute htrace RA)
      exact ⟨out, RB.trans R, HO⟩
    · intro n HT
      obtain ⟨out, R, HO⟩ := (ih hk).2 _ (HT.compute htrace RB)
      exact ⟨out, RA.trans R, HO⟩
  | symm _ ih => exact (ih hk).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Inferred comparison transfers an ignored Pi trace up to computation.
Only context independence and primitive trace preservation are required;
neither typed substitution nor guard alignment is an assumption. -/
theorem ProofShape.ComputedJointCompare.ignored_pi_trace
    (hctx : ∀ {Δ Δ' a b}, Step Δ a b → Step Δ' a b)
    (htrace : ∀ {Δ a b n}, Step Δ a b → IgnoredPiTrace a n → IgnoredPiTrace b n)
    (H : ComputedJointCompare Step Δ false a b) (HT : IgnoredPiTrace a n) :
    ∃ out, ScopedCompute Step Δ b out ∧ IgnoredPiTrace out n :=
  (inferred_trace_pair (Step := Step) hctx htrace H rfl).1 n HT

/-- Every primitive at stage zero preserves ignored Pi traces, including
constant beta expansion. Ordinary roots have incompatible heads; explicit
universe-conversion roots also cannot occur at a traced head. -/
theorem stage_zero_ignored_pi_trace
    (R : ErasedStaticStructureEtaExpansionStage D 0 Δ a b) (H : IgnoredPiTrace a n) :
    IgnoredPiTrace b n := by
  rcases R with (R | R) | R
  · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
  · cases R <;> cases H
  · cases R; exact H.constantExpansion

/-- A stage-zero inferred comparison against a displayed Pi exposes the
other Pi at stage zero, despite arbitrary intervening constant expansions.
The conclusion supplies an actual finite computation, not semantic adequacy. -/
theorem stage_zero_inferred_pi_exposure
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false
      (.forallE A B) T) :
    ∃ C E, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) Δ T (.forallE C E) := by
  obtain ⟨out, R, HO⟩ := H.ignored_pi_trace (fun H => H) stage_zero_ignored_pi_trace .pi
  obtain ⟨C, E, RB⟩ := HO.expose
  exact ⟨C, E, R.trans (.beta RB)⟩

/-- Independent sort typings upgrade common comparison before Pi exposure.
This consumes an existing comparison and assumes no completeness for ordinary
definitional equality. -/
theorem stage_zero_typed_pi_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) (Ea : proofErase Γ a = .forallE A B) :
    ∃ C E, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ b) (.forallE C E) := by
  have HI := proofErase_computed_joint_types_inferred
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ ha hb H
  rw [Ea] at HI
  exact stage_zero_inferred_pi_exposure HI

/-- Paired function exposure needs no displayed Pi on the right when its
annotation already compares with the left Pi at stage zero. Head exposure
computes the right annotation in its own context, and typed replay supplies
its actual domain, codomain and function typing. Only recursive paired body
exposure remains a premise; no context or native-type transfer is assumed. -/
theorem PairedIdentityExposure.function_of_compared_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hg : env.HasType univs Γ' g T)
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ' T))
    (HB : ∀ C E w z, env.HasType univs Γ' C (.sort w) →
      env.HasType univs (C :: Γ') E (.sort z) → env.HasType univs Γ' g (.forallE C E) →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ')
        (proofErase Γ' T) (.forallE (proofErase Γ' C) (proofErase (C :: Γ') E)) →
      PairedIdentityExposure D (proofEraseCtx (A :: Γ)) (proofEraseCtx (C :: Γ'))
        (proofErase (A :: Γ) B) (proofErase (C :: Γ') E)
        (.app (f.liftN 1) (etaArgument u)) (.app ((proofErase Γ' g).liftN 1) (etaArgument w))) :
    PairedIdentityExposure D (proofEraseCtx Γ) (proofEraseCtx Γ')
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ' T) f (proofErase Γ' g) := by
  obtain ⟨X, Y, R⟩ := stage_zero_inferred_pi_exposure HT
  have R' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ')
      (proofErase Γ' T) (.forallE X Y) := R.recontext_independent (fun H => H)
  obtain ⟨_, hT⟩ := hg.isType henv hΓ'
  obtain ⟨T', HE, ET⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ' hT rfl rfl R'
  obtain ⟨C, E, rfl, _, EX, EY⟩ := erase_forallE_inv ET
  obtain ⟨⟨w, hC⟩, z, hE⟩ := HE.hasType.2.forallE_inv henv
  rw [← EX, ← EY] at R'
  have Hbody := HB C E w z hC hE (HE.defeq hg) R'
  exact (PairedIdentityExposure.function hΓ hΓ' hA hB hC hE Hbody).annotations
    .refl (R'.mono (fun H => .inl H))

end Lean4Lean.VEnv.Strengthening
