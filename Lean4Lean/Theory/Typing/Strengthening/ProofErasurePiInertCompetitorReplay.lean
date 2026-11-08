import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionFrameProgress
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertComputedHeadReplay

/-! # Recover typed executions from raw continuation competitors

Ordinary equality of erased representatives is stable under interpreted
substitution. It recovers the typing needed to execute a raw competitor in
an existing projection continuation, preserving its exact primitive cost and
the original frame count. No guarded reduction is substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv erase_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private equality_simAt
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- Two raw shapes have ordinarily definitionally equal representatives in a
well-formed realization of their erased context. This carries no assertion
about directed computation or transport of native guards. -/
def ErasedTypedEquality (Δ : List ProofShape) (e f : ProofShape) : Prop :=
  ∃ Γ a b T, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.IsDefEq univs Γ a b T ∧ proofErase Γ a = e ∧ proofErase Γ b = f

/-- An ordinary erased equality can be realized at the exact type of any
actual representative of its source. Proof markers use the given proof;
nonproof representatives are aligned by erasure reflection. -/
theorem ErasedTypedEquality.realize (H : ErasedTypedEquality Δ e f)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (ht : env.HasType univs Γ a T) (Ea : proofErase Γ a = e) :
    ∃ b, env.IsDefEq univs Γ a b T ∧ proofErase Γ b = f := by
  obtain ⟨Γ₀, a₀, b₀, S, hΓ₀, EΓ₀, HE, Ea₀, Eb₀⟩ := H
  have W := proofEraseCtx_defeq hΓ₀ hΓ (EΓ₀.trans EΓ.symm)
  have HE' := HE.defeqDFC henv W
  have EA : proofErase Γ a₀ = e :=
    (proofErase_defeqCtx hΓ₀ W HE.hasType.1).symm.trans Ea₀
  have EB : proofErase Γ b₀ = f :=
    (proofErase_defeqCtx hΓ₀ W HE.hasType.2).symm.trans Eb₀
  by_cases hp : e = .proof
  · have ha₀ := proofErase_eq_proof.1 (EA.trans hp)
    have hb₀ := (isProof_congr hΓ HE').1 ha₀
    exact ⟨a, ht, Ea.trans (hp.trans ((proofErase_eq_proof.2 hb₀).symm.trans EB))⟩
  · have hn : ¬ IsProof Γ a := fun h => hp (Ea.symm.trans (proofErase_eq_proof.2 h))
    obtain ⟨_, HH⟩ := (proofErase_reflect hΓ ht HE'.hasType.1 (Ea.trans EA.symm)).2 hn
    exact ⟨b₀, ((HH.defeq hΓ).trans henv hΓ HE'.toU).of_l henv hΓ ht, EB⟩

/-- Reverse ordinary equality without reversing a guarded computation. -/
theorem ErasedTypedEquality.symm (H : ErasedTypedEquality Δ e f) : ErasedTypedEquality Δ f e := by
  obtain ⟨Γ, a, b, T, hΓ, EΓ, HE, Ea, Eb⟩ := H
  exact ⟨Γ, b, a, T, hΓ, EΓ, HE.symm, Eb, Ea⟩

/-- A typed raw source supplies reflexive ordinary equality. -/
theorem ErasedTypedEquality.refl (HT : TypedSource Δ e) : ErasedTypedEquality Δ e e := by
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, Ea⟩ := HT
  exact ⟨Γ, a, a, T, hΓ, EΓ, ht, Ea, Ea⟩

/-- Ordinary erased equality retains its source typing. -/
theorem ErasedTypedEquality.source (H : ErasedTypedEquality Δ e f) : TypedSource Δ e := by
  obtain ⟨Γ, a, b, T, hΓ, EΓ, HE, Ea, _⟩ := H
  exact ⟨Γ, a, T, hΓ, EΓ, HE.hasType.1, Ea⟩

/-- Ordinary erased equality retains its target typing. -/
theorem ErasedTypedEquality.target (H : ErasedTypedEquality Δ e f) : TypedSource Δ f := H.symm.source

/-- Realization at the shared endpoint composes equalities even when their
stored representatives, types, and context realizations differ. -/
theorem ErasedTypedEquality.trans (H : ErasedTypedEquality Δ e f)
    (H' : ErasedTypedEquality Δ f g) : ErasedTypedEquality Δ e g := by
  obtain ⟨Γ, a, b, T, hΓ, EΓ, HE, Ea, Eb⟩ := H
  obtain ⟨c, HC, Ec⟩ := H'.realize hΓ EΓ HE.hasType.2 Eb
  exact ⟨Γ, a, c, T, hΓ, EΓ, HE.trans HC, Ea, Ec⟩

/-- A source-typed directed computation supplies ordinary endpoint equality. -/
theorem ErasedTypedEquality.pi_inert_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ e) (R : ScopedCompute (PiInertStage D n) Δ e f) :
    ErasedTypedEquality Δ e f := by
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, Ea⟩ := HT
  obtain ⟨b, HE, Eb⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ ht EΓ Ea R
  exact ⟨Γ, a, b, T, hΓ, EΓ, HE, Ea, Eb⟩

/-- Substitute ordinary equality along an interpreted context map. This
transports no native stage or directed path. -/
theorem ErasedTypedEquality.subst (H : ErasedTypedEquality Δ e f)
    (W : ContextSubstitution Δ Θ τ) : ErasedTypedEquality Θ (e.subst τ) (f.subst τ) := by
  obtain ⟨Γ, a, b, T, hΓ, EΓ, HE, Ea, Eb⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
  exact ⟨Γ₀, a.subst σ, b.subst σ, T.subst σ, hΓ₀, EΓ₀,
    HE.subst henv.orderedStrong HS hΓ₀,
    (proofErase_subst_with hΓ₀ HS HE.hasType.1 ES).trans (congrArg (·.subst τ) Ea),
    (proofErase_subst_with hΓ₀ HS HE.hasType.2 ES).trans (congrArg (·.subst τ) Eb)⟩

/-- Replace the function in an actual typed erased application. -/
theorem ErasedTypedEquality.appFn (H : ErasedTypedEquality Δ e f)
    (HT : TypedSource Δ (.app e x)) : ErasedTypedEquality Δ (.app e x) (.app f x) := by
  obtain ⟨Γ, actual, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨g, a, rfl, hn, Eg, Ea⟩ := erase_app_inv Ee
  obtain ⟨_, _, hg, _⟩ := ht.app_inv henv hΓ
  obtain ⟨g', HG, Eg'⟩ := H.realize hΓ EΓ hg Eg
  have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HG) .refl T ht
  have hn' := mt (isProof_congr hΓ HH).2 hn
  exact ⟨Γ, .app g a, .app g' a, T, hΓ, EΓ, HH, Ee,
    by simp only [proofErase, if_neg hn', Eg', Ea]⟩

/-- Replace the head of an actual typed erased argument spine. -/
theorem ErasedTypedEquality.mkApps (H : ErasedTypedEquality Δ e f)
    (HT : TypedSource Δ (ProofShape.mkApps e args)) :
    ErasedTypedEquality Δ (ProofShape.mkApps e args) (ProofShape.mkApps f args) := by
  induction args using List.snoc_induction with
  | nil => exact H
  | snoc args x ih =>
    simp only [ProofShape.mkApps_snoc] at HT ⊢
    exact (ih ((ScopedHole.appFn .hole x).typed HT)).appFn HT

/-- Replace the body of an actual typed erased lambda, retaining its domain. -/
theorem ErasedTypedEquality.lamBody (H : ErasedTypedEquality (A :: Δ) e f)
    (HT : TypedSource Δ (.lam A e)) : ErasedTypedEquality Δ (.lam A e) (.lam A f) := by
  obtain ⟨Γ, actual, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨a, b, rfl, hn, Ea, Eb⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, ha⟩, _, hb⟩ := ht.lam_inv henv hΓ
  have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  have EΓa : proofEraseCtx (a :: Γ) = A :: Δ := by simp only [proofEraseCtx, Ea, EΓ]
  obtain ⟨b', HB, Eb'⟩ := H.realize hΓa EΓa hb Eb
  have HH := SimAt.lam henv.orderedStrong hΓ .refl (fun _ => equality_simAt hΓa HB) T ht
  have hn' := mt (isProof_congr hΓ HH).2 hn
  exact ⟨Γ, .lam a b, .lam a b', T, hΓ, EΓ, HH, Ee,
    by simp only [proofErase, if_neg hn', Ea, Eb']⟩

/-- Replace the major of an actual typed erased projection. -/
theorem ErasedTypedEquality.proj (H : ErasedTypedEquality Δ e f)
    (HT : TypedSource Δ (.proj family index e)) :
    ErasedTypedEquality Δ (.proj family index e) (.proj family index f) := by
  obtain ⟨Γ, actual, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨major, rfl, hn, EM⟩ := erase_proj_inv Ee
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  obtain ⟨major', HM, EM'⟩ := H.realize hΓ EΓ hm.hasType.2 EM
  have HH := SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HM) T ht
  have hn' := mt (isProof_congr hΓ HH).2 hn
  exact ⟨Γ, .proj family index major, .proj family index major', T, hΓ, EΓ, HH, Ee,
    by simp only [proofErase, if_neg hn', EM']⟩

/-- Every raw competitor ordinarily equal to the actual incoming endpoint
has a typed execution of the SAME continuation, with its own exact primitive
cost and the original number of frames. The induction realizes computations
only in their recorded scopes; it substitutes ordinary equality alone. -/
theorem PiInertProjectionRunFrames.replay_competitor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames)
    (HE : ErasedTypedEquality Δ e candidate) (HK : K candidate cost) :
    PiInertProjectionRunFrames D Ω family index out Δ K candidate cost frames := by
  induction H generalizing candidate cost with
  | projection HT HP R =>
    obtain ⟨n, RC⟩ := HK
    exact .projection HE.target (HE.proj HP).target RC
  | application HT W HTnext R H ih =>
    obtain ⟨n, cs, endpoint, tailCost, rfl, RC, HK⟩ := HK
    have EQ := (HE.subst W.interpretation).mkApps HTnext
    have EO := ErasedTypedEquality.pi_inert_compute heq hs HTnext R.forget
    have EC := ErasedTypedEquality.pi_inert_compute heq hs EQ.target RC.forget
    exact .application HE.target W EQ.target RC (ih (EO.symm.trans (EQ.trans EC)) HK)
  | retained HT SD RD WI H ih =>
    have EQ := HE.subst WI
    simp only [ProofShape.subst_id] at EQ
    have HL := EQ.lamBody (typed_spine_head H.forget.typed)
    exact .retained HE.target SD RD WI (ih (HL.mkApps H.forget.typed) HK)

/-- Competing computations from the SAME typed source have comparable
ordinary endpoints. Thus every raw competitor for an actual counted run can
be replayed as an actual run without changing its cost or frame count. -/
theorem PiInertProjectionRunFrames.replay_from_source
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    PiInertProjectionRunFrames D Ω family index out Δ K candidate cost frames := by
  exact H.replay_competitor heq hs
    ((ErasedTypedEquality.pi_inert_compute heq hs HT R.forget).symm.trans
      (ErasedTypedEquality.pi_inert_compute heq hs HT RC.forget)) HK

/-- An actual execution and any raw competitor from its original source
supply an unrestricted minimum at no greater cost than the competitor. The
minimum keeps the EXACT original continuation predicate and frame count.
In particular, a strictly cheaper raw bypass can be fed to an induction on
actual typed minima; no typing condition is added to the competitors. -/
theorem PiInertProjectionRunFrames.minimize_competitor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    ∃ smaller, smaller ≤ j+cost ∧
      ∃ later a endpoint b,
        ScopedComputeCount (PiInertStage D later) a Δ source endpoint ∧
        PiInertProjectionRunFrames D Ω family index out Δ K endpoint b frames ∧
        a+b = smaller ∧
        ∀ stage c endpoint' d, ScopedComputeCount (PiInertStage D stage) c Δ source endpoint' →
          K endpoint' d → smaller ≤ c+d := by
  classical
  let P (bound : Nat) := ∃ later a endpoint b,
    ScopedComputeCount (PiInertStage D later) a Δ source endpoint ∧ K endpoint b ∧ a+b = bound
  have select : ∀ bound, P bound → ∃ smaller, smaller ≤ bound ∧ P smaller ∧
      ∀ other, P other → smaller ≤ other := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro HB
      by_cases h : ∃ other, other < bound ∧ P other
      · obtain ⟨other, hlt, HP⟩ := h
        obtain ⟨smaller, hle, HP, HM⟩ := ih other hlt HP
        exact ⟨smaller, by omega, HP, HM⟩
      · refine ⟨bound, Nat.le_refl _, HB, ?_⟩
        intro other HP
        have hn : ¬ other < bound := fun hlt => h ⟨other, hlt, HP⟩
        omega
  obtain ⟨smaller, hle, ⟨later, a, endpoint, b, RA, HB, hab⟩, HM⟩ :=
    select (j+cost) ⟨m, j, candidate, cost, RC, HK, rfl⟩
  refine ⟨smaller, hle, later, a, endpoint, b, RA,
    H.replay_from_source heq hs HT R RA HB, hab, ?_⟩
  intro stage c endpoint' d RD HD
  exact HM (c+d) ⟨stage, c, endpoint', d, RD, HD, rfl⟩

/-- Package a competitor's recovered unrestricted minimum for the existing
induction interface. Its primitive cost is at most the raw competitor's cost,
and its frame count is unchanged. -/
theorem PiInertProjectionRunFrames.competitor_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (R : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames)
    (RC : ScopedComputeCount (PiInertStage D m) j Δ source candidate)
    (HK : K candidate cost) :
    ∃ smaller, smaller ≤ j+cost ∧
      PiInertProjectionFrameMinimum D Ω family index out Δ source smaller frames := by
  obtain ⟨smaller, hle, later, a, endpoint, b, RA, HB, hab, HM⟩ :=
    H.minimize_competitor heq hs HT R RC HK
  exact ⟨smaller, hle, K, later, a, b, endpoint, HT, RA, HB, hab, HM⟩

end Lean4Lean.VEnv.Strengthening
