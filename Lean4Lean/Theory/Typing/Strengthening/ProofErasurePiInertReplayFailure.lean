import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedContinuation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrimitiveCut

/-! # Locate failure of budget-preserving body-tail replay

A finite counted path either substitutes with no increase in primitive count,
or contains a typed primitive occurrence whose substituted endpoints admit no
replay costing at most one primitive at any finite stage. The failure records a compatible occurrence at the supplied endpoints and
count; binder constructors retain the lifted map.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- An unreplayed primitive occurrence in a counted derivation with these endpoints
and count. Proof indices do not distinguish proof-irrelevant derivations.
The root permits beta and any finite stage in a competing replay of cost at
most one. Compatible constructors record the occurrence's position; under a
binder, its map is lifted and its target domain is substituted. This is an
obstruction to local budget-preserving replay, not to all whole-path replay. -/
inductive PiInertCountedReplayFailure (D : Definitions) (n : Nat) :
    {Δ : List ProofShape} → {cost : Nat} → {a b : ProofShape} →
    ScopedComputeCount (PiInertStage D n) cost Δ a b → List ProofShape → ProofShape.Subst → Prop where
  | base (H : PiInertStage D n Δ a b) : TypedSource Δ a → ContextSubstitution Δ Θ τ →
      (∀ later j, j ≤ 1 → ¬ ScopedComputeCount (PiInertStage D later) j Θ (a.subst τ) (b.subst τ)) →
      PiInertCountedReplayFailure D n (.base H) Θ τ
  | transLeft {R : ScopedComputeCount (PiInertStage D n) cr Δ a b}
      {S : ScopedComputeCount (PiInertStage D n) cs Δ b c} :
      PiInertCountedReplayFailure D n R Θ τ → PiInertCountedReplayFailure D n (R.trans S) Θ τ
  | transRight {R : ScopedComputeCount (PiInertStage D n) cr Δ a b}
      {S : ScopedComputeCount (PiInertStage D n) cs Δ b c} :
      PiInertCountedReplayFailure D n S Θ τ → PiInertCountedReplayFailure D n (R.trans S) Θ τ
  | appFn {R : ScopedComputeCount (PiInertStage D n) cr Δ f g}
      {S : ScopedComputeCount (PiInertStage D n) cs Δ a b} :
      PiInertCountedReplayFailure D n R Θ τ → PiInertCountedReplayFailure D n (R.app S) Θ τ
  | appArg {R : ScopedComputeCount (PiInertStage D n) cr Δ f g}
      {S : ScopedComputeCount (PiInertStage D n) cs Δ a b} :
      PiInertCountedReplayFailure D n S Θ τ → PiInertCountedReplayFailure D n (R.app S) Θ τ
  | proj {R : ScopedComputeCount (PiInertStage D n) cr Δ a b} :
      PiInertCountedReplayFailure D n R Θ τ →
      PiInertCountedReplayFailure D n (R.proj (s := s) (i := i)) Θ τ
  | lamDomain {R : ScopedComputeCount (PiInertStage D n) cr Δ A A'}
      {S : ScopedComputeCount (PiInertStage D n) cs (A :: Δ) b b'} :
      PiInertCountedReplayFailure D n R Θ τ → PiInertCountedReplayFailure D n (R.lam S) Θ τ
  | lamBody {R : ScopedComputeCount (PiInertStage D n) cr Δ A A'}
      {S : ScopedComputeCount (PiInertStage D n) cs (A :: Δ) b b'} :
      PiInertCountedReplayFailure D n S (A.subst τ :: Θ) τ.lift →
      PiInertCountedReplayFailure D n (R.lam S) Θ τ
  | piDomain {R : ScopedComputeCount (PiInertStage D n) cr Δ A A'}
      {S : ScopedComputeCount (PiInertStage D n) cs (A :: Δ) b b'} :
      PiInertCountedReplayFailure D n R Θ τ → PiInertCountedReplayFailure D n (R.forallE S) Θ τ
  | piBody {R : ScopedComputeCount (PiInertStage D n) cr Δ A A'}
      {S : ScopedComputeCount (PiInertStage D n) cs (A :: Δ) b b'} :
      PiInertCountedReplayFailure D n S (A.subst τ :: Θ) τ.lift →
      PiInertCountedReplayFailure D n (R.forallE S) Θ τ

/-- A failed occurrence necessarily uses a primitive in the supplied path. -/
theorem PiInertCountedReplayFailure.positive
    {R : ScopedComputeCount (PiInertStage D n) cost Δ a b}
    (H : PiInertCountedReplayFailure D n R Θ τ) : 0 < cost := by
  induction H <;> omega

/-- Replay each actual primitive at a finite stage, allowing its budget to
shrink, or retain an unreplayed occurrence with the same endpoints and count. Actual source
realizations propagate through transitive intermediates and compatible nodes.
Only the ordinary endpoint interpretation is required. -/
theorem pi_inert_counted_substitution_or_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ a b)
    (HT : TypedSource Δ a) (W : ContextSubstitution Δ Θ τ) :
    (∃ later j, j ≤ cost ∧ ScopedComputeCount (PiInertStage D later) j Θ (a.subst τ) (b.subst τ)) ∨
      PiInertCountedReplayFailure D n R Θ τ := by
  classical
  induction R generalizing Θ τ with
  | @base Δ a b H =>
    by_cases HR : ∃ later j, j ≤ 1 ∧ ScopedComputeCount (PiInertStage D later) j Θ
        (a.subst τ) (b.subst τ)
    · exact .inl HR
    · exact .inr (.base H HT W (fun later j hj RJ => HR ⟨later, j, hj, RJ⟩))
  | beta H => exact .inl ⟨0, 0, by omega, .beta H.subst⟩
  | trans R S ihR ihS =>
    rcases ihR HT W with ⟨nr, jr, hjr, RR⟩ | HF
    · rcases ihS (HT.pi_inert_compute heq hs R.forget) W with ⟨ns, js, hjs, RS⟩ | HF
      · exact .inl ⟨max nr ns, jr+js, by omega,
          (RR.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).trans
            (RS.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩
      · exact .inr (.transRight (R := R) HF)
    · exact .inr (.transLeft (S := S) HF)
  | @app cr Δ f g cs a b R S ihR ihS =>
    rcases ihR ((ScopedHole.appFn .hole a).typed HT) W with ⟨nr, jr, hjr, RR⟩ | HF
    · rcases ihS ((ScopedHole.appArg f .hole).typed HT) W with ⟨ns, js, hjs, RS⟩ | HF
      · exact .inl ⟨max nr ns, jr+js, by omega,
          (RR.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).app
            (RS.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩
      · exact .inr (.appArg (R := R) HF)
    · exact .inr (.appFn (S := S) HF)
  | @proj cr Δ a b s i R ih =>
    rcases ih ((ScopedHole.proj s i .hole).typed HT) W with ⟨m, j, hj, RJ⟩ | HF
    · exact .inl ⟨m, j, hj, .proj RJ⟩
    · exact .inr (.proj HF)
  | @lam cr Δ A A' cs b b' R S ihR ihS =>
    rcases ihR ((ScopedHole.lamDomain .hole b).typed HT) W with ⟨nr, jr, hjr, RR⟩ | HF
    · rcases ihS ((ScopedHole.lamBody A .hole).typed HT) W.cons with ⟨ns, js, hjs, RS⟩ | HF
      · exact .inl ⟨max nr ns, jr+js, by omega,
          (RR.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).lam
            (RS.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩
      · exact .inr (.lamBody (R := R) HF)
    · exact .inr (.lamDomain (S := S) HF)
  | @forallE cr Δ A A' cs b b' R S ihR ihS =>
    rcases ihR ((ScopedHole.piDomain .hole b).typed HT) W with ⟨nr, jr, hjr, RR⟩ | HF
    · rcases ihS ((ScopedHole.piBody A .hole).typed HT) W.cons with ⟨ns, js, hjs, RS⟩ | HF
      · exact .inl ⟨max nr ns, jr+js, by omega,
          (RR.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).forallE
            (RS.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩
      · exact .inr (.piBody (R := R) HF)
    · exact .inr (.piDomain (S := S) HF)

/-- Extract a typed failed root with the original endpoint map lifted through
its surrounding binders. It may use a different realization of each erased
context, but no arbitrary substitute map is introduced by this extraction. -/
theorem PiInertCountedReplayFailure.root
    {R : ScopedComputeCount (PiInertStage D n) cost Δ a b}
    (H : PiInertCountedReplayFailure D n R Θ τ) :
    ∃ depth Ξ Ω source target,
      ContextSubstitution Ξ Ω (τ.liftN depth) ∧ TypedSource Ξ source ∧
      PiInertStage D n Ξ source target ∧
      ∀ later j, j ≤ 1 → ¬ ScopedComputeCount (PiInertStage D later) j Ω
        (source.subst (τ.liftN depth)) (target.subst (τ.liftN depth)) := by
  induction H with
  | base HR HT W HF => exact ⟨0, _, _, _, _, W, HT, HR, HF⟩
  | transLeft _ ih => exact ih
  | transRight _ ih => exact ih
  | appFn _ ih => exact ih
  | appArg _ ih => exact ih
  | proj _ ih => exact ih
  | lamDomain _ ih => exact ih
  | piDomain _ ih => exact ih
  | lamBody _ ih | piBody _ ih =>
    obtain ⟨depth, Ξ, Ω, source, target, W, HT, HR, HF⟩ := ih
    simp only [ProofShape.Subst.lift_liftN] at W HF
    exact ⟨depth+1, Ξ, Ω, source, target, W, HT, HR, HF⟩

/-- A Pi-inert root with no stage-zero justification is one of the five
actual guarded additions at a strictly earlier ambient guard stage. -/
theorem PiInertStage.guarded_of_not_zero
    (H : PiInertStage D n Δ a b) (H0 : ¬ PiInertStage D 0 Δ a b) :
    ∃ k, k < n ∧
      (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       NativeIdentityExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ a b ∨
       NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ a b) := by
  induction n with
  | zero => exact (H0 H).elim
  | succ n ih =>
    rcases H.1 with HR | HR
    · obtain ⟨k, hk, HG⟩ := ih ⟨HR, H.2⟩
      exact ⟨k, by omega, HG⟩
    · exact ⟨n, by omega, HR⟩

/-- Stage-zero primitives always replay at cost one under an interpreted map.
Consequently a failed root has no stage-zero justification with these exact
endpoints, even when the containing path is presented at a larger stage. -/
theorem PiInertCountedReplayFailure.guarded_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    {R : ScopedComputeCount (PiInertStage D n) cost Δ a b}
    (H : PiInertCountedReplayFailure D n R Θ τ) :
    0 < cost ∧ 0 < n ∧ ∃ depth Ξ Ω source target,
      ContextSubstitution Ξ Ω (τ.liftN depth) ∧ TypedSource Ξ source ∧
      PiInertStage D n Ξ source target ∧ ¬ PiInertStage D 0 Ξ source target ∧
      ∀ later j, j ≤ 1 → ¬ ScopedComputeCount (PiInertStage D later) j Ω
        (source.subst (τ.liftN depth)) (target.subst (τ.liftN depth)) := by
  obtain ⟨depth, Ξ, Ω, source, target, W, HT, HR, HF⟩ := H.root
  have Hzero : ¬ PiInertStage D 0 Ξ source target := by
    intro H0
    exact HF 0 1 (by omega)
      (pi_inert_zero_compute_count_substitution heq hs (.base H0) HT W)
  have hn : 0 < n := by
    by_contra hn
    have E : n = 0 := by omega
    exact Hzero (E ▸ HR)
  exact ⟨H.positive, hn, depth, Ξ, Ω, source, target, W, HT, HR, Hzero, HF⟩

/-- Exact native images rule out every recorded local failure, including
beneath binder extensions. This is a sufficient replay condition, not a
converse or a necessary condition for whole-path transport. -/
theorem PiInertCountedReplayFailure.no_native_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    {R : ScopedComputeCount (PiInertStage D n) cost Δ a b}
    (H : PiInertCountedReplayFailure D n R Θ τ)
    (W : StaticStructureEtaNativeSubstitution.ImageSubstitution D k Δ Θ τ) : False := by
  induction H with
  | base HR HT _ HF =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    exact HF (n+k) 1 (by omega)
      (pi_inert_compute_count_native_transport heq hs (.base HR) hΓ ht EΓ Ee W)
  | transLeft _ ih => exact ih W
  | transRight _ ih => exact ih W
  | appFn _ ih => exact ih W
  | appArg _ ih => exact ih W
  | proj _ ih => exact ih W
  | lamDomain _ ih => exact ih W
  | piDomain _ ih => exact ih W
  | lamBody _ ih | piBody _ ih =>
    exact ih (W.cons (erased_static_structure_eta_expansion_stage_rename heq hs k))

end Lean4Lean.VEnv.Strengthening
