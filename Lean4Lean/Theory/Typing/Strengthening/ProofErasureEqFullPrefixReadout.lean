import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCompletedEtaExecution

/-! # Read full target prefixes without completing the proof major

Completion of five Eq arguments suffices for a head-losing root reached by
component computation, even when the actual source has extra arguments.
A sort-ending minimum excludes structure eta; canonical typing then bounds
the root by five arguments, so its completion comes from the retained prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- Component computation of a longer actual spine preserves completion at
any selected prefix contained in the completed argument vector. Extra source
arguments and pending outputs need no target assignment. -/
theorem IteratedAmbientEqCompletion.compute_prefix_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HL : List.Forall₂ (· ≈ ·) ls rootLs) (HW : ∀ l ∈ rootLs, l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) (args ++ extra) (rootArgs ++ pending))
    (hlen : rootArgs.length ≤ args.length) :
    IteratedAmbientEqCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) := by
  have Htake : List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args
      ((rootArgs ++ pending).take args.length) := by
    simpa only [List.take_left] using Lean4Lean.List.forall₂_take HA args.length
  have HH := HP.compute_components heq hs hΓ HL HW Htake rootArgs.length
  simpa only [List.take_take, Nat.min_eq_left hlen, List.take_left] using HH

/-- A head-losing root reached through the component history of a full
completed five-argument prefix reads the original equation in any actual
sort-ending typed minimum. Extra arguments, including an erased proof major,
need not be completed. A hypothetical structure root would give the whole
pending spine a rigid-tail type, contradicting that same minimum. The other
head-losing roots have arity at most five by canonical typing and singleton
code generation, and thus inherit completion from the retained prefix. -/
theorem IteratedAmbientEqCompletion.read_full_prefix_loss_in_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : IteratedAmbientEqCompletion Γ v w [α,a,M,minor,b] Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5)
    (HL : List.Forall₂ (· ≈ ·) ls rootLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) Δ) (args ++ extra) (rootArgs ++ pending))
    (HR : PiInertStage D rootStage Δ (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (HM : PiInertTypedContinuationMinimum D Ω out Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ extra)) cost)
    (HC : ControlTyping Ω out (.sort outU))
    (RP : ScopedCompute (PiInertStage D prefixStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ extra))
      (ProofShape.mkApps (.const ``Eq.rec rootLs) (rootArgs ++ pending))) :
    env.IsDefEq univs Γ a b α := by
  have HTsource : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ extra)) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := HM
    exact HT
  have HTroot := RP.spine_cut_source_typed
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs prefixStage)) HTsource
  have Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D rootStage) Δ
      (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target := by
    intro H
    obtain ⟨c, hr, HTail⟩ := rigid_tail_of_native_structure
      (erased_static_structure_eta_expansion_stage_descent heq hs rootStage)
      HTroot ProofShape.const_spine_ne_proof H
    have HTwhole := HTsource.pi_inert_compute heq hs RP
    have Hwhole : RigidTailTyping Δ (ProofShape.mkApps (.const ``Eq.rec rootLs) (rootArgs ++ pending)) c := by
      rw [ProofShape.mkApps_append] at HTwhole ⊢
      exact HTail.mkApps hr HTwhole
    have Hsource := Hwhole.compute_backward
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs prefixStage))
      HTsource RP
    exact HM.no_rigid_tail heq hs HC hr Hsource
  have hroot := (typed_nonstructural_eq_head_loss_singleton heq hreg hoff hRec HTroot HR HN Hstruct).1
  have Hcompleted := HP.compute_prefix_components heq hs hΓ HL (typed_const_levels_wf HTroot) HA
    (by simpa only [hlen] using hroot)
  exact Hcompleted.read_loss heq hs hreg hoff hRec hΓ ht HR HN

/-- The completed first five arguments survive opening the next binder by
ordinary unused-binder insertion. The fresh sixth argument needs no target
inhabitant: a head-losing root in its actual component history is read by the
full-prefix theorem. This works through iterated insertions and needs only
the displayed domain sort, not a transported native recovery certificate. -/
theorem IteratedAmbientEqCompletion.read_full_eta_loss_in_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : IteratedAmbientEqCompletion Γ v w [α,a,M,minor,b] Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5) (SD : DomainSort Δ A u)
    (HL : List.Forall₂ (· ≈ ·) ls rootLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (A :: Δ))
      (args.map (·.liftN 1) ++ [etaArgument u]) (rootArgs ++ pending))
    (HR : PiInertStage D rootStage (A :: Δ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (HM : PiInertTypedContinuationMinimum D Ω out (A :: Δ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) cost)
    (HC : ControlTyping Ω out (.sort outU))
    (RP : ScopedCompute (PiInertStage D prefixStage) (A :: Δ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u))
      (ProofShape.mkApps (.const ``Eq.rec rootLs) (rootArgs ++ pending))) :
    env.IsDefEq univs Γ a b α := by
  have HP' : IteratedAmbientEqCompletion Γ v w [α,a,M,minor,b] (A :: Δ)
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.liftN 1))) := by
    simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using HP.under_domain SD
  have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u) =
      ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.liftN 1) ++ [etaArgument u]) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
  exact HP'.read_full_prefix_loss_in_minimum heq hs hreg hoff hRec hΓ ht
    (by simpa only [List.length_map] using hlen) HL HA HR HN (ES ▸ HM) HC (ES ▸ RP)

end Lean4Lean.VEnv.Strengthening
