import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqProofMajorHeadLoss

/-! # Rigid result families survive actual mixed continuations

Ordinary assigned types ending at a fixed rigid family remain so through
computation, interpreted substitution, application and retained lambdas. An
execution ending at a sort-typed output therefore cannot have such a source.
This uses ordinary typing transport only, not substitution of guarded paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- An actual type is a fixed constant family, possibly beneath Pi binders.
Its parameters and binder domains are unrestricted actual expressions. -/
inductive RigidTail (c : Name) : VExpr → Prop where
  | family : RigidTail c (VExpr.mkApps (.const c ls) args)
  | forallE : RigidTail c B → RigidTail c (.forallE A B)

omit [Params] in
/-- Ordinary substitution preserves the terminal family, including beneath
all retained binders. No native recovery certificate is substituted. -/
theorem RigidTail.subst (H : RigidTail c F) (σ : VExpr.Subst) : RigidTail c (F.subst σ) := by
  induction H generalizing σ with
  | family => simpa only [VExpr.subst_mkApps, VExpr.subst] using (RigidTail.family (c := c))
  | forallE _ ih => exact .forallE (ih _)

/-- A nonproof raw term has an actual assigned type ending in the indicated
family. Nonproof status permits erasure reflection in other realizations of
the same raw context. Rigidity of the family is supplied when it is used. -/
def RigidTailTyping (Δ : List ProofShape) (e : ProofShape) (c : Name) : Prop :=
  e ≠ .proof ∧ ∃ Γ f F, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ f F ∧ proofErase Γ f = e ∧ RigidTail c F

/-- Read the assigned rigid-tail type at any typed representative of the raw
term. Context conversion and nonproof erasure reflection preserve the exact
type expression and its terminal family. -/
theorem RigidTailTyping.realize
    (H : RigidTailTyping Δ e c) (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = Δ) (hf : env.HasType univs Γ f T) (Ef : proofErase Γ f = e) :
    ∃ F, env.HasType univs Γ f F ∧ RigidTail c F := by
  obtain ⟨hn, Γ₀, g, F, hΓ₀, EΓ₀, hg, Eg, HF⟩ := H
  have W := proofEraseCtx_defeq hΓ₀ hΓ (EΓ₀.trans EΓ.symm)
  have hg' := hg.defeqDFC henv W
  have Eg' := (proofErase_defeqCtx hΓ₀ W hg).symm.trans Eg
  have hng : ¬ IsProof Γ g := fun hp => hn (Eg'.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg' hf (Eg'.trans Ef.symm)).2 hng
  exact ⟨F, ((HE.defeq hΓ).of_l henv hΓ hg').hasType.2, HF⟩

/-- Compatible computation preserves the actual assigned rigid-tail type. -/
theorem RigidTailTyping.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : RigidTailTyping Δ e c) (R : ScopedCompute Step Δ e out) :
    RigidTailTyping Δ out c := by
  obtain ⟨hn, Γ, f, F, hΓ, EΓ, hf, Ef, HF⟩ := H
  obtain ⟨g, HE, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef R
  refine ⟨?_, Γ, g, F, hΓ, EΓ, HE.hasType.2, Eg, HF⟩
  intro E
  have hp := (isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (Eg.trans E))
  exact hn (Ef.symm.trans (proofErase_eq_proof.2 hp))

/-- A rigid-tail assignment at the endpoint can be read back along a typed
computation. Reify the path first and transfer the endpoint's actual assigned
type across semantic equality; this does not reverse the raw computation. -/
theorem RigidTailTyping.compute_backward
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ e) (R : ScopedCompute Step Δ e out)
    (H : RigidTailTyping Δ out c) : RigidTailTyping Δ e c := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, Ef⟩ := HT
  obtain ⟨g, HE, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef R
  obtain ⟨F, hgF, HF⟩ := H.realize hΓ EΓ HE.hasType.2 Eg
  refine ⟨?_, Γ, f, F, hΓ, EΓ, (HE.toU.of_r henv hΓ hgF).hasType.1, Ef, HF⟩
  intro E
  have hp := (isProof_congr hΓ HE).1 (proofErase_eq_proof.1 (Ef.trans E))
  exact H.1 (Eg.symm.trans (proofErase_eq_proof.2 hp))

/-- Interpreted endpoint substitution preserves the rigid-tail assignment.
Only actual terms and their ordinary typing derivations cross the boundary. -/
theorem RigidTailTyping.subst
    (H : RigidTailTyping Δ e c) (W : ContextSubstitution Δ Ω τ) :
    RigidTailTyping Ω (e.subst τ) c := by
  obtain ⟨hn, Γ, f, F, hΓ, EΓ, hf, Ef, HF⟩ := H
  obtain ⟨Γ', σ, hΓ', EΓ', WS, ES⟩ := W hΓ EΓ
  have EX : proofErase Γ' (f.subst σ) = e.subst τ :=
    (proofErase_subst_with hΓ' WS hf ES).trans (congrArg (·.subst τ) Ef)
  refine ⟨?_, Γ', f.subst σ, F.subst σ, hΓ', EΓ', hf.subst henv.orderedStrong WS hΓ', EX, HF.subst σ⟩
  intro E
  have hp := (isProof_subst hΓ' WS hf).1 (proofErase_eq_proof.1 (EX.trans E))
  exact hn (Ef.symm.trans (proofErase_eq_proof.2 hp))

/-- An actual application consumes a Pi binder of the assigned type. A rigid
family at the type's head cannot itself be applied, by Pi/head separation. -/
theorem RigidTailTyping.app
    (hr : env.Rigid c) (H : RigidTailTyping Δ f c)
    (HT : TypedSource Δ (.app f x)) : RigidTailTyping Δ (.app f x) c := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A, B, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨F, hfF, HF⟩ := H.realize hΓ EΓ hf Ef
  cases HF with
  | family =>
    obtain ⟨_, hF⟩ := hfF.isType henv hΓ
    exact (IsDefEqU.rigidApp_forallE_inv henv hΓ hr hF (hfF.uniqU henv hΓ hf)).elim
  | forallE HB =>
    have hx' := argument_at_displayed_domain hΓ hf hfF hx
    refine ⟨(by intro E; cases E), Γ, .app f₀ x₀, _, hΓ, EΓ, hfF.app hx', Ee, ?_⟩
    simpa only [VExpr.inst_eq] using HB.subst (VExpr.Subst.one x₀)

/-- Any actually typed pending argument spine preserves the terminal family. -/
theorem RigidTailTyping.mkApps
    (hr : env.Rigid c) (H : RigidTailTyping Δ f c)
    (HT : TypedSource Δ (ProofShape.mkApps f args)) :
    RigidTailTyping Δ (ProofShape.mkApps f args) c := by
  induction args using List.snoc_induction with
  | nil => exact H
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at HT ⊢
    exact (ih (typed_spine_head (args := [x]) HT)).app hr HT

/-- A typed retained lambda adds a Pi binder to the rigid-tail assignment.
The displayed annotation and actual body realization are recovered from the
whole lambda typing, so no annotation transport of guarded paths is needed. -/
theorem RigidTailTyping.lam
    (H : RigidTailTyping (A :: Δ) b c) (HT : TypedSource Δ (.lam A b)) :
    RigidTailTyping Δ (.lam A b) c := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EΓA : proofEraseCtx (A₀ :: Γ) = A :: Δ := by rw [proofEraseCtx, EA, EΓ]
  obtain ⟨F, hbF, HF⟩ := H.realize hΓA EΓA hb Eb
  exact ⟨(by intro E; cases E), Γ, .lam A₀ b₀, .forallE A₀ F,
    hΓ, EΓ, HasType.lam hA hbF, Ee, .forallE HF⟩

/-- A sort-typed final output cannot also have a rigid-tail assignment. -/
theorem ControlTyping.no_rigid_tail
    (hr : env.Rigid c) (HC : ControlTyping Δ e (.sort u)) : ¬ RigidTailTyping Δ e c := by
  intro H
  obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := HC
  obtain ⟨F, hfF, HF⟩ := H.realize hΓ EΓ hf Ef
  cases HF with
  | family =>
    obtain ⟨_, hF⟩ := hfF.isType henv hΓ
    exact henv.headInversion.sort_rigid hΓ hr
      ((hfF.uniqU henv hΓ hf).typeChain henv hΓ hF).symm
  | forallE => exact (hf.uniqU henv hΓ hfF).sort_forallE_inv henv hΓ

/-- The actual mixed continuation transports a rigid-tail assignment all the
way to its final output. Retained annotations use their existing identity
interpretation; application paths use ordinary assigned-type preservation. -/
theorem PiInertTypedContinuationRun.rigid_tail
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hr : env.Rigid c)
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck)
    (HT : RigidTailTyping Δ e c) : RigidTailTyping Ω out c := by
  induction H with
  | terminal => exact HT
  | application _ W HTapp R HK ih =>
    exact ih (((HT.subst W.interpretation).mkApps hr HTapp).compute
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs _)) R.forget)
  | retained _ _ _ WI HK ih =>
    have HB := HT.subst WI
    simp only [ProofShape.subst_id] at HB
    exact ih ((HB.lam (typed_spine_head HK.typed)).mkApps hr HK.typed)

/-- Every source of a typed minimum ending at a sort lacks a rigid-tail type.
The proof uses its actual execution, not the minimum property. -/
theorem PiInertTypedContinuationMinimum.no_rigid_tail
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HC : ControlTyping Ω out (.sort u))
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost)
    (hr : env.Rigid c) : ¬ RigidTailTyping Δ source c := by
  intro HT
  obtain ⟨K, n, cb, ck, endpoint, _, R, HK, _, _⟩ := H
  exact HC.no_rigid_tail hr (HK.rigid_tail heq hs hr (HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R.forget))

/-- Native structure recovery supplies an actual rigid-family assignment at
the nonproof source. This does not transport the recovery certificate. -/
theorem rigid_tail_of_native_structure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ e) (hn : e ≠ .proof)
    (H : NativeMaskedStructureExpansion Step Δ e target) :
    ∃ c, env.Rigid c ∧ RigidTailTyping Δ e c := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, rfl⟩ := HT
  cases H with
  | intro hi hx ha hp RN =>
    obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EF
    exact ⟨_, henv.projectionRigid hi, hn, Γ, f, _, hΓ, rfl, hfF, rfl, .family⟩

/-- A structure root followed by an actual typed continuation to a sort is
impossible. The suffix retains its original stage and scope; only actual
assigned types are propagated through the remaining mixed frames. -/
theorem pi_inert_structure_root_no_sort_continuation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ source) (hn : source ≠ .proof)
    (H : NativeMaskedStructureExpansion Guard Δ source target)
    (R : ScopedCompute (PiInertStage D n) Δ source endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HC : ControlTyping Ω out (.sort u)) : False := by
  obtain ⟨c, hr, HT⟩ := rigid_tail_of_native_structure hguard HT hn H
  exact HC.no_rigid_tail hr (HK.rigid_tail heq hs hr (HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R))

/-- A head-losing primitive in the computed proof-major body of an actual
sort-ending minimum proves the original equation. The six-argument structure
alternative is excluded: its rigid-family type transfers back along the
actual prefix and then survives the retained mixed continuation, contradicting
the final sort assignment. No lower proof or guarded substitution is used. -/
theorem EqHeadCompletion.read_proof_major_loss_in_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u)
    (HL : List.Forall₂ (· ≈ ·) ls rootLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: Ξ))
      (args.map (·.liftN 1) ++ [etaArgument u]) (rootArgs ++ pending))
    (HT : TypedSource (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs))
    (HR : PiInertStage D rootStage (rawA :: Ξ)
      (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (HM : PiInertTypedContinuationMinimum D Ω out (rawA :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) cost)
    (HC : ControlTyping Ω out (.sort outU))
    (RP : ScopedCompute (PiInertStage D prefixStage) (rawA :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u))
      (ProofShape.mkApps (.const ``Eq.rec rootLs) (rootArgs ++ pending))) :
    env.IsDefEq univs Δ a b α := by
  rcases H.read_proof_major_loss heq hs hreg hoff hRec hΔ ht hlen RN SD HL HA HT HR HN with
    HE | ⟨_, rfl, Hstruct⟩
  · exact HE
  · obtain ⟨c, hr, Hrigid⟩ := rigid_tail_of_native_structure
      (erased_static_structure_eta_expansion_stage_descent heq hs rootStage)
      HT ProofShape.const_spine_ne_proof Hstruct
    have HTsource : TypedSource (rawA :: Ξ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
      obtain ⟨_, _, _, _, _, HTsource, _⟩ := HM
      exact HTsource
    have Hsource := Hrigid.compute_backward
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs prefixStage))
      HTsource (by simpa only [List.append_nil] using RP)
    exact (HM.no_rigid_tail heq hs HC hr Hsource).elim

end Lean4Lean.VEnv.Strengthening
