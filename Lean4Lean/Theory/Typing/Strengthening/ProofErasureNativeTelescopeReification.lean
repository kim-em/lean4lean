import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares

/-! # Reifying generic computations before supplying telescope arguments

An exactly recovered function telescope can be opened by native eta. Compute
its generic body under the declared binders, then supply arbitrary typed
arguments and contract the administrative lambdas. Native certificates are
required for the function only, never for its actual argument images.

This is a forward path for computations of the generic application of that
function. It is not substitution closure for arbitrary typed bodies: relating
an unrelated codomain computation to this generic application remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
private theorem wrap_body_compute
    (R : ScopedCompute Step (ds.reverse ++ Δ) b b') :
    ScopedCompute Step Δ (ProofShape.wrapLams ds b) (ProofShape.wrapLams ds b') := by
  induction ds generalizing Δ with
  | nil => exact R
  | cons A ds ih =>
    exact .lam .refl (ih (by simpa only [List.reverse_cons, List.append_assoc,
      List.singleton_append] using R))

/-- A forward typed body computation closes beneath an arbitrary unchanged
dependent telescope. Proof-valued wrappers are handled by erasure directly. -/
theorem proofErase_scoped_compute_wrapLams_eq
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (HE : env.IsDefEq univs (ds.reverse ++ Γ) b b' T)
    (R : ScopedCompute Step (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) b) (proofErase (ds.reverse ++ Γ) b')) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapLams ds b)) (proofErase Γ (VExpr.wrapLams ds b')) := by
  have HL := HE.etaOpen_wrapLams hΓ hctx
  classical
  by_cases hp : IsProof Γ (VExpr.wrapLams ds b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact .refl
  have hp' : ¬ IsProof Γ (VExpr.wrapLams ds b') := fun h => hp ((isProof_congr hΓ HL).2 h)
  rw [proofErase_wrapLams_nonproof hctx hp, proofErase_wrapLams_nonproof hctx hp']
  exact wrap_body_compute (proofEraseDomains_context ▸ R)

/-- Forward computation of a function lifts through its whole literal typed
telescope. Argument recovery is not required at any dependent position. -/
theorem proofErase_scoped_compute_telescope_function
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ f g (VExpr.wrapForalls ds T))
    (HA : TelInst env univs Γ ds args)
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps f args)) (proofErase Γ (VExpr.mkApps g args)) := by
  have HEA := IsDefEq.mkApps_congr HE HA.1 rfl (fun j hj hj' _ => HA.2 j hj hj')
  classical
  by_cases hp : IsProof Γ (VExpr.mkApps f args)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HEA).1 hp)]
    exact .refl
  have hp' : ¬ IsProof Γ (VExpr.mkApps g args) := fun h => hp ((isProof_congr hΓ HEA).2 h)
  rw [proofErase_mkApps hΓ HEA.hasType.1 hp, proofErase_mkApps hΓ HEA.hasType.2 hp']
  exact .mkApps R (List.Forall₂.rfl (fun _ _ => .refl))

/-- Every full-union computation of the generic application can be run beneath
native eta's literal telescope. The result is an actual typed body and a forward
path from the original function to its lambda closure. No computation is
substituted, and arbitrary dependent proof or retained binders are included. -/
theorem static_structure_native_telescope_body_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds T))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds T)))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) (etaOpen ds.length f)) out) :
    ∃ b, env.IsDefEq univs (ds.reverse ++ Γ) (etaOpen ds.length f) b T ∧
      proofErase (ds.reverse ++ Γ) b = out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (VExpr.wrapLams ds b)) := by
  obtain ⟨hctx, hb⟩ := hf.etaOpen_wf henv.ordered hΓ
  obtain ⟨b, HE, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hctx hb rfl rfl RB
  exact ⟨b, HE, EB, (static_structure_native_eta_telescope heq hs hΓ hf RF).trans
    (proofErase_scoped_compute_wrapLams_eq hΓ hctx HE (EB ▸ RB))⟩

/-- Supplying arbitrary ordinary telescope arguments after generic computation
reaches the instantiated computed body exactly. This covers arbitrary retained
data arguments, even when their assigned domains have no native certificates.
The generic body must be the eta opening of the originally recovered function;
an arbitrary unrelated type body is not asserted to satisfy this law. -/
theorem static_structure_native_telescope_application_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds T))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds T)))
    (HA : TelInst env univs Γ ds args)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) (etaOpen ds.length f)) out) :
    ∃ b, env.IsDefEq univs (ds.reverse ++ Γ) (etaOpen ds.length f) b T ∧
      proofErase (ds.reverse ++ Γ) b = out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps f args)) (proofErase Γ (b.instOuter args)) := by
  obtain ⟨b, HE, EB, RF'⟩ := static_structure_native_telescope_body_compute heq hs hΓ hf RF RB
  have hctx := (hf.etaOpen_wf henv.ordered hΓ).1
  have HEF := (hf.etaOpen_defeq henv hΓ).trans (HE.etaOpen_wrapLams hΓ hctx)
  have RC := proofErase_scoped_compute_telescope_function hΓ HEF HA RF'
  have Hβ := VExpr.BetaRed.mkApps_wrapLams ds b args (Nat.le_of_eq HA.1.symm)
  rw [HA.1.symm, List.take_length, List.drop_length] at Hβ
  exact ⟨b, HE, EB, RC.trans (.beta (proofErase_beta_forward hΓ
    (HasType.mkApps_of_tel HEF.hasType.2 HA) Hβ))⟩

private theorem union_rename
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b) (W : ContextRenaming Δ Δ' σ) :
    ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
  obtain ⟨n, R⟩ := R
  exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n R W⟩

private theorem closed_compute_weak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs [] f T) (hg : env.HasType univs [] g U)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] f) (proofErase [] g)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) := by
  have W : Ctx.LiftN Γ.length 0 [] Γ := by simpa using Ctx.LiftN.zero (Γ := []) Γ
  have RL := R.rename (union_rename heq hs) (ContextRenaming.of_liftN (by trivial) hΓ W)
  simp only [subst_bvar_liftN] at RL
  rw [← proofErase_liftN (by trivial) hΓ W hf, ← proofErase_liftN (by trivial) hΓ W hg] at RL
  simpa only [(hf.closedN henv.ordered (by trivial)).liftN_eq (Nat.zero_le _),
    (hg.closedN henv.ordered (by trivial)).liftN_eq (Nat.zero_le _)] using RL

/-- A closed native telescope reifies its generic body's whole computation at
arbitrary typed captures in any ambient context. The captures may then compute
independently to raw images. The endpoint is the exact simultaneous raw
instantiation, with no native recovery required for any original or computed
capture. Dependent and proof binders, and arbitrary telescope length, are allowed. -/
theorem static_structure_closed_telescope_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs [] f (VExpr.wrapForalls ds T))
    (RF : ¬ IsProof [] f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx []) (proofErase [] f) (proofErase [] (VExpr.wrapForalls ds T)))
    (HA : TelInst env univs Γ ds args)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx ds.reverse)
      (proofErase ds.reverse (etaOpen ds.length f)) out)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps f args)) (out.instOuter images) := by
  obtain ⟨b, HE, EB, RC⟩ := static_structure_native_telescope_body_compute
    heq hs (by trivial) hf RF (by simpa only [List.append_nil] using RB)
  have hctx := (hf.etaOpen_wf henv.ordered (by trivial)).1
  have HEF := (hf.etaOpen_defeq henv (by trivial)).trans (HE.etaOpen_wrapLams (by trivial) hctx)
  have RL := closed_compute_weak heq hs hΓ hf HEF.hasType.2 RC
  have RA := proofErase_scoped_compute_telescope_function hΓ (HEF.weak0 henv.ordered) HA RL
  have Hβ := VExpr.BetaRed.mkApps_wrapLams ds b args (Nat.le_of_eq HA.1.symm)
  rw [HA.1.symm, List.take_length, List.drop_length] at Hβ
  have Rβ := proofErase_beta_forward hΓ
    (HasType.mkApps_of_tel (HEF.hasType.2.weak0 henv.ordered) HA) Hβ
  have R₁ := RA.trans (.beta Rβ)
  change ScopedCompute _ _ (proofErase Γ (VExpr.mkApps f args)) (proofErase Γ (b.instOuter args)) at R₁
  simp only [List.append_nil] at HE EB hctx
  rw [proofErase_instOuter hΓ hctx HE.hasType.2 HA, EB] at R₁
  have R₂ := proofErase_template_compute_captures (union_rename heq hs) hΓ hctx HE.hasType.2 HA RX
  rw [EB] at R₂
  exact R₁.trans R₂

/-- A literal declaration telescope supplies the function certificate itself.
Generic computations of a declared head therefore instantiate at arbitrary
dependent data/proof arguments and their computed images with no native image
premises. A merely convertible telescope is not substituted for this literal
declaration equality; obtaining its exact guard remains a separate task. -/
theorem static_structure_declared_telescope_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = ci.uvars)
    (HT : ci.type.instL ls = VExpr.wrapForalls ds T)
    (HA : TelInst env univs Γ ds args)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx ds.reverse)
      (proofErase ds.reverse (etaOpen ds.length (.const c ls))) out)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) (out.instOuter images) := by
  have hf : env.HasType univs [] (.const c ls) (VExpr.wrapForalls ds T) :=
    HT ▸ HasType.const hc hw hl
  apply static_structure_closed_telescope_instantiation heq hs hΓ hf ?_ HA RB RX
  intro hn
  rw [show proofErase [] (.const c ls) = .const c ls from if_neg hn, ← HT]
  exact .const hc hw hl

/-- A generic application computation instantiates exactly at an arbitrary
typed argument and then at any computed image of it. The original function's
Pi certificate supplies eta; neither argument needs native recovery. -/
theorem static_structure_native_application_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B)))
    (hx : env.HasType univs Γ x A)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) out)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (out.inst image) := by
  have HA : TelInst env univs Γ [A] [x] := by
    refine ⟨rfl, ?_⟩
    intro j hj _
    have : j = 0 := by simpa using hj
    subst j
    exact hx
  obtain ⟨b, HE, EB, RC⟩ := static_structure_native_telescope_application_compute
    (ds := [A]) heq hs hΓ hf RF HA RB
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) :=
    (hf.etaOpen_wf (domains := [A]) henv.ordered hΓ).1
  change env.IsDefEq univs (A :: Γ) (.app f.lift (.bvar 0)) b B at HE
  change proofErase (A :: Γ) b = out at EB
  have RI := proofErase_static_structure_compute_inst_argument heq hs hΓA HE.hasType.2 hx RX
  rw [EB] at RI
  exact RC.trans RI

/-- A computed Pi whose original codomain is a natively recovered family
application can be instantiated without native recovery of its argument. Pi
origin supplies the generic family computation; eta reifies it before the
argument is supplied. This replaces the retained-argument premise for this
concrete codomain shape, not for arbitrary dependent codomains. -/
theorem static_structure_native_family_pi_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.forallE A (.sort v)))
    (RG : ¬ IsProof Γ g → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ g) (proofErase Γ (.forallE A (.sort v))))
    (hx : env.HasType univs Γ x A)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A (.app g.lift (.bvar 0)))) (.forallE rawA rawB))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app g x)) (rawB.inst image) := by
  obtain ⟨_, hPi⟩ := hg.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := hPi.forallE_inv henv
  have hB := (hg.etaOpen_wf (domains := [A]) henv.ordered hΓ).2
  change env.HasType univs (A :: Γ) (.app g.lift (.bvar 0)) (.sort v) at hB
  rw [show proofErase Γ (.forallE A (.app g.lift (.bvar 0))) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RT
  obtain ⟨_, _, _, _, _, _, _, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hB RT
  exact static_structure_native_application_instantiation heq hs hΓ hg RG hx RB RX

/-- All selected outputs, including arbitrary conversion tails, retain the
original family application as a computation ancestor after its argument has
computed. The original argument is only ordinarily typed. The family head must
recover its displayed Pi, and the raw term function retains its stated type
origin; neither premise is silently inferred from ordinary conversion. -/
theorem static_structure_computed_native_family_application_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.forallE A (.sort v)))
    (RG : ¬ IsProof Γ g → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ g) (proofErase Γ (.forallE A (.sort v))))
    (hx : env.HasType univs Γ x A)
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A (.app g.lift (.bvar 0)))) T)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f image) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app g x)) out := by
  generalize EΔ : proofEraseCtx Γ = Δ at RN
  generalize E : ProofShape.app f image = e at RN
  induction RN with
  | app RF =>
    cases E
    rw [← EΔ] at RF ⊢
    exact static_structure_native_family_pi_inst heq hs hΓ hg RG hx (HN RF) RX
  | convert _ R ih => exact (ih EΔ E).trans R
  | bvar | sort | const | lam | forallE | proj => cases E

/-- Literal context declarations supply both origins for family applications.
An arbitrary typed argument may compute independently while every
native output of the dependent neutral application remains reachable from its
original assigned family. There is no native-argument or type-fork premise. -/
theorem static_structure_neutral_family_argument_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : Lookup Γ i (.forallE A (.sort v)))
    (hf : Lookup Γ j (.forallE A (.app (VExpr.bvar i).lift (.bvar 0))))
    (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar j) image) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar i) x)) out := by
  apply static_structure_computed_native_family_application_origin heq hs hΓ
    (HasType.bvar hg) (fun hn => proofErase_scoped_lookup_recovery hΓ hg hn .refl) hx ?_ RX RN
  intro T R
  have H := R.bvar_compute
  rwa [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hf] at H

end Lean4Lean.VEnv.Strengthening
