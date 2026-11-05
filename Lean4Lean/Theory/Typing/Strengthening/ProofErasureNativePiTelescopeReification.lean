import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeReification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTelescope

/-! # Reifying complete Pi histories as native family functions

Pi readout retains every dependent domain path in its original prefix context.
Those same paths change the domains of a native eta telescope. Whole type
computations may contain arbitrary expansion wrappers; only their administrative
beta residual is contracted to expose the marked telescope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
/-- A raw Pi telescope, in the same outermost-first order as wrapLams. -/
def ProofShape.wrapForalls (ds : List ProofShape) (body : ProofShape) : ProofShape :=
  ds.foldr .forallE body

omit [Params] in
/-- Dependent domain paths also change a Pi telescope around a body path. -/
theorem ProofShape.ScopedTelescopeCompute.wrapForalls
    (R : ScopedTelescopeCompute Step Δ ds ds')
    (RB : ScopedCompute Step (ds.reverse ++ Δ) b b') :
    ScopedCompute Step Δ (ProofShape.wrapForalls ds b) (ProofShape.wrapForalls ds' b') := by
  induction R with
  | nil => exact RB
  | cons RA RT ih =>
    apply ScopedCompute.forallE RA
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using RB

/-- A typed Pi telescope retains all its domains and its type-valued body. -/
theorem proofErase_wrapForalls_type
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B)) :
    proofErase Γ (VExpr.wrapForalls ds B) =
      ProofShape.wrapForalls (proofEraseDomains Γ ds) (proofErase (ds.reverse ++ Γ) B) := by
  induction ds generalizing Γ with
  | nil => rfl
  | cons A ds ih =>
    obtain ⟨u, hT⟩ := hT
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (VExpr.wrapForalls (A :: ds) B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) (VExpr.wrapForalls ds B)) from
      if_neg (not_isProof_of_sort hΓ hT), ih hΓA ⟨w, hB⟩]
    simp only [proofEraseDomains, ProofShape.wrapForalls, List.foldr_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Literal telescope endpoints expose exact domain and terminal-body histories.
All paths use the original contexts despite arbitrary intervening domain changes,
function eta, and structure eta. No substitution or argument recovery is assumed. -/
theorem static_structure_pi_telescope_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (hlen : ds.length = rawDs.length)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (ProofShape.wrapForalls rawDs out)) :
    ScopedTelescopeCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofEraseDomains Γ ds) rawDs ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) B) out := by
  induction ds generalizing Γ rawDs with
  | nil =>
    have : rawDs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst rawDs
    exact ⟨.nil, R⟩
  | cons A ds ih =>
    cases rawDs with
    | nil => simp at hlen
    | cons X rawDs =>
      obtain ⟨u, hT⟩ := hT
      obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
      rw [show proofErase Γ (VExpr.wrapForalls (A :: ds) B) =
        .forallE (proofErase Γ A) (proofErase (A :: Γ) (VExpr.wrapForalls ds B)) from
        if_neg (not_isProof_of_sort hΓ hT)] at R
      obtain ⟨_, _, _, _, _, _, RA, RB⟩ :=
        proofErase_static_structure_union_pi_components heq hs hΓ hA hB R
      obtain ⟨RT, RC⟩ := ih hΓA ⟨w, hB⟩ (Nat.succ.inj hlen) RB
      refine ⟨.cons RA RT, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using RC

/-- Every whole computation of a marked Pi telescope beta-exposes the same
number of binders. Both the computed domains and the residual type retain paths
from the original telescope. This only cleans the finite marked prefix, not the
arbitrary residual type or its computation. -/
theorem static_structure_pi_telescope_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) out) :
    ∃ rawDs body,
      ScopedTelescopeCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofEraseDomains Γ ds) rawDs ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
        (proofErase (ds.reverse ++ Γ) B) body ∧
      ProofShape.BetaRed out (ProofShape.wrapForalls rawDs body) := by
  induction ds generalizing Γ out with
  | nil => exact ⟨[], out, .nil, R, .refl⟩
  | cons A ds ih =>
    obtain ⟨u, hT⟩ := hT
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (VExpr.wrapForalls (A :: ds) B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) (VExpr.wrapForalls ds B)) from
      if_neg (not_isProof_of_sort hΓ hT)] at R
    obtain ⟨X, Y, ⟨_, _, _, _, _, _, RA, RB⟩, Rβ⟩ :=
      proofErase_static_structure_union_pi_origin heq hs hΓ hA hB R
    obtain ⟨rawDs, body, RT, RC, RBβ⟩ := ih hΓA ⟨w, hB⟩ RB
    refine ⟨X :: rawDs, body, .cons RA RT, ?_, Rβ.trans (.forallE .refl RBβ)⟩
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using RC

/-- A function ending in a sort cannot be a proof, at any dependent arity. -/
theorem not_isProof_telescope_to_sort
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u))) : ¬ IsProof Γ f := by
  induction ds generalizing Γ f with
  | nil => exact not_isProof_of_sort hΓ hf
  | cons A ds ih =>
    obtain ⟨⟨v, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    have hf' := hf.weak henv (B := A)
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0))
        (VExpr.wrapForalls ds (.sort u)) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using HasType.app hf' hx
    intro hp
    have hpw : IsProof (A :: Γ) f.lift := by
      simpa only [lift_eq_lift'] using hp.lift' (Ctx.Lift'.skip .refl)
    exact ih hΓA hb (IsProof.app_fn hΓA hf' hx hpw)

/-- A whole Pi history whose body is a native family's generic application
reifies as the family function's exact lambda telescope, with every computed
domain retained. This transfers full type histories, not only terminal bodies. -/
theorem static_structure_native_pi_telescope_reification
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u))))
    (hlen : ds.length = rawDs.length)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds (etaOpen ds.length f)))
      (ProofShape.wrapForalls rawDs out)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (ProofShape.wrapLams rawDs out) := by
  obtain ⟨hctx, hb⟩ := hf.etaOpen_wf henv.ordered hΓ
  obtain ⟨v, hT⟩ := VExpr.wrapForalls_defeq hctx hb
  obtain ⟨RT, RB⟩ := static_structure_pi_telescope_components heq hs hΓ ⟨v, hT.hasType.1⟩ hlen R
  have RE := static_structure_native_eta_telescope heq hs hΓ hf (fun _ => RF)
  have hη := hf.etaOpen_defeq henv hΓ
  rw [proofErase_wrapLams_nonproof hctx (not_isProof_telescope_to_sort hΓ hη.hasType.2)] at RE
  exact RE.trans (RT.wrapLams (proofEraseDomains_context ▸ RB))

/-- Changing all dependent domains by their original-prefix computation paths
preserves an exact native family guard. The resulting guard ends in the same
sort; no terminal-body recovery or native argument certificate is needed. -/
theorem static_structure_native_computed_telescope_domains
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (VExpr.wrapForalls ds (.sort u))))
    (RT : ScopedTelescopeCompute Step (proofEraseCtx Γ) (proofEraseDomains Γ ds) rawDs) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (ProofShape.wrapForalls rawDs (.sort u)) := by
  obtain ⟨hctx, hb⟩ := hf.etaOpen_wf henv.ordered hΓ
  obtain ⟨_, hSort⟩ := hb.isType henv hctx
  have ET := proofErase_wrapForalls_type hΓ (hf.isType henv hΓ)
  rw [show proofErase (ds.reverse ++ Γ) (.sort u) = .sort u from
    if_neg (not_isProof_of_sort hctx hSort)] at ET
  rw [ET] at RF
  exact RF.convert (RT.wrapForalls .refl)

/-- A whole type history can change the family's exact telescope guard as
well as its eta-expanded implementation. Both use the same computed dependent
domains, extracted from the literal type endpoint. -/
theorem static_structure_native_pi_telescope_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u))))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (hlen : ds.length = rawDs.length)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (ProofShape.wrapForalls rawDs out)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (ProofShape.wrapForalls rawDs (.sort u)) := by
  exact static_structure_native_computed_telescope_domains hΓ hf RF
    (static_structure_pi_telescope_components heq hs hΓ hT hlen R).1

/-- Arbitrary whole Pi computations reify after beta cleanup of only the
marked prefix. The same computed domains are retained in the family function
and its exact native guard. No normal form of the arbitrary body is asserted. -/
theorem static_structure_native_pi_telescope_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u))))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds (etaOpen ds.length f))) out) :
    ∃ rawDs body, ds.length = rawDs.length ∧
      ProofShape.BetaRed out (ProofShape.wrapForalls rawDs body) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (ProofShape.wrapLams rawDs body) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (ProofShape.wrapForalls rawDs (.sort u)) := by
  obtain ⟨hctx, hb⟩ := hf.etaOpen_wf henv.ordered hΓ
  obtain ⟨v, hT⟩ := VExpr.wrapForalls_defeq hctx hb
  obtain ⟨rawDs, body, RT, RB, Rβ⟩ :=
    static_structure_pi_telescope_origin heq hs hΓ ⟨v, hT.hasType.1⟩ R
  have RE := static_structure_native_eta_telescope heq hs hΓ hf (fun _ => RF)
  have hη := hf.etaOpen_defeq henv hΓ
  rw [proofErase_wrapLams_nonproof hctx (not_isProof_telescope_to_sort hΓ hη.hasType.2)] at RE
  exact ⟨rawDs, body, by simpa only [proofEraseDomains_length] using RT.length_eq,
    Rβ, RE.trans (RT.wrapLams (proofEraseDomains_context ▸ RB)),
    static_structure_native_computed_telescope_domains hΓ hf RF RT⟩

/-- Supplying a raw prefix after a whole type history retains the exact
corresponding family residual guard. Supply is a finite syntactic check; its
arguments require no native evidence. Conversions after this supply are not
asserted to lift back into the earlier generic type history. -/
theorem static_structure_native_pi_telescope_prefix_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u))))
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (hlen : ds.length = rawDs.length)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (ProofShape.wrapForalls rawDs out))
    (HS : ProofShape.supplyType images (ProofShape.wrapForalls rawDs (.sort u)) = some residual) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (proofErase Γ f) images) residual :=
  (static_structure_native_pi_telescope_guard heq hs hΓ hf RF hT hlen R).supply HS

/-- Literal paired declarations supply both native origins. Every selected
type of the constructor head reifies as a computation of its family head,
with the same changed parameter domains in the resulting native family guard.
The constructor has no field suffix here: its literal result is exactly the
family applied to the fresh parameter telescope. This is a head-history law;
interleaved conversions after actual arguments are supplied remain separate. -/
theorem static_structure_declared_constructor_telescope_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants ctor = some ci) (hwc : ∀ l ∈ cls, l.WF univs)
    (hlc : cls.length = ci.uvars)
    (hf : env.constants family = some fi) (hwf : ∀ l ∈ fls, l.WF univs)
    (hlf : fls.length = fi.uvars)
    (HTf : fi.type.instL fls = VExpr.wrapForalls ds (.sort u))
    (HTc : ci.type.instL cls =
      VExpr.wrapForalls ds (etaOpen ds.length (.const family fls)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.const ctor cls) selected) :
    ∃ rawDs body, ds.length = rawDs.length ∧
      ProofShape.BetaRed selected (ProofShape.wrapForalls rawDs body) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.const family fls) (ProofShape.wrapLams rawDs body) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.const family fls) (ProofShape.wrapForalls rawDs (.sort u)) := by
  have hft : env.HasType univs Γ (.const family fls) (VExpr.wrapForalls ds (.sort u)) :=
    HTf ▸ HasType.const hf hwf hlf
  have EF : proofErase Γ (.const family fls) = .const family fls :=
    if_neg (not_isProof_telescope_to_sort hΓ hft)
  have hfc : env.HasType univs [] (.const family fls) (fi.type.instL fls) := .const hf hwf hlf
  obtain ⟨_, hfT⟩ := hfc.isType henv (by trivial)
  have Eft := proofErase_closed_context ((henv.ordered.closedC hf).instL) hfT hΓ
  have RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.const family fls)) (proofErase Γ (VExpr.wrapForalls ds (.sort u))) := by
    rw [EF, ← HTf, Eft]
    exact .const hf hwf hlf
  have hct : env.HasType univs [] (.const ctor cls) (ci.type.instL cls) := .const hc hwc hlc
  obtain ⟨_, hcT⟩ := hct.isType henv (by trivial)
  have Ect := proofErase_closed_context ((henv.ordered.closedC hc).instL) hcT hΓ
  have RC := RN.const_compute hc
  rw [← Ect, HTc] at RC
  simpa only [EF] using static_structure_native_pi_telescope_origin heq hs hΓ hft RF RC

/-- A whole generic Pi history of a closed native family supplies an exact
instantiated terminal result after its marked telescope is beta-exposed. Actual
arguments may be arbitrary typed dependent data or proofs and may compute
independently. All type conversion in R precedes their supply; conversion after
a partial application is not moved across that application by this result. -/
theorem static_structure_closed_pi_history_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs [] f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx []) (proofErase [] f) (proofErase [] (VExpr.wrapForalls ds (.sort u))))
    (HA : TelInst env univs Γ ds args)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (VExpr.wrapForalls ds (etaOpen ds.length f))) out)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images) :
    ∃ rawDs body, ds.length = rawDs.length ∧
      ProofShape.BetaRed out (ProofShape.wrapForalls rawDs body) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps f args)) (body.instOuter images) := by
  obtain ⟨hctx, hb⟩ := hf.etaOpen_wf henv.ordered (by trivial)
  obtain ⟨v, hT⟩ := VExpr.wrapForalls_defeq hctx hb
  obtain ⟨rawDs, body, RT, RB, Rβ⟩ :=
    static_structure_pi_telescope_origin heq hs (by trivial) ⟨v, hT.hasType.1⟩ R
  exact ⟨rawDs, body, by simpa only [proofEraseDomains_length] using RT.length_eq,
    Rβ, static_structure_closed_telescope_instantiation heq hs hΓ hf (fun _ => RF) HA
      (by simpa only [List.append_nil] using RB) RX⟩

end Lean4Lean.VEnv.Strengthening
