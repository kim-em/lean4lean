import Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedHeaderDirection

/-! # A fixed syntactic header obstruction

The parameter headers here depend only on the old unit family and constructor
names. Their obstruction can therefore be re-established after installing new
constants and projection metadata, without transporting negative computation
facts through an environment extension.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private no_inserted_argument
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeaderAncestryBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private wrap_type fixed_prefix_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation

namespace ExplicitHeaderBoundary

def context (s : Name) : List VExpr :=
  [.const s [], .forallE (.const s []) (.sort (.succ .zero)), .const s []]
def oldDomain : VExpr := .app (.bvar 1) (.bvar 0)
def newDomain (c : Name) : VExpr := .app (.bvar 1) (.const c [])
def parameters (s : Name) : List VExpr := (context s).reverse ++ [oldDomain]
def storedHeader (s c : Name) : VExpr :=
  VExpr.wrapForalls ((context s).reverse ++ [newDomain c]) (.sort .zero)
def chosenHeader (s : Name) (v : VLevel := .zero) : VExpr :=
  VExpr.wrapForalls (parameters s) (.sort v)

variable [Params]

/-- Fixed domain syntax witnesses the ordinary equality and the fresh-index
obstruction in any well-formed environment retaining the old empty structure.
The theorem uses no hypotheses on newly added constants or projection entries. -/
theorem domains
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero))) :
    OnCtx (context s) (env.IsType univs) ∧
    env.IsDefEq univs (context s) oldDomain (newDomain info.ctorName) (.sort (.succ .zero)) ∧
    ∀ Step, ErasedScopedPrimitiveDescent Step →
      ¬ ScopedCompute Step (proofEraseCtx (context s))
        (proofErase (context s) (newDomain info.ctorName))
        (proofErase (context s) oldDomain) := by
  let S := VExpr.const s []
  let FT := VExpr.forallE S (.sort (.succ .zero))
  have hFT : env.HasType univs [] FT (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  let Γ₀ := [FT, S]
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hFT.weak0 henv.ordered⟩
  have hΓ : OnCtx (context s) (env.IsType univs) := ⟨hΓ₀, _, hS.weak0 henv.ordered⟩
  have hy₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hc₀ : env.HasType univs Γ₀ (.const info.ctorName []) S :=
    hy₀.unitLike_constructor henv hΓ₀ hi (params := []) hp.symm hx hz
  have hC₀ : env.HasType univs Γ₀ (.app (.bvar 0) (.const info.ctorName []))
      (.sort (.succ .zero)) := .app (show env.HasType univs Γ₀ (.bvar 0) FT from .bvar .zero) hc₀
  have W : Ctx.LiftN 1 0 Γ₀ (context s) := .zero [S]
  have hc : env.HasType univs (context s) (.const info.ctorName []) S := hc₀.weakN henv W
  have hzT : env.HasType univs (context s) (.bvar 0) S := .bvar .zero
  have hF : env.HasType univs (context s) (.bvar 1) FT := .bvar (.succ .zero)
  have HE : env.IsDefEq univs (context s) oldDomain (newDomain info.ctorName)
      (.sort (.succ .zero)) := .appDF hF (IsDefEq.unitLike (params := []) hi hp.symm hx hz hzT hc)
  refine ⟨hΓ, HE, ?_⟩
  intro Step hstep R
  have EF : proofErase (context s) (.bvar 1) = .bvar 1 :=
    if_neg (not_isProof_function_to_sort hΓ hF)
  have EZ : proofErase (context s) (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hzT)
  have EB : proofErase (context s) oldDomain = .app (.bvar 1) (.bvar 0) := by
    rw [show proofErase (context s) oldDomain = .app _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.1), EF, EZ]
  have EC : proofErase (context s) (newDomain info.ctorName) =
      (proofErase Γ₀ (.app (.bvar 0) (.const info.ctorName []))).liftN 1 0 :=
    proofErase_liftN hΓ₀ hΓ W hC₀
  rw [EC, EB] at R
  exact no_inserted_argument hstep hΓ₀ hΓ W hC₀ (j := 0) (by decide) (by decide) R

/-- The fixed stored header is ordinarily equal to the constructor's chosen
parameter header. This is the equality accepted by source header checking. -/
theorem header_equal
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero))) :
    ∃ v, env.IsDefEq univs [] (storedHeader s info.ctorName) (chosenHeader s) (.sort v) := by
  obtain ⟨hΓ, HE, _⟩ := domains hi hp hx hz hS
  have HP := IsDefEq.forallEDF HE.symm (HasType.sort (l := .zero) (by trivial))
  have hctx : OnCtx ((context s).reverse.reverse ++ []) (env.IsType univs) := by simpa using hΓ
  obtain ⟨v, H⟩ := VExpr.wrapForalls_defeq hctx (by simpa using HP)
  exact ⟨v, by simpa only [storedHeader, chosenHeader, parameters,
    EtaTelescope.wrapForalls_append_one] using H⟩

/-- The chosen header computes to the stored header by unit eta at the fresh
index. Hence the stored header is already a common reduct of the pair; the
reverse obstruction concerns the orientation of an exact certificate only. -/
theorem header_forward {D : PureObservation.Definitions}
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (chosenHeader s)) (proofErase [] (storedHeader s info.ctorName)) := by
  obtain ⟨hΓ, HE, _⟩ := domains hi hp hx hz hS
  have hzT : env.HasType univs (context s) (.bvar 0) (.const s []) := .bvar .zero
  have ES : proofErase (context s) (.const s []) = .const s [] :=
    if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  have hnz := not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hzT
  have hc := hzT.unitLike_constructor henv hΓ hi (params := []) hp.symm hx hz
  have EC : proofErase (context s) (.const info.ctorName []) = .const info.ctorName [] :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hc)
  have RN := proofErase_scoped_lookup_recovery (Step := ErasedUnitEtaExpansionStage D 0)
    hΓ (show Lookup (context s) 0 (.const s []) from .zero) hnz .refl
  rw [ES] at RN
  have RZ := (unit_eta_native_join hi hx hz (ps := []) hp.symm RN RN).1
  have RD : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (context s))
      (proofErase (context s) oldDomain) (proofErase (context s) (newDomain info.ctorName)) := by
    rw [show proofErase (context s) oldDomain = .app _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.1),
      show proofErase (context s) (newDomain info.ctorName) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ HE.hasType.2), EC]
    exact .app .refl (RZ.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩))
  have HP := IsDefEq.forallEDF HE (HasType.sort (l := .zero) (by trivial))
  have hΓB : OnCtx (oldDomain :: context s) (env.IsType univs) := ⟨hΓ, _, HE.hasType.1⟩
  have hΓC : OnCtx (newDomain info.ctorName :: context s) (env.IsType univs) := ⟨hΓ, _, HE.hasType.2⟩
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (context s))
      (proofErase (context s) (.forallE oldDomain (.sort .zero)))
      (proofErase (context s) (.forallE (newDomain info.ctorName) (.sort .zero))) := by
    rw [show proofErase (context s) (.forallE oldDomain (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.1),
      show proofErase (context s) (.forallE (newDomain info.ctorName) (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.2),
      show proofErase (oldDomain :: context s) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial))),
      show proofErase (newDomain info.ctorName :: context s) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓC (HasType.sort (by trivial)))]
    exact .forallE RD .refl
  have hctx : OnCtx ((context s).reverse.reverse ++ []) (env.IsType univs) := by simpa using hΓ
  have R := fixed_prefix_compute hctx ⟨_, by simpa using HP.hasType.1⟩
    ⟨_, by simpa using HP.hasType.2⟩ (by simpa using RP)
  simpa only [chosenHeader, parameters, storedHeader, EtaTelescope.wrapForalls_append_one] using R

/-- No choice of result universe makes the stored header compute to the
chosen parameter domains. In particular, existentially choosing the sort in a
computed family-header certificate cannot evade the obstruction. -/
theorem no_header_compute {D : PureObservation.Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hT : env.IsType univs [] (chosenHeader s v)) :
    ¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (storedHeader s info.ctorName)) (proofErase [] (chosenHeader s v)) := by
  obtain ⟨hΓ, HE, Hno⟩ := domains hi hp hx hz hS
  have hctx : OnCtx ((context s).reverse.reverse ++ []) (env.IsType univs) := by simpa using hΓ
  have hV := ((IsType.wrapForalls_inv henv (by trivial) hT).2.choose_spec).sort_inv henv.ordered
  have hPiC := HasType.forallE HE.hasType.2 (HasType.sort (l := .zero) (by trivial))
  have hPiB := HasType.forallE HE.hasType.1 (HasType.sort hV)
  have hTC : env.IsType univs []
      (VExpr.wrapForalls (context s).reverse (.forallE (newDomain info.ctorName) (.sort .zero))) :=
    wrap_type hctx ⟨_, by simpa using hPiC⟩
  have hTB : env.IsType univs []
      (VExpr.wrapForalls (context s).reverse (.forallE oldDomain (.sort v))) :=
    wrap_type hctx ⟨_, by simpa using hPiB⟩
  intro R
  simp only [storedHeader, chosenHeader, parameters, EtaTelescope.wrapForalls_append_one] at R
  change ScopedCompute _ _ (proofErase [] (VExpr.wrapForalls (context s).reverse
    (.forallE (newDomain info.ctorName) (.sort .zero))))
    (proofErase [] (VExpr.wrapForalls (context s).reverse (.forallE oldDomain (.sort v)))) at R
  rw [proofErase_wrapForalls_type (by trivial) hTB] at R
  have RB := (static_structure_pi_telescope_components heq hs (by trivial) hTC
    (by simp only [proofEraseDomains_length]) R).2
  simp only [List.reverse_reverse, List.append_nil] at RB
  rw [show proofErase (context s) (.forallE (newDomain info.ctorName) (.sort .zero)) =
      .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPiC),
    show proofErase (context s) (.forallE oldDomain (.sort v)) =
      .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPiB)] at RB
  obtain ⟨_, _, _, _, _, _, RD, _⟩ := proofErase_static_structure_union_pi_components
    heq hs hΓ HE.hasType.2 (HasType.sort (l := .zero) (by trivial)) RB
  exact Hno _ (erased_static_structure_eta_expansion_union_descent heq hs) RD

end ExplicitHeaderBoundary
end Lean4Lean.VEnv.Strengthening
