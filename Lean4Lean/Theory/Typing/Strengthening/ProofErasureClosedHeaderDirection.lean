import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeaderAncestryBoundary

/-! # Ordinary equality does not orient closed parameter-header computation

Closing a type-domain history under its whole context retains its direction.
Exact Pi-component extraction would turn a reverse closed-header computation
into the corresponding reverse open-domain computation. The fresh-index
boundary therefore survives in closed, equally long, sort-ending telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private fixed_prefix_compute wrap_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
variable [Params] {D : PureObservation.Definitions}

/-- Closed computation between sort-ending headers with the same context
prefix reflects to computation between their final parameter domains. The
whole closed history may contain arbitrary function/structure eta and opaque
controls; component extraction retains the exact chosen domain endpoint. -/
theorem static_structure_closed_header_domain_reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hB : env.HasType univs Γ B (.sort u))
    (hC : env.HasType univs Γ C (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [B]) (.sort .zero)))
      (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [C]) (.sort .zero)))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ C) := by
  have hPiB := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have hPiC := HasType.forallE hC (HasType.sort (l := .zero) (by trivial))
  have hctx : OnCtx (Γ.reverse.reverse ++ []) (env.IsType univs) := by simpa using hΓ
  have hTB : env.IsType univs [] (VExpr.wrapForalls Γ.reverse (.forallE B (.sort .zero))) :=
    wrap_type hctx ⟨_, by simpa using hPiB⟩
  have hTC : env.IsType univs [] (VExpr.wrapForalls Γ.reverse (.forallE C (.sort .zero))) :=
    wrap_type hctx ⟨_, by simpa using hPiC⟩
  simp only [EtaTelescope.wrapForalls_append_one] at R
  change ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
    (proofErase [] (VExpr.wrapForalls Γ.reverse (.forallE B (.sort .zero))))
    (proofErase [] (VExpr.wrapForalls Γ.reverse (.forallE C (.sort .zero)))) at R
  rw [proofErase_wrapForalls_type (by trivial) hTC] at R
  have RB := (static_structure_pi_telescope_components heq hs (by trivial) hTB
    (by simp only [proofEraseDomains_length]) R).2
  simp only [List.reverse_reverse, List.append_nil] at RB
  rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPiB),
    show proofErase Γ (.forallE C (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPiC)] at RB
  obtain ⟨B', C', HB', HC', EB', EC', RD, RC⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hB
      (HasType.sort (l := .zero) (by trivial)) RB
  exact RD

/-- Canonical Eq and a registered positive empty structure admit closed,
equally long sort-ending parameter headers that are ordinarily equal and
compute in one direction but not the other. Thus ordinary closed-header
equality cannot supply a directed header certificate in either chosen direction.
This is not a strengthening or joining counterexample: the forward endpoint
is an explicit common reduct. No new family/constructor declaration is installed. -/
theorem static_structure_closed_header_direction_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ B C v,
      OnCtx Γ (env.IsType univs) ∧
      env.IsDefEq univs []
        (VExpr.wrapForalls (Γ.reverse ++ [B]) (.sort .zero))
        (VExpr.wrapForalls (Γ.reverse ++ [C]) (.sort .zero)) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
        (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [B]) (.sort .zero)))
        (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [C]) (.sort .zero))) ∧
      ¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
        (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [C]) (.sort .zero)))
        (proofErase [] (VExpr.wrapForalls (Γ.reverse ++ [B]) (.sort .zero))) := by
  obtain ⟨Γ, B, C, hΓ, hB, hC, _, _, _, _, RBC, Hno⟩ :=
    static_structure_forward_header_exact_ancestry_failure heq hs hi hp hx hz hS
  obtain ⟨C', HC', EC'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hB rfl rfl RBC
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HC'.hasType.2 hC EC').2
    (not_isProof_of_sort hΓ HC'.hasType.2)
  have HBC := HC'.transU_l henv hΓ (HN.defeq hΓ)
  have HP := IsDefEq.forallEDF HBC (HasType.sort (l := .zero) (by trivial))
  have hctx : OnCtx (Γ.reverse.reverse ++ []) (env.IsType univs) := by simpa using hΓ
  obtain ⟨v, HE⟩ := VExpr.wrapForalls_defeq hctx (by simpa using HP)
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, _, hC⟩
  have RPi : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE B (.sort .zero))) (proofErase Γ (.forallE C (.sort .zero))) := by
    rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ HP.hasType.1),
      show proofErase Γ (.forallE C (.sort .zero)) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ HP.hasType.2),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial))),
      show proofErase (C :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓC (HasType.sort (by trivial)))]
    exact .forallE RBC .refl
  have RF := fixed_prefix_compute hctx ⟨_, by simpa using HP.hasType.1⟩
    ⟨_, by simpa using HP.hasType.2⟩ (by simpa using RPi)
  refine ⟨Γ, B, C, v, hΓ, ?_, ?_, ?_⟩
  · simpa only [EtaTelescope.wrapForalls_append_one] using HE
  · simpa only [EtaTelescope.wrapForalls_append_one] using RF
  · intro R
    exact Hno _ (erased_static_structure_eta_expansion_union_descent heq hs)
      (static_structure_closed_header_domain_reflect heq hs hΓ hC hB R)

/-- A proposed blanket alignment principle for equally long, closed,
sort-ending headers. It asks ordinary equality to determine a directed
computation, irrespective of its orientation. The next theorem refutes this
principle; it is not used as an assumption in the positive native-history work. -/
def ClosedSortHeaderDirectedAlignment (D : PureObservation.Definitions) : Prop :=
  ∀ {ps qs : List VExpr} {u : VLevel}, ps.length = qs.length →
    env.IsDefEqU univs [] (VExpr.wrapForalls ps (.sort u)) (VExpr.wrapForalls qs (.sort u)) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (VExpr.wrapForalls ps (.sort u)))
      (proofErase [] (VExpr.wrapForalls qs (.sort u)))

/-- Closing the domains and requiring equal arity does not repair directed
header alignment from ordinary equality. This refutes the blanket principle,
not the computed-header certificate for a particular registered declaration,
common-reduct existence, or canonical-Eq strengthening. -/
theorem not_closed_sort_header_directed_alignment
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ¬ ClosedSortHeaderDirectedAlignment D := by
  intro H
  obtain ⟨Γ, B, C, v, _, HE, _, Hno⟩ :=
    static_structure_closed_header_direction_boundary heq hs hi hp hx hz hS
  exact Hno (H (by simp) HE.symm.toU)

end Lean4Lean.VEnv.Strengthening
