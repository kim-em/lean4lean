import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonHeaderReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructureHeader
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedFieldRecovery

/-! # Native family checkpoints from joined declaration headers

A common reduct of the stored family header and the constructor's parameter
header supplies an actual typed telescope at which the family has exact native
recovery. The constructor's original parameter header also computes there.
This starts a history at the common checkpoint, without identifying arbitrary
selected histories that began before it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private closed_compute_weak
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeReification
variable [Params] {D : PureObservation.Definitions}

/-- The stored family header and the constructor's raw parameter header have
one shared computational output. Its syntax and typing are not prescribed.
This is a hypothesis about a particular declaration, not an assertion that
all ordinarily equal headers join or a sufficient strengthening obligation. -/
def CommonStructureFamilyHeader (D : PureObservation.Definitions)
    (s : Name) (info : VProjectionInfo) (ls : List VLevel) : Prop :=
  ∃ ps tail fi u shared,
    (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail) ∧
    env.constants s = some fi ∧ ls.length = fi.uvars ∧
    env.IsType univs [] (VExpr.wrapForalls ps (.sort u)) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (fi.type.instL ls)) shared ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (VExpr.wrapForalls ps (.sort u))) shared

/-- A directed computed-header certificate supplies a common header, with the
constructor's original parameter header as the shared endpoint. -/
theorem ComputedStructureFamilyHeader.common
    (H : ComputedStructureFamilyHeader D s info ls) : CommonStructureFamilyHeader D s info ls := by
  obtain ⟨ps, tail, fi, u, HT, hc, hl, hT, R⟩ := H
  exact ⟨ps, tail, fi, u, _, HT, hc, hl, hT, R, .refl⟩

/-- The opposite direction also suffices for a common header. It does not in
general supply the directed certificate; registered examples separate them. -/
theorem CommonStructureFamilyHeader.of_reverse
    (HT : (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail))
    (hc : env.constants s = some fi) (hl : ls.length = fi.uvars)
    (hT : env.IsType univs [] (VExpr.wrapForalls ps (.sort u)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (VExpr.wrapForalls ps (.sort u))) (proofErase [] (fi.type.instL ls))) :
    CommonStructureFamilyHeader D s info ls :=
  ⟨ps, tail, fi, u, _, HT, hc, hl, hT, .refl, R⟩

/-- A common header yields an actual typed literal checkpoint of the original
parameter arity. Both closed headers compute to it, and the family recovers it
natively in every well-formed context. The domains may differ from both input
headers. No joining, native-argument, or checkpoint-typing premise is added. -/
theorem CommonStructureFamilyHeader.checkpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : ∀ l ∈ ls, l.WF univs)
    (H : CommonStructureFamilyHeader D s info ls) :
    ∃ ps tail qs u,
      (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail) ∧
      qs.length = info.nparams ∧
      env.IsType univs [] (VExpr.wrapForalls ps (.sort u)) ∧
      env.IsType univs [] (VExpr.wrapForalls qs (.sort u)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
        (proofErase [] (VExpr.wrapForalls ps (.sort u)))
        (proofErase [] (VExpr.wrapForalls qs (.sort u))) ∧
      env.HasType univs Γ (.const s ls) (VExpr.wrapForalls qs (.sort u)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.const s ls)) (proofErase Γ (VExpr.wrapForalls qs (.sort u))) := by
  obtain ⟨ps, tail, fi, u, shared, HT, hc, hl, ⟨v, hT⟩, RF, RP⟩ := H
  obtain ⟨qs, hlen, hQ, RPQ, RFQ⟩ :=
    static_structure_common_header_checkpoint heq hs (by trivial) hT RP RF
  have hf : env.HasType univs [] (.const s ls) (fi.type.instL ls) := .const hc hw hl
  obtain ⟨w, hOld⟩ := hf.isType henv (by trivial)
  obtain ⟨Q, HQ, EQ⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) (by trivial) hOld rfl rfl RFQ
  obtain ⟨_, HN⟩ := (proofErase_reflect (by trivial) HQ.hasType.2 hQ EQ).2
    (not_isProof_of_sort (by trivial) HQ.hasType.2)
  have HE := HQ.toU.trans henv (by trivial) (HN.defeq (by trivial))
  have hf' := hf.defeqU_r henv (by trivial) HE
  have hfΓ := hf'.weak0 henv.ordered (Γ := Γ)
  have RΓ := closed_compute_weak heq hs hΓ hOld hQ RFQ
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL) hOld hΓ
  refine ⟨ps, tail, qs, u, HT, hlen.trans (VExpr.takeForalls_domains_length HT),
    ⟨v, hT⟩, ⟨v, hQ⟩, RPQ, hfΓ, ?_⟩
  rw [show proofErase Γ (.const s ls) = .const s ls from
    if_neg (not_isProof_telescope_to_sort hΓ hfΓ)]
  exact (ScopedTypeRecovery.const hc hw hl).convert (EC ▸ RΓ)

/-- At the shared checkpoint the existing native family-history machinery
starts without the refuted directed alignment assumption. This does not move
an arbitrary earlier constructor history to that checkpoint. -/
theorem CommonStructureFamilyHeader.native_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : ∀ l ∈ ls, l.WF univs)
    (H : CommonStructureFamilyHeader D s info ls) :
    ∃ qs u, qs.length = info.nparams ∧
      NativeFamilyPiHistory D Γ (.const s ls) u qs (etaOpen qs.length (.const s ls)) := by
  obtain ⟨_, _, qs, u, _, hlen, _, _, _, hf, RN⟩ := H.checkpoint heq hs hΓ hw
  exact ⟨qs, u, hlen, NativeFamilyPiHistory.initial heq hs hΓ hf RN⟩

/-- Supplying all raw parameter images after the common checkpoint gives an
exact native sort. Ordinary typing or native recovery of the images is not
needed by the recovery grammar. This constructs a selected recovery, without
claiming ancestry or joining of every other selected native output. -/
theorem CommonStructureFamilyHeader.supplied_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : ∀ l ∈ ls, l.WF univs)
    (H : CommonStructureFamilyHeader D s info ls) (hlen : images.length = info.nparams) :
    ∃ u, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const s ls) images) (.sort u) := by
  obtain ⟨_, _, qs, u, _, hqs, _, _, _, hf, RN⟩ := H.checkpoint heq hs hΓ hw
  obtain ⟨hctx, hSort⟩ := hf.etaOpen_wf henv.ordered hΓ
  have hu := (hSort.isType henv hctx).sort_inv henv.ordered
  rw [show proofErase Γ (.const s ls) = .const s ls from
      if_neg (not_isProof_telescope_to_sort hΓ hf),
    proofErase_wrapForalls_type hΓ (hf.isType henv hΓ),
    show proofErase (qs.reverse ++ Γ) (.sort u) = .sort u from
      if_neg (not_isProof_of_sort hctx (HasType.sort hu))] at RN
  exact ⟨u, RN.supply_ignored_fields (B := .sort u) (by
    simpa only [proofEraseDomains_length, hqs] using hlen)⟩

end Lean4Lean.VEnv.Strengthening
