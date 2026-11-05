import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofIndexFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationUnindexedPattern

/-! # Erased full spines of singleton recursors with proof indices -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {params : List VExpr} {D : PureObservation.Definitions}

/-- Every actual argument in a dependent proof suffix erases to a proof,
including when the suffix follows arbitrary fixed data parameters. -/
theorem proof_telescope_suffix_arguments
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : OnCtx params.reverse (env.IsType univs))
    (H : PropTelescope env univs params.reverse ds) (hps : ps.length = params.length)
    (ha : TelInst env univs Γ (params ++ ds) (ps ++ args)) :
    args.map (proofErase Γ) = List.replicate args.length .proof := by
  apply List.map_eq_replicate_iff.mpr
  intro a ham
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ham
  have hal : args.length = ds.length := by
    have := ha.1; simp only [List.length_append, hps] at this; omega
  let i := ds.length - 1 - j
  have hi : i < ds.length := by dsimp [i]; omega
  obtain ⟨A, hl⟩ := Lookup.ofLt (Γ := ds.reverse ++ params.reverse)
    (i := i) (by simp only [List.length_append, List.length_reverse]; omega)
  have hp : IsProof (ds.reverse ++ params.reverse) (.bvar i) := by
    by_contra hn
    have := proof_telescope_retained_lookup H hl hn
    omega
  have hctx : OnCtx (params ++ ds).reverse (env.IsType univs) := by
    simpa only [List.reverse_append] using H.wf hP
  have W := erasedTemplate_substEq hctx ha
  have ht : env.HasType univs (params ++ ds).reverse (.bvar i) A := by
    simpa only [List.reverse_append] using (HasType.bvar (env := env) (U := univs) hl)
  have hp' := (isProof_subst hΓ W ht).2 (by simpa only [List.reverse_append] using hp)
  simp only [VExpr.subst, Subst.ofList, dif_pos (show i < (ps ++ args).length by simp; omega)] at hp'
  have hpos : (ps ++ args).length - 1 - i = ps.length + j := by
    simp only [List.length_append]; dsimp [i]; omega
  apply proofErase_eq_proof.mpr
  simpa only [hpos, List.getElem_append_right (show ps.length ≤ ps.length + j by omega),
    Nat.add_sub_cancel_left] using hp'

/-- The index and major suffix of every fully applied registered singleton
recursor erases to proofs when its index telescope is propositional. -/
theorem registered_proof_index_suffix
    {data : RecursorData} {index : Fin data.schema.signature.constructors.size}
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (W : E.WF S (data.propParams levels) env univs)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (hpref : pre.length = data.indexOffset) (hidx : idx.length = data.numIndices)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) (pre ++ idx ++ [m])) T) :
    idx.map (proofErase Γ) = List.replicate data.numIndices .proof ∧ proofErase Γ m = .proof := by
  have F := RecursorData.singletonSignature H hlarge hzero
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := index.isLt; have := F.constructors; omega
  let P := data.propParams levels
  let X := (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)
  have hX : X.length = 2 := by simp [X, Instance.motives, Instance.minors, F.families, hcs]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hio, _, _⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  have hplen : P.length = data.numParams := (RecursorData.singletonLayout_lengths hS).2
  have hil : idx.length = S.indices.length := hidx.trans (RecursorData.singletonLayout_lengths hS).1.symm
  have hpref' : pre.length = P.length + 2 := hpref.trans hio
  let ps := pre.take data.numParams
  let xs := pre.drop data.numParams
  have hps : ps.length = P.length := by simp only [ps, List.length_take, hpref', hplen]; omega
  have hxs : xs.length = X.length := by simp only [xs, List.length_drop, hpref', hplen, hX]; omega
  have hpre : pre = ps ++ xs := (List.take_append_drop _ pre).symm
  have hc := HasType.const (Γ := Γ) F.recursor hw hlen
  rw [ProofIndexedSingleton.type_shape H hlarge hzero howner hS hE] at hc
  have htel := hc.mkApps_telInst henv hΓ (show VExpr.WF env univs Γ _ from ⟨_, ht⟩) (by
    simp only [List.length_append, List.length_singleton, Instance.length_insertBinders,
      hpref, hio, hil, ← hX]
    rfl)
  rw [hpre] at htel
  obtain ⟨_, hargs⟩ := GuardedSingleton.full_major_args W hX hps hxs hil htel
  have hia : TelInst env univs Γ (P ++ S.indices) (ps ++ idx) := by
    have hh := hargs.take (doms := P ++ S.indices) (more := [majorTy S P E])
    simpa [hps, hil, List.take_append, List.take_of_length_le] using hh
  have hP : OnCtx P.reverse (env.IsType univs) := by
    simpa using W.typed.indicesCtx 0 (Nat.zero_le _)
  have hiErase := proof_telescope_suffix_arguments hΓ hP hindices hps hia
  rw [hidx] at hiErase
  have hm := registered_major_isProof hΓ H (by simpa only [mkApps_snoc] using ht)
    (by simp only [List.length_append, hpref, hidx, RecursorData.majorOffset]) hzero
  exact ⟨hiErase, proofErase_eq_proof.mpr hm⟩

/-- Changing only the proof-index and major suffix of a typed full recursor
spine has reflexive erased computation. Ordinary equality supplies typing and
proof-status coherence, while the registered telescope determines the erasure. -/
theorem TypedComputationEq.proof_indices_spine
    {data : RecursorData} {index : Fin data.schema.signature.constructors.size}
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (W : E.WF S (data.propParams levels) env univs)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (hpref : pre.length = data.indexOffset)
    (hidx : idx.length = data.numIndices) (hidx' : idx'.length = data.numIndices)
    (HE : env.IsDefEq univs Γ (mkApps (.const data.name levels) (pre ++ idx ++ [m]))
      (mkApps (.const data.name levels) (pre ++ idx' ++ [m'])) T) :
    TypedComputationEq D Γ (mkApps (.const data.name levels) (pre ++ idx ++ [m]))
      (mkApps (.const data.name levels) (pre ++ idx' ++ [m'])) T := by
  apply TypedComputationEq.of_erasure_eq HE
  by_cases hp : IsProof Γ (mkApps (.const data.name levels) (pre ++ idx ++ [m]))
  · rw [proofErase_eq_proof.mpr hp, proofErase_eq_proof.mpr ((isProof_congr hΓ HE).1 hp)]
  have hp' := mt (isProof_congr hΓ HE).2 hp
  obtain ⟨hix, hm⟩ := registered_proof_index_suffix hΓ H hlarge hzero hw hlen howner hS hE W
    hindices hpref hidx HE.hasType.1
  obtain ⟨hix', hm'⟩ := registered_proof_index_suffix hΓ H hlarge hzero hw hlen howner hS hE W
    hindices hpref hidx' HE.hasType.2
  rw [proofErase_const_spine hΓ HE.hasType.1 hp, proofErase_const_spine hΓ HE.hasType.2 hp']
  simp only [List.map_append, List.map_cons, List.map_nil, hix, hix', hm, hm']

end Lean4Lean.VEnv.Strengthening
