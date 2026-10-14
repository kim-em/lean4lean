import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIota
import Lean4Lean.Theory.Typing.Strengthening.SingletonFamilyTransport

/-! # Erased family guards for singletons with proof fields

Canonical Eq extracts a typed constructor field instance from any major. When
every field is a proof, the erasure of its result family depends only on the
parameters and the stored constructor template. Matching that erased family to
the major's family gives a bare reconstructed constructor at the requested type.
The indices themselves may have arbitrary data types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params SingletonLayout PropElim
variable [Params] {S : SingletonLayout} {E : PropElim} {ps fields params idx : List VExpr}

/-- Every typed field instance of a proof-only layout erases to proof markers.
This uses its instantiated declared proposition, not a comparison with a second
field list or with the original constructor's indices. -/
theorem proofErase_singleton_fields (W : E.WF S params env univs)
    (hps : ps.length = params.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ fields)) :
    fields.map (proofErase Γ) = List.replicate S.fields.length ProofShape.proof := by
  have hfl : fields.length = S.fields.length := by
    have := hf.1
    simp only [List.length_append] at this
    omega
  apply List.ext_getElem
  · simp [hfl]
  intro j hj hj'
  have hjf : j < S.fields.length := by simpa [hfl] using hj
  have hfj : j < fields.length := by omega
  have hprefix : TelInst env univs Γ (params ++ S.fields.take j)
      ((ps ++ fields).take (params.length + j)) := by
    have hf' : TelInst env univs Γ ((params ++ S.fields.take j) ++ S.fields.drop j)
        (ps ++ fields) := by simpa only [List.append_assoc, List.take_append_drop] using hf
    simpa only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hjf)]
      using hf'.take
  have hp := HasType.closed_instOuter henv (W.typed.fieldsCtx j (Nat.le_of_lt hjf))
    (W.typed.fieldSort j hjf) hprefix
  simp only [SingletonLayout.fieldSort, hs j hjf, instOuter_sort] at hp
  have ht := hf.getD (j := params.length + j) (by simp; omega)
  simp only [getD_append_right' (show ps.length ≤ params.length + j by omega),
    getD_append_right' (Nat.le_add_right _ _), hps, Nat.add_sub_cancel_left,
    getD_of_lt hjf, getD_of_lt hfj] at ht
  simpa only [List.getElem_map, List.getElem_replicate] using
    (proofErase_eq_proof.2 ⟨_, ht, hp⟩)

/-- The family shape produced by a proof-only constructor is a fixed erased
template supplied only with parameters and one proof marker per field. -/
noncomputable def erasedSingletonFamily (S : SingletonLayout) (params : List VExpr)
    (E : PropElim) (ps : List ProofShape) : ProofShape :=
  (proofErase (params ++ S.fields).reverse (branchFamily S params E)).instOuter
    (ps ++ List.replicate S.fields.length .proof)

/-- Any typed constructor-field instance gives the same family template. This
also applies to an original constructor match before its proof fields disappear. -/
theorem proofErase_singleton_family_instance (W : E.WF S params env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hps : ps.length = params.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ fields)) :
    proofErase Γ ((branchFamily S params E).instOuter (ps ++ fields)) =
      erasedSingletonFamily S params E (ps.map (proofErase Γ)) := by
  have hΔ := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hΔ
  unfold erasedSingletonFamily
  rw [proofErase_instOuter hΓ hΔ (branchFamily_prop henv W) hf,
    List.map_append, proofErase_singleton_fields W hps hs hf]

/-- Extraction computes the same erased family at every major with these
parameter erasures. No index alignment or index-propositionality is needed. -/
theorem proofErase_transportedFamily (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    proofErase Γ (transportedFamily S params E ps idx m) =
      erasedSingletonFamily S params E (ps.map (proofErase Γ)) := by
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  exact proofErase_singleton_family_instance W hΓ hps hs hf

/-- Equal erased family shapes validate the bare constructor at the major's
actual indices. This is a typed reconstruction theorem, not exact syntactic
pattern replay: it uses canonical extraction and proof irrelevance. -/
theorem singleton_reconstruction_of_erased_family (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m]))
    (H : erasedSingletonFamily S params E (ps.map (proofErase Γ)) =
      proofErase Γ (mkApps E.family (ps ++ idx))) :
    env.IsDefEq univs Γ m (transportedCtor S params E ps idx m)
      (mkApps E.family (ps ++ idx)) := by
  have ht := transportedFamily_typings henv heq W hΓ hps hargs
  have hP := W.family_prop henv hps hargs
  have hshape := (proofErase_transportedFamily heq W hΓ hps hs hargs).trans H
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ ht.1 hP hshape).2 (not_isProof_of_sort hΓ ht.1)
  have hconv := (HC.defeq hΓ).of_l henv hΓ ht.1
  exact .proofIrrel hP (W.major_typed hps hargs) (hconv.defeq ht.2)

/-- A finite common computation of the erased family template and requested
family also suffices. All nodes use the already checked erased iota fragment;
no ambient declarative family comparison is a premise. -/
theorem singleton_reconstruction_of_erased_join (heq : env.HasCanonicalEq)
    (hD : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m]))
    (Ra : ProofShape.Compute (ErasedIotaPrimitive D)
      (erasedSingletonFamily S params E (ps.map (proofErase Γ))) out)
    (Rb : ProofShape.Compute (ErasedIotaPrimitive D)
      (proofErase Γ (mkApps E.family (ps ++ idx))) out) :
    env.IsDefEq univs Γ m (transportedCtor S params E ps idx m)
      (mkApps E.family (ps ++ idx)) := by
  have ht := transportedFamily_typings henv heq W hΓ hps hargs
  have hP := W.family_prop henv hps hargs
  rw [← proofErase_transportedFamily heq W hΓ hps hs hargs] at Ra
  have hconv := proofErase_compute_join_reflect hD (erased_iota_replay hD) hΓ ht.1 hP Ra Rb
  exact .proofIrrel hP (W.major_typed hps hargs) (hconv.defeq ht.2)

/-- Family computations performed above inserted binders still validate a
constructor below. This permits arbitrary data fields: their transports remain
in the two compared families and must be covered by the supplied computations. -/
theorem singleton_reconstruction_of_lifted_erased_join (heq : env.HasCanonicalEq)
    (hD : D.Sound env univs)
    (W : E.WF S params env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hW : Ctx.LiftN n k Γ Γ') (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m]))
    (Ra : ProofShape.Compute (ErasedIotaPrimitive D)
      (proofErase Γ' ((transportedFamily S params E ps idx m).liftN n k)) out)
    (Rb : ProofShape.Compute (ErasedIotaPrimitive D)
      (proofErase Γ' ((mkApps E.family (ps ++ idx)).liftN n k)) out) :
    env.IsDefEq univs Γ m (transportedCtor S params E ps idx m)
      (mkApps E.family (ps ++ idx)) := by
  have ht := transportedFamily_typings henv heq W hΓ hps hargs
  have hP := W.family_prop henv hps hargs
  have hconv := proofErase_iota_join_descend hD hΓ hΓ' hW ht.1 hP Ra Rb
  exact .proofIrrel hP (W.major_typed hps hargs) (hconv.defeq ht.2)

end Lean4Lean.VEnv.Strengthening
