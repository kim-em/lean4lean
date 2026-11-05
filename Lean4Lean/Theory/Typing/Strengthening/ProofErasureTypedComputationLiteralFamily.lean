import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDataFields
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonReconstruction

/-! # Literal singleton family comparison from data-domain chains

At literal constructor indices, value alignment is reflexive. Only the
comparison between the declared index domain and original field domain is left
as a computational premise. Dependent reconstruction and family comparison then
follow without assuming computation-chain completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim SingletonLayout
variable [Params] {D : PureObservation.Definitions} {params : List VExpr}

/-- Missing computational domain agreement at a literal constructor occurrence.
Ordinary type uniqueness supplies the corresponding definitional equations, but
has not been shown to supply these chains. This local condition is not claimed
to be a sufficient or strictly smaller replacement for strengthening. -/
def SingletonLiteralDataDomainChains (D : PureObservation.Definitions)
    (S : SingletonLayout) (E : PropElim) (Γ ps f : List VExpr) : Prop :=
  ∀ l k, l < S.fields.length → S.slot.getD l none = some k →
    TypedComputationEq D Γ
      ((S.indices.getD k default).instOuter
        (ps ++ (E.ctorIndices.map (·.instOuter (ps ++ f))).take k))
      ((S.fields.getD l default).instOuter (ps ++ f.take l))
      (.sort (S.sorts.getD l .zero))

/-- At literal constructor indices, all reconstructed fields have chains to
the original fields once the named data-domain comparison is supplied. The
major may be any proof of that family, and its extracted witnesses may be opaque. -/
theorem transportedFields_chain_at_literal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]))
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (HD : SingletonLiteralDataDomainChains D S E Γ ps f) :
    List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A)
      (transportedFields S params E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m
        S.fields.length) f := by
  have hfl : f.length = S.fields.length := by
    have := hf.1; simp only [List.length_append, hps] at this; omega
  have HL : ∀ l k, l < S.fields.length → S.slot.getD l none = some k →
      TypedComputationEq D Γ
        ((E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default) (f.getD l default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)) := by
    intro l k hl hslot
    rw [W.literal_index (by simpa using hf.1) hps hslot hl]
    have h := hf.getD (j := params.length + l) (by simp; omega)
    rw [getD_append_right' (by omega), getD_append_right' (by omega), hps,
      Nat.add_sub_cancel_left, List.take_append, List.take_of_length_le (by omega),
      hps, Nat.add_sub_cancel_left] at h
    exact .refl h
  simpa only [← hfl, List.take_length] using
    transportedFields_chain_of_data_alignment heq hs W hΓ hps hargs hf HL HD
      S.fields.length (Nat.le_refl _)

/-- The original constructor family and reconstructed family are connected by
an actual typed computation chain under the data-domain premise. No type-fork
joining is needed for this chain; a raw common reduct remains separate. -/
theorem transportedFamily_chain_at_literal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]))
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (HD : SingletonLiteralDataDomainChains D S E Γ ps f) :
    TypedComputationEq D Γ
      (transportedFamily S params E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m)
      (mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)))) (.sort .zero) := by
  have HX := transportedFields_chain_at_literal heq hs W hΓ hps hargs hf HD
  have hpa : TelInst env univs Γ params ps := by
    have := hf.take (doms := params) (more := S.fields)
    simpa [hps] using this
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hrec := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hrec
  have H := TypedComputationEq.closed_instOuter_congr hΓ hctx (branchFamily_prop henv W)
    hrec ((TypedComputationEq.telInst_refl hpa).append HX)
  have hl : (ps ++ f).length = params.length + S.fields.length := by simpa using hf.1
  have hfamily : (branchFamily S params E).instOuter (ps ++ f) =
      mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) := by
    simp only [branchFamily, instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append]
    rw [PropElim.instOuter_branch hl hps]
  simpa only [transportedFamily, hfamily, instOuter_sort] using H

/-- Type-fork joining turns the literal family chain into the common erased
reduct required by a singleton family guard. Both the data-domain chain premise
and type-fork joining remain explicit. -/
theorem transportedFamily_join_at_literal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]))
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (HD : SingletonLiteralDataDomainChains D S E Γ ps f) :
    ∃ shared, ProofShape.ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (transportedFamily S params E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m)) shared ∧
      ProofShape.ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))))) shared :=
  (transportedFamily_chain_at_literal heq hs W hΓ hps hargs hf HD).type_join heq hs HF hΓ

end Lean4Lean.VEnv.Strengthening
