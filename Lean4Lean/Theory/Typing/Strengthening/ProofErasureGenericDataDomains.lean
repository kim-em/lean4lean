import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationLiteralFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSubstitution

/-! # Generic data-domain chains specialize to every constructor occurrence

Only one domain comparison per data slot is needed in the declaration's generic
field context. Typed substitution specializes these comparisons to arbitrary
actual fields. The generic comparisons themselves remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim SingletonLayout
variable [Params] {D : PureObservation.Definitions} {params : List VExpr} {S : SingletonLayout} {E : PropElim}

/-- Missing domain computations, stated once per data field in the declaration
context. This is a finite collection for a fixed layout and universe instance;
no completeness from ordinary type uniqueness is assumed. -/
def SingletonGenericDataDomainChains (D : PureObservation.Definitions)
    (S : SingletonLayout) (params : List VExpr) (E : PropElim) : Prop :=
  ∀ l k, l < S.fields.length → S.slot.getD l none = some k →
    TypedComputationEq D (params ++ S.fields).reverse
      ((S.indices.getD k default).instOuter (branchPa S params ++ E.ctorIndices.take k))
      ((S.fields.getD l default).instOuter (branchPa S params ++ bvarRange l S.fields.length))
      (.sort (S.sorts.getD l .zero))

/-- The generic domain equations are already ordinary definitional equalities:
the index and field declarations type the same literal field variable. This
records the exact distinction between the known equations and the open chains. -/
theorem singleton_generic_data_domains_defeq
    (W : E.WF S params env univs) (hl : l < S.fields.length)
    (hslot : S.slot.getD l none = some k) :
    env.IsDefEq univs (params ++ S.fields).reverse
      ((S.indices.getD k default).instOuter (branchPa S params ++ E.ctorIndices.take k))
      ((S.fields.getD l default).instOuter (branchPa S params ++ bvarRange l S.fields.length))
      (.sort (S.sorts.getD l .zero)) := by
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hcl := W.typed.prefix_closed (fun i hi => W.typed.scope.fields i hi)
  have hid := TelInst.ident (env := env) (U := univs) [] hcl
  simp only [List.append_nil, List.length_append] at hid
  have hsplit : bvarRange (params.length + S.fields.length) (params.length + S.fields.length) =
      branchPa S params ++ bvarRange S.fields.length S.fields.length := by
    rw [bvarRange_append _ _ _ (Nat.le_refl _)]
    simp only [branchPa, Nat.add_sub_cancel_left]
  rw [hsplit] at hid
  have hf := hid.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by simp [branchPa]), getD_append_right' (by omega)] at hf
  simp only [branchPa, bvarRange_length, Nat.add_sub_cancel_left, List.take_append] at hf
  rw [List.take_of_length_le (by simp only [bvarRange_length]; omega),
    getD_of_lt (by simpa only [bvarRange_length] using hl), bvarRange_getElem _ _ _ hl,
    bvarRange_take _ _ _ (Nat.le_of_lt hl)] at hf
  have hk := W.typed.scope.slot_lt l k hslot
  have hx := W.ctorIndices_typed.getD (j := params.length + k) (by simp; omega)
  rw [getD_append_right' (by simp [branchPa]), getD_append_right' (by omega)] at hx
  simp only [branchPa, bvarRange_length, Nat.add_sub_cancel_left, List.take_append] at hx
  rw [List.take_of_length_le (by simp only [bvarRange_length]; omega), W.slot_literal l k hslot] at hx
  have hp : TelInst env univs (params ++ S.fields).reverse (params ++ S.fields.take l)
      (branchPa S params ++ bvarRange l S.fields.length) := by
    have hsplit : params ++ S.fields = (params ++ S.fields.take l) ++ S.fields.drop l := by
      rw [List.append_assoc, List.take_append_drop]
    rw [hsplit] at hid
    have hp := hid.take
    rw [← hsplit] at hp
    simpa only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hl),
      List.take_append, branchPa, bvarRange_length, Nat.add_sub_cancel_left,
      List.take_of_length_le (show (bvarRange params.length (params.length + S.fields.length)).length ≤ params.length + l by simp),
      bvarRange_take _ _ _ (Nat.le_of_lt hl)] using hp
  have hY := HasType.closed_instOuter henv (W.typed.fieldsCtx l (Nat.le_of_lt hl))
    (W.typed.fieldSort l hl) hp
  simp only [instOuter_sort, fieldSort, hslot] at hY
  rw [← getD_of_lt hl] at hY
  exact (hx.uniqU henv hctx hf).of_r henv hctx hY

/-- Typed simultaneous instantiation specializes every generic domain chain.
Only ordinary telescope typing of the actual fields is required: no native
certificates, data-value chains or type-fork joining enter this specialization. -/
theorem SingletonGenericDataDomainChains.specialize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (HD : SingletonGenericDataDomainChains D S params E) :
    SingletonLiteralDataDomainChains D S E Γ ps f := by
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hfl : f.length = S.fields.length := by
    have := hf.1; simp only [List.length_append, hps] at this; omega
  have hlen : (ps ++ f).length = params.length + S.fields.length := by simpa using hf.1
  intro l k hl hslot
  have hk := W.typed.scope.slot_lt l k hslot
  have H := (HD l k hl hslot).subst heq hs hΓ (erasedTemplate_substEq hctx hf)
  simp only [← instOuter_eq_subst, instOuter_sort] at H
  have hX : (S.indices.getD k default).ClosedN (branchPa S params ++ E.ctorIndices.take k).length := by
    simpa only [List.length_append, branchPa, bvarRange_length, List.length_take,
      W.ctorIndices_length, Nat.min_eq_left (Nat.le_of_lt hk)] using W.typed.scope.indices_getD k
  have hY : (S.fields.getD l default).ClosedN (branchPa S params ++ bvarRange l S.fields.length).length := by
    simpa only [List.length_append, branchPa, bvarRange_length] using W.typed.scope.fields_getD l
  rw [instOuter_instOuter _ _ _ hX, instOuter_instOuter _ _ _ hY,
    List.map_append, List.map_append, instOuter_branch hlen hps, List.map_take] at H
  have hfields : (bvarRange l S.fields.length).map (·.instOuter (ps ++ f)) = f.take l := by
    rw [instOuter_bvarRange _ _ _ (Nat.le_of_lt hl) (by rw [hlen]; omega), hlen,
      show params.length + S.fields.length - S.fields.length = ps.length by omega,
      List.drop_left]
  rwa [hfields] at H

/-- A finite set of generic data-domain chains suffices for the family chain
at every typed literal occurrence and every proof major at that occurrence. -/
theorem SingletonGenericDataDomainChains.family_chain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]))
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (HD : SingletonGenericDataDomainChains D S params E) :
    TypedComputationEq D Γ
      (transportedFamily S params E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m)
      (mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)))) (.sort .zero) :=
  transportedFamily_chain_at_literal heq hs W hΓ hps hargs hf (HD.specialize heq hs W hΓ hps hf)

end Lean4Lean.VEnv.Strengthening
