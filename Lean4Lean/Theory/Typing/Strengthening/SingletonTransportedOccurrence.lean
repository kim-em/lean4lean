import Lean4Lean.Theory.Typing.Strengthening.SingletonStepExtraction

/-! # Typed singleton field extraction at arbitrary indices

Each telescope witness is extracted from the major into Prop. The reconstructed
data fields retain the resulting type casts. Thus this program is typed without
an aligned constructor instance; comparison with an aligned generated prefix is
a separate theorem.
-/
namespace Lean4Lean
open VExpr VEnv SingletonLayout

namespace VEnv
/-- Substitution through a field instance whose declaration telescope is closed.
The surrounding context telescope is supplied by a typed argument instance. -/
theorem TelInst.instOuter_closed (henv : env.WF)
    (H : TelInst env U (Δ.reverse ++ Γ) doms args)
    (hcl : ∀ j (hj : j < doms.length), doms[j].ClosedN j)
    (ht : TelInst env U Γ Δ t) :
    TelInst env U Γ doms (args.map (·.instOuter t)) := by
  refine ⟨by simpa using H.1, ?_⟩
  intro j hj hd
  have hja : j < args.length := by simpa using hj
  have h := IsDefEq.instOuter_telescope henv (H.2 j hja hd) ht.1 ht.2
  rw [instOuter_instOuter _ _ _ (by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hja)] using hcl j hd)] at h
  simpa only [List.getElem_map, List.map_take] using h.hasType.1
end VEnv

namespace PropElim
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Generic step propositions specialize to the supplied providers at any major. -/
theorem stepBody_at_occurrence (hscope : S.Scoped params.length)
    (hps : ps.length = params.length) (hidx : idx.length = S.indices.length) :
    (S.stepBody (genericPa S params) (genericIa S) j).instOuter (ps ++ idx ++ [m]) =
      S.stepBody ps idx j := by
  have hlen : (ps ++ idx ++ [m]).length = params.length + S.indices.length + 1 := by
    simp [hps, hidx, Nat.add_assoc]
  have hpaτ : (genericPa S params).map (fun x => x.subst (Subst.ofList (ps ++ idx ++ [m]))) = ps := by
    have hh := instOuter_bvarRange params.length (params.length + S.indices.length + 1)
      (ps ++ idx ++ [m]) (by omega) (by rw [hlen]; omega)
    simp only [← instOuter_eq_subst]
    rw [genericPa, hh, hlen, Nat.sub_self, List.drop_zero, List.append_assoc, List.take_left' hps]
  have hiaτ : (genericIa S).map (fun x => x.subst (Subst.ofList (ps ++ idx ++ [m]))) = idx := by
    have hh := instOuter_bvarRange S.indices.length (S.indices.length + 1)
      (ps ++ idx ++ [m]) (by omega) (by rw [hlen]; omega)
    simp only [← instOuter_eq_subst]
    rw [genericIa, hh, hlen,
      show params.length + S.indices.length + 1 - (S.indices.length + 1) = ps.length by omega,
      List.append_assoc, List.drop_left, List.take_left' hidx]
  rw [instOuter_eq_subst,
    stepBody_subst (by simpa [genericPa] using hscope) (by simp [genericIa]), hpaτ, hiaτ]

/-- The telescope witnesses generated from an arbitrary major, including type
equalities proved by propositional elimination. -/
def transportedWitnesses (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List VExpr) (m : VExpr) : Nat → List VExpr
  | 0 => []
  | i + 1 =>
    let t := transportedWitnesses S params E ps idx m i
    t ++ [mkApps (stepValue S params E i) (ps ++ idx ++ [m] ++ t)]

/-- The field terms retain each data-slot transport instead of deleting it. -/
def transportedFields (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List VExpr) (m : VExpr) (i : Nat) : List VExpr :=
  S.substHat ps idx i (transportedWitnesses S params E ps idx m i)

/-- Every generated witness is typed along the actual cast telescope, without
assuming a typed constructor instance or index alignment. -/
theorem transportedWitnesses_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m])) :
    ∀ i, i ≤ S.fields.length → TelInst env U Γ (S.tel ps idx i).1
      (transportedWitnesses S params E ps idx m i) := by
  have hidx : idx.length = S.indices.length := by have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  intro i
  induction i with
  | zero => intro _; exact TelInst.nil
  | succ i ih =>
    intro hi
    have ht := ih (Nat.le_of_succ_le hi)
    have hv := (stepValue_typed henv heq W (show i < S.fields.length from hi)).weak0 henv.ordered (Γ := Γ)
    have hvargs := HasType.mkApps_of_tel hv hargs
    change env.HasType U Γ _ ((S.stepBody (genericPa S params) (genericIa S) i).instOuter _) at hvargs
    rw [stepBody_at_occurrence W.typed.scope hps hidx] at hvargs
    have hnext := HasType.mkApps_of_tel hvargs ht
    rw [← mkApps_append] at hnext
    exact ht.append_one hnext

/-- The extracted fields form a typed instance of the constructor's entire
field telescope (or any prefix), at arbitrary well-typed indices and major.
Casts remain in the fields; their result indices need not be definitionally the
original indices, so this alone does not type the reconstructed constructor at
the major's original family instance. -/
theorem transportedFields_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hi : i ≤ S.fields.length) :
    TelInst env U Γ (params ++ S.fields.take i)
      (ps ++ transportedFields S params E ps idx m i) := by
  have hidx : idx.length = S.indices.length := by have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hpa : TelInst env U Γ params ps := by
    have := hia.take (doms := params) (more := S.indices)
    simpa [hps] using this
  obtain ⟨_, hfields⟩ := tel_typed henv heq W.typed hΓ hpa hia hidx i hi
  have ht := transportedWitnesses_typed henv heq W hps hargs i hi
  have hcl : ∀ j (hj : j < (params ++ S.fields.take i).length),
      (params ++ S.fields.take i)[j].ClosedN j := by
    exact W.typed.prefix_closed fun l hl => by
      simp only [List.length_take] at hl
      simpa only [List.getElem_take] using W.typed.scope.fields l (by omega)
  have hf := hfields.instOuter_closed henv hcl ht
  have hlen : (transportedWitnesses S params E ps idx m i).length = i := ht.1.trans (S.tel_length ps idx i).1
  rw [List.map_append, tel_instOuter (W.typed.scope.mono_pa hps) hidx i _ hlen] at hf
  have hpaeq : (ps.map (fun x => x.liftN i)).map
      (fun x => x.instOuter (transportedWitnesses S params E ps idx m i)) = ps := by
    simp only [List.map_map]
    conv => rhs; rw [← List.map_id ps]
    apply List.map_congr_left
    intro x _
    exact liftN_instOuter_len hlen
  rw [hpaeq] at hf
  exact hf

/-- Transported extraction always constructs a proof at its own constructor
indices. It does not assert that those indices convert to the original ones. -/
theorem transportedConstructor_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m])) :
    let fields := transportedFields S params E ps idx m S.fields.length
    env.HasType U Γ (mkApps E.ctor (ps ++ fields))
      (mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ fields)))) := by
  intro fields
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hfl : fields.length = S.fields.length := by
    have := hf.1
    simp only [List.length_append] at this
    change (transportedFields S params E ps idx m S.fields.length).length = S.fields.length
    omega
  have hΔ : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  have hc := HasType.closed_instOuter henv hΔ W.ctor_typed hf
  have hctor : (ctorApp S params E).instOuter (ps ++ fields) = mkApps E.ctor (ps ++ fields) := by
    unfold ctorApp
    rw [bvarRange_split]
    exact mkApps_instOuter_heads W.ctor_closed ps fields params.length S.fields.length hps hfl
  have hlen : (ps ++ fields).length = params.length + S.fields.length := by simp [hps, hfl]
  have hfamily : (mkApps E.family (branchPa S params ++ E.ctorIndices)).instOuter (ps ++ fields) =
      mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ fields))) := by
    simp only [instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append, branchPa]
    rw [instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; exact Nat.le_refl _), hlen,
      Nat.sub_self, List.drop_zero, List.take_left' hps]
  rw [hctor, hfamily] at hc
  exact hc

end PropElim
end Lean4Lean
