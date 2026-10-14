import Lean4Lean.Theory.Typing.Strengthening.SingletonOccurrenceContexts

/-! # Transporting a reconstructed singleton proof to its original family

The reconstructed constructor has its own indices. Propositional elimination
produces an equality of its family proposition with the original proposition.
Casting the constructor along that equality supplies a proof at the original
indices, without assuming their definitional alignment.
-/
namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- The proposition at the constructor's literal field variables. -/
def branchFamily (S : SingletonLayout) (params : List VExpr) (E : PropElim) : VExpr :=
  mkApps E.family (branchPa S params ++ E.ctorIndices)

/-- The proposition at the reconstructed constructor's own indices. -/
def transportedFamily (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List VExpr) (m : VExpr) : VExpr :=
  (branchFamily S params E).instOuter
    (ps ++ transportedFields S params E ps idx m S.fields.length)

/-- Reconstructed constructor proof, before transport to the requested indices. -/
def transportedCtor (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List VExpr) (m : VExpr) : VExpr :=
  (ctorApp S params E).instOuter
    (ps ++ transportedFields S params E ps idx m S.fields.length)

/-- The constructor's family proposition is typed in the closed field context. -/
theorem branchFamily_prop (henv : env.WF) (W : E.WF S params env U) :
    env.HasType U (params ++ S.fields).reverse (branchFamily S params E) (.sort .zero) :=
  W.family_prop henv (by simp [branchPa]) W.branchArgs

/-- The transported family and its reconstructed constructor are typed at any
well-typed major occurrence, regardless of index alignment. -/
theorem transportedFamily_typings (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.HasType U Γ (transportedFamily S params E ps idx m) (.sort .zero) ∧
    env.HasType U Γ (transportedCtor S params E ps idx m)
      (transportedFamily S params E ps idx m) := by
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  exact ⟨by simpa only [transportedFamily, instOuter_sort] using
    HasType.closed_instOuter henv hctx (branchFamily_prop henv W) hf,
    HasType.closed_instOuter henv hctx W.ctor_typed hf⟩

/-- The generic reconstructed family specializes to the actual occurrence. -/
theorem transportedFamily_at (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hidx : idx.length = S.indices.length) :
    (transportedFamily S params E (genericPa S params) (genericIa S) (.bvar 0)).instOuter
      (ps ++ idx ++ [m]) = transportedFamily S params E ps idx m := by
  have ht := transportedFields_typed henv heq W W.genericCtx (by simp [genericPa])
    (W.genericArgs henv) (Nat.le_refl S.fields.length)
  rw [List.take_length] at ht
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hclosed := ((branchFamily_prop henv W).closedN' henv.ordered.closed
    (CtxWF.closed henv.ordered hctx)).1
  unfold transportedFamily
  rw [instOuter_eq_subst, instOuter_subst_closed _ _ (by
    simpa only [List.length_reverse, ← ht.1] using hclosed), List.map_append]
  simp only [← instOuter_eq_subst, (generic_at hps hidx).1,
    transportedFields_at henv heq W hps hidx (Nat.le_refl S.fields.length)]

/-- At a literal constructor occurrence, reconstructed fields recover its
family definitionally. The arbitrary-occurrence theorem below will only give
a propositional equality, extracted using this branch. -/
theorem transportedFamily_at_constructor_eq (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) :
    env.IsDefEq U (params ++ S.fields).reverse
      (transportedFamily S params E (branchPa S params) E.ctorIndices (ctorApp S params E))
      (branchFamily S params E) (.sort .zero) := by
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hid := TelInst.ident (env := env) (U := U) []
    (W.typed.prefix_closed (fun l hl => W.typed.scope.fields l hl))
  simp only [List.append_nil, List.length_append] at hid
  rw [bvarRange_split] at hid
  have hf : TelInst env U (params ++ S.fields).reverse (params ++ S.fields)
      (branchPa S params ++ bvarRange S.fields.length S.fields.length) := hid
  have ha := W.branchArgs
  have hw := transportedWitnesses_typed henv heq W (by simp [branchPa]) ha
    S.fields.length (Nat.le_refl _)
  have hwlen := hw.1.trans (S.tel_length _ _ _).1
  have hfields : ∀ l, l < S.fields.length →
      env.IsDefEqU U (params ++ S.fields).reverse
        ((transportedFields S params E (branchPa S params) E.ctorIndices
          (ctorApp S params E) S.fields.length).getD l default)
        ((bvarRange S.fields.length S.fields.length).getD l default) := by
    intro l hl
    have h := IsDefEq.instOuter_telescope henv
      (tel_branch henv heq W.typed W.ctorIndices_typed W.ctorIndices_length
        W.slot_literal S.fields.length (Nat.le_refl _) l hl) hw.1 hw.2
    rw [liftN_instOuter_len hwlen] at h
    have hmap := tel_instOuter (W.typed.scope.mono_pa (pa := branchPa S params) (by simp [branchPa]))
      W.ctorIndices_length S.fields.length _ hwlen
    have hget := congrArg (fun xs : List VExpr => xs.getD l default) hmap
    rw [getD_of_lt (by simpa [(S.tel_length _ _ _).2] using hl), List.getElem_map,
      ← getD_of_lt (d := (default : VExpr)) (by simpa [(S.tel_length _ _ _).2] using hl)] at hget
    simp only [branchPa] at hget h
    rw [hget] at h
    exact ⟨_, h⟩
  have ht := transportedFields_typed henv heq W hctx (by simp [branchPa]) ha
    (Nat.le_refl S.fields.length)
  rw [List.take_length] at ht
  have hcf := IsDefEq.closed_instOuter_congr' henv hctx hctx (branchFamily_prop henv W)
    ht.1 hf.1 (fun j hj => by
      by_cases hjP : j < params.length
      · rw [getD_append_left' (by simpa [branchPa] using hjP),
          getD_append_left' (by simpa [branchPa] using hjP)]
        have := ht.getD hj
        rwa [getD_append_left' (by simpa [branchPa] using hjP)] at this
      · have hl : j - params.length < S.fields.length := by simp at hj; omega
        have hc := hfields _ hl
        have hjt := ht.getD hj
        rw [getD_append_right' (by simp [branchPa]; omega)] at hjt
        simp only [branchPa, bvarRange_length] at hjt
        have hc' := hc.of_l henv hctx hjt
        rw [getD_append_right' (by simp only [branchPa, bvarRange_length]; omega),
          getD_append_right' (by simp only [branchPa, bvarRange_length]; omega)]
        simpa only [branchPa, bvarRange_length] using hc')
  have hclosed := ((branchFamily_prop henv W).closedN' henv.ordered.closed
    (CtxWF.closed henv.ordered hctx)).1
  simp only [branchPa] at hcf
  rw [← bvarRange_split, instOuter_range_bvar' _ _ _ (by simpa [Nat.add_comm] using hclosed) (Nat.le_refl _),
    Nat.sub_self, liftN_zero, instOuter_sort] at hcf
  exact hcf

/-- Proposition asserting equality of the reconstructed and requested families. -/
def familyWitnessBody (S : SingletonLayout) (params : List VExpr) (E : PropElim) : VExpr :=
  eqApp (.succ .zero) (.sort .zero)
    (transportedFamily S params E (genericPa S params) (genericIa S) (.bvar 0))
    (mkApps E.family (genericPa S params ++ genericIa S))

/-- Reflexivity is a valid branch because reconstruction computes at constructors. -/
def familyWitnessBranch (S : SingletonLayout) (params : List VExpr) (E : PropElim) : VExpr :=
  eqReflApp (.succ .zero) (.sort .zero)
    (transportedFamily S params E (branchPa S params) E.ctorIndices (ctorApp S params E))

/-- Closed extraction of the family equality, by elimination into Prop. -/
def familyWitness (S : SingletonLayout) (params : List VExpr) (E : PropElim) : VExpr :=
  valueOf S params E (familyWitnessBody S params E) (familyWitnessBranch S params E)

/-- The generic family equality specializes to the occurrence's two propositions. -/
theorem familyWitnessBody_at (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hidx : idx.length = S.indices.length) :
    (familyWitnessBody S params E).instOuter (ps ++ idx ++ [m]) =
      eqApp (.succ .zero) (.sort .zero) (transportedFamily S params E ps idx m)
        (mkApps E.family (ps ++ idx)) := by
  simp only [familyWitnessBody, eqApp_instOuter, instOuter_sort,
    transportedFamily_at henv heq W hps hidx, instOuter_mkApps,
    instOuter_closed0 W.family_closed, List.map_append,
    (generic_at hps hidx).1, (generic_at hps hidx).2]

/-- The equality extractor is typed at arbitrary indices; its branch uses only
the checked definitional reconstruction at literal constructor indices. -/
theorem familyWitness_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) :
    env.HasType U [] (familyWitness S params E) (typeOf S params E (familyWitnessBody S params E)) := by
  apply valueOf_typed henv W
  · have htypes := transportedFamily_typings henv heq W W.genericCtx (by simp [genericPa])
      (W.genericArgs henv)
    exact HasType.eqApp heq trivial (HasType.sort trivial) htypes.1
      (W.family_prop henv (by simp [genericPa]) (W.genericArgs henv))
  · rw [familyWitnessBody_at henv heq W (by simp [branchPa]) W.ctorIndices_length]
    have h := transportedFamily_at_constructor_eq henv heq W
    have hs : env.HasType U (params ++ S.fields).reverse (.sort .zero) (.sort (.succ .zero)) :=
      .sort trivial
    exact (IsDefEq.eqApp_r heq (show (VLevel.succ .zero).WF U from trivial) hs h.hasType.1 h).defeq
      (HasType.eqReflApp heq trivial hs h.hasType.1)

/-- Specializing the closed extractor provides the family equality proof. -/
theorem familyWitness_at_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.HasType U Γ (mkApps (familyWitness S params E) (ps ++ idx ++ [m]))
      (eqApp (.succ .zero) (.sort .zero) (transportedFamily S params E ps idx m)
        (mkApps E.family (ps ++ idx))) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have h := HasType.mkApps_of_tel ((familyWitness_typed henv heq W).weak0
    henv.ordered (Γ := Γ)) hargs
  change env.HasType U Γ _ ((familyWitnessBody S params E).instOuter _) at h
  rwa [familyWitnessBody_at henv heq W hps hidx] at h

/-- Constructor reconstruction at arbitrary indices, retaining the family cast. -/
def castedConstructor (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List VExpr) (m : VExpr) : VExpr :=
  typeCast .zero (transportedFamily S params E ps idx m) (mkApps E.family (ps ++ idx))
    (mkApps (familyWitness S params E) (ps ++ idx ++ [m]))
    (transportedCtor S params E ps idx m)

/-- The casted constructor is always a proof of the original family instance. -/
theorem castedConstructor_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.HasType U Γ (castedConstructor S params E ps idx m) (mkApps E.family (ps ++ idx)) := by
  have ht := transportedFamily_typings henv heq W hΓ hps hargs
  exact HasType.typeCast henv.ordered heq trivial ht.1 (W.family_prop henv hps hargs)
    (familyWitness_at_typed henv heq W hps hargs) ht.2

/-- Every major is definitionally its transported reconstructed constructor.
The outer cast remains, so this does not expose a bare constructor to iota. -/
theorem transported_singleton_eta (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.IsDefEq U Γ m (castedConstructor S params E ps idx m) (mkApps E.family (ps ++ idx)) :=
  .proofIrrel (W.family_prop henv hps hargs) (W.major_typed hps hargs)
    (castedConstructor_typed henv heq W hΓ hps hargs)

/-- Exposing the bare reconstructed constructor is exactly conversion of its
family to the requested family. Propositional family equality alone does not
discharge this remaining definitional obligation. -/
theorem bare_constructor_iff_family_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.IsDefEqU U Γ m (transportedCtor S params E ps idx m) ↔
      env.IsDefEq U Γ (transportedFamily S params E ps idx m)
        (mkApps E.family (ps ++ idx)) (.sort .zero) := by
  have ht := transportedFamily_typings henv heq W hΓ hps hargs
  have hm := W.major_typed hps hargs
  constructor
  · intro h
    have hc := (h.of_l henv hΓ hm).hasType.2
    exact (ht.2.uniqU henv hΓ hc).of_l henv hΓ ht.1
  · intro h
    exact ⟨_, IsDefEq.proofIrrel (W.family_prop henv hps hargs) hm (h.defeq ht.2)⟩

end Lean4Lean.PropElim
