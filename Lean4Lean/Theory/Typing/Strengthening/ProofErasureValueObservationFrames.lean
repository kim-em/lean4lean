import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueDemandObservation

/-! # Beta and expansion frames for value-carrying observations -/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PiOriginObservation (FixedTail)
variable [Params] {D : PureObservation.Definitions}

/-- Control keys read a head or call a function; value keys instead permit
arbitrary computation at their opaque typed payload. -/
inductive Key.Control : Key → Prop where
  | head : Control (.head args)
  | app : Control (.app keys o)

omit [Params] in
/-- Control keys have a sort or Pi assignment, excluding structure majors. -/
theorem Demand.headed (H : Demand p o) (HK : o.Control) : p.Headed := by
  cases H with
  | value => cases HK
  | head => exact .sort
  | fn => exact .arrow

/-- Observations of control variables retain their ordinary node typings. -/
def Sets.Typed (S : Sets) (Δ : List ProofShape) : Prop :=
  ∀ i t o, S i t o → Typing Δ (.bvar i) t

/-- A fresh demanded control has a visible domain and therefore remains a variable. -/
theorem Sets.Typed.cons (H : S.Typed Δ)
    (HX : p.Visible → Typing (A :: Δ) (.bvar 0) p)
    (HK : ∀ key ∈ keys, Demand p key) (SD : DomainSort Δ A u) :
    (Sets.cons p keys S).Typed (A :: Δ) := by
  intro i t key hi
  cases i with
  | zero => obtain ⟨rfl, hk⟩ := hi; exact HX (HK key hk).visible
  | succ i =>
    have HT := H i t key hi
    have HW : ContextSubstitution Δ (A :: Δ) (fun i => .bvar (i+1)) := HT.weak_interpretation SD
    simpa only [ProofShape.subst] using HT.subst HW

/-- An opaque value observation may append any full-union computation. -/
theorem Obs.value_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e .data (.value a))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e out) :
    Obs D c n Δ S out .data (.value a) := by
  have HT := H.typing
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, _, Ef⟩ := HT
  have HC : ScopedValueChain D Δ e e := ⟨Γ, hΓ, EΓ, f, f, T, .refl hf, Ef, Ef⟩
  exact .value_step (H.typing.compute (erased_static_structure_eta_expansion_union_descent heq hs) R)
    H (HC.compute heq hs R)

/-- Identity interpretation changes only node witnesses, keeping the labels fixed. -/
theorem Obs.context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    Obs D c n Δ' S e t o := by
  simpa only [ProofShape.subst_id] using H.rename heq hs W
    (show FixedTail n n ProofShape.Subst.id from fun _ => rfl) (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta substitutes control observations and their value chains. -/
theorem Obs.beta_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S (.app (.lam A b) a) t o) (HS : S.Typed Δ) :
    Obs D c n Δ S (b.inst a) t o := by
  cases H with
  | value HT HC =>
    exact .value (HT.compute (erased_static_structure_eta_expansion_union_descent heq hs) (.beta .beta))
      (HC.compute heq hs (.beta .beta))
  | value_step HT HO HC =>
    exact .value_step (HT.compute (erased_static_structure_eta_expansion_union_descent heq hs) (.beta .beta))
      HO (HC.compute heq hs (.beta .beta))
  | app HT HF HX =>
    cases HF with
    | lam HL HK HB =>
      have R := HB.subst heq hs HT.beta_interpretation
        (show FixedTail (n+1) n (ProofShape.Subst.one a) from by
          intro i; simp [ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.id, Nat.add_right_comm])
        (T := S) (fun i t key hi HD => by
          cases i with
          | zero => obtain ⟨rfl, hk⟩ := hi; exact HX key hk
          | succ i => exact .var (HS i t key hi) HD hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using R

/-- A primitive-shaped control observation can only have the designated head. -/
theorem Obs.primitive_head (H : Obs D c n Δ S e t o) (HK : o.Control) (HH : PrimitiveHead e) :
    e.constHead = some c := by
  induction H with
  | const => rfl
  | var => exact HH.elim
  | value | value_step => cases HK
  | app _ _ _ ihf _ => exact ihf .app HH
  | lam => exact HH.elim

/-- Sort syntax cannot carry a control key. -/
theorem Obs.not_sort (H : Obs D c n Δ S (.sort u) t o) (HK : o.Control) : False := by
  cases H <;> cases HK

/-- Native eta preserves control demands; opaque values use their chain rule. -/
theorem Obs.native_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs D c n Δ S e t o) (HK : o.Control)
    (R : NativeEtaExpansion Step Δ e out) : Obs D c n Δ S out t o := by
  cases H.demand with
  | value => cases HK
  | head => exact (H.typing.no_eta_sort hstep R).elim
  | @fn keys A B o Hkeys HO =>
    obtain ⟨A', u, rfl, HT, HB, SD, HX⟩ := H.typing.eta_parts hstep R
    apply Obs.lam HT Hkeys
    apply Obs.app HB (H.lift heq hs SD)
    intro key hk
    obtain ⟨E, HV⟩ := HX (Hkeys key hk).visible
    rw [E]
    exact .var HV (Hkeys key hk) ⟨rfl, hk⟩

/-- Constant expansion ignores its arbitrary added argument. -/
theorem Obs.constant_expansion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) : Obs D c n Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame H.demand.visible
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro (H.typing.ne_proof H.demand.visible)))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift heq hs SD)) (by simp)

/-- Native identity expansion demands its original value or control payload. -/
theorem Obs.native_identity
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs D c n Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) :
    Obs D c n Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep H.demand.visible RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H.demand
      · exact .var (HF.lam_parts.2 H.demand.visible) H.demand ⟨rfl, by simp⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
