import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueDemandApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStablePrimitives

/-! # Typed operational interpretation of value observations

Function demands quantify over actually typed applications. This permits
opaque value histories and proof slots without treating a raw proof marker as
a polymorphic object-language term or applying merely profile-compatible terms.
-/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PiOriginObservation (FixedTail)
variable [Params] {D : PureObservation.Definitions}

/-- Value keys retain chains; head keys beta-read a rigid spine with pointwise
chains; function keys are tested only at actually typed applications. -/
def Realizes (D : PureObservation.Definitions) (c : Name) (Δ : List ProofShape)
    (n : Nat) (e : ProofShape) : Key → Prop
  | .value a => ScopedValueChain D Δ (a.liftN n) e
  | .head args => ∃ ls outputs, BetaRed e (ProofShape.mkApps (.const c ls) outputs) ∧
      List.Forall₂ (ScopedValueChain D Δ) (args.map (·.liftN n)) outputs
  | .app keys o => ∀ a, TypedSource Δ (.app e a) →
      (∀ key ∈ keys, Realizes D c Δ n a key) → Realizes D c Δ n (.app e a) o
termination_by o => sizeOf o

/-- A typed beta predecessor has the same operational meaning. At value keys
this appends a reversed chain instead of asserting a forward argument path. -/
theorem Realizes.beta_back
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ e) (R : BetaRed e e') (H : Realizes D c Δ n e' o) :
    Realizes D c Δ n e o := by
  cases o with
  | value a =>
    simp only [Realizes] at H ⊢
    exact H.trans heq hs ((ScopedValueChain.refl HT).compute heq hs (.beta R)).symm
  | head args =>
    simp only [Realizes] at H ⊢
    obtain ⟨ls, outputs, RB, HC⟩ := H
    exact ⟨ls, outputs, R.trans RB, HC⟩
  | app keys o =>
    simp only [Realizes] at H ⊢
    intro a HTa HA
    have R' := ProofShape.BetaRed.app R (.refl (e := a))
    have HT' := ((ScopedValueChain.refl (D := D) HTa).compute heq hs (.beta R')).symm.source
    exact Realizes.beta_back heq hs HTa R' (H a HT' HA)
termination_by sizeOf o

/-- A literal rigid constant consumes typed proof/data slots. The accumulated
arguments already carry histories, and each new data demand adds another one. -/
theorem constant_realizes
    (HT : Typing Δ (ProofShape.mkApps (.const c ls) actual) (argumentProfile slots .sort))
    (HA : List.Forall₂ (ScopedValueChain D Δ) (done.map (·.liftN n)) actual)
    (HP : ∀ s ∈ slots, s.1 = true → s.2 = .proof) :
    Realizes D c Δ n (ProofShape.mkApps (.const c ls) actual)
      (argumentKey slots (.head (done ++ slots.map Prod.snd))) := by
  induction slots generalizing actual done with
  | nil =>
    simp only [argumentKey, Realizes]
    exact ⟨ls, actual, .refl, by simpa using HA⟩
  | cons s slots ih =>
    simp only [argumentKey, Realizes]
    intro a HApp HX
    obtain ⟨HArg, HNext⟩ := HT.app_parts HApp
    have HC : ScopedValueChain D Δ (s.2.liftN n) a := by
      cases hb : s.1 with
      | false => simpa only [Realizes] using HX (.value s.2) (by simp [slotKeys, hb])
      | true =>
        have HE : a = .proof := (show Typing Δ a .proof from by simpa [argumentProfile, slotProfile, hb] using HArg).proof_eq
        have HS := HP s (List.mem_cons_self ..) hb
        rw [HS, ProofShape.liftN, ← HE]
        exact ScopedValueChain.refl HArg.source
    have HNext' : Typing Δ (ProofShape.mkApps (.const c ls) (actual ++ [a])) (argumentProfile slots .sort) := by
      simpa only [ProofShape.mkApps_snoc] using HNext
    have HC' : List.Forall₂ (ScopedValueChain D Δ) ((done ++ [s.2]).map (·.liftN n)) (actual ++ [a]) := by
      simpa only [List.map_append, List.map_cons, List.map_nil] using HA.append (.cons HC .nil)
    have HR := ih HNext' HC' (fun s hs => HP s (List.mem_cons_of_mem _ hs))
    simpa only [ProofShape.mkApps_snoc, List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using HR

/-- Typed context interpretations compose with a beta argument to replace the
fresh variable, fixing the original outer labels. -/
private theorem cons_interpretation (W : ContextSubstitution Δ Δ' σ)
    (HB : ContextSubstitution (A.subst σ :: Δ') Δ' (ProofShape.Subst.one a)) :
    ContextSubstitution (A :: Δ) Δ' (σ.cons a) := by
  have H : ContextSubstitution (A :: Δ) Δ' (fun i => (σ.lift i).subst (ProofShape.Subst.one a)) :=
    ContextSubstitution.comp W.cons HB
  have E : (fun i => (σ.lift i).subst (ProofShape.Subst.one a)) = σ.cons a := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [ProofShape.Subst.lift, ProofShape.Subst.one, ProofShape.Subst.cons,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
  intro Γ hΓ EΓ
  have HR := H hΓ EΓ
  simpa only [E] using HR

/-- Every finite observation has its operational interpretation under typed
substitution supplying the demanded controls. Histories stay in the actual
target context, so no strengthening of chains is used in the lambda case. -/
theorem Obs.realizes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → Realizes D c Δ' m (σ i) key) :
    Realizes D c Δ' m (e.subst σ) o := by
  induction H generalizing Δ' m σ with
  | const H HP =>
    simpa only [ProofShape.subst, ProofShape.mkApps, spineKey, List.nil_append] using
      (constant_realizes (actual := []) (done := []) (H.subst W) .nil HP)
  | var _ _ h => exact hσ _ _ _ h
  | value _ HC =>
    have HC' := HC.subst heq hs W
    rw [HT.payload] at HC'
    simpa only [Realizes] using HC'
  | value_step _ _ HC ih =>
    have HV := ih W HT hσ
    simp only [Realizes] at HV ⊢
    exact HV.trans heq hs (HC.subst heq hs W)
  | app H _ _ ihf iha =>
    have HF := ihf W HT hσ
    simp only [Realizes] at HF
    exact HF _ (H.subst W).source (fun key hk => iha key hk W HT hσ)
  | @lam Δ A b p q keys n S o H HK _ ih =>
    simp only [Realizes, ProofShape.subst]
    intro a HApp HA
    have HB : ContextSubstitution (A.subst σ :: Δ') Δ' (ProofShape.Subst.one a) :=
      (typing_ignored HApp).beta_interpretation
    have HR := ih (cons_interpretation W HB) HT.cons (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact HA key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back heq hs HApp (E ▸ (BetaRed.beta (A := A.subst σ))) HR

/-- A closed head observation exposes a literal rigid spine and a scoped
value history for every argument. No normalization of the arguments is assumed. -/
theorem Obs.head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c 0 Δ (fun _ _ _ => False) e .sort (.head args)) :
    ∃ ls outputs, BetaRed e (ProofShape.mkApps (.const c ls) outputs) ∧
      List.Forall₂ (ScopedValueChain D Δ) args outputs := by
  have W : ContextSubstitution Δ Δ ProofShape.Subst.id := by
    intro Γ hΓ EΓ
    exact ⟨Γ, VExpr.Subst.id, hΓ, EΓ, Ctx.SubstEq.id henv.ordered hΓ,
      fun hl hn => by simp only [VExpr.Subst.id, ProofShape.Subst.id, proofErase, if_neg hn]⟩
  have HR := H.realizes heq hs W (show FixedTail 0 0 ProofShape.Subst.id from fun _ => rfl)
    (fun _ _ _ h => h.elim)
  simpa only [Realizes, ProofShape.subst_id, ProofShape.liftN_zero, List.map_id'] using HR

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
