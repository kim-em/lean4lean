import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTrackedHeadHole

/-! # Typed canonical Eq heads cannot contract by ordinary core rules

Canonical typing forces the sixth argument to erase to a proof marker.
Registered iota patterns inspect precisely that argument and require a visible
constructor. This excludes core roots without any argument ancestry premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private computed_prefix_length
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaComputed
variable [Params]

/-- The major of any actually typed six-argument canonical Eq recursor is a
literal erased proof, regardless of the other arguments or their history. -/
theorem typed_eq_major_proof (heq : env.HasCanonicalEq)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) [α,a,M,m,b,p])) :
    p = .proof := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  have hlen : actual.length = 6 := by
    have HL := congrArg List.length Eargs
    simpa only [List.length_map, List.length_cons, List.length_nil] using HL.symm
  obtain ⟨α₀, a₀, M₀, m₀, b₀, p₀, rfl⟩ :
      ∃ α₀ a₀ M₀ m₀ b₀ p₀, actual = [α₀,a₀,M₀,m₀,b₀,p₀] := by
    cases actual with | nil => simp at hlen | cons x xs =>
    cases xs with | nil => simp at hlen | cons y ys =>
    cases ys with | nil => simp at hlen | cons z zs =>
    cases zs with | nil => simp at hlen | cons q qs =>
    cases qs with | nil => simp at hlen | cons r rs =>
    cases rs with | nil => simp at hlen | cons s ss =>
    cases ss with
    | nil => exact ⟨_, _, _, _, _, _, rfl⟩
    | cons t ts => simp at hlen
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ (show VExpr.WF env univs Γ _ from ⟨_, ht⟩)
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hls : ls.length = 2 := hl
  obtain ⟨v, w, rfl⟩ : ∃ v w, ls = [v,w] := by
    cases ls with | nil => simp at hls | cons v ls =>
    cases ls with | nil => simp at hls | cons w ls =>
    cases ls with
    | nil => exact ⟨_, _, rfl⟩
    | cons l ls => simp at hls
  obtain ⟨_, hw, hα, ha, _, _, hb, hp⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have EP := proofErase_eq_proof.2 ⟨_, hp, HasType.eqApp heq hw hα ha hb⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Eargs
  exact Eargs.2.2.2.2.2.trans EP

private theorem typed_eq_pattern_no_match
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (HT : TypedSource Δ e) (hh : e.constHead = some ``Eq.rec)
    (hp : Pat pat rhs) (hm : Matches pat e levels captures) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  have hn := hm.constHead.symm.trans hh
  cases sp with
  | defn c =>
    have hc : c = ``Eq.rec := Option.some.inj hn
    subst c
    rw [(pat_const_not_unfolding hp).1] at hreg
    cases hreg
  | iota c major ctor fields =>
    have hc : c = ``Eq.rec := by
      rw [Pattern.constHead_eq, SimplePattern.iota_headConst] at hn
      exact Option.some.inj hn
    subst c
    have hmj := ConstructorObservation.recursor_major_offset hreg hp
    rw [hoff] at hmj
    subst major
    cases hm with
    | app hfn harg =>
      cases hfn with | var hfn =>
      cases hfn with | var hfn =>
      cases hfn with | var hfn =>
      cases hfn with | var hfn =>
      cases hfn with | var hfn =>
      cases hfn
      exact harg.ne_proof (typed_eq_major_proof heq HT)

/-- Ordinary core reduction cannot act at any typed canonical Eq head.
Registered rules require a visible constructor in the sixth slot; typing
forces that slot to be a proof marker. No prefix-length bound is assumed. -/
theorem typed_eq_no_core_root
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ e) (hh : e.constHead = some ``Eq.rec) :
    ¬ ErasedIotaPrimitive D e out := by
  intro H
  rcases H with (H | H) | H
  · cases H with
    | delta H => cases Option.some.inj hh; exact hD _ _ H
    | projIota => cases hh
  · cases H with
    | select hp _ hm | apply hp _ hm => exact typed_eq_pattern_no_match heq hreg hoff HT hh hp hm
  · cases H with
    | intro hp _ _ hm => exact typed_eq_pattern_no_match heq hreg hoff HT hh hp hm

/-- A typed head-losing Eq root without structure recovery is a singleton
root and has at most five arguments. Short arity is derived from singleton
code generation after core exclusion, not assumed as an ancestry substitute. -/
theorem typed_nonstructural_eq_head_loss_singleton
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    args.length ≤ 5 ∧
      (ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
        ∃ k, k < n ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) args) target) := by
  classical
  have HS := (WrappedConstHead.const (c := ``Eq.rec) (ls := ls)).mkApps args
  obtain ⟨HL, HC, HI, HE⟩ := HS.loss_exclusions (Δ := Δ) HN
  by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target
  · exact ⟨Nat.le_of_eq (computed_prefix_length HQ), .inl HQ⟩
  have Hcore : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
    rintro (Hcore | Hlevel)
    · exact typed_eq_no_core_root heq hreg hoff hD HT (constHead_mkApps _ _) Hcore
    · exact HL Hlevel
  rcases static_other_spine_root HR.1 Hcore HQ Hstruct with Hconst | ⟨k, hk, HG | HId | HEta⟩
  · exact (HC Hconst).elim
  · exact ⟨HG.2.eq_rec_arity_le heq, .inr ⟨k, hk, HG⟩⟩
  · exact (HI _ HId).elim
  · exact (HE _ HEta).elim

/-- The remaining ancestry failure occurs at an actual singleton primitive
of arity at most five. Its exact tracked hole and counted paths are retained.
The missing claim is completion of these arguments to the original target;
short arity and singleton classification alone do not prove that claim. -/
def SingletonEqHeadCompletionFailure (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (budget : Nat) : Prop :=
  ∃ Ξ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Ξ Θ,
    cp+1+ct ≤ budget ∧ TrackedHeadHole C ∧ TypedSource Ξ source ∧
    ScopedComputeCount (PiInertStage D n) cp Ξ source (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)) ∧
    TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∧
    ¬ WrappedConstHead ``Eq.rec target ∧
    (∀ k, ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) ∧
    args.length ≤ 5 ∧
    (ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
      ∃ k, k < n ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target) ∧
    ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint ∧
    ¬ EqHeadCompletion Δ v w original Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)

/-- Classify the very same selected failure as a short singleton root using
its actual typing and structure exclusion. No new path or root is chosen. -/
theorem NonstructuralEqHeadCompletionFailure.singleton
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : NonstructuralEqHeadCompletionFailure D Δ v w original budget) :
    SingletonEqHeadCompletionFailure D Δ v w original budget := by
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, RT, HP⟩ := H
  obtain ⟨hlen, HG⟩ := typed_nonstructural_eq_head_loss_singleton
    heq hreg hoff hD HTroot HR HN (Hstruct n)
  exact ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, hlen, HG, RT, HP⟩

/-- Forget the derived arity and singleton classification while retaining
all previous root, path, hole and structure-exclusion evidence. -/
theorem SingletonEqHeadCompletionFailure.forget
    (H : SingletonEqHeadCompletionFailure D Δ v w original budget) :
    NonstructuralEqHeadCompletionFailure D Δ v w original budget := by
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, _, _, RT, HP⟩ := H
  exact ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, RT, HP⟩

end Lean4Lean.VEnv.Strengthening
