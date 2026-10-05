import Lean4Lean.Theory.Typing.AnchoredNativeSeedCollection
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceProofIrrel

/-! An uncopied proof field consumes an actual empty binder pack. Emptiness
is proved from its original proposition and variable payloads, even when the
seed was assembled by unions of differently graded source observations. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeArgumentSeed.proofEmpty
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument proposition : VExpr}
    (seed : NativeArgumentSeed env U registry target locals σ available argument)
    (originalProposition : OriginalTypePayload sourceEnv env U registry source
      proposition (.sort .zero))
    (originalArgument : OriginalTypePayload sourceEnv env U registry source argument proposition)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available) :
    seed.demand = .empty := by
  have propositionCorrect := (originalProposition.2 target locals σ σ available closed
    hTarget substitutions fits).2.2.1
  obtain ⟨value⟩ := (originalArgument.2 target locals σ σ available closed
    hTarget substitutions fits).1 seed.observation seed.resources
  have propositionTyped := value.requestedCertificate.sortCorrect propositionCorrect
    (show Relevant .zero false from rfl) value.typeAvailable
  exact value.requestedTyped.proof_empty propositionTyped

private theorem pack_empty_needs (required : Footprint)
    (empty : ∀ need, (0, need) ∈ required → need.rank ≤ rank ∧ need.atGrade rank = .empty) :
    ∃ outside, BinderPack rank .empty required outside := by
  induction required with
  | nil => exact ⟨[], .nil⟩
  | cons entry rest ih =>
    obtain ⟨outside, tail⟩ := ih (fun need member => empty need (List.mem_cons_of_mem _ member))
    obtain ⟨index, need⟩ := entry
    cases index with
    | zero =>
      obtain ⟨bound, equal⟩ := empty need List.mem_cons_self
      exact ⟨outside, by simpa only [equal, Profile.union, Profile.empty, Profile.mk,
        Profile.atoms, List.nil_append] using BinderPack.local need bound tail⟩
    | succ index => exact ⟨(index, need) :: outside, .external index need tail⟩

theorem NativeSeedCover.emptyPack
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument : VExpr} {required : Footprint} {minimum : Nat}
    (cover : NativeSeedCover env U registry target locals σ available argument
      (argumentNeeds required 0) minimum)
    (empty : cover.seed.demand = .empty) :
    ∃ outside, BinderPack cover.seed.rank .empty required outside := by
  apply pack_empty_needs
  intro need member
  obtain ⟨bound, included⟩ := cover.covered need (mem_argumentNeeds.mpr member)
  refine ⟨bound, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro atom ha
  have impossible := included atom ha
  rw [empty] at impossible
  cases impossible

/-- The proof branch is produced from retained original evidence; neither
an empty aggregate demand nor a whole-demand valuation entry is assumed. -/
theorem NativeSeedCover.proofPack
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument proposition : VExpr} {required : Footprint} {minimum : Nat}
    (cover : NativeSeedCover env U registry target locals σ available argument
      (argumentNeeds required 0) minimum)
    (originalProposition : OriginalTypePayload sourceEnv env U registry source
      proposition (.sort .zero))
    (originalArgument : OriginalTypePayload sourceEnv env U registry source argument proposition)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available) :
    ∃ outside, BinderPack cover.seed.rank .empty required outside :=
  cover.emptyPack (cover.seed.proofEmpty originalProposition originalArgument closed
    hTarget substitutions fits)

end Lean4Lean.AnchoredSource.Adapted
