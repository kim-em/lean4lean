import Lean4Lean.Theory.Typing.AnchoredNativeRetelescopeBinder

/-! The recursive retelescoping context retains the row certificate's local
requirements and the actual computational seed requirements together. New
certificate leaves are packed from availability in this fixed finite context. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

namespace NativeRetelescopeBinder
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
  {A B : VExpr} {key : Key n} {output : Atom n}
  (binder : NativeRetelescopeBinder env U registry target locals σ available A B key output)

def nextNeeds (extra : List Need) : List Need :=
  (binder.row.bodyFootprint.localNeeds ++ extra) ++
    (binder.row.bodyFootprint.localNeeds ++ extra).flatMap Need.singletons

theorem nextCoverage (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    ∀ need ∈ binder.nextNeeds extra, need.rank ≤ n ∧
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
  have original : ∀ need ∈ binder.row.bodyFootprint.localNeeds ++ extra,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨bound, included⟩ := binder.row.pack.localNeeds need member
      exact ⟨bound, fun atom h => binder.row.covered atom (included atom h)⟩
    · exact ⟨extraBound need member, extraCovered need member⟩
  intro need member
  rcases List.mem_append.mp member with member | member
  · exact original need member
  · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp selected
    obtain ⟨bound, included⟩ := original old oldMember
    refine ⟨bound, ?_⟩
    intro high member
    apply included high
    simp only [Need.atGrade, dif_pos bound] at member ⊢
    exact raiseProfile_subset bound
      (fun a h => by cases List.mem_singleton.mp h; exact atomMember) high member

theorem nextClosed (extra : List Need) (closed : available.AtomClosed) :
    (Valuation.push (binder.nextNeeds extra) available).AtomClosed :=
  Valuation.push_atomized_closed closed _

theorem bodyAvailable (extra : List Need) :
    binder.row.bodyFootprint.Available (Valuation.push (binder.nextNeeds extra) available) := by
  have original := binder.row.pack.available binder.row.outsideAvailable
  intro index need member
  cases index with
  | zero => exact List.mem_append_left _ (List.mem_append_left _ (original 0 need member))
  | succ index => exact original (index + 1) need member

/-- Only actual original domain formation and the stored anchor guard are
used to form the next raw and semantic substitutions. -/
theorem nextFits (henv : env.Ordered) {source : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    (formedA : env.HasType U source A (.sort level))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) ∧
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons key.anchor) (Valuation.push (binder.nextNeeds extra) available) := by
  have coverage := binder.nextCoverage extra extraBound extraCovered
  obtain ⟨_, anchorTyped, _, _, _, _, anchorRelated, _⟩ := binder.guard.anchor
  have actualRelated := Related.convert henv binder.guard.inputTyped binder.guard.domains anchorRelated
  exact ⟨.cons substitutions formedA (binder.guard.path.cast anchorTyped),
    fits.pushDiagonal henv hTarget binder.row.domain binder.row.domainAvailable
      binder.row.inputTyped actualRelated (binder.nextNeeds extra)
      (fun need member => (coverage need member).1)
      (fun need member => (coverage need member).2)⟩

/-- The recursive child's newly interpreted domain certificates may change
its footprint. Availability, not equality with the old footprint, gives the
exact binder pack and literal input coverage needed to rebuild the plan. -/
theorem rebuildAvailable
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    (binder : NativeRetelescopeBinder env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available A B key output)
    (origin : signature.domains[arguments.length]? = some A)
    (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    {bodyFootprint : Footprint}
    (body : NativeInitialTree env U registry target signature (arguments ++ [key.anchor])
      (.singleton output) bodyFootprint)
    (resources : bodyFootprint.Available (Valuation.push (binder.nextNeeds extra) available)) :
    ∃ footprint, Nonempty (NativeInitialTree env U registry target signature arguments
      (Profile.fn binder.actualKey output) footprint) ∧ footprint.Available available := by
  have coverage := binder.nextCoverage extra extraBound extraCovered
  obtain ⟨packed, outside, pack, covered, outsideAvailable⟩ :=
    Footprint.pack_available resources (fun need member => (coverage need member).1)
      (fun need member => (coverage need member).2)
  refine ⟨binder.row.domainFootprint ++ outside,
    ⟨binder.initialTree origin body pack covered⟩, ?_⟩
  intro index need member
  exact (List.mem_append.mp member).elim (binder.row.domainAvailable index need)
    (outsideAvailable index need)

end NativeRetelescopeBinder
end Lean4Lean.AnchoredSource.Adapted
