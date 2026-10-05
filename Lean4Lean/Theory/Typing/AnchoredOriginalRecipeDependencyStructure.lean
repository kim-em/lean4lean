import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePruning
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private BinderPack.external_mem from Lean4Lean.Theory.Typing.AnchoredSourceBinder
open private traceRename from Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem piDependencyCongr
    {firstDomain secondDomain firstBody secondBody : {n : Nat} → Profile n → Valuation → Prop}
    (domain : ∀ {n} (profile : Profile n) available, firstDomain profile available ↔ secondDomain profile available)
    (body : ∀ {n} (profile : Profile n) available, firstBody profile available ↔ secondBody profile available)
    {atom : Atom n} :
    RecipePiDependency firstDomain firstBody available atom ↔
      RecipePiDependency secondDomain secondBody available atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | pi A B support rows =>
      simp only [RecipePiDependency, domain, body]
    | pad atom => exact ih
    | _ => rfl

/-- Universe equivalence preserves exactly the raw constructors traversed by
the compiler; no same-displayed-expression R is being inferred here. -/
theorem RecipeDependencyProfile.levels
    (equal : EqUpToLevels U expression other) {profile : Profile n} :
    RecipeDependencyProfile env U registry target expression profile available ↔
      RecipeDependencyProfile env U registry target other profile available := by
  induction equal generalizing n available with
  | bvar => rfl
  | forallE domains bodies domainIH bodyIH =>
    simp only [RecipeDependencyProfile]
    constructor <;> intro supplied atom member
    · exact (piDependencyCongr (fun p a => domainIH) (fun p a => bodyIH)).mp (supplied atom member)
    · exact (piDependencyCongr (fun p a => domainIH) (fun p a => bodyIH)).mpr (supplied atom member)
  | _ => simp only [RecipeDependencyProfile]

/-- The actual finite transfer program supplies dependency evidence for each
required leaf. No interpreted value or completed destination code is assumed. -/
theorem RecipeResourceTransfer.dependencies
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (resources : footprint.Available available) :
    ∀ index need, (index, need) ∈ required →
      RecipeVariableDependency env U registry target available index need.profile := by
  induction transfer with
  | nil => intro _ _ member; cases member
  | cons query tail ih =>
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨_, ⟨.legacy query.variableTrace⟩,
        fun i requested selected => resources i requested (List.mem_append_left _ selected)⟩
    · exact ih (fun i requested selected => resources i requested (List.mem_append_right _ selected))
        index need member

/-- The exact atomized input table supplies any lower-grade demand literally
covered by the input. This constructs a finite variable query via subprofile
selection and grade lowering, rather than treating subset as availability. -/
theorem recipeDependencyInputs.supplies
    {profile : Profile n} {need : Need} (bounded : need.rank ≤ n)
    (covered : (need.atGrade n).atoms ⊆ profile.atoms) :
    RecipeVariableDependency env U registry target
      (Valuation.push (recipeDependencyInputs profile) available) 0 need.profile := by
  let observation : Obs env U registry target [] Subst.id (.bvar 0) profile [(0, ⟨n, profile⟩)] :=
    .var [] Subst.id 0 profile
  obtain ⟨fp, ⟨query⟩, atomized⟩ := observation.subprofile covered
  have query' : Obs env U registry target [] Subst.id (.bvar 0)
      (raiseProfile n bounded need.profile) fp := by
    simpa only [Need.atGrade, dif_pos bounded] using query
  let lowered := Obs.lower bounded query'
  refine ⟨fp, ⟨.legacy lowered.variableTrace⟩, ?_⟩
  intro index requested member
  have zero : index = 0 := query.variableTrace.indices member
  subst index
  have initial : Footprint.Available [(0, ⟨n, profile⟩)]
      (Valuation.push [⟨n, profile⟩] available) := by
    intro i wanted selected
    cases List.mem_singleton.mp selected
    exact List.mem_singleton_self _
  exact atomized.available initial 0 requested member

/-- BinderPack exposes every actual body leaf as a finite dependency in the
new input table or in the previous outer table. This is the native row step
for the program interpreter, independent of its old/new anchor values. -/
theorem BinderPack.dependencySupply
    (pack : BinderPack n packed required outside)
    (covered : packed.atoms ⊆ input.atoms)
    (resources : ∀ index need, (index, need) ∈ outside →
      RecipeVariableDependency env U registry target available index need.profile) :
    ∀ index need, (index, need) ∈ required →
      RecipeVariableDependency env U registry target
        (Valuation.push (recipeDependencyInputs input) available) index need.profile := by
  intro index need member
  cases index with
  | zero =>
    have localMember : need ∈ required.localNeeds ++ required.localNeeds.flatMap Need.singletons :=
      List.mem_append_left _ (Footprint.mem_localNeeds.mpr member)
    have info := pack.atomized_localNeeds need localMember
    exact recipeDependencyInputs.supplies info.1 (fun atom member => covered (info.2 atom member))
  | succ index =>
    obtain ⟨fp, ⟨trace⟩, supplied⟩ := resources index need (BinderPack.external_mem pack member)
    refine ⟨fp.map (fun entry => (entry.1 + 1, entry.2)), traceRename trace Nat.succ, ?_⟩
    intro i requested selected
    obtain ⟨⟨oldIndex, oldNeed⟩, oldMember, equal⟩ := List.mem_map.mp selected
    cases equal
    exact supplied oldIndex oldNeed oldMember

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
