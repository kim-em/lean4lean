import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport

/-! Data witness operations use only laws at their preceding rank. The joint
rank construction supplies these records with the actual lower relation; no
operation assumes a source adequacy theorem or a same-rank semantic cast. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure LowerTransport (env : VEnv) (U : Nat) (lower : Relations n) : Prop where
  code : ∀ {Γ Δ ρ left right profile}, MixedInsertion env U Γ Δ ρ →
    lower.code Γ left right profile →
    lower.code Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ)
  term : ∀ {Γ Δ ρ left right type value support}, MixedInsertion env U Γ Δ ρ →
    lower.term Γ left right type value support →
    lower.term Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (support.rename ρ)

structure LowerEquality (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) extends LowerTransport env U lower : Prop where
  retag : ∀ {Γ left right type value before after}, value.HasType after →
    lower.code Γ type type after → lower.term Γ left right type value before →
    lower.term Γ left right type value after
  symm : ∀ {Γ left right type value support}, lower.term Γ left right type value support →
    lower.term Γ right left type value support
  trans : registry.Scoped → ∀ {Γ left middle right type value before after},
    lower.term Γ left middle type value before → lower.term Γ middle right type value after →
    lower.term Γ left right type value after

variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
  {lower : Relations n}

theorem admission_transport (henv : env.Ordered) (laws : LowerTransport env U lower)
    (route : MixedInsertion env U Γ Δ ρ) (admitted : RequestAdmission env U lower Γ key left right) :
    RequestAdmission env U lower Δ (key.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admitted
  refine ⟨route.eq henv anchor, route.eq henv pair, ?_, ?_,
    laws.code route code, laws.term route first, laws.term route last⟩
  · exact (Profile.rename_hasType_iff (ρ := ρ)).mpr typed
  · simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr formed

theorem admission_trans (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (first : RequestAdmission env U lower Γ key left middle)
    (second : RequestAdmission env U lower Γ key middle right) :
    RequestAdmission env U lower Γ key left right := by
  obtain ⟨anchor, pair, _, _, _, before, across⟩ := first
  obtain ⟨_, next, typed, formed, code, _, after⟩ := second
  exact ⟨anchor, pair.trans next, typed, formed, code,
    before, laws.trans hscoped across after⟩

theorem admission_symm (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (admitted : RequestAdmission env U lower Γ key left right) :
    RequestAdmission env U lower Γ key right left := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := admitted
  exact ⟨anchor.trans pair, pair.symm, typed, formed, code,
    laws.trans hscoped first last, laws.symm last⟩

theorem Arguments.transport (henv : env.Ordered) (laws : LowerTransport env U lower)
    (route : MixedInsertion env U Γ Δ ρ) (arguments : Arguments env U lower Γ keys xs ys) :
    Arguments env U lower Δ (keys.map (DataRequest.rename ρ)) (xs.map (·.lift' ρ)) (ys.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (admission_transport henv laws route head) ih

theorem Arguments.trans (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (first : Arguments env U lower Γ keys xs ys) (second : Arguments env U lower Γ keys ys zs) :
    Arguments env U lower Γ keys xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (admission_trans laws hscoped head next) (ih rest)

theorem Arguments.symm (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (arguments : Arguments env U lower Γ keys xs ys) : Arguments env U lower Γ keys ys xs := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (admission_symm laws hscoped head) ih

noncomputable def FamilyWitness.changeBase (henv : env.Ordered)
    (chain : ContextChain env U Γ Δ)
    (witness : FamilyWitness env U registry lower Γ left right demand) :
    FamilyWitness env U registry lower Δ left right demand :=
  { witness with
    leftExposure := witness.leftExposure.context henv chain
    rightExposure := witness.rightExposure.context henv chain }

theorem FamilyRelation.atBase (formed : OnCtx Γ (env.IsType U))
    (related : FamilyRelation env U registry lower Γ left right demand) :
    Nonempty (FamilyWitness env U registry lower Γ left right demand) := by
  have renamed : demand.rename .refl = demand := by
    unfold FamilyData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, FamilyData.map_id]
  simpa only [lift'_refl, renamed] using related Γ .refl (.refl formed)

theorem FamilyRelation.mixed (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (related : FamilyRelation env U registry lower Γ left right demand) :
    FamilyRelation env U registry lower Δ (left.lift' ρ) (right.lift' ρ) (demand.rename ρ) := by
  intro Ω τ future
  obtain ⟨base, extended, changed⟩ := route.pullFuture henv future
  obtain ⟨witness⟩ := related base (ρ.comp τ) extended
  simpa only [lift'_comp, FamilyData.rename_comp] using
    (show Nonempty _ from ⟨witness.changeBase henv changed⟩)

def FamilyWitness.symm (laws : LowerEquality env U registry lower)
    (witness : FamilyWitness env U registry lower Γ left right demand) :
    FamilyWitness env U registry lower Γ right left demand :=
  { witness with
    leftLevel := witness.rightLevel, rightLevel := witness.leftLevel
    leftRelevance := witness.rightRelevance, rightRelevance := witness.leftRelevance
    path := witness.path.symm
    leftType := witness.rightType, rightType := witness.leftType
    leftLevels := witness.rightLevels, rightLevels := witness.leftLevels
    leftArguments := witness.rightArguments, rightArguments := witness.leftArguments
    leftExposure := witness.rightExposure, rightExposure := witness.leftExposure
    leftTerminal := witness.rightTerminal, rightTerminal := witness.leftTerminal
    leftUniverses := witness.rightUniverses, rightUniverses := witness.leftUniverses
    arguments := witness.arguments.symm laws witness.registryScoped }

private theorem family_lift (name : Name) (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

private theorem family_spine (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs = (.const name levels, arguments) := by
  have getSpine : ∀ (head : VExpr) arguments accumulated,
      getAppFnArgs.go (mkApps head arguments) accumulated =
        getAppFnArgs.go head (arguments ++ accumulated) := by
    intro head arguments
    induction arguments generalizing head with
    | nil => intro accumulated; rfl
    | cons arg rest ih => intro accumulated; exact ih (.app head arg) accumulated
  simp only [getAppFnArgs, getSpine, getAppFnArgs.go, List.append_nil]

theorem FamilyWitness.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : FamilyWitness env U registry lower Γ left middle demand)
    (second : FamilyWitness env U registry lower Γ middle right demand) :
    Nonempty (FamilyWitness env U registry lower Γ left right demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps, heads⟩ :=
    first.rightExposure.sameHead henv first.registryScoped second.leftExposure
      first.rightTerminal second.leftTerminal
  have middleArguments : first.rightArguments.map (·.lift' i) = second.leftArguments.map (·.lift' j) := by
    rw [family_lift, family_lift] at heads
    simpa only [family_spine] using congrArg Prod.snd (congrArg VExpr.getAppFnArgs heads)
  obtain ⟨leftExposure⟩ := first.leftExposure.transport henv firstLeg
  obtain ⟨rightExposure⟩ := second.rightExposure.transport henv secondLeg
  have firstArguments := first.arguments.transport henv laws.toLowerTransport firstLeg
  have secondArguments := second.arguments.transport henv laws.toLowerTransport secondLeg
  simp only [List.map_map, Function.comp_def, DataRequest.rename_comp, maps] at firstArguments secondArguments
  rw [middleArguments] at firstArguments
  refine ⟨{
    registryScoped := first.registryScoped
    headInert := first.headInert
    leftLevel := first.leftLevel, rightLevel := second.rightLevel
    leftRelevance := first.leftRelevance, rightRelevance := second.rightRelevance
    context := Ω, map := second.map.comp j
    path := ?_, leftType := ?_, rightType := ?_
    leftLevels := first.leftLevels, rightLevels := second.rightLevels
    leftArguments := first.leftArguments.map (·.lift' i)
    rightArguments := second.rightArguments.map (·.lift' j)
    leftExposure := ?_, rightExposure := ?_
    leftTerminal := ?_, rightTerminal := ?_
    leftUniverses := first.leftUniverses, rightUniverses := second.rightUniverses
    arguments := firstArguments.trans laws first.registryScoped secondArguments }⟩
  · have before := firstLeg.path henv first.path
    have after := secondLeg.path henv second.path
    simp only [← lift'_comp, maps] at before after
    exact before.trans after
  · simpa only [HasType, family_lift, lift'] using firstLeg.eq henv first.leftType
  · simpa only [HasType, family_lift, lift'] using secondLeg.eq henv second.rightType
  · simpa only [family_lift, maps] using leftExposure
  · simpa only [family_lift] using rightExposure
  · rw [← family_lift, CanonicalDataHead.step_rename registry first.registryScoped, first.leftTerminal]; rfl
  · rw [← family_lift, CanonicalDataHead.step_rename registry first.registryScoped, second.rightTerminal]; rfl

theorem FamilyRelation.symm (laws : LowerEquality env U registry lower)
    (related : FamilyRelation env U registry lower Γ left right demand) :
    FamilyRelation env U registry lower Γ right left demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact ⟨witness.symm laws⟩

theorem FamilyRelation.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : FamilyRelation env U registry lower Γ left middle demand)
    (second : FamilyRelation env U registry lower Γ middle right demand) :
    FamilyRelation env U registry lower Γ left right demand := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  exact before.trans henv laws after


noncomputable def ConstructorWitness.changeBase (henv : env.Ordered)
    (chain : ContextChain env U Γ Δ)
    (witness : ConstructorWitness env U registry lower Γ left right type demand) :
    ConstructorWitness env U registry lower Δ left right type demand :=
  { witness with
    leftExposure := witness.leftExposure.context henv chain
    rightExposure := witness.rightExposure.context henv chain }

noncomputable def RecordWitness.changeBase (henv : env.Ordered)
    (chain : ContextChain env U Γ Δ)
    (witness : RecordWitness env U registry lower Γ left right type demand) :
    RecordWitness env U registry lower Δ left right type demand :=
  { witness with
    baseWF := chain.targetWF henv witness.baseWF
    insertion := by simpa only [Lift.refl_comp] using
      MixedInsertion.comp (.context (chain.symm henv)) witness.insertion }

theorem ConstructorRelation.context (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : ConstructorRelation env U registry lower Γ left right type demand) :
    ConstructorRelation env U registry lower Δ left right type demand := by
  intro Ω ρ future
  obtain ⟨base, extended, changed⟩ := (MixedInsertion.context chain).pullFuture henv future
  obtain ⟨witness⟩ := related base ρ (by simpa only [Lift.refl_comp] using extended)
  exact ⟨witness.changeBase henv changed⟩

theorem RecordRelation.context (henv : env.Ordered) (chain : ContextChain env U Γ Δ)
    (related : RecordRelation env U registry lower Γ left right type demand) :
    RecordRelation env U registry lower Δ left right type demand := by
  intro Ω ρ future
  obtain ⟨base, extended, changed⟩ := (MixedInsertion.context chain).pullFuture henv future
  obtain ⟨witness⟩ := related base ρ (by simpa only [Lift.refl_comp] using extended)
  exact ⟨witness.changeBase henv changed⟩

end Lean4Lean.AnchoredSemantics.RankedData
