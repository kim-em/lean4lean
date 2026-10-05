import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel

/-! Finite actions in the retained recipe dependency interpreter. The laws
below are proved for the raw expression by structural induction; their Pi
case uses the already established laws for its domain and body. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem legacySelect
    (closed : available.AtomClosed)
    (trace : VariableTrace env U registry target index profile footprint)
    (member : atom ∈ profile.atoms) (resources : footprint.Available available) :
    RecipeVariableDependency env U registry target available index (.singleton atom) := by
  induction trace with
  | leaf profile =>
    exact RecipeVariableDependency.leaf
      (closed index _ (resources _ _ List.mem_cons_self) _ (List.mem_map_of_mem member))
  | empty => cases member
  | union left right leftIH rightIH =>
    rcases List.mem_append.mp member with member | member
    · exact leftIH member (fun i need h => resources i need (List.mem_append_left _ h))
    · exact rightIH member (fun i need h => resources i need (List.mem_append_right _ h))
  | view trace view ih =>
    cases List.mem_singleton.mp member
    exact ⟨_, ⟨.legacy (.view trace view)⟩, resources⟩
  | pad trace ih =>
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨fp, ⟨next⟩, supplied⟩ := ih oldMember resources
    exact ⟨fp, ⟨.pad next⟩, supplied⟩
  | unpad trace ih =>
    obtain ⟨fp, ⟨next⟩, supplied⟩ := ih (List.mem_map_of_mem member) resources
    exact ⟨fp, ⟨.unpad next⟩, supplied⟩
  | rowShift trace ih =>
    cases List.mem_singleton.mp member
    exact ⟨_, ⟨.legacy (.rowShift trace)⟩, resources⟩

theorem RecipeVariableDependency.select
    (closed : available.AtomClosed)
    (dependency : RecipeVariableDependency env U registry target available index profile)
    (member : atom ∈ profile.atoms) :
    RecipeVariableDependency env U registry target available index (.singleton atom) := by
  obtain ⟨footprint, ⟨trace⟩, resources⟩ := dependency
  -- Literal selection is available on observations at every intrinsic type.
  induction trace with
  | legacy trace => exact legacySelect closed trace member resources
  | union left right leftIH rightIH =>
    rcases List.mem_append.mp member with member | member
    · exact leftIH member (fun i need h => resources i need (List.mem_append_left _ h))
    · exact rightIH member (fun i need h => resources i need (List.mem_append_right _ h))
  | code trace action formed ih =>
    exact ⟨_, ⟨.code (.code trace action formed) (.select member) (action.preservesSort formed)⟩, resources⟩
  | action trace action ih =>
    cases List.mem_singleton.mp member
    exact ⟨_, ⟨.action trace action⟩, resources⟩
  | pad trace ih =>
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨fp, ⟨next⟩, supplied⟩ := ih oldMember resources
    exact ⟨fp, ⟨.pad next⟩, supplied⟩
  | unpad trace ih =>
    obtain ⟨fp, ⟨next⟩, supplied⟩ := ih (List.mem_map_of_mem member) resources
    exact ⟨fp, ⟨.unpad next⟩, supplied⟩

theorem RecipeVariableDependency.union
    (left : RecipeVariableDependency env U registry target available index p)
    (right : RecipeVariableDependency env U registry target available index q) :
    RecipeVariableDependency env U registry target available index (p.union q) := by
  obtain ⟨lf, ⟨l⟩, hl⟩ := left
  obtain ⟨rf, ⟨r⟩, hr⟩ := right
  exact ⟨lf ++ rf, ⟨.union l r⟩,
    fun i need member => (List.mem_append.mp member).elim (hl i need) (hr i need)⟩

private theorem profileViewEach
    {p q : Profile n}
    (view : ProfileView env U registry target p q)
    (each : ∀ atom ∈ p.atoms, RecipeVariableDependency env U registry target available index (.singleton atom)) :
    RecipeVariableDependency env U registry target available index q := by
  match p, q, view with
  | _, _, .nil => exact ⟨[], ⟨.legacy .empty⟩, fun _ _ member => by cases member⟩
  | _, _, .cons head tail =>
    obtain ⟨fp, ⟨trace⟩, resources⟩ := each _ List.mem_cons_self
    exact RecipeVariableDependency.union
      ⟨fp, ⟨.action trace (.view head)⟩, resources⟩
      (profileViewEach tail (fun atom member => each atom (List.mem_cons_of_mem _ member)))
termination_by sizeOf view

theorem RecipeVariableDependency.profileView
    (closed : available.AtomClosed)
    (view : ProfileView env U registry target p q)
    (dependency : RecipeVariableDependency env U registry target available index p) :
    RecipeVariableDependency env U registry target available index q :=
  profileViewEach view (fun atom member => RecipeVariableDependency.select closed dependency member)

/-- Only the finite head table changes; all outer resources stay literal. -/
theorem RecipeResourceDependency.changeInputs
    (closed : available.AtomClosed)
    (head : RecipeVariableDependency env U registry target
      (Valuation.push (recipeDependencyInputs newInput) available) 0 oldInput) :
    RecipeResourceDependency env U registry target
      (Valuation.push (recipeDependencyInputs oldInput) available)
      (Valuation.push (recipeDependencyInputs newInput) available) := by
  intro index need member
  cases index with
  | succ index => exact RecipeVariableDependency.leaf member
  | zero =>
    change need ∈ recipeDependencyInputs oldInput at member
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact head
    · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp member
      cases List.mem_singleton.mp oldMember
      obtain ⟨atom, atomMember, equal⟩ := List.mem_map.mp selected
      cases equal
      exact RecipeVariableDependency.select
        (Valuation.push_atomized_closed closed _) head atomMember

theorem RecipeResourceDependency.inputsView
    (closed : available.AtomClosed)
    (view : ProfileView env U registry target newInput oldInput) :
    RecipeResourceDependency env U registry target
      (Valuation.push (recipeDependencyInputs oldInput) available)
      (Valuation.push (recipeDependencyInputs newInput) available) := by
  apply RecipeResourceDependency.changeInputs closed
  exact RecipeVariableDependency.profileView (Valuation.push_atomized_closed closed _)
    view (RecipeVariableDependency.leaf (need := ⟨_, newInput⟩)
      (List.mem_append_left _ List.mem_cons_self))

theorem RecipeResourceDependency.inputsPad
    (closed : available.AtomClosed) (input : Profile n) :
    RecipeResourceDependency env U registry target
      (Valuation.push (recipeDependencyInputs input) available)
      (Valuation.push (recipeDependencyInputs input.pad) available) := by
  apply RecipeResourceDependency.changeInputs closed
  exact ⟨[(0, ⟨n+1, input.pad⟩)], ⟨.unpad (.legacy (.leaf input.pad))⟩,
    fun i need member => by
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ List.mem_cons_self⟩

theorem RecipeResourceDependency.inputsUnpad
    (closed : available.AtomClosed) (input : Profile n) :
    RecipeResourceDependency env U registry target
      (Valuation.push (recipeDependencyInputs input.pad) available)
      (Valuation.push (recipeDependencyInputs input) available) := by
  apply RecipeResourceDependency.changeInputs closed
  exact ⟨[(0, ⟨n, input⟩)], ⟨.pad (.legacy (.leaf input))⟩,
    fun i need member => by
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ List.mem_cons_self⟩

/-- Internal induction hypotheses for one smaller raw expression. -/
structure RecipeDependencyLaws (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (model : {n : Nat} → Profile n → Valuation → Prop) : Prop where
  empty : ∀ {n available}, model (Profile.empty : Profile n) available
  union : ∀ {n} {p q : Profile n} {available}, model p available → model q available → model (p.union q) available
  select : ∀ {n} {p : Profile n} {atom available}, available.AtomClosed →
    model p available → atom ∈ p.atoms → model (.singleton atom) available
  pad : ∀ {n} {p : Profile n} {available}, model p available → model p.pad available
  unpad : ∀ {n} {p : Profile n} {available}, model p.pad available → model p available
  code : ∀ {n m relevant next} {p : Profile n} {q : Profile m} {available},
    available.AtomClosed → SortableCodeAction env U registry target relevant p next q →
    p.HasType (.sort relevant) → model p available → model q available
  action : ∀ {n} {a b : Atom n} {available}, available.AtomClosed →
    AtomAction env U registry target a b → model (.singleton a) available → model (.singleton b) available
  move : ∀ {n} {p : Profile n} {first second},
    RecipeResourceDependency env U registry target first second → model p first → model p second

abbrev RecipePiProfileDependency
    (domain body : {n : Nat} → Profile n → Valuation → Prop)
    (profile : Profile n) (available : Valuation) : Prop :=
  ∀ atom ∈ profile.atoms, RecipePiDependency domain body available atom

namespace RecipePiProfileDependency
variable {domain body : {n : Nat} → Profile n → Valuation → Prop}

theorem empty : RecipePiProfileDependency domain body (Profile.empty : Profile n) available :=
  fun _ member => nomatch member

theorem union
    (left : RecipePiProfileDependency domain body p available)
    (right : RecipePiProfileDependency domain body q available) :
    RecipePiProfileDependency domain body (p.union q) available :=
  fun atom member => (List.mem_append.mp member).elim (left atom) (right atom)

theorem pad
    (dependency : RecipePiProfileDependency domain body p available) :
    RecipePiProfileDependency domain body p.pad available := by
  intro atom member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  exact dependency old present

theorem unpad
    (dependency : RecipePiProfileDependency domain body p.pad available) :
    RecipePiProfileDependency domain body p available :=
  fun atom member => dependency (.pad atom) (List.mem_map_of_mem member)

theorem down
    (dependency : RecipePiProfileDependency domain body (p : Profile (n+1)) available) :
    RecipePiProfileDependency domain body p.down available := by
  intro atom member
  obtain ⟨old, present, member⟩ := List.mem_flatMap.mp member
  have origin := dependency old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad old => cases List.mem_singleton.mp member; exact origin

theorem select (dependency : RecipePiProfileDependency domain body p available)
    (member : atom ∈ p.atoms) :
    RecipePiProfileDependency domain body (.singleton atom) available := by
  intro selected present
  cases List.mem_singleton.mp present
  exact dependency _ member

theorem not_sort (dependency : RecipePiProfileDependency domain body
    (Profile.sort (n := n) relevant) available) : False := by
  cases n <;> exact dependency _ List.mem_cons_self

theorem sortFlags_nil
    (dependency : RecipePiProfileDependency domain body (p : Profile n) available) :
    p.sortFlags = [] := by
  induction n with
  | zero =>
    cases p with
    | nil => rfl
    | cons a rest => exact False.elim (dependency a List.mem_cons_self)
  | succ n ih => exact ih dependency.down

variable (domainLaws : RecipeDependencyLaws env U registry target domain)
    (bodyLaws : RecipeDependencyLaws env U registry target body)

include domainLaws bodyLaws in
theorem rankShift (closed : available.AtomClosed)
    (dependency : RecipePiProfileDependency domain body (p : Profile (n+1)) available) :
    RecipePiProfileDependency domain body p.rankShift available := by
  intro atom member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  have origin := dependency old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad => exact origin
  | pi A B support rows =>
    refine ⟨domainLaws.pad origin.1, ?_⟩
    intro key output member
    obtain ⟨⟨oldKey, oldOutput⟩, present, equal⟩ := List.mem_map.mp member
    cases equal
    exact bodyLaws.move (RecipeResourceDependency.inputsPad closed oldKey.input)
      (bodyLaws.pad (origin.2 oldKey oldOutput present))

include domainLaws bodyLaws in
theorem unshift (closed : available.AtomClosed)
    (key : Key n) (formed : p.HasType (.sort relevant))
    (dependency : RecipePiProfileDependency domain body (p : Profile (n+2)) available) :
    RecipePiProfileDependency domain body (p.unshift key) available := by
  intro atom member
  obtain ⟨old, present, member⟩ := List.mem_flatMap.mp member
  have origin := dependency old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi A B support rows =>
    cases List.mem_singleton.mp member
    have typed := Profile.HasType.pi_iff.mp (formed.singleton_of_mem present)
    refine ⟨domainLaws.code closed .down (Profile.WF.pi_iff.mp typed.1).1 origin.1, ?_⟩
    intro other output member
    obtain ⟨same, oldOutput, oldMember, rfl⟩ := Rows.mem_unshift.mp member
    subst other
    exact bodyLaws.move (RecipeResourceDependency.inputsUnpad closed key.input)
      (bodyLaws.code (Valuation.push_atomized_closed closed _) .down
        (typed.2 key.pad oldOutput oldMember) (origin.2 key.pad oldOutput oldMember))

include domainLaws bodyLaws in
theorem focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {p available relevant}, available.AtomClosed → focused ≤ p →
      p.HasType (.sort relevant) → RecipePiProfileDependency domain body p available →
      RecipePiProfileDependency domain body focused available := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {p available relevant}, available.AtomClosed → focused ≤ p →
        p.HasType (.sort relevant) → RecipePiProfileDependency domain body p available →
        RecipePiProfileDependency domain body focused available) with
  | nil => exact fun _ _ _ _ => empty
  | cons first tail ihFirst ihTail =>
    intro p available relevant closed bound formed dependency
    exact union (ihFirst closed (Profile.le_trans (Profile.le_union_left _ _) bound) formed dependency)
      (ihTail closed (Profile.le_trans (Profile.le_union_right _ _) bound) formed dependency)
  | @sort n atom relevant typed p available flag closed bound formed dependency =>
    cases n with
    | zero => exact False.elim (dependency _ (Profile.sort_le_mem_zero bound))
    | succ n => exact False.elim (dependency _ (Profile.sort_le_mem bound))
  | @family n value data typed p available flag closed bound formed dependency =>
    obtain ⟨other, present, covered⟩ := bound _ List.mem_cons_self
    cases other <;> try contradiction
    exact False.elim (dependency _ present)
  | @fn n support result A B key output inputMinimal outputMinimal supportFormed _ _
      p available relevant closed bound formed dependency =>
    obtain ⟨oldSupport, oldRows, present, supportBound, rowsBound⟩ :=
      Profile.pi_le_inv bound List.mem_cons_self
    have old := dependency _ present
    have typed := Profile.HasType.pi_iff.mp (formed.singleton_of_mem present)
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨domainLaws.code closed (.focusMinimal inputMinimal supportBound)
      (Profile.WF.pi_iff.mp typed.1).1 old.1, ?_⟩
    intro selected result member
    cases List.mem_singleton.mp member
    obtain ⟨oldResult, oldMember, resultBound⟩ := rowsBound key _ List.mem_cons_self
    exact bodyLaws.code (Valuation.push_atomized_closed closed _)
      (.focusMinimal outputMinimal resultBound) (typed.2 key oldResult oldMember)
      (old.2 key oldResult oldMember)
  | @pad n atom support lower ih p available relevant closed bound formed dependency =>
    exact (ih closed (by simpa only [Profile.down_pad] using bound.down)
      (by simpa only [Profile.down_sort] using formed.down) dependency.down).pad

end RecipePiProfileDependency

noncomputable def ProfileView.dependencyCodeAction
    {p q : Profile n}
    (view : ProfileView env U registry target p q) (profile : Profile n) (relevant : Bool) :
    SortableCodeAction env U registry target relevant profile relevant (view.mapType profile) := by
  match p, q, view with
  | _, _, .nil => exact .id
  | _, _, .cons head tail => exact .union (.map head) (ProfileView.dependencyCodeAction tail profile relevant)
termination_by sizeOf view

theorem RecipeDependencyLaws.unions
    {profiles : List (Profile n)}
    (laws : RecipeDependencyLaws env U registry target model)
    (dependencies : ∀ p ∈ profiles, model p available) :
    model (Profile.unions profiles) available := by
  induction profiles with
  | nil => exact laws.empty
  | cons head tail ih =>
    exact laws.union (dependencies head List.mem_cons_self)
      (ih (fun p member => dependencies p (List.mem_cons_of_mem _ member)))

namespace RecipePiProfileDependency
variable {domain body : {n : Nat} → Profile n → Valuation → Prop}
    (domainLaws : RecipeDependencyLaws env U registry target domain)
    (bodyLaws : RecipeDependencyLaws env U registry target body)

include domainLaws bodyLaws in
theorem map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (closed : available.AtomClosed) (formed : profile.HasType (.sort relevant))
    (dependency : RecipePiProfileDependency domain body profile available) :
    RecipePiProfileDependency domain body (change.mapType profile) available := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact dependency
  | _ + 1, _, _, .reanchor (key := oldKey) admitted =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := dependency old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      refine ⟨origin.1, ?_⟩
      intro key result member
      rcases mem_reanchorRows.mp member with oldMember | ⟨rfl, oldMember⟩
      · exact origin.2 key result oldMember
      · exact origin.2 oldKey result oldMember
  | _ + 1, _, _, .domainRekey (key := oldKey) path typed supportFormed related =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := dependency old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      simp only [domainRekeyAtom]
      split
      · refine ⟨origin.1, ?_⟩
        intro key result member
        rcases mem_reanchorRows.mp member with oldMember | ⟨rfl, oldMember⟩
        · exact origin.2 key result oldMember
        · exact origin.2 oldKey result oldMember
      · exact origin
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := dependency old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      simp only [AtomView.mapType, inputTypes] at *
      split
      · refine ⟨?_, ?_⟩
        · have typed := Profile.HasType.pi_iff.mp (formed.singleton_of_mem present)
          apply domainLaws.union origin.1
          apply domainLaws.unions
          intro result member
          obtain ⟨selected, selectedMember, rfl⟩ := List.mem_map.mp member
          exact domainLaws.code closed (ProfileView.dependencyCodeAction backward selected true)
            (Basis.minimal selectedMember).formation
            (domainLaws.code closed (.focusMinimal (Basis.minimal selectedMember) (Basis.valid selectedMember).2)
              (Profile.WF.pi_iff.mp typed.1).1 origin.1)
        · intro key result member
          rcases mem_reanchorRows.mp member with oldMember | ⟨rfl, oldMember⟩
          · exact origin.2 key result oldMember
          · exact bodyLaws.move (RecipeResourceDependency.inputsView closed forward)
              (origin.2 _ result oldMember)
      · exact origin
  | _ + 2, _, _, .commutePadFn _ _ =>
    exact rankShift domainLaws bodyLaws closed dependency.down
  | _ + 2, _, _, .uncommutePadFn key _ =>
    exact (unshift domainLaws bodyLaws closed key formed dependency).pad
  | _ + 1, _, _, .fn wanted child =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := dependency old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      have typed := Profile.HasType.pi_iff.mp (formed.singleton_of_mem present)
      refine ⟨origin.1, ?_⟩
      intro key result member
      rcases mem_outputRows.mp member with oldMember | ⟨rfl, oldResult, oldMember, rfl⟩
      · exact origin.2 key result oldMember
      · exact bodyLaws.code (Valuation.push_atomized_closed closed _) (.map child)
          (typed.2 _ oldResult oldMember) (origin.2 _ oldResult oldMember)
  | _ + 1, _, _, .pad child =>
    exact (RecipePiProfileDependency.map child closed
      (by simpa only [Profile.down_sort] using formed.down) dependency.down).pad
  | _, _, _, .trans first second =>
    exact RecipePiProfileDependency.map second closed (first.mapType_sort formed)
      (RecipePiProfileDependency.map first closed formed dependency)
termination_by sizeOf change

include domainLaws bodyLaws in
theorem support
    (action : SupportAction env U registry target n)
    (closed : available.AtomClosed) (formed : profile.HasType (.sort relevant))
    (dependency : RecipePiProfileDependency domain body profile available) :
    RecipePiProfileDependency domain body (action.apply profile) available := by
  induction action with
  | id => exact dependency
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, dependency.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change => exact map domainLaws bodyLaws change closed formed dependency
  | output wanted child ih =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := dependency old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      have typed := Profile.HasType.pi_iff.mp (formed.singleton_of_mem present)
      refine ⟨origin.1, ?_⟩
      intro key result member
      rcases mem_outputRows.mp member with oldMember | ⟨rfl, oldResult, oldMember, rfl⟩
      · exact origin.2 key result oldMember
      · exact bodyLaws.code (Valuation.push_atomized_closed closed _) (.support child)
          (typed.2 _ oldResult oldMember) (origin.2 _ oldResult oldMember)
  | pad child ih =>
    exact (ih (by simpa only [Profile.down_sort] using formed.down) dependency.down).pad
  | comp first second firstIH secondIH =>
    exact secondIH (first.preservesSort formed) (firstIH formed dependency)
  | union first second firstIH secondIH =>
    exact union (firstIH formed dependency) (secondIH formed dependency)

include domainLaws bodyLaws in
theorem code
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (closed : available.AtomClosed) (formed : profile.HasType (.sort flag))
    (dependency : RecipePiProfileDependency domain body profile available) :
    RecipePiProfileDependency domain body nextProfile available := by
  induction action with
  | id | retag => exact dependency
  | comp first second firstIH secondIH =>
    exact secondIH (first.preservesSort formed) (firstIH formed dependency)
  | union first second firstIH secondIH =>
    exact union (firstIH formed dependency) (secondIH formed dependency)
  | pad => exact dependency.pad
  | down => exact dependency.down
  | unpad => exact dependency.unpad
  | sortPad => exact False.elim dependency.not_sort
  | familyPad => exact False.elim (dependency _ List.mem_cons_self)
  | map change => exact map domainLaws bodyLaws change closed formed dependency
  | support action => exact support domainLaws bodyLaws action closed formed dependency
  | select member => exact dependency.select member
  | focusMinimal minimal bound => exact focusMinimal domainLaws bodyLaws minimal closed bound formed dependency

private theorem atomView
    {domain body : {n : Nat} → Profile n → Valuation → Prop}
    {a b : Atom n} (change : AtomView env U registry target a b)
    (dependency : RecipePiDependency domain body available a) :
    RecipePiDependency domain body available b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact dependency
  | _ + 1, _, _, .reanchor _ => cases dependency
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases dependency
  | _ + 1, _, _, .input _ _ => cases dependency
  | _ + 2, _, _, .commutePadFn _ _ => cases dependency
  | _ + 2, _, _, .uncommutePadFn _ _ => cases dependency
  | _ + 1, _, _, .fn _ _ => cases dependency
  | k + 1, _, _, .pad child => exact atomView (n := k) child dependency
  | _, _, _, .trans first second => exact atomView second (atomView first dependency)
termination_by sizeOf change

include domainLaws bodyLaws in
theorem atomAction {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (closed : available.AtomClosed)
    (dependency : RecipePiDependency domain body available a) :
    RecipePiDependency domain body available b := by
  induction action with
  | view change => exact atomView change dependency
  | @code relevant rank a next b action formed =>
    have inputs : RecipePiProfileDependency domain body (.singleton a) available := by
      intro atom member
      cases List.mem_singleton.mp member
      exact dependency
    exact code domainLaws bodyLaws action closed formed inputs _ List.mem_cons_self
  | fn => cases dependency
  | pad child ih => exact ih dependency
  | comp first second firstIH secondIH => exact secondIH (firstIH dependency)

end RecipePiProfileDependency

/-- All finite action laws hold for the actual syntactic dependency model.
The recursion is on the original raw expression, independently of semantic
F calls and of any changed row anchor. -/
theorem RecipeDependencyProfile.laws
    (expression : VExpr) :
    RecipeDependencyLaws env U registry target
      (RecipeDependencyProfile env U registry target expression) := by
  induction expression with
  | bvar index =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [RecipeDependencyProfile]
    · exact ⟨[], ⟨.legacy .empty⟩, fun _ _ member => by cases member⟩
    · exact RecipeVariableDependency.union
    · exact RecipeVariableDependency.select
    · intro n p available dependency
      obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
      exact ⟨fp, ⟨.pad trace⟩, resources⟩
    · intro n p available dependency
      obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
      exact ⟨fp, ⟨.unpad trace⟩, resources⟩
    · intro n m relevant next p q available closed action formed dependency
      obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
      exact ⟨fp, ⟨.code trace action formed⟩, resources⟩
    · intro n a b available closed action dependency
      obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
      exact ⟨fp, ⟨.action trace action⟩, resources⟩
    · intro n p first second replacement dependency
      exact RecipeVariableDependency.transport dependency replacement
  | forallE A B domainIH bodyIH =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [RecipeDependencyProfile]
    · exact RecipePiProfileDependency.empty
    · exact RecipePiProfileDependency.union
    · intro n p atom available closed dependency member
      exact RecipePiProfileDependency.select dependency member
    · exact RecipePiProfileDependency.pad
    · exact RecipePiProfileDependency.unpad
    · intro n m relevant next p q available closed action formed dependency
      exact RecipePiProfileDependency.code domainIH bodyIH action closed formed dependency
    · intro n a b available closed action dependency atom member
      cases List.mem_singleton.mp member
      exact RecipePiProfileDependency.atomAction domainIH bodyIH action closed
        (dependency a List.mem_cons_self)
    · intro n p first second replacement dependency
      intro atom member
      exact RecipePiDependency.transport domainIH.move bodyIH.move replacement (dependency atom member)
  | _ =>
    constructor <;> intros <;> simp only [RecipeDependencyProfile]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
