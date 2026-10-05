import Lean4Lean.Theory.Typing.AnchoredFrame
import Lean4Lean.Theory.Typing.AnchoredExposureTransport
import Lean4Lean.Theory.Typing.CanonicalTraceReflection

/-! Absorption of an inhabited proof insertion by canonical exposures.
Only the generated front telescope is reconstructed at the original base.
The final private display context and all of its components remain unchanged. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

private theorem proofSkip_inv
    {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {ρ : Lift} {P : VExpr}
    (H : ProofInsertion env U Γ (P :: Δ) ρ.skip) :
    ∃ q, ProofInsertion env U Γ Δ ρ ∧
      env.HasType U Δ P (.sort .zero) ∧ env.HasType U Δ q P := by
  cases H with
  | skip previous hP hq => exact ⟨_, previous, hP, hq⟩

/-- Pull back only the literally renamed generated front. The second leg
retains every reconstructed front binder and inserts the old base proofs. -/
theorem ProofInsertion.unrenameFront
    {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {ρ : Lift}
    (added : List VExpr) (I : ProofInsertion env U Γ Δ ρ)
    (H : ProofInsertion env U Δ (renameAdded ρ added ++ Δ)
      (.skipN .refl added.length)) (henv : env.Ordered) :
    ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length) ∧
    ProofInsertion env U (added ++ Γ) (renameAdded ρ added ++ Δ)
      (ρ.consN added.length) := by
  induction added with
  | nil => exact ⟨.refl I.baseWF, I⟩
  | cons P rest ih =>
    change ProofInsertion env U Δ
      (P.lift' (ρ.consN rest.length) :: (renameAdded ρ rest ++ Δ))
      (.skip (.skipN .refl rest.length)) at H
    obtain ⟨q, previous, hP, hq⟩ := proofSkip_inv H
    obtain ⟨front, retained⟩ := ih previous
    obtain ⟨F, hF⟩ := retained.toEmbedding henv
    have hP' : env.HasType U (rest ++ Γ) P (.sort .zero) := by
      have hp := hP.subst henv F.typed F.baseWF
      simpa only [← hF, F.leftInv, subst] using hp
    have hq' := hq.subst henv F.typed F.baseWF
    have hdomain : (P.lift' (ρ.consN rest.length)).subst F.retract = P := by
      rw [← hF, F.leftInv]
    rw [hdomain] at hq'
    exact ⟨front.skip hP' hq', retained.cons hP'⟩

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- Absorb a witnessed insertion at an exposure's source, retaining exactly
its final context and head. No private component is retracted. -/
theorem Exposure.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {ρ map : Lift} {expression head : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (E : Exposure env U registry Δ (expression.lift' ρ) Ω map head) :
    Nonempty (Exposure env U registry Γ expression Ω (ρ.comp map) head) := by
  obtain ⟨added, result, trace, ha, hr⟩ := E.trace.unrename hscoped
  have generated : ProofInsertion env U Δ (renameAdded ρ added ++ Δ)
      (.skipN .refl added.length) := by
    simpa only [ha, renameAdded_length] using E.generated
  obtain ⟨front, retained⟩ := ProofInsertion.unrenameFront added I generated henv
  refine ⟨{
    added := added
    result := result
    postMap := (ρ.consN added.length).comp E.postMap
    trace := trace
    generated := front
    postContext := E.postContext
    post := ?_
    terminal := E.terminal
    map_eq := ?_
    result_eq := ?_
    sound := ?_
    headType := E.headType }⟩
  · exact retained.comp (ha ▸ E.post) henv
  · rw [← Lift.comp_assoc, Lift.skipN_comp_consN, Lift.refl_comp]
    have hm := congrArg (ρ.comp ·) E.map_eq
    simpa only [ha, renameAdded_length, ← Lift.comp_assoc, Lift.comp_skipN, Lift.comp] using hm
  · simpa only [lift'_comp, ← hr] using E.result_eq
  · simpa only [lift'_comp] using E.sound

/-- The private Pi display is retained literally; only its source exposures
and the composite map change. -/
theorem PiWitness.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (W : PiWitness env U registry lower Δ (left.lift' ρ) (right.lift' ρ)
      (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows)) :
    Nonempty (PiWitness env U registry lower Γ left right A B domain rows) := by
  obtain ⟨leftExposure⟩ := W.leftExposure.absorb henv hscoped I
  obtain ⟨rightExposure⟩ := W.rightExposure.absorb henv hscoped I
  refine ⟨{
    context := W.context
    map := ρ.comp W.map
    leftDomain := W.leftDomain
    leftBody := W.leftBody
    rightDomain := W.rightDomain
    rightBody := W.rightBody
    leftExposure := leftExposure
    rightExposure := rightExposure
    leftDomainType := W.leftDomainType
    rightDomainType := W.rightDomainType
    leftBodyType := W.leftBodyType
    rightBodyType := W.rightBodyType
    domains := W.domains
    bodies := W.bodies
    prototypeDomainPath := ?_
    prototypeBodyPath := ?_
    domainRelated := ?_
    rowDomains := ?_
    rowBodies := ?_ }⟩
  · simpa only [lift'_comp] using W.prototypeDomainPath
  · simpa only [show (ρ.comp W.map).cons = ρ.cons.comp W.map.cons from rfl,
      lift'_comp] using W.prototypeBodyPath
  · simpa only [Profile.rename_comp] using W.domainRelated
  · intro key output hmem
    have hw := W.rowDomains (key.rename ρ) (output.rename ρ)
      (List.mem_map.mpr ⟨(key, output), hmem, rfl⟩)
    simpa only [Key.rename_comp, Profile.rename_comp, Key.rename, ← lift'_comp] using hw
  · intro key output hmem Ω τ future x y admitted
    have hw := W.rowBodies (key.rename ρ) (output.rename ρ)
      (List.mem_map.mpr ⟨(key, output), hmem, rfl⟩) Ω τ future x y
    have ha : Admission env U lower Ω (Key.rename (W.map.comp τ) (Key.rename ρ key)) x y := by
      simpa only [Key.rename_comp, Lift.comp_assoc] using admitted
    simpa only [Profile.rename_comp, Lift.comp_assoc] using hw ha

private theorem SortRelated.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right : VExpr} {relevant : Bool}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (H : SortRelated env U registry Δ (left.lift' ρ) (right.lift' ρ) relevant) :
    SortRelated env U registry Γ left right relevant := by
  obtain ⟨Ω, τ, u, v, ⟨hl⟩, ⟨hr⟩, huv, hu⟩ := H
  exact ⟨Ω, ρ.comp τ, u, v, hl.absorb henv hscoped I,
    hr.absorb henv hscoped I, huv, hu⟩

/-- A term display absorbs only a lifted source and assigned type. Its
actual terminal world and all private constructor arguments stay fixed. -/
theorem ConstructorExposure.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {ρ map : Lift} {expression type head : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (E : ConstructorExposure env U registry Δ (expression.lift' ρ) (type.lift' ρ) Ω map head) :
    Nonempty (ConstructorExposure env U registry Γ expression type Ω (ρ.comp map) head) := by
  obtain ⟨added, result, trace, ha, hr⟩ := E.trace.unrename hscoped
  have generated : ProofInsertion env U Δ (renameAdded ρ added ++ Δ)
      (.skipN .refl added.length) := by
    simpa only [ha, renameAdded_length] using E.generated
  obtain ⟨front, retained⟩ := ProofInsertion.unrenameFront added I generated henv
  refine ⟨{
    added := added
    result := result
    postMap := (ρ.consN added.length).comp E.postMap
    trace := trace
    generated := front
    postContext := E.postContext
    post := retained.comp (ha ▸ E.post) henv
    terminal := E.terminal
    map_eq := ?_
    result_eq := ?_
    sound := ?_ }⟩
  · rw [← Lift.comp_assoc, Lift.skipN_comp_consN, Lift.refl_comp]
    have hm := congrArg (ρ.comp ·) E.map_eq
    simpa only [ha, renameAdded_length, ← Lift.comp_assoc, Lift.comp_skipN, Lift.comp] using hm
  · simpa only [lift'_comp, ← hr] using E.result_eq
  · simpa only [lift'_comp] using E.sound

theorem RankedData.FamilyWitness.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right : VExpr} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (W : RankedData.FamilyWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (demand.rename ρ)) :
    Nonempty (RankedData.FamilyWitness env U registry lower Γ left right demand) := by
  obtain ⟨leftExposure⟩ := W.leftExposure.absorb henv hscoped I
  obtain ⟨rightExposure⟩ := W.rightExposure.absorb henv hscoped I
  refine ⟨{
    registryScoped := W.registryScoped
    headInert := W.headInert
    context := W.context
    map := ρ.comp W.map
    leftLevel := W.leftLevel
    rightLevel := W.rightLevel
    leftRelevance := W.leftRelevance
    rightRelevance := W.rightRelevance
    path := ?_
    leftType := ?_
    rightType := ?_
    leftLevels := W.leftLevels
    rightLevels := W.rightLevels
    leftArguments := W.leftArguments
    rightArguments := W.rightArguments
    leftExposure := leftExposure
    rightExposure := rightExposure
    leftTerminal := W.leftTerminal
    rightTerminal := W.rightTerminal
    leftUniverses := W.leftUniverses
    rightUniverses := W.rightUniverses
    arguments := ?_ }⟩
  · simpa only [lift'_comp] using W.path
  · simpa only [FamilyData.rename, FamilyData.map] using W.leftType
  · simpa only [FamilyData.rename, FamilyData.map] using W.rightType
  · have arguments := W.arguments
    change RankedData.Arguments env U lower W.context
      ((demand.arguments.map (DataRequest.rename ρ)).map (DataRequest.rename W.map))
      W.leftArguments W.rightArguments at arguments
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using arguments

theorem RankedData.FamilyRelation.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right : VExpr} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (H : RankedData.FamilyRelation env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (demand.rename ρ)) :
    RankedData.FamilyRelation env U registry lower Γ left right demand := by
  intro Ω τ future
  obtain ⟨V, i, j, hi, hj, he⟩ := I.pushout future henv
  obtain ⟨W⟩ := H V j hj
  have typed : RankedData.FamilyWitness env U registry lower V
      ((left.lift' τ).lift' i) ((right.lift' τ).lift' i) ((demand.rename τ).rename i) := by
    simpa only [← lift'_comp, FamilyData.rename_comp, he] using W
  exact typed.absorb henv hscoped hi

/-- Code evidence absorbs generated inhabited proof insertions. All code
operands and the complete profile must be actual lifts from the base. -/
theorem TypeRelated.absorb
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right : VExpr} {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (H : TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ)
      (profile.rename ρ)) :
    TypeRelated env U registry Γ left right profile := by
  induction n generalizing Γ Δ ρ left right with
  | zero =>
    intro Ω τ future atom ha
    obtain ⟨V, i, j, hi, hj, he⟩ := I.pushout future henv
    have hc := H V j hj
    simp only [← lift'_comp, ← Profile.rename_comp] at hc
    rw [he] at hc
    simp only [lift'_comp, Profile.rename_comp] at hc
    have ham : atom ∈ ((profile.rename τ).rename i).atoms := by
      simpa [Profile.rename, Profile.atoms, Atom.rename] using ha
    exact SortRelated.absorb henv hscoped hi (hc atom ham)
  | succ n ih =>
    intro Ω τ future atom ha
    obtain ⟨V, i, j, hi, hj, he⟩ := I.pushout future henv
    have hc := H V j hj
    simp only [← lift'_comp, ← Profile.rename_comp] at hc
    rw [he] at hc
    simp only [lift'_comp, Profile.rename_comp] at hc
    have ham : atom.rename i ∈ ((profile.rename τ).rename i).atoms :=
      List.mem_map.mpr ⟨atom, ha, rfl⟩
    have h := hc (atom.rename i) ham
    cases atom with
    | sort relevant => exact SortRelated.absorb henv hscoped hi h
    | fn key output => exact False.elim h
    | ctor _ | record _ => exact False.elim h
    | family demand =>
      obtain ⟨witness⟩ := h
      exact witness.absorb henv hscoped hi
    | pi A B domain rows =>
      obtain ⟨display⟩ := h
      exact display.absorb henv hscoped hi
    | pad atom =>
      change TypeRelated env U registry V ((left.lift' τ).lift' i)
        ((right.lift' τ).lift' i) (.singleton (atom.rename i)) at h
      rw [← Profile.rename_singleton] at h
      exact ih hi h

end Lean4Lean.AnchoredSemantics
