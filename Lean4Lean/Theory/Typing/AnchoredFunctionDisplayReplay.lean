import Lean4Lean.Theory.Typing.AnchoredLiteralFunctionDisplay
import Lean4Lean.Theory.Typing.AnchoredFunctionSeed

/-! Replay a function capability through a fixed concrete row display.
Canonical trace synchronization and inhabited-frame absorption keep the
selected codomain and result support fixed across repeated RHS evaluations. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Proof saturation changes the source world, while preserving every private
component of the chosen display literally. -/
noncomputable def PiWitness.absorbLiteral
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (W : PiWitness env U registry lower Δ (left.lift' ρ) (right.lift' ρ)
      (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows)) :
    PiWitness env U registry lower Γ left right A B domain rows := by
  let leftExposure := Classical.choice (W.leftExposure.absorb henv hscoped I)
  let rightExposure := Classical.choice (W.rightExposure.absorb henv hscoped I)
  refine {
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
    rowBodies := ?_ }
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

/-- A function's arbitrary chosen display can be replaced by the actual
display retained in a finite application path. -/
theorem FunctionBehavior.atDisplay
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {oldTypeProfile : Profile (n + 1)}
    {newA newB : VExpr} {newDom newResult : Profile n} {newRows : List (Key n × Profile n)}
    (henv : env.Ordered)
    (newDisplay : PiWitness env U registry (relations env U registry n)
      Γ type type newA newB newDom newRows)
    (newRow : (key, newResult) ∈ newRows)
    (newTyped : (Profile.singleton output).HasType newResult)
    (hold : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output oldTypeProfile) :
    FunctionRowBehavior env U registry Γ left right type key output newResult newDisplay := by
  obtain ⟨_, oldA, oldB, oldDom, oldRows, oldResult, _, oldRow, oldTyped,
    oldDisplay, oldBehavior⟩ := hold
  intro V τ future x y admitted
  obtain ⟨C, i, j, oldInsertion, newInsertion, hmaps, _, hbodies⟩ :=
    oldDisplay.leftExposure.samePi newDisplay.leftExposure henv
  obtain ⟨W, α, β, proof, extension, hpush⟩ := newInsertion.pushout future henv
  obtain ⟨oldW, oldFuture, changed⟩ := oldInsertion.pullFuture henv extension
  have hmap : oldDisplay.map.comp (i.comp β) = (newDisplay.map.comp τ).comp α := by
    rw [← Lift.comp_assoc, hmaps, Lift.comp_assoc, hpush, ← Lift.comp_assoc]
  have hbody : oldDisplay.leftBody.lift' (i.comp β).cons =
      newDisplay.leftBody.lift' (τ.comp α).cons := by
    calc
      _ = (oldDisplay.leftBody.lift' i.cons).lift' β.cons := lift'_comp
      _ = (newDisplay.leftBody.lift' j.cons).lift' β.cons := congrArg (·.lift' β.cons) hbodies
      _ = newDisplay.leftBody.lift' (j.comp β).cons := lift'_comp.symm
      _ = _ := congrArg (fun ρ => newDisplay.leftBody.lift' ρ.cons) hpush
  have htype : (oldDisplay.leftBody.lift' (i.comp β).cons).inst (x.lift' α) =
      ((newDisplay.leftBody.lift' τ.cons).inst x).lift' α := by
    rw [hbody, lift'_inst_hi, ← lift'_comp]
    rfl
  have harg : Admitted env U registry W (key.rename (oldDisplay.map.comp (i.comp β)))
      (x.lift' α) (y.lift' α) := by
    simpa only [← Key.rename_comp, hmap] using
      proof.admitted henv admitted
  have oldArg := (changed.symm henv).admitted henv harg
  obtain ⟨oldLeft, oldRight, oldCross⟩ :=
    oldBehavior oldW (i.comp β) oldFuture (x.lift' α) (y.lift' α) oldArg
  have oldOutputs := And.intro (changed.term henv oldLeft)
    (And.intro (changed.term henv oldRight) (changed.term henv oldCross))
  have newCode : TypeRelated env U registry W
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      (((newDisplay.leftBody.lift' τ.cons).inst x).lift' α)
      ((newResult.rename (newDisplay.map.comp τ)).rename α) :=
    proof.code henv (TypeRelated.left_diagonal
      (newDisplay.rowBodies key newResult newRow V τ future x y admitted).1)
  have newValueTyped := (Profile.rename_hasType_iff
    (ρ := (newDisplay.map.comp τ).comp α)).mpr newTyped
  simp only [Profile.rename_singleton] at newValueTyped
  simp only [hmap, htype] at oldOutputs
  rw [← Profile.rename_comp] at newCode
  obtain ⟨hleft, hright, hpair⟩ := oldOutputs
  have hleft' := Related.retag henv newValueTyped newCode hleft
  have hright' := Related.retag henv newValueTyped newCode hright
  have hpair' := Related.retag henv newValueTyped newCode hpair
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hleft'
  constructor
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hright'
  · apply proof.termBack henv
    simpa only [lift', ← lift'_comp, Profile.rename_singleton,
      ← Atom.rename_comp, ← Profile.rename_comp] using hpair'


/-- Function atoms admit a concrete base-world behavior.  This does not
retract private domain syntax: the inhabited insertion is moved into each
exposure and the full composite map is retained. -/
theorem Related.functionBehavior
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type (.fn key output) support) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output support := by
  have seed := related.fn_seed henv hscoped hΓ
  have base := related (.fn key output) (List.mem_singleton_self _)
    Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at base
  rcases base with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn (key.rename ρ) (output.rename ρ))
      (List.mem_singleton_self _)
    obtain ⟨_, A, B, domain, rows, result, cover, row, typed, display, applyRow⟩ := behavior
    obtain ⟨atom, baseCover, same⟩ := List.mem_map.mp cover
    cases atom with
    | sort | fn | pad | family | ctor | record => cases same
    | pi baseA baseB baseDomain baseRows =>
      simp only [Atom.rename_pi] at same
      cases same
      obtain ⟨⟨baseKey, baseResult⟩, baseRow, rowEq⟩ := List.mem_map.mp row
      have sameKey : baseKey = key := Key.rename_inj.mp (Prod.mk.inj rowEq).1
      subst baseKey
      have sameResult := (Prod.mk.inj rowEq).2
      subst result
      let restored := display.absorbLiteral henv hscoped insertion
      refine ⟨seed, baseA, baseB, baseDomain, baseRows, baseResult, baseCover, baseRow, ?_, restored, ?_⟩
      · apply (Profile.rename_hasType_iff (ρ := ρ)).mp
        simpa only [Profile.rename_singleton] using typed
      · intro Ω τ future x y admitted
        have admitted' : Admitted env U registry Ω
            ((key.rename ρ).rename (display.map.comp τ)) x y := by
          simpa only [restored, PiWitness.absorbLiteral, Admitted, Key.rename_comp,
            Lift.comp_assoc] using admitted
        have outputs := applyRow Ω τ future x y admitted'
        simpa only [restored, PiWitness.absorbLiteral, lift'_comp,
          Atom.rename_comp, Profile.rename_comp, Lift.comp_assoc] using outputs

/-- Replay an arbitrary semantic proof at the concrete row selected earlier.
The conclusion is independent of the proof's saturation frame and type support. -/
theorem Related.atDisplay
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)} {result : Profile n}
    {A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (display : PiWitness env U registry (relations env U registry n)
      Γ type type A B domain rows)
    (row : (key, result) ∈ rows)
    (typed : (Profile.singleton output).HasType result)
    (related : Related env U registry Γ left right type (.fn key output) support) :
    FunctionRowBehavior env U registry Γ left right type key output result display :=
  FunctionBehavior.atDisplay henv display row typed
    (related.functionBehavior henv hscoped hΓ)

end Lean4Lean.AnchoredSemantics
