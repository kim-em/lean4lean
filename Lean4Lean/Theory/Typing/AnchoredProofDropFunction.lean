import Lean4Lean.Theory.Typing.AnchoredProofDropPi
import Lean4Lean.Theory.Typing.AnchoredCoreIntroduction
import Lean4Lean.Theory.Typing.AnchoredFramedFunctionSeed

/-! Combine the raw projected display and the two strictly lower-rank DROP
steps. The projection package contains syntax, typed frames and literal
commuting equations only. Its concrete producer remains separate. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure ProofDropPiProjection
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {Γsmall Γlarge : List VExpr} (initial : SplitTypedEmbedding env U Γsmall Γlarge)
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge left right (A.lift' initial.liftMap) (B.lift' initial.liftMap.cons)
      (domain.rename initial.liftMap) (Rows.rename initial.liftMap rows)) where
  raw : RawPiDisplay env U registry Γsmall
    (left.subst initial.retract) (right.subst initial.retract) A B
  frame : ProofDropPiFrame env U registry initial.liftMap raw large
  futures : ∀ Δ ρ, FutureInsertion env U raw.context Δ ρ →
    Nonempty { square : ProofDropPiFuture env U registry initial.liftMap raw large Δ ρ //
      ∀ expression : VExpr,
        (expression.lift' (large.map.comp square.oldMap)).subst square.frame.retract =
          (expression.subst initial.retract).lift' (raw.map.comp ρ) }

noncomputable def ProofDropPiProjection.display
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lowerDrop : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right : VExpr} {profile : Profile n},
        TypeRelated env U registry Δ left right (profile.rename frame.liftMap) →
        TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile)
    {Γsmall Γlarge : List VExpr} {initial : SplitTypedEmbedding env U Γsmall Γlarge}
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    {large : PiWitness env U registry (relations env U registry n)
      Γlarge left right (A.lift' initial.liftMap) (B.lift' initial.liftMap.cons)
      (domain.rename initial.liftMap) (Rows.rename initial.liftMap rows)}
    (projection : ProofDropPiProjection env U registry initial large) :
    PiWitness env U registry (relations env U registry n) Γsmall
      (left.subst initial.retract) (right.subst initial.retract) A B domain rows :=
  large.dropWith henv lowerDrop projection.raw projection.frame
    (fun Δ ρ future => let ⟨square⟩ := projection.futures Δ ρ future; ⟨square.val⟩)

/-- Recover the base key from the actual old core and rebuild the same covering
row. All dependent application calls are to the strictly lower term DROP. -/
theorem FunctionBehavior.dropWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lowerCode : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right : VExpr} {profile : Profile n},
        TypeRelated env U registry Δ left right (profile.rename frame.liftMap) →
        TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile)
    (lowerTerm : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right type : VExpr} {value support : Profile n},
        Related env U registry Δ left right type
          (value.rename frame.liftMap) (support.rename frame.liftMap) →
        Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
          (type.subst frame.retract) value support)
    {Γsmall Γlarge : List VExpr} (initial : SplitTypedEmbedding env U Γsmall Γlarge)
    (insertion : ProofInsertion env U Γsmall Γlarge initial.liftMap)
    {left right type : VExpr} {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (project : ∀ {A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
      (large : PiWitness env U registry (relations env U registry n)
        Γlarge type type (A.lift' initial.liftMap) (B.lift' initial.liftMap.cons)
        (domain.rename initial.liftMap) (Rows.rename initial.liftMap rows)),
      Nonempty (ProofDropPiProjection env U registry initial large))
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry Γlarge type type (support.rename initial.liftMap))
    (old : FunctionBehavior env U registry (relations env U registry n)
      Γlarge left right type (key.rename initial.liftMap) (output.rename initial.liftMap)
      (support.rename initial.liftMap)) :
    FunctionBehavior env U registry (relations env U registry n)
      Γsmall (left.subst initial.retract) (right.subst initial.retract)
      (type.subst initial.retract) key output support := by
  have core : CoreRelated env U registry Γlarge left right type
      ((Profile.fn key output).rename initial.liftMap) (support.rename initial.liftMap) := by
    refine ⟨Profile.rename_hasType_iff.mpr typed, code, ?_⟩
    intro atom member
    have eq : atom = AtomData.fn (key.rename initial.liftMap) (output.rename initial.liftMap) :=
      List.mem_singleton.mp member
    subst atom
    exact old
  have related := core.related henv hscoped
  have seed := Related.fn_seed_inFrame henv hscoped insertion (by
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] using related)
  obtain ⟨_, A', B', domain', rows', result', member, row, resultTyped, large, behavior⟩ := old
  obtain ⟨baseAtom, baseMember, atomEq⟩ := List.mem_map.mp member
  cases baseAtom with
  | sort flag => cases atomEq
  | fn k o => cases atomEq
  | pad a => cases atomEq
  | family _ | ctor _ | record _ => cases atomEq
  | pi A B domain rows =>
    simp only [Atom.rename_pi] at atomEq
    cases atomEq
    obtain ⟨pair, rowMember, pairEq⟩ := List.mem_map.mp row
    rcases pair with ⟨oldKey, result⟩
    have keyEq : oldKey = key := Key.rename_inj.mp (Prod.mk.inj pairEq).1
    subst oldKey
    have resultEq := (Prod.mk.inj pairEq).2
    subst result'
    have resultTyped' : (Profile.singleton output).HasType result := by
      apply Profile.rename_hasType_iff.mp
      simpa only [Profile.rename_singleton] using resultTyped
    obtain ⟨projection⟩ := project large
    let small := projection.display henv lowerCode
    refine ⟨seed, A, B, domain, rows, result, baseMember, rowMember, resultTyped', small, ?_⟩
    apply FunctionRowBehavior.dropWith henv lowerTerm small large ?_ behavior
    intro Δ ρ future
    obtain ⟨⟨square, operands⟩⟩ := projection.futures Δ ρ future
    refine ⟨{
      oldWorld := square.oldWorld
      oldMap := square.oldMap
      oldFuture := square.oldFuture
      largerWorld := square.largeWorld
      contextChange := square.changed
      frame := square.frame
      insertion := square.insertion
      keys := ?_
      output := ?_
      support := ?_
      operands := operands
      body := square.leftBody }⟩
    · simp only [← Key.rename_comp, square.square]
      rfl
    · simp only [← Atom.rename_comp, square.square]
      rfl
    · simp only [← Profile.rename_comp, square.square]
      rfl

end Lean4Lean.AnchoredSemantics
