import Lean4Lean.Theory.Typing.AnchoredProofDropFunction
import Lean4Lean.Theory.Typing.AnchoredProofDropZero
import Lean4Lean.Theory.Typing.AnchoredConstructorDrop
import Lean4Lean.Theory.Typing.AnchoredRecordDrop

/-! The rank successor of proof DROP. The only unclosed input in this module
is the concrete RAW paired-display projection; all semantic calls either use
the strictly lower rank or the code theorem proved before the term theorem. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

/-- The remaining raw producer, stated separately so its absence cannot be
mistaken for a completed semantic contraction theorem. -/
def RawPiDropAt (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (n : Nat) : Prop :=
  ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
    ProofInsertion env U Γ Δ frame.liftMap →
    ∀ {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
      (display : PiWitness env U registry (relations env U registry n) Δ left right
        (A.lift' frame.liftMap) (B.lift' frame.liftMap.cons)
        (domain.rename frame.liftMap) (Rows.rename frame.liftMap rows)),
      Nonempty (ProofDropPiProjection env U registry frame display)

theorem TypeRelated.drop_succ
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (project : RawPiDropAt env U registry n)
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
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right : VExpr} {profile : Profile (n + 1)}
    (H : TypeRelated env U registry Δ left right (profile.rename frame.liftMap)) :
    TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile := by
  intro V τ future atom member
  obtain ⟨base, baseMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
    frame.pushoutChosen insertion future henv
  subst i
  have original := H W j largerFuture
    ((base.rename τ).rename next.liftMap) (by
      rw [← Atom.rename_comp, ← square, Atom.rename_comp]
      exact List.mem_map_of_mem (List.mem_map_of_mem baseMember))
  have commute (e : VExpr) : (e.lift' j).subst next.retract = (e.subst frame.retract).lift' τ := by
    rw [subst_lift', nextRetract, lift'_subst]
  cases base with
  | sort flag =>
    have dropped := SortRelated.drop henv hscoped next original
    simpa only [commute, CodeAtom, Atom.rename, TypeRelated] using dropped
  | fn | ctor | record => exact original.elim
  | family demand =>
    obtain ⟨large⟩ := original
    have large' : RankedData.FamilyWitness env U registry (relations env U registry n) W
        (left.lift' j) (right.lift' j) ((demand.rename τ).rename next.liftMap) := large
    obtain ⟨small⟩ := large'.drop henv hscoped ⟨lowerCode, lowerTerm⟩ next proof
    change Nonempty (RankedData.FamilyWitness env U registry (relations env U registry n) V
      ((left.subst frame.retract).lift' τ) ((right.subst frame.retract).lift' τ) (demand.rename τ))
    exact ⟨by simpa only [commute] using small⟩
  | pi A B domain rows =>
    obtain ⟨large⟩ := original
    obtain ⟨projection⟩ := project next proof large
    have small := projection.display henv lowerCode
    exact ⟨by simpa only [commute] using small⟩
  | pad atom =>
    have original' : TypeRelated env U registry W (left.lift' j) (right.lift' j)
        ((Profile.singleton (atom.rename τ)).rename next.liftMap) := by
      simpa only [Profile.rename_singleton, Atom.rename, CodeAtom, TypeRelated] using original
    have dropped := lowerCode next proof original'
    simpa only [commute, CodeAtom, Atom.rename, TypeRelated] using dropped

theorem CoreRelated.drop_succ
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (project : RawPiDropAt env U registry n)
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
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right type : VExpr} {value support : Profile (n + 1)}
    (H : CoreRelated env U registry Δ left right type
      (value.rename frame.liftMap) (support.rename frame.liftMap)) :
    CoreRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
      (type.subst frame.retract) value support := by
  have typed := Profile.rename_hasType_iff.mp H.1
  refine ⟨typed, H.2.1.drop_succ henv hscoped project lowerCode lowerTerm frame insertion, ?_⟩
  intro atom member
  have original := H.2.2 (atom.rename frame.liftMap) (List.mem_map_of_mem member)
  cases atom with
  | fn key output =>
    exact FunctionBehavior.dropWith henv hscoped lowerCode lowerTerm frame insertion
      (fun display => project frame insertion display) (typed.singleton_of_mem member)
      H.2.1 original
  | pad atom =>
    have original' : Related env U registry Δ left right type
        ((Profile.singleton atom).rename frame.liftMap) (support.down.rename frame.liftMap) := by
      simpa only [Profile.rename_singleton, Profile.down_rename, Atom.rename, TermAtom, Related] using original
    exact lowerTerm frame insertion original'
  | sort flag =>
    have original' : TypeRelated env U registry Δ left right
        ((Profile.sort (n := n + 1) flag).rename frame.liftMap) := by
      rw [Profile.rename_sort]
      exact original
    exact original'.drop_succ henv hscoped project lowerCode lowerTerm frame insertion
  | family demand =>
    have original' : TypeRelated env U registry Δ left right
        ((Profile.singleton (n := n + 1) (.family demand)).rename frame.liftMap) := original
    exact original'.drop_succ henv hscoped project lowerCode lowerTerm frame insertion
  | ctor demand =>
    exact RankedData.ConstructorRelation.drop henv hscoped ⟨lowerCode, lowerTerm⟩ frame insertion original
  | record demand =>
    exact RankedData.RecordRelation.drop henv hscoped ⟨lowerCode, lowerTerm⟩ frame insertion original
  | pi A B domain rows =>
    have original' : TypeRelated env U registry Δ left right
        ((Profile.pi A B domain rows).rename frame.liftMap) := by
      simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, TermAtom, TypeRelated, relations] using original
    exact original'.drop_succ henv hscoped project lowerCode lowerTerm frame insertion

end Lean4Lean.AnchoredSemantics
