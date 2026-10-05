import Lean4Lean.Theory.Typing.AnchoredProofDropRow
import Lean4Lean.Theory.Typing.AnchoredProfileUnrenaming

/-! The Pi step of protected-profile proof contraction. Raw trace/frame
projection is explicit input to this intermediate constructor; no semantic
operation is hidden in that projection. The only semantic hypothesis is the
strictly smaller rank contraction theorem. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure RawPiDisplay (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right prototypeDomain prototypeBody : VExpr) where
  context : List VExpr
  map : Lift
  leftDomain : VExpr
  leftBody : VExpr
  rightDomain : VExpr
  rightBody : VExpr
  leftExposure : Exposure env U registry Γ left context map (.forallE leftDomain leftBody)
  rightExposure : Exposure env U registry Γ right context map (.forallE rightDomain rightBody)
  leftDomainType : env.IsType U context leftDomain
  rightDomainType : env.IsType U context rightDomain
  leftBodyType : env.IsType U (leftDomain :: context) leftBody
  rightBodyType : env.IsType U (rightDomain :: context) rightBody
  domains : TypeConversion env U context leftDomain rightDomain
  bodies : TypeConversion env U (leftDomain :: context) leftBody rightBody
  prototypeDomainPath : TypeConversion env U context leftDomain (prototypeDomain.lift' map)
  prototypeBodyPath : TypeConversion env U (leftDomain :: context)
    leftBody (prototypeBody.lift' map.cons)

structure ProofDropPiFrame
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {Γsmall Γlarge : List VExpr} {smallLeft smallRight largeLeft largeRight A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (initialMap : Lift)
    (small : RawPiDisplay env U registry Γsmall smallLeft smallRight A B)
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge largeLeft largeRight (A.lift' initialMap) (B.lift' initialMap.cons)
      (domain.rename initialMap) (Rows.rename initialMap rows)) where
  postWorld : List VExpr
  postMap : Lift
  post : FutureInsertion env U large.context postWorld postMap
  largeWorld : List VExpr
  changed : ContextChain env U postWorld largeWorld
  frame : SplitTypedEmbedding env U small.context largeWorld
  insertion : ProofInsertion env U small.context largeWorld frame.liftMap
  square : initialMap.comp (large.map.comp postMap) = small.map.comp frame.liftMap
  leftDomain : (large.leftDomain.lift' postMap).subst frame.retract = small.leftDomain
  rightDomain : (large.rightDomain.lift' postMap).subst frame.retract = small.rightDomain

structure ProofDropPiFuture
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {Γsmall Γlarge : List VExpr} {smallLeft smallRight largeLeft largeRight A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (initialMap : Lift)
    (small : RawPiDisplay env U registry Γsmall smallLeft smallRight A B)
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge largeLeft largeRight (A.lift' initialMap) (B.lift' initialMap.cons)
      (domain.rename initialMap) (Rows.rename initialMap rows))
    (Δ : List VExpr) (ρ : Lift) where
  oldWorld : List VExpr
  oldMap : Lift
  oldFuture : FutureInsertion env U large.context oldWorld oldMap
  largeWorld : List VExpr
  changed : ContextChain env U oldWorld largeWorld
  frame : SplitTypedEmbedding env U Δ largeWorld
  insertion : ProofInsertion env U Δ largeWorld frame.liftMap
  square : initialMap.comp (large.map.comp oldMap) = (small.map.comp ρ).comp frame.liftMap
  leftBody : (large.leftBody.lift' oldMap.cons).subst frame.retract.lift = small.leftBody.lift' ρ.cons
  rightBody : (large.rightBody.lift' oldMap.cons).subst frame.retract.lift = small.rightBody.lift' ρ.cons

/-- Rebuild the semantic Pi fields after an actual raw display projection. -/
noncomputable def PiWitness.dropWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lowerDrop : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right : VExpr} {profile : Profile n},
        TypeRelated env U registry Δ left right (profile.rename frame.liftMap) →
        TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile)
    {Γsmall Γlarge : List VExpr} {smallLeft smallRight largeLeft largeRight A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    {initialMap : Lift}
    (small : RawPiDisplay env U registry Γsmall smallLeft smallRight A B)
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge largeLeft largeRight (A.lift' initialMap) (B.lift' initialMap.cons)
      (domain.rename initialMap) (Rows.rename initialMap rows))
    (frame : ProofDropPiFrame env U registry initialMap small large)
    (futures : ∀ Δ ρ, FutureInsertion env U small.context Δ ρ →
      Nonempty (ProofDropPiFuture env U registry initialMap small large Δ ρ)) :
    PiWitness env U registry (relations env U registry n)
      Γsmall smallLeft smallRight A B domain rows where
  context := small.context
  map := small.map
  leftDomain := small.leftDomain
  leftBody := small.leftBody
  rightDomain := small.rightDomain
  rightBody := small.rightBody
  leftExposure := small.leftExposure
  rightExposure := small.rightExposure
  leftDomainType := small.leftDomainType
  rightDomainType := small.rightDomainType
  leftBodyType := small.leftBodyType
  rightBodyType := small.rightBodyType
  domains := small.domains
  bodies := small.bodies
  prototypeDomainPath := small.prototypeDomainPath
  prototypeBodyPath := small.prototypeBodyPath
  domainRelated := by
    have old := frame.changed.code henv (TypeRelated.future henv frame.post large.domainRelated)
    have old' : TypeRelated env U registry frame.largeWorld
        (large.leftDomain.lift' frame.postMap) (large.rightDomain.lift' frame.postMap)
        ((domain.rename small.map).rename frame.frame.liftMap) := by
      simpa only [← Profile.rename_comp, Lift.comp_assoc, frame.square] using old
    have dropped := lowerDrop frame.frame frame.insertion old'
    simpa only [TypeRelated, frame.leftDomain, frame.rightDomain] using dropped
  rowDomains := by
    intro key result row
    obtain ⟨support, typed, formed, bounded, path, code⟩ :=
      large.rowDomains (key.rename initialMap) (result.rename initialMap)
        (List.mem_map.mpr ⟨(key, result), row, rfl⟩)
    have bound' : support.rename frame.postMap ≤
        (domain.rename small.map).rename frame.frame.liftMap := by
      change Profile.LE _ _
      have old := (Profile.rename_le_iff (ρ := frame.postMap)).mpr bounded
      simpa only [← Profile.rename_comp, Lift.comp_assoc, frame.square] using old
    obtain ⟨baseSupport, baseEq, baseBound⟩ := Profile.unrename_le bound'
    have typed' : (key.rename small.map).input.HasType baseSupport := by
      apply (Profile.rename_hasType_iff (ρ := frame.frame.liftMap)).mp
      rw [baseEq]
      have old := (Profile.rename_hasType_iff (ρ := frame.postMap)).mpr typed
      simpa only [Key.rename, ← Profile.rename_comp, Lift.comp_assoc, frame.square] using old
    have formed' : baseSupport.HasType (.sort true) := by
      apply (Profile.rename_hasType_iff (ρ := frame.frame.liftMap)).mp
      rw [baseEq, Profile.rename_sort]
      simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := frame.postMap)).mpr formed
    have raw := frame.changed.path henv (path.weak' henv frame.post.weakening)
    have raw := raw.substTarget henv frame.frame.baseWF frame.frame.typed
    have leftEq : (((key.rename initialMap).domain.lift' large.map).lift' frame.postMap).subst
        frame.frame.retract = key.domain.lift' small.map := by
      simp only [Key.rename, ← lift'_comp, Lift.comp_assoc, frame.square]
      rw [lift'_comp, frame.frame.leftInv]
    have raw' : TypeConversion env U small.context (key.domain.lift' small.map) small.leftDomain := by
      simpa only [leftEq, frame.leftDomain] using raw
    have old := frame.changed.code henv (TypeRelated.future henv frame.post code)
    rw [← baseEq] at old
    have dropped := lowerDrop frame.frame frame.insertion old
    have code' : TypeRelated env U registry small.context
        (key.domain.lift' small.map) small.leftDomain baseSupport := by
      simpa only [leftEq, frame.leftDomain] using dropped
    exact ⟨baseSupport, typed', formed', baseBound, raw', code'⟩
  rowBodies := by
    intro key result row Δ ρ future x y admitted
    obtain ⟨square⟩ := futures Δ ρ future
    have lifted := Admitted.future henv square.insertion.toFuture admitted
    have oldAdmission : Admitted env U registry square.largeWorld
        ((key.rename initialMap).rename (large.map.comp square.oldMap))
        (x.lift' square.frame.liftMap) (y.lift' square.frame.liftMap) := by
      simpa only [← Key.rename_comp, square.square] using lifted
    obtain ⟨first, second, cross⟩ := large.rowBodies
      (key.rename initialMap) (result.rename initialMap)
      (List.mem_map.mpr ⟨(key, result), row, rfl⟩)
      square.oldWorld square.oldMap square.oldFuture
      (x.lift' square.frame.liftMap) (y.lift' square.frame.liftMap)
      ((square.changed.symm henv).admitted henv oldAdmission)
    have first := square.changed.code henv first
    have second := square.changed.code henv second
    have cross := square.changed.code henv cross
    have supports : (result.rename initialMap).rename (large.map.comp square.oldMap) =
        (result.rename (small.map.comp ρ)).rename square.frame.liftMap := by
      simp only [← Profile.rename_comp, square.square]
    rw [supports] at first second cross
    have first := lowerDrop square.frame square.insertion first
    have second := lowerDrop square.frame square.insertion second
    have cross := lowerDrop square.frame square.insertion cross
    have leftBody (argument : VExpr) :
        (((large.leftBody.lift' square.oldMap.cons).inst (argument.lift' square.frame.liftMap)).subst
          square.frame.retract) = (small.leftBody.lift' ρ.cons).inst argument := by
      rw [subst_inst, square.leftBody, square.frame.leftInv]
    have rightBody (argument : VExpr) :
        (((large.rightBody.lift' square.oldMap.cons).inst (argument.lift' square.frame.liftMap)).subst
          square.frame.retract) = (small.rightBody.lift' ρ.cons).inst argument := by
      rw [subst_inst, square.rightBody, square.frame.leftInv]
    simpa only [TypeRelated, leftBody, rightBody] using And.intro first (And.intro second cross)

end Lean4Lean.AnchoredSemantics
