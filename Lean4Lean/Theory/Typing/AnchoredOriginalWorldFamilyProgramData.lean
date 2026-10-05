import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFundedFamilyHeaderData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantControl

/-! Constant-family selection retains either the exact old telescope header
or the finite rigid program. The latter owns its literal input annotation and
every enclosing canonical packet; no declaration telescope is asserted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

structure WorldRigidFamilyLeaf (strata : EquationStratification env) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (name : Name) (levels : List VLevel)
    (frontier : List (World strata.rules.length)) where
  sourceEnv : VEnv
  source : List VExpr
  assigned : VExpr
  node : EndpointState sourceEnv U source (.const name levels) assigned
  locals : List Nat
  substitution : Subst
  frozenLevels : List VLevel
  rank : Nat
  plan : RigidFamilySpine rank
  support : Profile rank
  input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support
  controls : OriginalWorldControls strata sourceEnv
  controlled : ControlledStoredQuery controls frontier
    (.observation (input.observation node locals substitution))

inductive WorldRigidFamilyProgram (strata : EquationStratification env) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (name : Name) (levels : List VLevel)
    (frontier : List (World strata.rules.length)) : Type where
  | literal (leaf : WorldRigidFamilyLeaf strata U registry target name levels frontier)
  | canonical (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
      (annotation : WorldObsProvenance strata packet.query)
      (storedControls : OriginalWorldControls strata packet.owner.selected.origin.source)
      (storedProvenance : EndpointProvenance .nil (.ref packet.site))
      (child : WorldRigidFamilyProgram strata U registry target name levels frontier)

noncomputable def WorldRigidFamilyProgram.leaf
    (program : WorldRigidFamilyProgram strata U registry target name levels frontier) :
    WorldRigidFamilyLeaf strata U registry target name levels frontier :=
  match program with
  | .literal leaf => leaf
  | .canonical _ _ _ _ child => child.leaf

inductive WorldFamilyProgramAt {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel)
    (frontier : List (World strata.rules.length)) (parent : World strata.rules.length) : Type where
  | telescope (selected : WorldFundedFamilyHeaderAt controls U registry target name levels frontier parent)
  | rigid (program : WorldRigidFamilyProgram strata U registry target name levels frontier)

noncomputable def WorldFamilyProgramAt.rank
    (selected : WorldFamilyProgramAt controls U registry target name levels frontier parent) : Nat :=
  match selected with
  | .telescope header => header.header.rank
  | .rigid program => program.leaf.rank

noncomputable def WorldFamilyProgramAt.atom
    (selected : WorldFamilyProgramAt controls U registry target name levels frontier parent) : Atom selected.rank :=
  match selected with
  | .telescope header => header.header.atom
  | .rigid program => program.leaf.plan.atom name program.leaf.frozenLevels []

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
