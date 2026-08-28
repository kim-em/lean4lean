import Lean4Lean.Verify.Typing.ProjectionMetadata
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Complete production-to-abstract provenance needed before expanding a
projection headed by `familyName`.  The production `InductiveVal` is tied to
one source family, its finite installation certificate, and the exact primary
recursor visible in the abstract environment. -/
structure ProductionProjectionFamily
    (safety : DefinitionSafety) (constants : ConstMap) (env : VEnv)
    (familyName : Name) (familyInfo : InductiveVal) where
  decl : VInductDecl
  familyIdx : Nat
  alignment : ProductionFamilyAlignment constants decl familyIdx familyInfo
  familyNameExact : familyInfo.name = familyName
  installed : VEnv.InstalledInductCertificate env decl
  recursor : VConstVal
  recursorName : recursor.name = mkRecName familyName
  recursorLookup : env.constants (mkRecName familyName) =
    some recursor.toVConstant
  recursorShape : Nonempty
    (decl.NestedRecursorShape
      (decl.types[familyIdx]'alignment.familyIdx_lt) recursor)

/-- Exact constructor metadata available after the executable projection
expander has established that the production family has one constructor.
The field count remains the value computed by `constructorInfo`; its equality
with the source telescope calculation is inherited from production
alignment, rather than accepted from projection elaboration. -/
structure ProductionProjectionConstructor
    {safety : DefinitionSafety} {constants : ConstMap} {env : VEnv}
    {familyName : Name} {familyInfo : InductiveVal}
    (P : ProductionProjectionFamily safety constants env familyName
      familyInfo) where
  constructorName : Name
  productionSingle : familyInfo.ctors = [constructorName]
  sourceSingle :
    (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors.length = 1
  alignment : ProductionConstructorAlignment constants P.decl
    P.familyIdx 0 familyInfo

/-- A successful one-constructor metadata match selects the exact aligned
constructor at position zero.  In particular this exposes the verified
`numFields` calculation needed to check the projection index and build the
minor telescope. -/
theorem ProductionProjectionFamily.constructorOfSingle
    (P : ProductionProjectionFamily safety constants env familyName
      familyInfo)
    (hconstructors : familyInfo.ctors = [constructorName]) :
    Nonempty (ProductionProjectionConstructor P) := by
  have hsourceLength :
      (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors.length = 1 := by
    rw [← P.alignment.constructors]
    simp [hconstructors]
  have hsource : 0 <
      (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors.length := by
    omega
  rcases P.alignment.constructor 0 hsource with ⟨Hconstructor⟩
  exact ⟨{
    constructorName := constructorName
    productionSingle := hconstructors
    sourceSingle := hsourceLength
    alignment := Hconstructor }⟩

/-- Persistent inductive provenance deterministically supplies the complete
projection-family certificate for a successful production family lookup.
The safety premise is the ordinary visibility check already required when
translating constants; no projection-specific provider is introduced. -/
theorem InstalledInductiveProvenance.projectionFamily
    (H : InstalledInductiveProvenance safety constants env)
    (hfamily : constants.find? familyName = some (.inductInfo familyInfo))
    (hvisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety) :
    Nonempty (ProductionProjectionFamily safety constants env
      familyName familyInfo) := by
  rcases H familyName familyInfo hfamily hvisible with ⟨P⟩
  have howner : (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt) ∈
      P.decl.types :=
    List.getElem_mem P.alignment.familyIdx_lt
  rcases ProjectionMetadata.installedInductCertificate_recNameLookup
      P.installed howner with
    ⟨recursor, hname, hlookup, Hshape⟩
  have hfamilyName :
      (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).name =
        familyName := by
    rw [← P.alignment.name, ← P.name]
  exact ⟨{
    decl := P.decl
    familyIdx := P.familyIdx
    alignment := P.alignment
    familyNameExact := P.name.symm
    installed := P.installed
    recursor := recursor
    recursorName := by simpa [hfamilyName] using hname
    recursorLookup := by simpa [hfamilyName] using hlookup
    recursorShape := Hshape }⟩

end VerifyInductive

end Lean4Lean
