import Lean4Lean.Verify.Inductive.Primitive.Shape
import Lean4Lean.Verify.Inductive.Install.Ordinary

/-! # The primitive run

The executable runs a recognized `Bool` or `Nat` declaration through the same pipeline with the
primitive-name exception enabled (`allowPrimitive := true`). Its header and constructor phases
are verified separately for the two finite shapes (the ordinary boundary theorems exclude
primitive names); the recursor phase is shared (`ConstructorCheck.recursorPhasesWF`).

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Primitive/{Run,Headers,Constructors,ConstructorCheck,ConstructorParams,BatchInstallation,
Constants,Context}.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The exact checker context selected by the executable's primitive branch. -/
def primitiveAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe : Bool) (fuel : FuelConfig) : AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := true, fuel := fuel }

/-- Complete primitive run-with-stats result: the same shape as `OrdinaryInstallation`. -/
abbrev PrimitiveInstallation
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (outEnv : Environment) : Prop :=
  OrdinaryInstallation c stats nparams depth indTypes isUnsafe sourceEnv outEnv

/-- The constructor phase of a primitive declaration: the primitive names are installed with
their canonical types (`VEnv.HasPrimitives` is preserved by the resulting checking context). -/
theorem AddInductive.constructorPhase.primitiveWF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hsafety : isUnsafe = (c'.safety != .safe))
    (Hshape : PrimitiveInductiveShape c'.lparams nparams indTypes.toList isUnsafe)
    (hallow : c'.allowPrimitive = true)
    (hclosed : MutualInductivesClosed c'.env)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c').WF
      fun out => ∃ decl, P.headers.Describes decl ∧
        ∃ R : ConstructorCheck c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes out.1,
          R.classes = out.2 := by
  -- WAVE 2 STUB (Primitive): not provable as stated. `ConstructorCheck` extends
  -- `CheckedFormation`, whose `headers : HeaderEnvironment` carries
  -- `context : ContextWF {c with env := headerEnv}`, hence `VEnv.HasPrimitives` of the header
  -- model `sourceEnv.addConstVals decl.typeConstants`. For `Bool` (and `Nat`) that model
  -- contains the family without its constructors, which violates the `containsImplies` spec
  -- of `HasPrimitives`. The source branch verified this phase without a valid header-only
  -- context (`PrimitiveHeaderEnvironment`, `LocalContextWF`, the atomic batch of
  -- `Primitive/BatchInstallation.lean`); the interface needs a primitive variant of
  -- `HeaderEnvironment`/`CheckedFormation` (or a `ContextWF` without `HasPrimitives`) before
  -- this can be ported.
  have := hsafety; have := Hshape; have := hallow; have := hclosed; have := hpresent; sorry

/-- Source-aligned primitive result, retaining the exact abstract model from
which the executable header traversal began. -/
def PrimitiveRunResult
    (source : AddInductive.Context) (Hsource : ContextWF source) (nparams : Nat)
    (types : List InductiveType) (outEnv : Environment) : Prop :=
  ∃ c' stats, ∃ Hc' : ContextWF c',
    ∃ P : HeaderPhase Hsource nparams types.toArray c' Hc' stats,
      PrimitiveInductiveShape c'.lparams nparams types.toArray.toList (source.safety != .safe) ∧
      PrimitiveInstallation c' stats nparams P.depth Hc'.venv types.toArray
        (source.safety != .safe) outEnv

/-- The complete executable primitive checker. -/
theorem AddInductive.run.primitiveSourceAlignedWF
    {c : AddInductive.Context} {types : List InductiveType}
    (nparams numNested : Nat) (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams types.toArray.toList (c.safety != .safe))
    (hallow : c.allowPrimitive = true)
    (hctx : Hc.mlctx.vlctx = [])
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF (PrimitiveRunResult c Hc nparams types) := by
  have hnonempty : 0 < types.toArray.size := by
    have := Hshape.types_nonempty
    cases h : types with
    | nil => rw [h] at this; exact absurd rfl this
    | cons _ _ => simp
  show (Kernel.Environment.checkDuplicatedUnivParams c.lparams >>= fun _ =>
      AddInductive.checkInductiveTypes nparams types.toArray (fun stats =>
        AddInductive.runWithStats stats nparams types.toArray numNested (c.safety != .safe))
        c).WF _
  refine Except.WF.bind (Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams)
    fun _ hnodup => ?_
  refine AddInductive.checkInductiveTypes.WF _ _ Hc hctx hnonempty fun {c' stats} Hc' P => ?_
  have hsafety : (c.safety != .safe) = (c'.safety != .safe) := by rw [P.safety_eq]
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams types.toArray.toList
      (c.safety != .safe) := by
    rw [P.lparams_eq]; exact Hshape
  unfold AddInductive.runWithStats
  refine AddInductive.M.WF_bind
    (AddInductive.constructorPhase.primitiveWF P numNested _ hsafety Hshape'
      (P.allowPrimitive_eq.trans hallow) (P.env_eq ▸ Hclosed) (P.env_eq ▸ Hpresent))
    fun out Hout => ?_
  obtain ⟨ctorEnv, positivity⟩ := out
  obtain ⟨decl, -, R, hclasses⟩ := Hout
  refine (R.recursorPhasesWF (by rw [P.lparams_eq]; exact hnodup) hsafety
    (by rw [P.safety_eq]; exact HnotPartial)
    (fun _ => by simpa using Hshape'.recursorsNonprimitive) hclasses.symm).mono
    fun outEnv Hrec => ⟨c', stats, Hc', P, Hshape', decl, ctorEnv, R, Hrec⟩

end VerifyInductive
end Lean4Lean
