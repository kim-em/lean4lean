import Lean4Lean.Verify.Inductive.PrimitiveEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The canonical abstract `Bool` family constant. -/
def primitiveBoolType : VConstVal :=
  { name := ``Bool, uvars := 0, type := .sort (.succ .zero) }

/-- The canonical abstract `Bool.false` constructor constant. -/
def primitiveBoolFalse : VConstVal :=
  { name := ``Bool.false, uvars := 0, type := .bool }

/-- The canonical abstract `Bool.true` constructor constant. -/
def primitiveBoolTrue : VConstVal :=
  { name := ``Bool.true, uvars := 0, type := .bool }

/-- The complete abstract constant batch installed by the canonical primitive
`Bool` declaration.  The batch is deliberately atomic: `HasPrimitives` is
false after only the family header has been installed. -/
def primitiveBoolConstants : List VConstVal :=
  [primitiveBoolType, primitiveBoolFalse, primitiveBoolTrue]

/-- The canonical abstract `Nat` family constant. -/
def primitiveNatType : VConstVal :=
  { name := ``Nat, uvars := 0, type := .sort (.succ .zero) }

/-- The canonical abstract `Nat.zero` constructor constant. -/
def primitiveNatZero : VConstVal :=
  { name := ``Nat.zero, uvars := 0, type := .nat }

/-- The canonical abstract `Nat.succ` constructor constant. -/
def primitiveNatSucc : VConstVal :=
  { name := ``Nat.succ, uvars := 0, type := .forallE .nat .nat }

/-- The complete abstract constant batch installed by the canonical primitive
`Nat` declaration. -/
def primitiveNatConstants : List VConstVal :=
  [primitiveNatType, primitiveNatZero, primitiveNatSucc]

theorem primitiveBoolConstants_names :
    primitiveBoolConstants.map (·.name) =
      [``Bool, ``Bool.false, ``Bool.true] := rfl

theorem primitiveNatConstants_names :
    primitiveNatConstants.map (·.name) =
      [``Nat, ``Nat.zero, ``Nat.succ] := rfl

/-- Evidence that a complete finite batch was installed in one abstract
environment transition.  In particular, this certificate makes no claim that
any proper prefix of `constants` produces a valid checking environment. -/
structure PrimitiveBootstrapInstallation
    (env out : VEnv) (constants : List VConstVal) : Prop where
  installed : env.addConstVals constants = some out

/-- Atomic batch installation only extends the abstract environment. -/
theorem PrimitiveBootstrapInstallation.le
    (H : PrimitiveBootstrapInstallation env out constants) : env ≤ out :=
  VEnv.addConstVals_le H.installed

/-- Every member of an atomically installed bootstrap batch has its exact
abstract constant metadata in the completed environment. -/
theorem PrimitiveBootstrapInstallation.lookup
    (H : PrimitiveBootstrapInstallation env out constants)
    (hci : ci ∈ constants) :
    out.constants ci.name = some ci.toVConstant :=
  VEnv.addConstVals_get H.installed hci

/-- A complete canonical Bool batch restores the primitive invariant.  No
intermediate environment is asserted to satisfy `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addBoolBootstrap
    {env out : VEnv}
    (H : env.HasPrimitives)
    (Hadd : env.addConstVals primitiveBoolConstants = some out) :
    out.HasPrimitives := by
  have hle : env ≤ out := VEnv.addConstVals_le Hadd
  have hBool : out.constants ``Bool = some
      ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
    simpa [primitiveBoolType] using VEnv.addConstVals_get Hadd
      (show primitiveBoolType ∈ primitiveBoolConstants by
        simp [primitiveBoolConstants])
  have hFalse : out.constants ``Bool.false = some
      ({ uvars := 0, type := .bool } : VConstant) := by
    simpa [primitiveBoolFalse] using VEnv.addConstVals_get Hadd
      (show primitiveBoolFalse ∈ primitiveBoolConstants by
        simp [primitiveBoolConstants])
  have hTrue : out.constants ``Bool.true = some
      ({ uvars := 0, type := .bool } : VConstant) := by
    simpa [primitiveBoolTrue] using VEnv.addConstVals_get Hadd
      (show primitiveBoolTrue ∈ primitiveBoolConstants by
        simp [primitiveBoolConstants])
  have same (name : Name)
      (hneBool : name ≠ ``Bool)
      (hneFalse : name ≠ ``Bool.false)
      (hneTrue : name ≠ ``Bool.true) :
      out.constants name = env.constants name := by
    apply VEnv.addConstVals_constants_of_forall_ne Hadd
    intro ci hci
    simp [primitiveBoolConstants, primitiveBoolType, primitiveBoolFalse,
      primitiveBoolTrue] at hci
    rcases hci with rfl | rfl | rfl
    · exact Ne.symm hneBool
    · exact Ne.symm hneFalse
    · exact Ne.symm hneTrue
  have oldContains (name : Name)
      (hneBool : name ≠ ``Bool)
      (hneFalse : name ≠ ``Bool.false)
      (hneTrue : name ≠ ``Bool.true) :
      out.contains name → env.contains name := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, by rwa [same name hneBool hneFalse hneTrue] at hci⟩
  have newContains {name : Name} : env.contains name → out.contains name := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, hle.constants hci⟩
  have natOld : out.contains ``Nat → env.contains ``Nat :=
    oldContains ``Nat (by decide) (by decide) (by decide)
  refine {
    bool := fun _ => ⟨⟨_, hFalse⟩, ⟨_, hTrue⟩⟩
    boolFalse := fun h => by rw [hFalse] at h; exact Option.some.inj h |>.symm
    boolTrue := fun h => by rw [hTrue] at h; exact Option.some.inj h |>.symm
    nat := fun h =>
      let ⟨hzero, hsucc⟩ := H.nat (natOld h)
      ⟨newContains hzero, newContains hsucc⟩
    natZero := fun h => H.natZero (by
      rwa [same ``Nat.zero (by decide) (by decide) (by decide)] at h)
    natSucc := fun h => H.natSucc (by
      rwa [same ``Nat.succ (by decide) (by decide) (by decide)] at h)
    natAdd := fun h a b =>
      (H.natAdd (oldContains ``Nat.add (by decide) (by decide) (by decide) h)
        a b).mono hle
    natSub := fun h a b =>
      (H.natSub (oldContains ``Nat.sub (by decide) (by decide) (by decide) h)
        a b).mono hle
    natMul := fun h a b =>
      (H.natMul (oldContains ``Nat.mul (by decide) (by decide) (by decide) h)
        a b).mono hle
    natPow := fun h a b =>
      (H.natPow (oldContains ``Nat.pow (by decide) (by decide) (by decide) h)
        a b).mono hle
    natGcd := fun h a b =>
      (H.natGcd (oldContains ``Nat.gcd (by decide) (by decide) (by decide) h)
        a b).mono hle
    natMod := fun h a b =>
      (H.natMod (oldContains ``Nat.mod (by decide) (by decide) (by decide) h)
        a b).mono hle
    natDiv := fun h a b =>
      (H.natDiv (oldContains ``Nat.div (by decide) (by decide) (by decide) h)
        a b).mono hle
    natBEq := fun h a b =>
      (H.natBEq (oldContains ``Nat.beq (by decide) (by decide) (by decide) h)
        a b).mono hle
    natBLE := fun h a b =>
      (H.natBLE (oldContains ``Nat.ble (by decide) (by decide) (by decide) h)
        a b).mono hle
    natLAnd := fun h a b =>
      (H.natLAnd (oldContains ``Nat.land (by decide) (by decide) (by decide) h)
        a b).mono hle
    natLOr := fun h a b =>
      (H.natLOr (oldContains ``Nat.lor (by decide) (by decide) (by decide) h)
        a b).mono hle
    natXor := fun h a b =>
      (H.natXor (oldContains ``Nat.xor (by decide) (by decide) (by decide) h)
        a b).mono hle
    natShiftLeft := fun h a b =>
      (H.natShiftLeft
        (oldContains ``Nat.shiftLeft (by decide) (by decide) (by decide) h)
        a b).mono hle
    natShiftRight := fun h a b =>
      (H.natShiftRight
        (oldContains ``Nat.shiftRight (by decide) (by decide) (by decide) h)
        a b).mono hle
    charOfNat := fun h => H.charOfNat (by
      rwa [same ``Char.ofNat (by decide) (by decide) (by decide)] at h)
    stringOfList := fun h => by
      rcases H.stringOfList (by
        rwa [same ``String.ofList (by decide) (by decide) (by decide)] at h) with
        ⟨hci, hnil, hcons⟩
      exact ⟨hci, hnil.mono hle, hcons.mono hle⟩ }

/-- A complete canonical Nat batch restores the primitive invariant. -/
theorem VEnv.HasPrimitives.addNatBootstrap
    {env out : VEnv}
    (H : env.HasPrimitives)
    (Hadd : env.addConstVals primitiveNatConstants = some out) :
    out.HasPrimitives := by
  have hle : env ≤ out := VEnv.addConstVals_le Hadd
  have hNat : out.constants ``Nat = some
      ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
    simpa [primitiveNatType] using VEnv.addConstVals_get Hadd
      (show primitiveNatType ∈ primitiveNatConstants by
        simp [primitiveNatConstants])
  have hZero : out.constants ``Nat.zero = some
      ({ uvars := 0, type := .nat } : VConstant) := by
    simpa [primitiveNatZero] using VEnv.addConstVals_get Hadd
      (show primitiveNatZero ∈ primitiveNatConstants by
        simp [primitiveNatConstants])
  have hSucc : out.constants ``Nat.succ = some
      ({ uvars := 0, type := .forallE .nat .nat } : VConstant) := by
    simpa [primitiveNatSucc] using VEnv.addConstVals_get Hadd
      (show primitiveNatSucc ∈ primitiveNatConstants by
        simp [primitiveNatConstants])
  have same (name : Name)
      (hneNat : name ≠ ``Nat)
      (hneZero : name ≠ ``Nat.zero)
      (hneSucc : name ≠ ``Nat.succ) :
      out.constants name = env.constants name := by
    apply VEnv.addConstVals_constants_of_forall_ne Hadd
    intro ci hci
    simp [primitiveNatConstants, primitiveNatType, primitiveNatZero,
      primitiveNatSucc] at hci
    rcases hci with rfl | rfl | rfl
    · exact Ne.symm hneNat
    · exact Ne.symm hneZero
    · exact Ne.symm hneSucc
  have oldContains (name : Name)
      (hneNat : name ≠ ``Nat)
      (hneZero : name ≠ ``Nat.zero)
      (hneSucc : name ≠ ``Nat.succ) :
      out.contains name → env.contains name := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, by rwa [same name hneNat hneZero hneSucc] at hci⟩
  have newContains {name : Name} : env.contains name → out.contains name := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, hle.constants hci⟩
  refine {
    bool := fun h =>
      let ⟨hfalse, htrue⟩ := H.bool
        (oldContains ``Bool (by decide) (by decide) (by decide) h)
      ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun h => H.boolFalse (by
      rwa [same ``Bool.false (by decide) (by decide) (by decide)] at h)
    boolTrue := fun h => H.boolTrue (by
      rwa [same ``Bool.true (by decide) (by decide) (by decide)] at h)
    nat := fun _ => ⟨⟨_, hZero⟩, ⟨_, hSucc⟩⟩
    natZero := fun h => by rw [hZero] at h; exact Option.some.inj h |>.symm
    natSucc := fun h => by rw [hSucc] at h; exact Option.some.inj h |>.symm
    natAdd := fun h a b =>
      (H.natAdd (oldContains ``Nat.add (by decide) (by decide) (by decide) h)
        a b).mono hle
    natSub := fun h a b =>
      (H.natSub (oldContains ``Nat.sub (by decide) (by decide) (by decide) h)
        a b).mono hle
    natMul := fun h a b =>
      (H.natMul (oldContains ``Nat.mul (by decide) (by decide) (by decide) h)
        a b).mono hle
    natPow := fun h a b =>
      (H.natPow (oldContains ``Nat.pow (by decide) (by decide) (by decide) h)
        a b).mono hle
    natGcd := fun h a b =>
      (H.natGcd (oldContains ``Nat.gcd (by decide) (by decide) (by decide) h)
        a b).mono hle
    natMod := fun h a b =>
      (H.natMod (oldContains ``Nat.mod (by decide) (by decide) (by decide) h)
        a b).mono hle
    natDiv := fun h a b =>
      (H.natDiv (oldContains ``Nat.div (by decide) (by decide) (by decide) h)
        a b).mono hle
    natBEq := fun h a b =>
      (H.natBEq (oldContains ``Nat.beq (by decide) (by decide) (by decide) h)
        a b).mono hle
    natBLE := fun h a b =>
      (H.natBLE (oldContains ``Nat.ble (by decide) (by decide) (by decide) h)
        a b).mono hle
    natLAnd := fun h a b =>
      (H.natLAnd (oldContains ``Nat.land (by decide) (by decide) (by decide) h)
        a b).mono hle
    natLOr := fun h a b =>
      (H.natLOr (oldContains ``Nat.lor (by decide) (by decide) (by decide) h)
        a b).mono hle
    natXor := fun h a b =>
      (H.natXor (oldContains ``Nat.xor (by decide) (by decide) (by decide) h)
        a b).mono hle
    natShiftLeft := fun h a b =>
      (H.natShiftLeft
        (oldContains ``Nat.shiftLeft (by decide) (by decide) (by decide) h)
        a b).mono hle
    natShiftRight := fun h a b =>
      (H.natShiftRight
        (oldContains ``Nat.shiftRight (by decide) (by decide) (by decide) h)
        a b).mono hle
    charOfNat := fun h => H.charOfNat (by
      rwa [same ``Char.ofNat (by decide) (by decide) (by decide)] at h)
    stringOfList := fun h => by
      rcases H.stringOfList (by
        rwa [same ``String.ofList (by decide) (by decide) (by decide)] at h) with
        ⟨hci, hnil, hcons⟩
      exact ⟨hci, hnil.mono hle, hcons.mono hle⟩ }

/-- The completed atomic Bool batch restores `HasPrimitives`; no validity
claim is made about its family-only prefix. -/
theorem PrimitiveBootstrapInstallation.boolHasPrimitives
    (B : PrimitiveBootstrapInstallation env out primitiveBoolConstants)
    (H : env.HasPrimitives) : out.HasPrimitives :=
  VEnv.HasPrimitives.addBoolBootstrap H B.installed

/-- The completed atomic Nat batch restores `HasPrimitives`; no validity claim
is made about its family-only prefix. -/
theorem PrimitiveBootstrapInstallation.natHasPrimitives
    (B : PrimitiveBootstrapInstallation env out primitiveNatConstants)
    (H : env.HasPrimitives) : out.HasPrimitives :=
  VEnv.HasPrimitives.addNatBootstrap H B.installed

end VerifyInductive
end Lean4Lean
