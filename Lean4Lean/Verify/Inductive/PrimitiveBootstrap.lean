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

/-- A primitive specification survives a batch extension when the constant it
inspects is unchanged.  The other constants and definitional equations used
by the specification are covariant in the environment. -/
theorem PrimSpec.Holds.monoOfConstantsEq
    {env out : VEnv} {s : PrimSpec} {name : Name}
    (H : s.Holds env name) (hle : env ≤ out)
    (hsame : out.constants name = env.constants name) :
    s.Holds out name := by
  have old : out.contains name → env.contains name := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, by rwa [hsame] at hci⟩
  have new {n} : env.contains n → out.contains n := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, hle.constants hci⟩
  cases s with
  | containsImplies ns => exact fun h n hn => new (H (old h) n hn)
  | typeEq => exact fun _ h => H _ (hsame ▸ h)
  | reflectsNatNat => exact fun h => ⟨(H (old h)).1.mono hle, fun a => ((H (old h)).2 a).mono hle⟩
  | reflectsNatNatNat =>
    exact fun h => ⟨(H (old h)).1.mono hle, fun a b => ((H (old h)).2 a b).mono hle⟩
  | reflectsNatNatBool =>
    exact fun h => ⟨(H (old h)).1.mono hle, fun a b => ((H (old h)).2 a b).mono hle⟩
  | reflectsBitwise =>
    exact fun h => ⟨fun _ hc => (H (old h)).1 _ (hsame ▸ hc),
      fun env' hle' => (H (old h)).2 env' (hle.trans hle')⟩
  | stringOfList =>
    intro _ h
    obtain ⟨h1, h2, h3⟩ := H _ (hsame ▸ h)
    exact ⟨h1, h2.mono hle, h3.mono hle⟩

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
  intro p hp
  rcases p with ⟨name, spec⟩
  by_cases hBool : name = ``Bool
  · have heq : (name, spec) =
        (``Bool, .containsImplies [``Bool.false, ``Bool.true]) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hBool
    cases heq
    intro _ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact ⟨_, hFalse⟩
    · exact ⟨_, hTrue⟩
  by_cases hFalseName : name = ``Bool.false
  · have heq : (name, spec) = (``Bool.false, .typeEq .bool) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hFalseName
    cases heq
    intro _ h
    rw [hFalse] at h
    exact Option.some.inj h |>.symm
  by_cases hTrueName : name = ``Bool.true
  · have heq : (name, spec) = (``Bool.true, .typeEq .bool) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hTrueName
    cases heq
    intro _ h
    rw [hTrue] at h
    exact Option.some.inj h |>.symm
  exact PrimSpec.Holds.monoOfConstantsEq (s := spec) (H (name, spec) hp) hle
    (same name hBool hFalseName hTrueName)

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
  intro p hp
  rcases p with ⟨name, spec⟩
  by_cases hNatName : name = ``Nat
  · have heq : (name, spec) =
        (``Nat, .containsImplies [``Nat.zero, ``Nat.succ]) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hNatName
    cases heq
    intro _ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact ⟨_, hZero⟩
    · exact ⟨_, hSucc⟩
  by_cases hZeroName : name = ``Nat.zero
  · have heq : (name, spec) = (``Nat.zero, .typeEq .nat) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hZeroName
    cases heq
    intro _ h
    rw [hZero] at h
    exact Option.some.inj h |>.symm
  by_cases hSuccName : name = ``Nat.succ
  · have heq : (name, spec) =
        (``Nat.succ, .typeEq (.forallE .nat .nat)) :=
      List.nodup_keys_unique primSpecs_nodup hp (by simp [primSpecs]) hSuccName
    cases heq
    intro _ h
    rw [hSucc] at h
    exact Option.some.inj h |>.symm
  exact PrimSpec.Holds.monoOfConstantsEq (s := spec) (H (name, spec) hp) hle
    (same name hNatName hZeroName hSuccName)

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
