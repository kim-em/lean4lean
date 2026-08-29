import Lean4Lean.Verify.Typing.Projection
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Verify.Typing.ProjectionRelationCore
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean

open Lean

namespace CanonicalProjectionExpansion.InstalledOrigin

def mono
    (H : CanonicalProjectionExpansion.InstalledOrigin env U P)
    (Henv : env ≤ env') :
    CanonicalProjectionExpansion.InstalledOrigin env' U P where
  decl := H.decl
  owner := H.owner
  ctor := H.ctor
  recursor := H.recursor
  eliminator := H.eliminator
  installed := H.installed.mono Henv
  owner_mem := H.owner_mem
  owner_name := H.owner_name
  owner_single := H.owner_single
  recursor_name := H.recursor_name
  recursor_lookup := Henv.constants H.recursor_lookup
  eliminator_lookup := Henv.constants H.eliminator_lookup
  recursor_shape := H.recursor_shape
  familyLevels_length := H.familyLevels_length
  familyLevels_wf := H.familyLevels_wf
  resultLevel_wf := H.resultLevel_wf
  params_length := H.params_length
  indices_length := H.indices_length

def instL
    (H : CanonicalProjectionExpansion.InstalledOrigin env U P)
    (substitution : List VLevel)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    CanonicalProjectionExpansion.InstalledOrigin env U'
      (P.instL substitution) where
  decl := H.decl
  owner := H.owner
  ctor := H.ctor
  recursor := H.recursor
  eliminator := H.eliminator
  installed := H.installed
  owner_mem := H.owner_mem
  owner_name := H.owner_name
  owner_single := H.owner_single
  recursor_name := H.recursor_name
  recursor_lookup := H.recursor_lookup
  eliminator_lookup := H.eliminator_lookup
  recursor_shape := H.recursor_shape
  familyLevels_length := by simpa [CanonicalProjectionExpansion.instL] using
    H.familyLevels_length
  familyLevels_wf := by
    intro level hlevel
    simp only [CanonicalProjectionExpansion.instL, List.mem_map] at hlevel
    rcases hlevel with ⟨source, hsource, rfl⟩
    exact VLevel.WF.inst Hlevels
  resultLevel_wf := VLevel.WF.inst Hlevels
  params_length := by simpa [CanonicalProjectionExpansion.instL] using
    H.params_length
  indices_length := by simpa [CanonicalProjectionExpansion.instL] using
    H.indices_length

def liftN
    (H : CanonicalProjectionExpansion.InstalledOrigin env U P)
    (n k : Nat) :
    CanonicalProjectionExpansion.InstalledOrigin env U (P.liftN n k) where
  decl := H.decl
  owner := H.owner
  ctor := H.ctor
  recursor := H.recursor
  eliminator := H.eliminator
  installed := H.installed
  owner_mem := H.owner_mem
  owner_name := H.owner_name
  owner_single := H.owner_single
  recursor_name := H.recursor_name
  recursor_lookup := H.recursor_lookup
  eliminator_lookup := H.eliminator_lookup
  recursor_shape := H.recursor_shape
  familyLevels_length := by simpa [CanonicalProjectionExpansion.liftN] using
    H.familyLevels_length
  familyLevels_wf := by simpa [CanonicalProjectionExpansion.liftN] using
    H.familyLevels_wf
  resultLevel_wf := by simpa [CanonicalProjectionExpansion.liftN] using
    H.resultLevel_wf
  params_length := by simpa [CanonicalProjectionExpansion.liftN] using
    H.params_length
  indices_length := by simpa [CanonicalProjectionExpansion.liftN] using
    H.indices_length

def lift'
    (H : CanonicalProjectionExpansion.InstalledOrigin env U P)
    (lift : Lift) :
    CanonicalProjectionExpansion.InstalledOrigin env U (P.lift' lift) where
  decl := H.decl
  owner := H.owner
  ctor := H.ctor
  recursor := H.recursor
  eliminator := H.eliminator
  installed := H.installed
  owner_mem := H.owner_mem
  owner_name := H.owner_name
  owner_single := H.owner_single
  recursor_name := H.recursor_name
  recursor_lookup := H.recursor_lookup
  eliminator_lookup := H.eliminator_lookup
  recursor_shape := H.recursor_shape
  familyLevels_length := by simpa [CanonicalProjectionExpansion.lift'] using
    H.familyLevels_length
  familyLevels_wf := by simpa [CanonicalProjectionExpansion.lift'] using
    H.familyLevels_wf
  resultLevel_wf := by simpa [CanonicalProjectionExpansion.lift'] using
    H.resultLevel_wf
  params_length := by simpa [CanonicalProjectionExpansion.lift'] using
    H.params_length
  indices_length := by simpa [CanonicalProjectionExpansion.lift'] using
    H.indices_length

def instN
    (H : CanonicalProjectionExpansion.InstalledOrigin env U P)
    (substitution : VExpr) (k : Nat) :
    CanonicalProjectionExpansion.InstalledOrigin env U
      (P.instN substitution k) where
  decl := H.decl
  owner := H.owner
  ctor := H.ctor
  recursor := H.recursor
  eliminator := H.eliminator
  installed := H.installed
  owner_mem := H.owner_mem
  owner_name := H.owner_name
  owner_single := H.owner_single
  recursor_name := H.recursor_name
  recursor_lookup := H.recursor_lookup
  eliminator_lookup := H.eliminator_lookup
  recursor_shape := H.recursor_shape
  familyLevels_length := by simpa [CanonicalProjectionExpansion.instN] using
    H.familyLevels_length
  familyLevels_wf := by simpa [CanonicalProjectionExpansion.instN] using
    H.familyLevels_wf
  resultLevel_wf := by simpa [CanonicalProjectionExpansion.instN] using
    H.resultLevel_wf
  params_length := by simpa [CanonicalProjectionExpansion.instN] using
    H.params_length
  indices_length := by simpa [CanonicalProjectionExpansion.instN] using
    H.indices_length

end CanonicalProjectionExpansion.InstalledOrigin

namespace CanonicalProjectionExpansion.InstalledTyping

def mono
    (H : CanonicalProjectionExpansion.InstalledTyping env U Gamma P)
    (Henv : env ≤ env') :
    CanonicalProjectionExpansion.InstalledTyping env' U Gamma P where
  toInstalledOrigin := H.toInstalledOrigin.mono Henv
  majorType := H.majorType.mono Henv

def defeqCtx
    (H : CanonicalProjectionExpansion.InstalledTyping env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    CanonicalProjectionExpansion.InstalledTyping env U GammaTwo P where
  toInstalledOrigin := H.toInstalledOrigin
  majorType := H.majorType.defeqDFC Henv Hctx

def instL
    (H : CanonicalProjectionExpansion.InstalledTyping env U Gamma P)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    CanonicalProjectionExpansion.InstalledTyping env U'
      (Gamma.map (VExpr.instL substitution)) (P.instL substitution) where
  toInstalledOrigin := H.toInstalledOrigin.instL substitution Hlevels
  majorType := by
    change env.HasType U' (Gamma.map (VExpr.instL substitution))
      (P.major.instL substitution)
      (VExpr.mkApps (.const H.owner.name
        (P.familyLevels.map (VLevel.inst substitution)))
        (P.params.map (VExpr.instL substitution) ++
          P.indices.map (VExpr.instL substitution)))
    simpa [CanonicalProjectionExpansion.instL, List.map_append, VExpr.instL] using
      H.majorType.instL Hlevels

def weakN
    (H : CanonicalProjectionExpansion.InstalledTyping env U Gamma P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    CanonicalProjectionExpansion.InstalledTyping env U Gamma'
      (P.liftN n k) where
  toInstalledOrigin := H.toInstalledOrigin.liftN n k
  majorType := by
    change env.HasType U Gamma' (P.major.liftN n k)
      (VExpr.mkApps (.const H.owner.name P.familyLevels)
        (P.params.map (fun param => param.liftN n k) ++
          P.indices.map (fun index => index.liftN n k)))
    simpa [CanonicalProjectionExpansion.liftN, VExpr.liftN] using
      H.majorType.weakN Henv W

def weak'
    (H : CanonicalProjectionExpansion.InstalledTyping env U Gamma P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.Lift' lift Gamma Gamma') :
    CanonicalProjectionExpansion.InstalledTyping env U Gamma'
      (P.lift' lift) where
  toInstalledOrigin := H.toInstalledOrigin.lift' lift
  majorType := by
    change env.HasType U Gamma' (P.major.lift' lift)
      (VExpr.mkApps (.const H.owner.name P.familyLevels)
        (P.params.map (VExpr.lift' · lift) ++
          P.indices.map (VExpr.lift' · lift)))
    have Hmajor := H.majorType.weak' Henv W
    rw [VExpr.lift'_mkApps] at Hmajor
    simpa [VExpr.lift', List.map_append] using Hmajor

def instN
    (H : CanonicalProjectionExpansion.InstalledTyping env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    CanonicalProjectionExpansion.InstalledTyping env U Gamma
      (P.instN substitution k) where
  toInstalledOrigin := H.toInstalledOrigin.instN substitution k
  majorType := by
    change env.HasType U Gamma (P.major.inst substitution k)
      (VExpr.mkApps (.const H.owner.name P.familyLevels)
        (P.params.map (fun param => param.inst substitution k) ++
          P.indices.map (fun index => index.inst substitution k)))
    simpa [CanonicalProjectionExpansion.instN, VExpr.inst] using
      H.majorType.instN Henv W Hsubstitution

end CanonicalProjectionExpansion.InstalledTyping

/-- Environment validity for one canonical projection expansion.  Unlike the
old environment-free `TrProj`, this certificate records actual typing
derivations in the environment where the projection is translated.

The certificate is deliberately proof-relevant and finite.  It is intended
to be constructed by the verified canonical expander from installed
structure metadata, never exposed as a declaration-checker premise. -/
theorem CanonicalProjectionExpansion.WF.mono
    (H : CanonicalProjectionExpansion.WF env U Gamma P)
    (Henv : env ≤ env') :
    CanonicalProjectionExpansion.WF env' U Gamma P where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.mono Henv⟩
  majorWF := H.majorWF.mono Henv
  targetWF := H.targetWF.mono Henv

theorem CanonicalProjectionExpansion.WF.defeqCtx
    (H : CanonicalProjectionExpansion.WF env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    CanonicalProjectionExpansion.WF env U GammaTwo P where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.defeqCtx Henv Hctx⟩
  majorWF := H.majorWF.defeqDFC Henv Hctx
  targetWF := H.targetWF.defeqDFC Henv Hctx

/-- Changing the major along definitional equality changes the canonical
eliminator application by definitional equality and preserves its typing. -/
theorem CanonicalProjectionExpansion.WF.replaceMajor
    (H : CanonicalProjectionExpansion.WF env U Gamma P)
    (major : VExpr)
    (Henv : VEnv.WF env) (Hctx : OnCtx Gamma (env.IsType U))
    (Hmajor : env.IsDefEqU U Gamma P.major major) :
    CanonicalProjectionExpansion.WF env U Gamma
      (P.replaceMajor major) := by
  rcases H.installed with ⟨installed⟩
  have HmajorType : env.HasType U Gamma major
      (VExpr.mkApps (.const installed.owner.name P.familyLevels)
        (P.params ++ P.indices)) :=
    installed.majorType.defeqU_l Henv Hctx Hmajor
  let head := VExpr.mkApps
    (.const (mkCasesOnName P.structName)
      (P.resultLevel :: P.familyLevels))
    (P.params ++ [P.motive] ++ P.indices)
  have HoldShape : P.target = .app (.app head P.major) P.minor := by
    simp [CanonicalProjectionExpansion.target, head, VExpr.mkApps,
      List.foldl_append]
  have HnewShape : (P.replaceMajor major).target =
      .app (.app head major) P.minor := by
    simp [CanonicalProjectionExpansion.target,
      CanonicalProjectionExpansion.replaceMajor,
      CanonicalProjectionExpansion.minor,
      CanonicalProjectionExpansion.fieldVar, head, VExpr.mkApps,
      List.foldl_append]
  have HoldWF : VExpr.WF env U Gamma (.app (.app head P.major) P.minor) := by
    simpa [HoldShape] using H.targetWF
  rcases HoldWF.app_inv Henv.ordered Hctx with
    ⟨minorDomain, minorBody, Hfunction, Hminor⟩
  have HinnerWF : VExpr.WF env U Gamma (.app head P.major) :=
    ⟨_, Hfunction⟩
  rcases HinnerWF.app_inv Henv.ordered Hctx with
    ⟨majorDomain, majorBody, Hhead, HoldMajor⟩
  have HmajorAtDomain : env.IsDefEq U Gamma P.major major majorDomain :=
    Hmajor.of_l Henv Hctx HoldMajor
  have HheadEq : env.IsDefEq U Gamma head head
      (.forallE majorDomain majorBody) :=
    Hhead
  have HinnerBase : env.IsDefEq U Gamma (.app head P.major)
      (.app head major) (majorBody.inst P.major) :=
    .appDF HheadEq HmajorAtDomain
  have HinnerTypes : env.IsDefEqU U Gamma
      (majorBody.inst P.major) (.forallE minorDomain minorBody) :=
    (HinnerBase.hasType.1.uniqU Henv Hctx Hfunction)
  have Hinner : env.IsDefEq U Gamma (.app head P.major)
      (.app head major) (.forallE minorDomain minorBody) :=
    HinnerTypes.defeqDF Henv Hctx HinnerBase
  have HminorEq : env.IsDefEq U Gamma P.minor P.minor minorDomain :=
    Hminor
  have Htargets : env.IsDefEqU U Gamma P.target
      (P.replaceMajor major).target := by
    rw [HoldShape, HnewShape]
    exact (VEnv.IsDefEq.appDF Hinner HminorEq).toU
  exact {
    installed := ⟨{
      toInstalledOrigin := {
        installed.toInstalledOrigin with
        params_length := installed.params_length
        indices_length := installed.indices_length }
      majorType := by
        simpa [CanonicalProjectionExpansion.replaceMajor] using HmajorType }⟩
    majorWF := Hmajor.symm.trans Henv Hctx
      (H.majorWF.trans Henv Hctx Hmajor)
    targetWF := Htargets.symm.trans Henv Hctx
      (H.targetWF.trans Henv Hctx Htargets) }

theorem CanonicalProjectionExpansion.WF.instL
    (H : CanonicalProjectionExpansion.WF env U Gamma P)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    CanonicalProjectionExpansion.WF env U'
      (Gamma.map (VExpr.instL substitution)) (P.instL substitution) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.instL Hlevels⟩
  majorWF := by
    change env.IsDefEqU U' (Gamma.map (VExpr.instL substitution))
      (P.major.instL substitution) (P.major.instL substitution)
    exact H.majorWF.instL Hlevels
  targetWF := by
    rw [CanonicalProjectionExpansion.target_instL]
    exact H.targetWF.instL Hlevels

theorem CanonicalProjectionExpansion.WF.weakN
    (H : CanonicalProjectionExpansion.WF env U Gamma P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    CanonicalProjectionExpansion.WF env U Gamma' (P.liftN n k) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.weakN Henv W⟩
  majorWF := by
    change env.IsDefEqU U Gamma' (P.major.liftN n k)
      (P.major.liftN n k)
    exact H.majorWF.weakN Henv W
  targetWF := by
    rw [CanonicalProjectionExpansion.target_liftN]
    exact H.targetWF.weakN Henv W

theorem CanonicalProjectionExpansion.WF.weak'
    (H : CanonicalProjectionExpansion.WF env U Gamma P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.Lift' lift Gamma Gamma') :
    CanonicalProjectionExpansion.WF env U Gamma' (P.lift' lift) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.weak' Henv W⟩
  majorWF := by
    change env.IsDefEqU U Gamma' (P.major.lift' lift)
      (P.major.lift' lift)
    exact H.majorWF.weak' Henv W
  targetWF := by
    rw [CanonicalProjectionExpansion.target_lift']
    exact H.targetWF.weak' Henv W

theorem CanonicalProjectionExpansion.WF.instN
    (H : CanonicalProjectionExpansion.WF env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    CanonicalProjectionExpansion.WF env U Gamma
      (P.instN substitution k) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.instN Henv W Hsubstitution⟩
  majorWF := by
    change env.IsDefEqU U Gamma (P.major.inst substitution k)
      (P.major.inst substitution k)
    exact H.majorWF.instN Henv W Hsubstitution
  targetWF := by
    rw [CanonicalProjectionExpansion.target_instN]
    exact H.targetWF.instN Henv W Hsubstitution

namespace EnvTrProj

/-- Projection evidence is monotone in the abstract environment because both
typing certificates are. -/
theorem mono
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : env ≤ env') :
    EnvTrProj env' U Gamma structName index major target := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      exact .canonical P hstruct hindex hmajor (Hwf.mono Henv)

/-- Reinterpreting an unchanged expansion in a definitionally equal context
is ordinary typing transport, not projection-specific compatibility. -/
theorem defeqCtx
    (H : EnvTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    EnvTrProj env U GammaTwo structName index major target := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      exact .canonical P hstruct hindex hmajor (Hwf.defeqCtx Henv Hctx)

theorem sourceWF
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma major := by
  cases H with
  | canonical P _ _ hmajor Hwf =>
      simpa [hmajor] using Hwf.majorWF

theorem targetWF
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma target := by
  cases H with
  | canonical P _ _ _ Hwf => exact Hwf.targetWF

theorem wf
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma target :=
  H.targetWF

/-- Fresh-name absence for projection output is derived from environment and
context well-formedness.  It does not assume that expansion preserves the
syntactic support of the major premise. -/
theorem noFreshConsts
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : OnCtx Gamma (env.IsType U)) :
    target.containsAnyConst names = false :=
  H.targetWF.noFreshConsts Henv Hfresh Hctx

/-- Universe substitution is derived componentwise from the canonical
expansion and the ordinary typing substitution theorem. -/
theorem instL
    (H : EnvTrProj env U Gamma structName index major target)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    EnvTrProj env U' (Gamma.map (VExpr.instL substitution)) structName index
      (major.instL substitution) (target.instL substitution) := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      have Hcanonical : EnvTrProj env U'
          (Gamma.map (VExpr.instL substitution)) structName index
          (major.instL substitution) (P.instL substitution).target :=
        .canonical (P.instL substitution) hstruct hindex
          (by simp [CanonicalProjectionExpansion.instL, hmajor])
          (Hwf.instL Hlevels)
      simpa using Hcanonical

/-- Context weakening is derived from the binder-aware lift of canonical
projection data and ordinary typing weakening. -/
theorem weakN
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    EnvTrProj env U Gamma' structName index (major.liftN n k)
      (target.liftN n k) := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      have Hcanonical : EnvTrProj env U Gamma' structName index
          (major.liftN n k) (P.liftN n k).target :=
        .canonical (P.liftN n k) hstruct hindex
          (by simp [CanonicalProjectionExpansion.liftN, hmajor])
          (Hwf.weakN Henv W)
      simpa using Hcanonical

/-- Single-cutoff weakening, expressed through the canonical binder-aware
`LiftN` operation used by projection expansions. -/
theorem weak'
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.Lift' n Gamma Gamma') :
    EnvTrProj env U Gamma' structName index (major.lift' n)
      (target.lift' n) := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      have Hcanonical : EnvTrProj env U Gamma' structName index
          (major.lift' n) (P.lift' n).target :=
        .canonical (P.lift' n) hstruct hindex
          (by simp [CanonicalProjectionExpansion.lift', hmajor])
          (Hwf.weak' Henv W)
      simpa using Hcanonical

/-- Context instantiation is derived from the binder-aware instantiation of
canonical projection data and ordinary typing substitution. -/
theorem instN
    (H : EnvTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    EnvTrProj env U Gamma structName index (major.inst substitution k)
      (target.inst substitution k) := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      have Hcanonical : EnvTrProj env U Gamma structName index
          (major.inst substitution k) (P.instN substitution k).target :=
        .canonical (P.instN substitution k) hstruct hindex
          (by simp [CanonicalProjectionExpansion.instN, hmajor])
          (Hwf.instN Henv W Hsubstitution)
      simpa using Hcanonical

/-- Inversion exposes the exact finite expansion and its derived environment
certificate.  Clients can apply `CanonicalProjectionExpansion.target_noConsts`
to these concrete fields; no universally quantified behavior is accepted. -/
theorem expansion
    (H : EnvTrProj env U Gamma structName index major target) :
    ∃ P : CanonicalProjectionExpansion,
      P.structName = structName ∧ P.index = index ∧
      P.major = major ∧ P.target = target ∧
        CanonicalProjectionExpansion.WF env U Gamma P := by
  cases H with
  | canonical P hstruct hindex hmajor Hwf =>
      exact ⟨P, hstruct, hindex, hmajor, rfl, Hwf⟩

end EnvTrProj

end Lean4Lean
