import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Tele
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ProjOrigin

/-! # Semantic facts about projection-registered constructor types (stage C)

A constructor type registered by a projection entry is well formed in an earlier environment
`E` of the declaration history (`VEnv.ProjOrigin`). Given soundness of `E`'s derivations in the
model of the final environment, which the D11 induction provides, the constructor type at any
universe levels is soundly a type (`Model.ctorTypeSound`). Its telescope of binder domains is
sound domain by domain (`Model.ctorTypePiSD`). These lemmas depend only on `SoundAt`,
`SD` and `PiSD`, not on the observation clauses. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env E : VEnv} {U : Nat} {Δ : List VExpr}

private theorem instL_wrapForalls_aux (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls ds body).instL ls =
      VExpr.wrapForalls (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢
    rw [ih]

/-- The soundness hypothesis on an earlier environment `E`. -/
def SoundEnvAt (env E : VEnv) (U : Nat) (Δ : List VExpr) : Prop :=
  ∀ {Γ t t' T}, E.IsDefEqStrong U Γ t t' T → SoundAt env U Δ Γ t t' T

/-- A closed type of `E`, at universe levels, is soundly a type. -/
theorem typeSound_of (hE : E.Ordered) (hsE : SoundEnvAt env E U Δ) {u0 : Nat} {T0 : VExpr}
    (hT : E.IsType u0 [] T0) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ∃ w, SoundAt env U Δ [] (T0.instL ls) (T0.instL ls) (.sort w) := by
  obtain ⟨w, h⟩ := IsType.instL hls hT
  exact ⟨w, hsE (IsDefEq.strong hE (show OnCtx [] (E.IsType U) from trivial) h)⟩

/-- The domains and codomains of a Pi telescope typed in `E` are sound, with strong
derivations in any extension `env` of `E`. -/
theorem piSD_of (hE : E.Ordered) (hle : E ≤ env) (hsE : SoundEnvAt env E U Δ) :
    ∀ {Γ ds R u}, OnCtx Γ (E.IsType U) → E.HasType U Γ (VExpr.wrapForalls ds R) (.sort u) →
      PiSD env U Δ Γ ds R
  | _, [], _, _, _, _ => .nil
  | Γ, A :: ds, R, u, hΓ, h => by
    obtain ⟨⟨v, hA⟩, ⟨w, hB⟩⟩ := HasType.forallE_inv hE h
    have sA := IsDefEq.strong hE hΓ hA
    have hΓ' : OnCtx (A :: Γ) (E.IsType U) := ⟨hΓ, v, hA⟩
    have sB := IsDefEq.strong hE hΓ' hB
    exact .cons ⟨sA.mono hle, hsE sA⟩ ⟨sB.mono hle, hsE sB⟩ (piSD_of hE hle hsE hΓ' hB)

/-- **The registered constructor type is soundly a type**, at any well-formed universe levels,
given soundness of the environment in which the projection entry's constructor was checked. -/
theorem ctorTypeSound (henv : env.WF) {S : Name} {info : VProjectionInfo}
    (hproj : env.projections S info)
    (hsE : ∀ {E : VEnv}, E.Ordered → E ≤ env → (∃ (base : VEnv) (dsb : List VDecl) (cis : List VConstVal), base.WF' dsb ∧
      base.addConstVals cis = some E) → SoundEnvAt env E U Δ)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ∃ w, SoundAt env U Δ [] (info.ctorType.instL ls) (info.ctorType.instL ls) (.sort w) := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨base, envTypes, dsb, decl, type, ctor, hbase, htypes, hle, hord, -, -, -, hu, -, -, -,
    -, hct, -, hwf, -, -⟩ := H.projOrigin hproj
  rw [hct]
  exact typeSound_of hord (hsE hord hle ⟨base, dsb, _, hbase, htypes⟩) hwf hls

/-- **The registered constructor type's telescope is sound**, domain by domain. -/
theorem ctorTypePiSD (henv : env.WF) {S : Name} {info : VProjectionInfo}
    (hproj : env.projections S info)
    (hsE : ∀ {E : VEnv}, E.Ordered → E ≤ env → (∃ (base : VEnv) (dsb : List VDecl) (cis : List VConstVal), base.WF' dsb ∧
      base.addConstVals cis = some E) → SoundEnvAt env E U Δ)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) {doms : List VExpr} {R : VExpr}
    (hshape : info.ctorType = VExpr.wrapForalls doms R) :
    PiSD env U Δ [] (doms.map (·.instL ls)) (R.instL ls) := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨base, envTypes, dsb, decl, type, ctor, hbase, htypes, hle, hord, -, -, -, hu, -, -, -,
    -, hct, -, hwf, -, -⟩ := H.projOrigin hproj
  obtain ⟨w, h⟩ := IsType.instL hls hwf
  rw [← hct, hshape, instL_wrapForalls_aux] at h
  exact piSD_of hord hle (hsE hord hle ⟨base, dsb, _, hbase, htypes⟩) trivial h

end Model
end VEnv
end Lean4Lean
