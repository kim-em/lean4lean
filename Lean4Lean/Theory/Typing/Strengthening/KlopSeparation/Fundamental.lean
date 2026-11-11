import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqConst

/-! # The fundamental theorem of the Klop model

`KlopInventory.sound`: in an environment with the Klop inventory, every strong derivation at
universe-parameter count `0` satisfies the semantic judgment `Sem` together with the head
invariant `SpineOK` on both sides (`SemS`). The induction is assembled here from the rule
cases proved in `Sound.lean`, `SoundLam.lean`, `SoundBeta.lean`, `SoundEta.lean` and
`Spine.lean`.

**Open obligations** (named theorems with `sorry`, each with a docstring):

* `constOK_EqRec`: `Eq.rec` is an element of its declared type (the other eight constants
  are proved in `Consts.lean`, `EqConsts.lean` and `EqConst.lean`);
* `KlopInventory.sem_extra`: the two definitional equations (`extra`);
* `KlopInventory.sem_pat`: the ι rule of `Eq.rec` (`pat`).

The four projection rules have no instance: `no_projDF`, `no_proj`/`no_projIota`, and the
index count of `eqProjInfo` for `structEta` and `unitLike`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower

/-- The semantic judgment with the head invariant on both sides. -/
def SemS (𝕋 : UniverseTower) (env : VEnv) (Γ : List VExpr) (a b A : VExpr) : Prop :=
  𝕋.Sem Γ a b A ∧ ∀ ρ w, 𝕋.ValOK Γ ρ w → 𝕋.SpineOK env ρ w a A ∧ 𝕋.SpineOK env ρ w b A

end UniverseTower

variable {env : VEnv}

/-- **Open obligation: `Eq.rec`.** `⟦Eq.rec.{v, u}⟧` is an element of the denotation of its
declared type, and `recVal` realizes it when the motive universe is `0`.

Missing: six nested abstractions; the body `recBody` is an element of the fibre `M b •`
(the fibres of the motive over coarsely related endpoints have the same elements,
`ValidAny.tyRel_same`; the successor is used only in the fibre `T`) and respects the coarse
relations in every argument; `recVal` applied to six realizers reduces to the minor premise's
value when the major is `r` (then the endpoints are identical) and to `bot` otherwise. -/
theorem constOK_EqRec (𝕋 : UniverseTower) (ls : List VLevel) :
    𝕋.ConstOK ``Eq.rec ls (canonicalEqRecType.instL ls) := by
  sorry

/-- The constant rule: every constant of the environment satisfies the semantic judgment.
Depends on `constOK_EqRec`. -/
theorem KlopInventory.sem_const (𝕋 : UniverseTower) (heq : env.HasCanonicalEq)
    (K : KlopInventory env)
    {Γ : List VExpr} {c : Name} {ci : VConstant} {ls ls' : List VLevel}
    (h : env.constants c = some ci) (hl : ls.length = ci.uvars)
    (hls : List.Forall₂ (· ≈ ·) ls ls') {u : VLevel}
    (HT : 𝕋.Sem Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u)) :
    𝕋.Sem Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  refine UniverseTower.sem_const_of ?_ (UniverseTower.constDen_congr hls) HT
  rcases K.constants_only c ci h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases Option.some.inj (heq.1.symm.trans h); exact UniverseTower.constOK_Eq ls
  · cases Option.some.inj (heq.2.1.symm.trans h); exact UniverseTower.constOK_EqRefl ls
  · cases Option.some.inj (heq.2.2.1.symm.trans h); exact constOK_EqRec 𝕋 ls
  · cases Option.some.inj (K.T.symm.trans h); exact UniverseTower.constOK_T ls
  · cases Option.some.inj (K.E.symm.trans h); exact UniverseTower.constOK_E ls
  · cases Option.some.inj (K.P.symm.trans h); exact UniverseTower.constOK_P ls
  · cases Option.some.inj (K.H.symm.trans h)
    have := UniverseTower.constOK_H (𝕋 := 𝕋) ls
    simpa [VExpr.instL, VExpr.eqApp, VLevel.inst] using this
  · cases Option.some.inj (K.C.symm.trans h); exact UniverseTower.constOK_C ls
  · cases Option.some.inj (K.Fix.symm.trans h); exact UniverseTower.constOK_Fix ls

/-- **Open obligation: the definitional equations of `C` and `Fix`.**

Missing: `den ρ klopC = den ρ klopCBody` (the body is an `Eq.rec` over `T` with endpoints `x`
and `x + 1`, which differ, so `recBody` returns `x + 1`; the arguments have to be shown to
lie in the successive domains so that the six `mkApp (mkLam …)` reduce), and
`den ρ klopFix = den ρ klopFixBody` (both are `•`: the body is an abstraction over the empty
proposition). -/
theorem KlopInventory.sem_extra (𝕋 : UniverseTower) (K : KlopInventory env)
    {Γ : List VExpr} {df : VDefEq} {ls : List VLevel} (h : env.defeqs df)
    (hl : ls.length = df.uvars)
    (Hl : 𝕋.SemS env Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls))
    (Hr : 𝕋.SemS env Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)) :
    𝕋.Sem Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  sorry

/-- **Open obligation: the ι rule of `Eq.rec`.**

Missing: from the head invariant of the redex `Eq.rec α a M m b (Eq.refl α' a')` (the chain
of its six arguments through the declared type of `Eq.rec`), when `⟦α⟧ = T` and the fibre is
`T` all six prefixes are non-collapsed, so the value `r` of the major premise realizes
`⟦@Eq α a b⟧`, hence the endpoints are identical and `recBody` returns the minor premise; in
every other case `recBody` returns the minor premise or `•` by definition. The reduct is a
β-chain selecting the minor premise. -/
theorem KlopInventory.sem_pat (𝕋 : UniverseTower) (K : KlopInventory env)
    {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2}
    (hp : env.pats p r) (hm : p.Matches e m1 m2)
    (He : 𝕋.SemS env Γ e e A) (Hr : 𝕋.SemS env Γ (r.1.apply m1 m2) (r.1.apply m1 m2) A) :
    𝕋.Sem Γ e (r.1.apply m1 m2) A := by
  sorry

/-- `projDF` has no instance: the projection entry of `Eq` has no field, so `fieldType` is
`none`. After instantiating the two parameters the constructor type is an application of
`Eq`, which is not a Π-type. -/
theorem KlopInventory.no_projDF (K : KlopInventory env) {typeName : Name}
    {info : VProjectionInfo} (h : env.projections typeName info) {levels : List VLevel}
    {params : List VExpr} {index : Nat} {sourceMajor fieldType : VExpr}
    (hlv : levels.length = info.uvars) (hpar : params.length = info.nparams) :
    info.fieldType typeName levels params index sourceMajor ≠ some fieldType := by
  have := (K.projections_only _ _ h).2
  subst this
  match params, hpar with
  | [p0, p1], _ =>
    simp [VProjectionInfo.fieldType, eqProjInfo, canonicalEqReflType, hlv,
      VProjectionInfo.instantiateProjectionParameters,
      VProjectionInfo.instantiateProjectionFields, VExpr.instL, VExpr.inst]

/-- A term is not a projection. -/
def NotProj (e : VExpr) : Prop := ∀ n i x, e ≠ .proj n i x

theorem notProj_inst {e e' : VExpr} (he : NotProj e) (he' : NotProj e') :
    NotProj (e.inst e') := by
  intro n i x h
  cases e with
  | bvar j =>
    simp only [VExpr.inst, VExpr.instVar] at h
    split at h
    · cases h
    · split at h
      · rw [VExpr.liftN_zero] at h; exact he' _ _ _ h
      · cases h
  | proj n' i' x' => exact he _ _ _ rfl
  | sort => cases h
  | const => cases h
  | app => cases h
  | lam => cases h
  | forallE => cases h

/-- **No side of a strong derivation is a projection.** A `.proj` side can only be introduced
by `projDF`, which has no instance; every other rule takes its sides from premises or builds
them with another constructor. -/
theorem KlopInventory.no_proj (K : KlopInventory env) {Γ : List VExpr} {a b A : VExpr}
    (H : env.IsDefEqStrong 0 Γ a b A) : NotProj a ∧ NotProj b := by
  induction H with
  | bvar => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | constDF => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | appDF => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | projDF hinfo _ hlv hpar _ hft _ _ _ _ _ _ _ _ _ =>
    exact absurd hft (K.no_projDF hinfo hlv hpar)
  | lamDF => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | forallEDF => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ _ _ ihe ihe' _ _ =>
    exact ⟨fun _ _ _ h => (nomatch h), notProj_inst ihe.1 ihe'.1⟩
  | eta _ _ _ _ _ _ _ _ _ _ _ ihe _ _ => exact ⟨fun _ _ _ h => (nomatch h), ihe.1⟩
  | proofIrrel _ _ _ _ ihh ihh' => exact ⟨ihh.1, ihh'.1⟩
  | extra h _ _ _ _ _ _ _ _ _ _ _ ihl ihr => exact ⟨ihl.1, ihr.1⟩
  | pat _ _ _ _ _ _ ihe ihr _ => exact ⟨ihe.1, ihr.1⟩
  | projIota _ _ _ _ ihs _ => exact (ihs.1 _ _ _ rfl).elim
  | structEta hinfo _ hi _ _ _ _ =>
    have := (K.projections_only _ _ hinfo).2
    subst this
    exact absurd hi (by decide)
  | unitLike hinfo _ hi _ _ _ _ _ =>
    have := (K.projections_only _ _ hinfo).2
    subst this
    exact absurd hi (by decide)

/-- `projIota` has no instance. -/
theorem KlopInventory.no_projIota (K : KlopInventory env) {Γ : List VExpr}
    {typeName : Name} {index : Nat} {x b A : VExpr}
    (H : env.IsDefEqStrong 0 Γ (.proj typeName index x) b A) : False :=
  (K.no_proj H).1 _ _ _ rfl

/-- **The fundamental theorem of the model**, modulo the open obligations above. -/
theorem KlopInventory.sound (𝕋 : UniverseTower) (heq : env.HasCanonicalEq)
    (K : KlopInventory env)
    {Γ : List VExpr} {a b A : VExpr} (H : env.IsDefEqStrong 0 Γ a b A) :
    𝕋.SemS env Γ a b A := by
  induction H with
  | bvar h _ _ _ =>
    exact ⟨UniverseTower.sem_bvar h, fun ρ w _ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), UniverseTower.spineOK_of_not_spine (fun h => h)⟩⟩
  | symm _ ih => exact ⟨ih.1.symm, fun ρ w hρ => ⟨(ih.2 ρ w hρ).2, (ih.2 ρ w hρ).1⟩⟩
  | trans _ _ ih1 ih2 =>
    exact ⟨ih1.1.trans ih2.1, fun ρ w hρ => ⟨(ih1.2 ρ w hρ).1, (ih2.2 ρ w hρ).2⟩⟩
  | sortDF _ _ h =>
    exact ⟨UniverseTower.sem_sort h, fun ρ w _ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), UniverseTower.spineOK_of_not_spine (fun h => h)⟩⟩
  | @constDF c ci ls ls' u Γ h _ _ hl hls _ _ _ _ ih =>
    refine ⟨K.sem_const 𝕋 heq h hl hls ih.1, fun ρ w hρ => ⟨UniverseTower.spineOK_const h, ?_⟩⟩
    exact (UniverseTower.spineOK_const (ls := ls') h).defeq (ih.1 ρ w hρ).2.1.symm
  | appDF _ _ _ _ _ _ _ ihA ihB ihf iha ihBa =>
    refine ⟨UniverseTower.Sem.app ihA.1 ihB.1 ihf.1 iha.1 ihBa.1, fun ρ w hρ => ?_⟩
    obtain ⟨-, haa', ham, hav, -⟩ := iha.1 ρ w hρ
    refine ⟨(ihf.2 ρ w hρ).1.app ham fun h => (hav h).1, ?_⟩
    have h2 := (ihf.2 ρ w hρ).2.app (haa' ▸ ham) fun h => (hav h).2
    exact h2.defeq (ihBa.1 ρ w hρ).2.1.symm
  | projDF hinfo _ hlv hpar _ hft _ _ _ _ _ _ _ _ _ =>
    exact absurd hft (K.no_projDF hinfo hlv hpar)
  | lamDF _ _ _ _ _ _ _ ihA ihB _ ihb _ =>
    exact ⟨UniverseTower.Sem.lam ihA.1 ihB.1 ihb.1, fun ρ w _ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), UniverseTower.spineOK_of_not_spine (fun h => h)⟩⟩
  | forallEDF _ _ _ _ _ ihA ihB _ =>
    exact ⟨UniverseTower.Sem.forallE ihA.1 ihB.1, fun ρ w _ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), UniverseTower.spineOK_of_not_spine (fun h => h)⟩⟩
  | defeqDF _ _ _ ihT ih =>
    refine ⟨ihT.1.defeq ih.1, fun ρ w hρ => ?_⟩
    have hAB := (ihT.1 ρ w hρ).2.1
    exact ⟨(ih.2 ρ w hρ).1.defeq hAB, (ih.2 ρ w hρ).2.defeq hAB⟩
  | beta _ _ _ _ _ _ _ _ ihA _ ihe ihe' _ ihr =>
    exact ⟨UniverseTower.Sem.beta ihA.1 ihe.1 ihe'.1 ihr.1, fun ρ w hρ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), (ihr.2 ρ w hρ).1⟩⟩
  | eta _ _ _ _ _ _ _ _ ihA ihB _ ihe _ _ =>
    exact ⟨UniverseTower.Sem.eta ihA.1 ihB.1 ihe.1, fun ρ w hρ =>
      ⟨UniverseTower.spineOK_of_not_spine (fun h => h), (ihe.2 ρ w hρ).1⟩⟩
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact ⟨UniverseTower.Sem.proofIrrel ihp.1 ihh.1 ihh'.1, fun ρ w hρ =>
      ⟨(ihh.2 ρ w hρ).1, (ihh'.2 ρ w hρ).1⟩⟩
  | extra h _ hl _ _ _ _ _ _ _ _ _ ihl ihr =>
    exact ⟨K.sem_extra 𝕋 h hl ihl ihr, fun ρ w hρ => ⟨(ihl.2 ρ w hρ).1, (ihr.2 ρ w hρ).1⟩⟩
  | pat hp hm _ _ _ _ ihe ihr _ =>
    exact ⟨K.sem_pat 𝕋 hp hm ihe ihr, fun ρ w hρ => ⟨(ihe.2 ρ w hρ).1, (ihr.2 ρ w hρ).1⟩⟩
  | projIota _ hs _ _ _ _ => exact (K.no_projIota hs).elim
  | structEta hinfo _ hi _ _ _ _ =>
    have := (K.projections_only _ _ hinfo).2
    subst this
    exact absurd hi (by decide)
  | unitLike hinfo _ hi _ _ _ _ _ =>
    have := (K.projections_only _ _ hinfo).2
    subst this
    exact absurd hi (by decide)

/-- Definitionally equal closed terms have equal denotations. Depends on
`KlopInventory.sound`. -/
theorem KlopInventory.den_sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {a b A : VExpr} (H : env.IsDefEq 0 [] a b A) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ a = 𝕋.den ρ b :=
  ((K.sound 𝕋 heq (H.strong henv.orderedStrong (Γ := []) trivial)).1 ρ (fun _ => .bot)
    (𝕋.valOK_nil ρ _)).2.1

end VEnv.Strengthening
end Lean4Lean
