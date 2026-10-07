import Lean4Lean.Theory.Typing.Countermodel.EnvWF
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# The larger-context derivation

In the smaller context

```text
K : (v : F c) → P v → Type,  v : F c,  p : I c v (leftMap v),  r : J c v (rightMap v)
```

let `SI := I.rec (motive := fun _ _ _ _ => Type) K c v (leftMap v) p` and
`SJ := J.rec (motive := fun _ _ _ _ => Type) K c v (rightMap v) r`. After adding
`q : P v`, proof irrelevance, the iota rules, beta and congruence give

```text
SI ≡ I.rec .. (I.mk v q) ≡ K v q ≡ J.rec .. (J.mk v q) ≡ SJ   : Type
```

(`InductiveStrengtheningPressure.Abstract.proofMajorJoin` in
`docs/inductives/SingletonStrengthening.lean` is the template).
-/

namespace Lean4Lean.Countermodel

open VEnv

def lvl2 : VLevel := .succ lvl1

/-- `(v : F c) → P v → Type`. -/
def Kty : VExpr := .forallE eFc (.forallE (.app eP (.bvar 0)) (.sort lvl1))

namespace FamSpec
variable (sp : FamSpec)

/-- The constant motive `fun n v w h => Type`. -/
def mot : VExpr :=
  .lam eC (.lam (.app eF (.bvar 0)) (.lam (.app eF (.bvar 1))
    (.lam (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl1))))

/-- The recursor at elimination universe `Sort 2`. -/
def recC : VExpr := .const sp.recName [lvl2]

/-- All constants, the recursor and its iota rule are installed. -/
structure Full (E : VEnv) : Prop where
  B : Base E
  m : sp.MapOK E
  f : sp.FamOK E
  c : sp.CtorOK E
  r : sp.RecOK E
  d : E.defeqs sp.rule

end FamSpec

/-- The smaller context `r, p, v, K` (innermost first). -/
def ctxS : List VExpr :=
  [specJ.famApp ec (.bvar 1) (.app specJ.eMap (.bvar 1)),
    specI.famApp ec (.bvar 0) (.app specI.eMap (.bvar 0)), eFc, Kty]

/-- The larger context, with `q : P v` innermost. -/
def ctxL : List VExpr := .app eP (.bvar 2) :: ctxS

/-- `I.rec (fun _ _ _ _ => Type) K c v (leftMap v) p` in the smaller context. -/
def SI : VExpr :=
  VExpr.mkApps specI.recC [specI.mot, .bvar 3, ec, .bvar 2, .app specI.eMap (.bvar 2), .bvar 1]

/-- `J.rec (fun _ _ _ _ => Type) K c v (rightMap v) r` in the smaller context. -/
def SJ : VExpr :=
  VExpr.mkApps specJ.recC [specJ.mot, .bvar 3, ec, .bvar 2, .app specJ.eMap (.bvar 2), .bvar 0]

theorem fullI : specI.Full envCM :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl⟩, ⟨rfl⟩, ⟨rfl⟩, ⟨rfl⟩, .inr (.inl rfl)⟩

theorem fullJ : specJ.Full envCM :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl⟩, ⟨rfl⟩, ⟨rfl⟩, ⟨rfl⟩, .inl rfl⟩

theorem envCM_ordered : envCM.Ordered := envCM_wf.ordered

/-! ## Beta for the constant motive -/

section
variable {E : VEnv} {U : Nat} {Γ : List VExpr}

theorem beta' {A e B a e' B' : VExpr} (h1 : E.HasType U (A::Γ) e B) (h2 : E.HasType U Γ a A)
    (he : e.inst a = e') (hB : B.inst a = B') : E.IsDefEq U Γ (.app (.lam A e) a) e' B' :=
  he ▸ hB ▸ .beta h1 h2

theorem appDF' {f f' a a' A B B' : VExpr} (h1 : E.IsDefEq U Γ f f' (.forallE A B))
    (h2 : E.IsDefEq U Γ a a' A) (hB : B.inst a = B') :
    E.IsDefEq U Γ (.app f a) (.app f' a') B' :=
  hB ▸ .appDF h1 h2

end

namespace FamSpec
variable {sp : FamSpec} {E : VEnv} {Γ : List VExpr}

def motT (sp : FamSpec) : VExpr :=
  .forallE eC (.forallE (.app eF (.bvar 0)) (.forallE (.app eF (.bvar 1))
    (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl2))))

theorem motT_eq : sp.motiveType.instL [lvl2] = sp.motT := rfl

section
variable (B : Base E) (hf : sp.FamOK E)
include B hf

theorem tySort1' {Γ} : E.HasType 0 Γ (.sort lvl1) (.sort lvl2) :=
  HasType.sort (by simp [lvl1, VLevel.WF])

theorem ty_mot_layers :
    E.HasType 0 (idxCtx Γ) (.lam (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl1))
      (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl2)) ∧
    E.HasType 0 (.app eF (.bvar 0) :: eC :: Γ)
      (.lam (.app eF (.bvar 1)) (.lam (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl1)))
      (.forallE (.app eF (.bvar 1)) (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0))
        (.sort lvl2))) ∧
    E.HasType 0 (eC :: Γ)
      (.lam (.app eF (.bvar 0)) (.lam (.app eF (.bvar 1))
        (.lam (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl1))))
      (.forallE (.app eF (.bvar 0)) (.forallE (.app eF (.bvar 1))
        (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lvl2)))) ∧
    E.HasType 0 Γ sp.mot sp.motT := by
  have l3 := HasType.lam (ty_idx_fam (Γ := Γ) B hf) (tySort1' B hf)
  have l2 := HasType.lam (ty_idx_F1 (Γ := Γ) B hf) l3
  have l1 := HasType.lam (ty_idx_F0 (Γ := Γ) B hf) l2
  exact ⟨l3, l2, l1, HasType.lam (tyC (Γ := Γ) B) l1⟩

variable (hm : sp.MapOK E) (hE : E.Ordered)
include hm hE

/-- `(fun n v w h => Type) c v (map v) h ≡ Type`. -/
theorem motBeta {v h : VExpr} (hv : E.HasType 0 Γ v eFc)
    (hh : E.HasType 0 Γ h (sp.famApp ec v (.app sp.eMap v))) :
    E.IsDefEq 0 Γ (app4 sp.mot ec v (.app sp.eMap v) h) (.sort lvl1) (.sort lvl2) := by
  obtain ⟨-, -, l1, -⟩ := ty_mot_layers (Γ := Γ) B hf
  have hw := tyMapApp hm hv
  -- first argument
  have t1 : E.IsDefEq 0 Γ (.app sp.mot ec)
      (.lam eFc (.lam eFc (.lam (sp.famApp ec (.bvar 1) (.bvar 0)) (.sort lvl1))))
      (.forallE eFc (.forallE eFc (.forallE (sp.famApp ec (.bvar 1) (.bvar 0)) (.sort lvl2)))) :=
    beta' l1 (tyc B) rfl rfl
  -- second argument
  have b2 : E.HasType 0 (eFc :: Γ) (.lam eFc (.lam (sp.famApp ec (.bvar 1) (.bvar 0)) (.sort lvl1)))
      (.forallE eFc (.forallE (sp.famApp ec (.bvar 1) (.bvar 0)) (.sort lvl2))) :=
    HasType.lam (tyFc B) (HasType.lam
      (tyFamApp hf (tyc B) (HasType.bvar (.succ .zero)) (HasType.bvar .zero)) (tySort1' B hf))
  have t2 : E.IsDefEq 0 Γ (.app (.app sp.mot ec) v)
      (.lam eFc (.lam (sp.famApp ec v.lift (.bvar 0)) (.sort lvl1)))
      (.forallE eFc (.forallE (sp.famApp ec v.lift (.bvar 0)) (.sort lvl2))) :=
    (appDF' t1 hv (by simp [VExpr.inst, famApp, eFam, ec, eFc, eF])).trans
      (beta' b2 hv (by simp [VExpr.inst, famApp, eFam, ec, eFc, eF])
        (by simp [VExpr.inst, famApp, eFam, ec, eFc, eF]))
  -- third argument
  have hv' : E.HasType 0 (eFc :: Γ) v.lift eFc := hv.weak hE
  have b3 : E.HasType 0 (eFc :: Γ) (.lam (sp.famApp ec v.lift (.bvar 0)) (.sort lvl1))
      (.forallE (sp.famApp ec v.lift (.bvar 0)) (.sort lvl2)) :=
    HasType.lam (tyFamApp hf (tyc B) hv' (HasType.bvar .zero)) (tySort1' B hf)
  have t3 : E.IsDefEq 0 Γ (.app (.app (.app sp.mot ec) v) (.app sp.eMap v))
      (.lam (sp.famApp ec v (.app sp.eMap v)) (.sort lvl1))
      (.forallE (sp.famApp ec v (.app sp.eMap v)) (.sort lvl2)) :=
    (appDF' t2 hw (by simp [VExpr.inst, VExpr.inst_lift, famApp, eFam, ec])).trans
      (beta' b3 hw (by simp [VExpr.inst, VExpr.inst_lift, famApp, eFam, ec])
        (by simp [VExpr.inst, VExpr.inst_lift, famApp, eFam, ec]))
  -- fourth argument
  have b4 : E.HasType 0 (sp.famApp ec v (.app sp.eMap v) :: Γ) (.sort lvl1) (.sort lvl2) :=
    tySort1' B hf
  exact (appDF' t3 hh rfl).trans (beta' b4 hh rfl rfl)

end
end FamSpec
/-! ## The recursor spine and its reduction in the larger context -/

namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

/-- The minor premise type at the constant motive. -/
def minorD (sp : FamSpec) : VExpr :=
  .forallE eFc (.forallE (.app eP (.bvar 0))
    (app4 sp.mot ec (.bvar 1) (.app sp.eMap (.bvar 1)) (sp.ctorApp (.bvar 1) (.bvar 0))))

theorem minorD_eq : (sp.minorType.instL [lvl2]).inst sp.mot = sp.minorD := rfl

/-- The recursor spine `rec mot K c v (map v)` in the larger context. -/
def spine (sp : FamSpec) : VExpr :=
  VExpr.mkApps sp.recC [sp.mot, .bvar 4, ec, .bvar 3, .app sp.eMap (.bvar 3)]

section
variable (Fu : sp.Full E) (hE : E.Ordered)
include Fu hE

theorem Kconv {Γ} : ∃ u, E.IsDefEq 0 Γ Kty sp.minorD (.sort u) := by
  have hv : E.HasType 0 (.app eP (.bvar 0) :: eFc :: Γ) (.bvar 1) eFc := HasType.bvar (.succ .zero)
  have hh : E.HasType 0 (.app eP (.bvar 0) :: eFc :: Γ) (.bvar 0) (.app eP (.bvar 1)) :=
    HasType.bvar .zero
  have hb := motBeta Fu.B Fu.f Fu.m hE hv (tyCtorApp Fu.c hv hh)
  exact ⟨_, .forallEDF (tyFc Fu.B) (.forallEDF (tyPapp Fu.B (HasType.bvar .zero)) hb.symm)⟩

theorem ty_K : E.HasType 0 ctxL (.bvar 4) sp.minorD := by
  obtain ⟨_, h⟩ := Kconv (Γ := ctxL) Fu hE
  exact .defeqDF h (HasType.bvar (.succ (.succ (.succ (.succ .zero)))))

theorem ty_v : E.HasType 0 ctxL (.bvar 3) eFc := HasType.bvar (.succ (.succ (.succ .zero)))
theorem ty_q : E.HasType 0 ctxL (.bvar 0) (.app eP (.bvar 3)) := HasType.bvar .zero

theorem ty_mot {Γ} : E.HasType 0 Γ sp.mot sp.motT := (ty_mot_layers Fu.B Fu.f).2.2.2

theorem ty_spine : E.HasType 0 ctxL sp.spine
    (.forallE (sp.famApp ec (.bvar 3) (.app sp.eMap (.bvar 3)))
      (app4 sp.mot ec (.bvar 4) (.app sp.eMap (.bvar 4)) (.bvar 0))) := by
  have hrec : E.HasType 0 ctxL sp.recC (sp.recType.instL [lvl2]) :=
    HasType.const Fu.r.recursor (by simp [lvl2, lvl1, VLevel.WF]) rfl
  have hv := ty_v Fu hE
  exact HasType.app (HasType.app (HasType.app (HasType.app (HasType.app hrec (ty_mot Fu hE))
    (ty_K Fu hE)) (tyc Fu.B)) hv) (tyMapApp Fu.m hv)

end
end FamSpec
/-! ## The iota step -/

namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

theorem lvl2_wf : ∀ l ∈ [lvl2], l.WF 0 := by simp [lvl2, lvl1, VLevel.WF]

/-- Beta-reduce a four-binder lambda applied to `mot, K, v, q`, given open typings
of its layers in the larger context. -/
theorem beta4 (hE : E.Ordered) {A1 A2 A3 A4 b T4 : VExpr}
    (O1 : E.HasType 0 (A1 :: ctxL) (.lam A2 (.lam A3 (.lam A4 b)))
      (.forallE A2 (.forallE A3 (.forallE A4 T4))))
    (O2 : E.HasType 0 (A2 :: A1 :: ctxL) (.lam A3 (.lam A4 b)) (.forallE A3 (.forallE A4 T4)))
    (O3 : E.HasType 0 (A3 :: A2 :: A1 :: ctxL) (.lam A4 b) (.forallE A4 T4))
    (O4 : E.HasType 0 (A4 :: A3 :: A2 :: A1 :: ctxL) b T4)
    {a1 a2 a3 a4 : VExpr}
    (h1 : E.HasType 0 ctxL a1 A1) (h2 : E.HasType 0 ctxL a2 (A2.inst a1))
    (h3 : E.HasType 0 ctxL a3 ((A3.inst a1 1).inst a2))
    (h4 : E.HasType 0 ctxL a4 (((A4.inst a1 2).inst a2 1).inst a3)) :
    E.IsDefEq 0 ctxL (app4 (.lam A1 (.lam A2 (.lam A3 (.lam A4 b)))) a1 a2 a3 a4)
      ((((b.inst a1 3).inst a2 2).inst a3 1).inst a4)
      ((((T4.inst a1 3).inst a2 2).inst a3 1).inst a4) := by
  -- open typings with the earlier arguments substituted
  have P2 := HasType.instN hE (.succ .zero) O2 h1
  have P3 := HasType.instN hE (.succ .zero) (HasType.instN hE (.succ (.succ .zero)) O3 h1) h2
  have P4 := HasType.instN hE (.succ .zero)
    (HasType.instN hE (.succ (.succ .zero))
      (HasType.instN hE (.succ (.succ (.succ .zero))) O4 h1) h2) h3
  have c1 := IsDefEq.beta O1 h1
  have c2 := (IsDefEq.appDF c1 h2).trans (IsDefEq.beta P2 h2)
  have c3 := (IsDefEq.appDF c2 h3).trans (IsDefEq.beta P3 h3)
  exact (IsDefEq.appDF c3 h4).trans (IsDefEq.beta P4 h4)

end FamSpec
namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

section
variable (Fu : sp.Full E) (hE : E.Ordered)
include Fu hE

/-- The iota rule, applied to `mot, K, v, q` and beta-reduced on both sides. -/
theorem iota_applied :
    E.IsDefEq 0 ctxL (.app sp.spine (sp.ctorApp (.bvar 3) (.bvar 0)))
      (.app (.app (.bvar 4) (.bvar 3)) (.bvar 0))
      (app4 sp.mot ec (.bvar 3) (.app sp.eMap (.bvar 3)) (sp.ctorApp (.bvar 3) (.bvar 0))) := by
  have hl := ty_rule_lhs_open (Γ0 := ctxL) Fu.B Fu.m Fu.f Fu.c Fu.r
  have hr := ty_rule_rhs_open (Γ0 := ctxL) Fu.B Fu.m Fu.f Fu.c
  have h1 : E.HasType 0 ctxL sp.mot sp.motT := ty_mot Fu hE
  have h2 : E.HasType 0 ctxL (.bvar 4) sp.minorD := ty_K Fu hE
  have h3 : E.HasType 0 ctxL (.bvar 3) eFc := ty_v Fu hE
  have h4 : E.HasType 0 ctxL (.bvar 0) (.app eP (.bvar 3)) := ty_q Fu hE
  have bl := beta4 hE (HasType.instL lvl2_wf hl.2.2.2) (HasType.instL lvl2_wf hl.2.2.1)
    (HasType.instL lvl2_wf hl.2.1) (HasType.instL lvl2_wf hl.1) h1 h2 h3 h4
  have br := beta4 hE (HasType.instL lvl2_wf hr.2.2.2) (HasType.instL lvl2_wf hr.2.2.1)
    (HasType.instL lvl2_wf hr.2.1) (HasType.instL lvl2_wf hr.1) h1 h2 h3 h4
  have ex : E.IsDefEq 0 ctxL (sp.rule.lhs.instL [lvl2]) (sp.rule.rhs.instL [lvl2])
      (sp.rule.type.instL [lvl2]) := .extra Fu.d lvl2_wf rfl
  have a4 := IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF ex h1) h2) h3) h4
  exact bl.symm.trans (a4.trans br)

theorem recRed {maj : VExpr}
    (hmaj : E.HasType 0 ctxL maj (sp.famApp ec (.bvar 3) (.app sp.eMap (.bvar 3)))) :
    E.IsDefEq 0 ctxL (.app sp.spine maj) (.app (.app (.bvar 4) (.bvar 3)) (.bvar 0))
      (.sort lvl1) := by
  have hv := ty_v Fu hE
  have hctor := tyCtorApp Fu.c hv (ty_q Fu hE)
  have pI : E.IsDefEq 0 ctxL maj (sp.ctorApp (.bvar 3) (.bvar 0))
      (sp.famApp ec (.bvar 3) (.app sp.eMap (.bvar 3))) :=
    .proofIrrel (tyFamApp Fu.f (tyc Fu.B) hv (tyMapApp Fu.m hv)) hmaj hctor
  have e1 : E.IsDefEq 0 ctxL (.app sp.spine maj) (.app sp.spine (sp.ctorApp (.bvar 3) (.bvar 0)))
      (app4 sp.mot ec (.bvar 3) (.app sp.eMap (.bvar 3)) maj) :=
    appDF' (ty_spine Fu hE) pI (by simp [VExpr.inst, app4, mot, famApp, eFam, eMap, ec, eF, eC]; exact ⟨rfl, rfl, rfl⟩)
  have e1' := IsDefEq.defeqDF (motBeta Fu.B Fu.f Fu.m hE hv hmaj) e1
  have e2' := IsDefEq.defeqDF (motBeta Fu.B Fu.f Fu.m hE hv hctor) (iota_applied Fu hE)
  exact e1'.trans e2'

end
end FamSpec

/-! ## Deliverable 2 -/

theorem SI_lift : SI.liftN 1 0 = .app specI.spine (.bvar 2) := rfl
theorem SJ_lift : SJ.liftN 1 0 = .app specJ.spine (.bvar 1) := rfl

/-- **Deliverable 2.** In the larger context the two endpoints are definitionally
equal at `Type`. -/
theorem larger_defeq : envCM.IsDefEq 0 ctxL (SI.liftN 1 0) (SJ.liftN 1 0) (.sort lvl1) := by
  have hE := envCM_ordered
  have hp : envCM.HasType 0 ctxL (.bvar 2)
      (specI.famApp ec (.bvar 3) (.app specI.eMap (.bvar 3))) :=
    HasType.bvar (.succ (.succ .zero))
  have hr : envCM.HasType 0 ctxL (.bvar 1)
      (specJ.famApp ec (.bvar 3) (.app specJ.eMap (.bvar 3))) :=
    HasType.bvar (.succ .zero)
  rw [SI_lift, SJ_lift]
  exact (FamSpec.recRed fullI hE hp).trans (FamSpec.recRed fullJ hE hr).symm

theorem ctx_lift : Ctx.LiftN 1 0 ctxS ctxL := .one

theorem ctxL_wf : OnCtx ctxL (envCM.IsType 0) := by
  have B : Base envCM := fullI.B
  refine ⟨⟨⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨_, .forallE (tyFc B) (.forallE (tyPapp B (HasType.bvar .zero)) (tySort1 B))⟩
  · exact ⟨_, tyFc B⟩
  · exact ⟨_, FamSpec.tyFamApp fullI.f (tyc B) (HasType.bvar .zero)
      (FamSpec.tyMapApp fullI.m (HasType.bvar .zero))⟩
  · exact ⟨_, FamSpec.tyFamApp fullJ.f (tyc B) (HasType.bvar (.succ .zero))
      (FamSpec.tyMapApp fullJ.m (HasType.bvar (.succ .zero)))⟩
  · exact ⟨_, tyPapp B (HasType.bvar (.succ (.succ .zero)))⟩

end Lean4Lean.Countermodel
