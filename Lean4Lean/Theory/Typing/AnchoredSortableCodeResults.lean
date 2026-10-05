import Lean4Lean.Theory.Typing.AnchoredSortableSupport
import Lean4Lean.Theory.Typing.AnchoredSortableTransferClosures
import Lean4Lean.Theory.Typing.AnchoredSortableLive
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionTyping

/-! Exact code-result closures retain a source certificate for the actual
assigned type, even when that type is not syntactically a universe. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right assigned : VExpr}

namespace SortableTermTransferResult

def fromCode (henv : env.Ordered) {profile support : Profile n} {footprint typeFootprint : Footprint}
    (certificate : SortableCert env U registry Γ locals τ right relevant profile footprint)
    (resources : footprint.Available available)
    (valueCode : TypeRelated env U registry Γ (left.subst σ) (right.subst τ) profile)
    (typeCertificate : SortableCert env U registry Γ locals σ assigned true support typeFootprint)
    (typeResources : typeFootprint.Available available) (typed : profile.HasType support)
    (typeCode : TypeRelated env U registry Γ (assigned.subst σ) (assigned.subst σ) support) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant profile :=
  ⟨⟨footprint, certificate, resources, valueCode⟩, support, typeFootprint, typeCertificate,
    typeResources, typed, typeCode, Related.of_sortable_code henv certificate.formed typed valueCode typeCode⟩

noncomputable def supportAction (henv : env.Ordered) (hscoped : registry.Scoped)
    (action : SupportAction env U registry Γ n)
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (profile : Profile n)) :
    SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (action.apply profile) :=
  fromCode henv (.support action result.certificate) result.available
    (action.codeMap henv hscoped result.related)
    (.support .flatSorts result.typeCertificate) result.typeAvailable
    ((SortableCodeAction.support (relevant := relevant) action).typedAtSorts
      (result.certificate.formed.flatSorts result.typed))
    (result.typeCode.flatSorts henv)

def computational (henv : env.Ordered)
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) :
    SortableComputationalTransferResult env U registry Γ locals σ τ available left right assigned profile where
  rank := _
  bound := Nat.le_refl _
  raw := profile
  footprint := result.footprint
  observation := .code relevant result.certificate
  adapter := by rw [raiseProfile_self]; exact .refl _
  resources := result.available
  live := result.certificate.live
  support := result.support
  typeFootprint := result.typeFootprint
  typeCertificate := result.typeCertificate
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_self] using result.typed
  rawTyped := result.typed
  typeCode := result.typeCode
  related := by simpa only [raiseProfile_self] using result.termRelated
  rawRelated := (result.termRelated.symm henv).left_diagonal

def retag (result : SortableTermTransferResult env U registry Γ locals σ τ available
    left right assigned relevant profile) (formed : profile.HasType (.sort nextRelevant)) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned nextRelevant profile :=
  { result with certificate := .observe (.code relevant result.certificate) formed }

def pad (henv : env.Ordered)
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant profile.pad :=
  fromCode henv result.certificate.pad result.available (result.related.pad henv)
    result.typeCertificate.pad result.typeAvailable result.typed.pad (result.typeCode.pad henv)

def down (henv : env.Ordered) {profile : Profile (n + 1)}
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant profile.down :=
  fromCode henv result.certificate.down result.available (result.related.down henv)
    result.typeCertificate.down result.typeAvailable result.typed.down (result.typeCode.down henv)

def unpad (henv : env.Ordered) {profile : Profile n}
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile.pad) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant profile := by
  simpa only [Profile.down_pad] using result.down henv

def select (henv : env.Ordered) {profile : Profile n} {atom : Atom n}
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) (member : atom ∈ profile.atoms) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant (.singleton atom) :=
  fromCode henv (.select result.certificate member) result.available (result.related.singleton member)
    result.typeCertificate result.typeAvailable (result.typed.singleton_of_mem member) result.typeCode

def focusMinimal (henv : env.Ordered) {value focused support : Profile n}
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant support) (minimal : Minimal value focused) (bound : focused ≤ support) :
    SortableTermTransferResult env U registry Γ locals σ τ available left right assigned relevant focused :=
  fromCode henv (.focusMinimal result.certificate minimal bound) result.available
    (result.related.focusMinimal henv minimal bound) result.typeCertificate result.typeAvailable
    (result.typed.restrict bound minimal.formation.wf_value) result.typeCode

theorem map (henv : env.Ordered) (hscoped : registry.Scoped) {profile : Profile n} {a b : Atom n}
    (view : AtomView env U registry Γ a b)
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) :
    Nonempty (SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (view.mapType profile)) := by
  obtain ⟨support, footprint, ⟨certificate⟩, resources, typed, code⟩ :=
    result.typeCertificate.mapSupport view result.certificate.formed result.typed result.typeCode henv result.typeAvailable
  exact ⟨fromCode henv (.map view result.certificate) result.available
    (view.codeMap henv hscoped result.related) certificate resources typed code⟩

theorem sortPad (henv : env.Ordered)
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (Profile.sort (n := n) flag)) :
    Nonempty (SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (Profile.sort (n := n + 1) flag)) := by
  have singleton : ∃ atom : Atom n, Profile.sort (n := n) flag = .singleton atom := by
    cases n <;> exact ⟨_, rfl⟩
  obtain ⟨atom, equal⟩ := singleton
  obtain ⟨cover, ⟨certificate⟩, typed, code⟩ := result.typeCertificate.sortCover
    (equal ▸ result.certificate.formed) (equal ▸ result.typed) result.typeCode henv
  rw [← equal] at typed
  exact ⟨fromCode henv result.certificate.sortPad result.available result.related.sortPad
    certificate.sortPad result.typeAvailable typed.sortPad code.sortPad⟩

theorem familyPad (henv : env.Ordered) {family : FamilyData (Profile n)}
    (result : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (Profile.singleton (n := n + 1) (.family family))) :
    Nonempty (SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (Profile.singleton (n := n + 2) (.family family.pad))) := by
  obtain ⟨cover, ⟨certificate⟩, typed, code⟩ := result.typeCertificate.sortCover
    result.certificate.formed result.typed result.typeCode henv
  exact ⟨fromCode henv result.certificate.familyPad result.available (result.related.familyPad henv)
    certificate.sortPad result.typeAvailable typed.familyPad code.sortPad⟩

def union (henv : env.Ordered) {p q : Profile n}
    (first : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant p)
    (second : SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant q) :
    SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant (p.union q) := by
  have combine {a b : VExpr} {p q : Profile n}
      (one : TypeRelated env U registry Γ a b p) (two : TypeRelated env U registry Γ a b q) :
      TypeRelated env U registry Γ a b (p.union q) := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim (fun h => one.singleton h) (fun h => two.singleton h)
  exact fromCode henv (.union first.certificate second.certificate)
    (fun i need h => (List.mem_append.mp h).elim (first.available i need) (second.available i need))
    (combine first.related second.related) (.union first.typeCertificate second.typeCertificate)
    (fun i need h => (List.mem_append.mp h).elim (first.typeAvailable i need) (second.typeAvailable i need))
    (first.typed.union_types second.typed) (combine first.typeCode second.typeCode)

end SortableTermTransferResult

theorem SortableComputationalTransferResult.sortableResult
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (result : SortableComputationalTransferResult env U registry Γ locals σ τ available
      left right assigned profile) (formed : profile.HasType (.sort relevant)) :
    Nonempty (SortableTermTransferResult env U registry Γ locals σ τ available
      left right assigned relevant profile) := by
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := result.toSortableGradedResult.code henv closed formed
  exact ⟨SortableTermTransferResult.fromCode henv certificate resources
    ((result.requestedRelated henv hΓ).code_of_sortable henv hscoped hΓ formed)
    result.requestedCertificate result.typeAvailable result.requestedTyped
    (result.typeCode.lower henv result.bound)⟩

end Lean4Lean.AnchoredSource.Adapted
