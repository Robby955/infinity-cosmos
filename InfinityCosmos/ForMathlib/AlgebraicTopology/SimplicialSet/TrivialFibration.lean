import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products

universe u

namespace SSet

open CategoryTheory Limits MorphismProperty Simplicial
open MonoidalCategory MonoidalClosed HomotopicalAlgebra

section trivialFibration

/-- The local class `BoundaryInclusions` agrees with mathlib's generating cofibrations for
simplicial sets. -/
lemma boundaryInclusions_eq_modelCategoryQuillen_I :
    BoundaryInclusions = modelCategoryQuillen.I := by
  ext X Y f
  constructor
  · intro hf
    cases hf with
    | mk n => exact modelCategoryQuillen.boundary_ι_mem_I n
  · intro hf
    rw [modelCategoryQuillen.I, MorphismProperty.ofHoms_iff] at hf
    rcases hf with ⟨n, hn⟩
    cases hn
    exact BoundaryInclusion.mk n

instance trivialFibration_isStableUnderBaseChange :
    TrivialFibration.IsStableUnderBaseChange := by
  change BoundaryInclusions.rlp.IsStableUnderBaseChange
  infer_instance

instance trivialFibration_isStableUnderProductsOfShape (J : Type*) :
    TrivialFibration.IsStableUnderProductsOfShape J := by
  change BoundaryInclusions.rlp.IsStableUnderProductsOfShape J
  infer_instance

/-- A trivial fibration has the right lifting property against all monomorphisms. -/
lemma TrivialFibration.rlp_monomorphisms {X Y : SSet} {p : X ⟶ Y}
    (hp : TrivialFibration p) : (MorphismProperty.monomorphisms SSet).rlp p := by
  rw [SSet.rlp_monomorphisms]
  simpa [TrivialFibration, boundaryInclusions_eq_modelCategoryQuillen_I] using hp

/-- Trivial fibrations of simplicial sets are exactly the maps with the right lifting property
against all monomorphisms. -/
lemma trivialFibration_eq_rlp_monomorphisms :
    TrivialFibration = (MorphismProperty.monomorphisms SSet.{u}).rlp := by
  change BoundaryInclusions.rlp = (MorphismProperty.monomorphisms SSet.{u}).rlp
  rw [boundaryInclusions_eq_modelCategoryQuillen_I]
  exact SSet.rlp_monomorphisms.symm

private noncomputable def arrowIsoRange {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
  Arrow.isoMk' i (Subcomplex.range i).ι (asIso (Subcomplex.toRange i)) (Iso.refl _) (by
    simp)

/-- The pushout-product of a monomorphism with a boundary inclusion is a monomorphism. -/
lemma pushoutProduct_boundary_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    Mono ((Arrow.mk i □ Arrow.mk (∂Δ[n].ι)).hom) := by
  let S : Y.Subcomplex := Subcomplex.range i
  let T : (Δ[n] : SSet.{u}).Subcomplex := ∂Δ[n]
  have htarget : (MorphismProperty.monomorphisms SSet.{u})
      ((Arrow.mk S.ι □ Arrow.mk T.ι).hom) := by
    have hUnion : (MorphismProperty.monomorphisms SSet.{u}) (S.unionProd T).ι := by
      infer_instance
    exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
      (Subcomplex.unionProd.ιIso S T)).1 hUnion
  have e : (Arrow.mk i □ Arrow.mk T.ι) ≅ (Arrow.mk S.ι □ Arrow.mk T.ι) :=
    ((MonoidalCategory.Arrow.pushoutProduct.mapIso (arrowIsoRange i)).app (Arrow.mk T.ι))
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff e).2 htarget

/-- Trivial fibrations of simplicial sets are stable under pullback. -/
lemma TrivialFibration.of_isPullback {X Y Y' S : SSet} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : TrivialFibration g) : TrivialFibration g' :=
  MorphismProperty.of_isPullback sq hg

/-- Products of trivial fibrations of simplicial sets are trivial fibrations. -/
lemma TrivialFibration.piMap {J : Type*} {X Y : J → SSet} [HasProduct X] [HasProduct Y]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, TrivialFibration (f j)) :
    TrivialFibration (Limits.Pi.map f) := by
  let α : Discrete.functor X ⟶ Discrete.functor Y :=
    Discrete.natTrans (fun j : Discrete J => f j.as)
  change BoundaryInclusions.rlp (limMap α)
  refine MorphismProperty.limMap (W := BoundaryInclusions.rlp) α ?_
  intro j
  change BoundaryInclusions.rlp (f j.as)
  simpa [TrivialFibration] using hf j.as

/-- Pullback-hom projections along monomorphisms preserve trivial fibrations of simplicial sets. -/
lemma TrivialFibration.pullbackObjObjπ {X₁ Y₁ E B : SSet.{u}} {i : X₁ ⟶ Y₁}
    {p : E ⟶ B} [Mono i] (hp : TrivialFibration p)
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    TrivialFibration sq₁₃.π := by
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  change BoundaryInclusions.rlp sq₁₃.π
  intro A B j hj
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i j) sq₁₃]
  cases hj with
  | mk n =>
      change HasLiftingProperty ((Arrow.mk i □ Arrow.mk (∂Δ[n].ι)).hom) p
      exact hp _ (pushoutProduct_boundary_mono i n)

/-- Every map from the terminal simplex `Δ[0]` is a monomorphism. -/
lemma mono_yonedaEquiv_symm_zero {X : SSet} (x : X _⦋0⦌) :
    Mono (yonedaEquiv.symm x : Δ[0] ⟶ X) where
  right_cancellation := by
    intro Z g h _w
    exact isTerminalDeltaZero.hom_ext g h

/-- The generating maps for quasi-category isofibrations are monomorphisms of simplicial sets. -/
lemma innerHornIsoInclusions_le_monomorphisms :
    InnerHornIsoInclusions ≤ MorphismProperty.monomorphisms SSet := by
  intro X Y f hf
  rcases hf with h | h | h
  · cases h with
    | mk n i low high => infer_instance
  · cases h with
    | mk =>
        haveI := mono_yonedaEquiv_symm_zero coherentIso.x₀
        exact MorphismProperty.monomorphisms.infer_property _
  · cases h with
    | mk =>
        haveI := mono_yonedaEquiv_symm_zero coherentIso.x₁
        exact MorphismProperty.monomorphisms.infer_property _

/-- A trivial fibration of simplicial sets between quasi-categories is an isofibration. -/
lemma TrivialFibration.toIsofibration {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) : Isofibration p := by
  exact MorphismProperty.antitone_rlp innerHornIsoInclusions_le_monomorphisms p.hom
    hp.rlp_monomorphisms

/-- A trivial fibration of simplicial sets admits a section. -/
noncomputable def TrivialFibration.section {X Y : SSet} {p : X ⟶ Y}
    (hp : TrivialFibration p) : Y ⟶ X := by
  haveI : Mono (initial.to Y : ⊥_ SSet ⟶ Y) := inferInstance
  haveI : HasLiftingProperty (initial.to Y : ⊥_ SSet ⟶ Y) p :=
    hp.rlp_monomorphisms _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) :=
    CommSq.mk (by simp [initial.to_comp])
  exact sq.lift

/-- The section of a trivial fibration is a right inverse. -/
@[reassoc (attr := simp)]
lemma TrivialFibration.section_comp {X Y : SSet} {p : X ⟶ Y}
    (hp : TrivialFibration p) : hp.section ≫ p = 𝟙 Y := by
  unfold TrivialFibration.section
  simp

end trivialFibration

end SSet
