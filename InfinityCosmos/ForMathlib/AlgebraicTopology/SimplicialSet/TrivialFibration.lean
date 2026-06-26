import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products

namespace SSet

open CategoryTheory Limits MorphismProperty Simplicial

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
