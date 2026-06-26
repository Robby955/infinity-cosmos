import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products

namespace SSet

open CategoryTheory Limits MorphismProperty

section trivialFibration

instance trivialFibration_isStableUnderBaseChange :
    TrivialFibration.IsStableUnderBaseChange := by
  change BoundaryInclusions.rlp.IsStableUnderBaseChange
  infer_instance

instance trivialFibration_isStableUnderProductsOfShape (J : Type*) :
    TrivialFibration.IsStableUnderProductsOfShape J := by
  change BoundaryInclusions.rlp.IsStableUnderProductsOfShape J
  infer_instance

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

end trivialFibration

end SSet
