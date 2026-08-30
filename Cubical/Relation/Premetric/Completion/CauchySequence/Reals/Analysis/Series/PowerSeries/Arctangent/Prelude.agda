module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; doubleℕ) public
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (1+_) public
open import Cubical.Data.Int.Fast.Base as ℤ using (pos) public
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ ; fromNatℚ) public
open import Cubical.Data.Rationals.Inverse as ℚInv public
open import Cubical.Data.Rationals.Order as ℚ public
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs public
open import Cubical.Algebra.CommRing public
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Algebra.OrderedCommRing public
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals public
open PositiveRationals public
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real public
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue public using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar public
  using (nonnegative-scalar-abs ; scalar-preserves≤ ; zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base as Scalar public
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Interleaving public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Derivative public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Primitive public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Laws public
  using (negativePower ; alternate-mul-left)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform public

oneℝ : Real.ℝ
oneℝ = CommRingStr.1r (snd ℝCommRing)

onePositiveRational : ℚ₊
onePositiveRational = successorPositiveRational zero

module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing
module ℝRing = Ring.RingTheory (CommRing→Ring ℝCommRing)
