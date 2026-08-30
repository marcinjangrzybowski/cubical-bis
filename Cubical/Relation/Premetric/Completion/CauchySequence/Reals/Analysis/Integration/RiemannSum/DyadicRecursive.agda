module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (sub-self ; sub-zero-right ; neg-add)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
  using (mul-assoc)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (add-monotone ; abs-triangle ; x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; nonnegative→abs-self
    ; mul-preserves≤-left-nonnegative
    ; mul-preserves≤-right-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
  using (≤→zero≤difference)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (scalar-sub)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; ≤<ℝ-trans ; <ℝ-weaken ; <ℚ→<ℝ)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (absDifference<→closeness ; closeness→absDifference<)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Equality
  using (dyadicRadius ; dyadicReal)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.ScalarCompatibility
  using (mul-rational-right-as-scalar)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
  using (midpoint ; midpoint-lower ; midpoint-upper ; pointsInIntervalDistanceBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Equal
  using (dyadicWidthSequence ; dyadicWidthIsLimitZero)


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
  module ℚComm = CommRingStr (snd ℚCommRing)

  split-widths : ∀ a m b →
    (m Group.- a) Add.+ (b Group.- m) ≡ b Group.- a
  split-widths a m b =
    ℝRing.+ShufflePairs m (Neg.- a) b (Neg.- m)
    ∙ cong₂ Add._+_
        (add-comm m b) (add-comm (Neg.- a) (Neg.- m))
    ∙ sym (add-assoc b m ((Neg.- m) Add.+ (Neg.- a)))
    ∙ cong (b Add.+_) (add-assoc m (Neg.- m) (Neg.- a))
    ∙ cong (b Add.+_)
        (cong (Add._+ (Neg.- a)) (add-inverse-right m)
        ∙ add-zero-left (Neg.- a))

  sum-difference-split : ∀ x y u v →
    (x Add.+ y) Group.- (u Add.+ v) ≡
    (x Group.- u) Add.+ (y Group.- v)
  sum-difference-split x y u v =
    cong ((x Add.+ y) Add.+_) (sym (ℝRing.-Dist u v))
    ∙ ℝRing.+ShufflePairs x y (Neg.- u) (Neg.- v)


-- A recursive presentation exposes the binary geometry hidden by the flat
-- `Fin (2^n)` representation.  It is useful for refinement arguments because
-- both halves can be handled structurally, without quotient/remainder index
-- arithmetic or a choice of representatives.

dyadicRecursiveSum :
  (Real.ℝ → Real.ℝ) → Real.ℝ → Real.ℝ → ℕ → Real.ℝ
dyadicRecursiveSum f a b zero =
  (b Group.- a) Mul.· f a
dyadicRecursiveSum f a b (suc n) =
  dyadicRecursiveSum f a (midpoint a b) n Add.+
  dyadicRecursiveSum f (midpoint a b) b n


midpoint-widths : ∀ a b →
  (midpoint a b Group.- a) Add.+
  (b Group.- midpoint a b) ≡
  b Group.- a
midpoint-widths a b = split-widths a (midpoint a b) b


private
  half-double : ∀ x → midpoint x x ≡ x
  half-double x =
    scalar-dist-right rationalHalf x x
    ∙ sym (scalar-dist-left rationalHalf rationalHalf x)
    ∙ cong (Scalar._⋆ x) ℚ!
    ∙ scalar-id x


midpoint-left-width : ∀ a b →
  midpoint a b Group.- a ≡
  rationalHalf Scalar.⋆ (b Group.- a)
midpoint-left-width a b =
  cong (midpoint a b Group.-_) (sym (half-double a))
  ∙ sym (scalar-sub rationalHalf
      (a Add.+ b) (a Add.+ a))
  ∙ cong (rationalHalf Scalar.⋆_)
      (sum-difference-split a b a a
      ∙ cong₂ Add._+_ (sub-self a)
          (refl {x = b Group.- a})
      ∙ add-zero-left (b Group.- a))


midpoint-right-width : ∀ a b →
  b Group.- midpoint a b ≡
  rationalHalf Scalar.⋆ (b Group.- a)
midpoint-right-width a b =
  cong (λ x → x Group.- midpoint a b) (sym (half-double b))
  ∙ sym (scalar-sub rationalHalf
      (b Add.+ b) (a Add.+ b))
  ∙ cong (rationalHalf Scalar.⋆_)
      (sum-difference-split b b a b
      ∙ cong₂ Add._+_ (refl {x = b Group.- a})
          (sub-self b)
      ∙ add-zero-right (b Group.- a))


dyadicRecursiveSum-constant : ∀ a b c n →
  dyadicRecursiveSum (λ _ → c) a b n ≡
  (b Group.- a) Mul.· c
dyadicRecursiveSum-constant a b c zero = refl
dyadicRecursiveSum-constant a b c (suc n) =
  cong₂ Add._+_
    (dyadicRecursiveSum-constant a (midpoint a b) c n)
    (dyadicRecursiveSum-constant (midpoint a b) b c n)
  ∙ sym (mul-distrib-over-add-left
      (midpoint a b Group.- a)
      (b Group.- midpoint a b) c)
  ∙ cong (Mul._· c) (midpoint-widths a b)


dyadicRecursiveSum-add : ∀ f g a b n →
  dyadicRecursiveSum (λ x → f x Add.+ g x) a b n ≡
  dyadicRecursiveSum f a b n Add.+
  dyadicRecursiveSum g a b n
dyadicRecursiveSum-add f g a b zero =
  mul-distrib-over-add-right (b Group.- a) (f a) (g a)
dyadicRecursiveSum-add f g a b (suc n) =
  cong₂ Add._+_
    (dyadicRecursiveSum-add f g a (midpoint a b) n)
    (dyadicRecursiveSum-add f g (midpoint a b) b n)
  ∙ ℝRing.+ShufflePairs
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum g a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n)
      (dyadicRecursiveSum g (midpoint a b) b n)


dyadicRecursiveSum-neg : ∀ f a b n →
  dyadicRecursiveSum (λ x → Neg.- f x) a b n ≡
  Neg.- dyadicRecursiveSum f a b n
dyadicRecursiveSum-neg f a b zero =
  ℝRing.-DistR· (b Group.- a) (f a)
dyadicRecursiveSum-neg f a b (suc n) =
  cong₂ Add._+_
    (dyadicRecursiveSum-neg f a (midpoint a b) n)
    (dyadicRecursiveSum-neg f (midpoint a b) b n)
  ∙ sym (neg-add
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n))


dyadicRecursiveSum-scale : ∀ c f a b n →
  dyadicRecursiveSum (λ x → c Mul.· f x) a b n ≡
  c Mul.· dyadicRecursiveSum f a b n
dyadicRecursiveSum-scale c f a b zero =
  mul-assoc (b Group.- a) c (f a)
  ∙ cong (Mul._· f a) (mul-comm (b Group.- a) c)
  ∙ sym (mul-assoc c (b Group.- a) (f a))
dyadicRecursiveSum-scale c f a b (suc n) =
  cong₂ Add._+_
    (dyadicRecursiveSum-scale c f a (midpoint a b) n)
    (dyadicRecursiveSum-scale c f (midpoint a b) b n)
  ∙ sym (mul-distrib-over-add-right c
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n))


-- If every function value on an interval is within `error` of one fixed
-- reference value, every recursive dyadic sum is within total-width times
-- that error.  The bound is independent of the subdivision depth.  This is
-- the structural estimate needed to compare an arbitrary fine dyadic level
-- with the coarser level whose cells supply the reference values.

dyadicRecursiveSum-constantAbsBound :
  ∀ f a b c error n →
  (a≤b : a ≤ℝ b) →
  (∀ x → a ≤ℝ x → x ≤ℝ b →
    Abs.absℝ (f x Group.- c) ≤ℝ error) →
  Abs.absℝ
    (dyadicRecursiveSum f a b n Group.-
      (b Group.- a) Mul.· c)
  ≤ℝ (b Group.- a) Mul.· error
dyadicRecursiveSum-constantAbsBound
  f a b c error zero a≤b close =
  subst
    (λ z → z ≤ℝ (b Group.- a) Mul.· error)
    (sym
      (cong Abs.absℝ
        (sym (ℝRing.·DistR-
          (b Group.- a) (f a) c))
      ∙ abs-mul (b Group.- a) (f a Group.- c)
      ∙ cong (Mul._· Abs.absℝ (f a Group.- c))
          (nonnegative→abs-self
            (b Group.- a) (≤→zero≤difference a b a≤b))))
    (mul-preserves≤-left-nonnegative
      (Abs.absℝ (f a Group.- c)) error (b Group.- a)
      (close a (≤ℝ-refl a) a≤b)
      (≤→zero≤difference a b a≤b))
dyadicRecursiveSum-constantAbsBound
  f a b c error (suc n) a≤b close =
  subst
    (λ z →
      Abs.absℝ
        (dyadicRecursiveSum f a b (suc n) Group.-
          (b Group.- a) Mul.· c)
      ≤ℝ z)
    total-bound
    (subst
      (λ z → Abs.absℝ z ≤ℝ
        ((midpoint a b Group.- a) Mul.· error) Add.+
        ((b Group.- midpoint a b) Mul.· error))
      (sym difference-split)
      combined-bound)
  where
  left-difference : Real.ℝ
  left-difference =
    dyadicRecursiveSum f a (midpoint a b) n Group.-
    (midpoint a b Group.- a) Mul.· c

  right-difference : Real.ℝ
  right-difference =
    dyadicRecursiveSum f (midpoint a b) b n Group.-
    (b Group.- midpoint a b) Mul.· c

  left-bound : Real.ℝ
  left-bound = (midpoint a b Group.- a) Mul.· error

  right-bound : Real.ℝ
  right-bound = (b Group.- midpoint a b) Mul.· error

  left-estimate : Abs.absℝ left-difference ≤ℝ left-bound
  left-estimate =
    dyadicRecursiveSum-constantAbsBound
      f a (midpoint a b) c error n
      (midpoint-lower a b a≤b)
      (λ x a≤x x≤mid →
        close x a≤x
          (≤ℝ-trans x (midpoint a b) b x≤mid
            (midpoint-upper a b a≤b)))

  right-estimate : Abs.absℝ right-difference ≤ℝ right-bound
  right-estimate =
    dyadicRecursiveSum-constantAbsBound
      f (midpoint a b) b c error n
      (midpoint-upper a b a≤b)
      (λ x mid≤x x≤b →
        close x
          (≤ℝ-trans a (midpoint a b) x
            (midpoint-lower a b a≤b) mid≤x)
          x≤b)

  combined-bound :
    Abs.absℝ (left-difference Add.+ right-difference) ≤ℝ
    left-bound Add.+ right-bound
  combined-bound =
    ≤ℝ-trans
      (Abs.absℝ (left-difference Add.+ right-difference))
      (Abs.absℝ left-difference Add.+ Abs.absℝ right-difference)
      (left-bound Add.+ right-bound)
      (abs-triangle left-difference right-difference)
      (add-monotone
        (Abs.absℝ left-difference) left-bound
        (Abs.absℝ right-difference) right-bound
        left-estimate right-estimate)

  difference-split :
    (dyadicRecursiveSum f a (midpoint a b) n Add.+
      dyadicRecursiveSum f (midpoint a b) b n) Group.-
      (b Group.- a) Mul.· c
    ≡
    (dyadicRecursiveSum f a (midpoint a b) n Group.-
      (midpoint a b Group.- a) Mul.· c) Add.+
    (dyadicRecursiveSum f (midpoint a b) b n Group.-
      (b Group.- midpoint a b) Mul.· c)
  difference-split =
    cong
      ((dyadicRecursiveSum f a (midpoint a b) n Add.+
        dyadicRecursiveSum f (midpoint a b) b n) Group.-_)
      (cong (Mul._· c) (sym (midpoint-widths a b))
      ∙ mul-distrib-over-add-left
          (midpoint a b Group.- a)
          (b Group.- midpoint a b) c)
    ∙ cong
        ((dyadicRecursiveSum f a (midpoint a b) n Add.+
          dyadicRecursiveSum f (midpoint a b) b n) Add.+_)
        (sym (ℝRing.-Dist
          ((midpoint a b Group.- a) Mul.· c)
          ((b Group.- midpoint a b) Mul.· c)))
    ∙ ℝRing.+ShufflePairs
        (dyadicRecursiveSum f a (midpoint a b) n)
        (dyadicRecursiveSum f (midpoint a b) b n)
        (Neg.- ((midpoint a b Group.- a) Mul.· c))
        (Neg.- ((b Group.- midpoint a b) Mul.· c))

  total-bound :
    ((midpoint a b Group.- a) Mul.· error) Add.+
      ((b Group.- midpoint a b) Mul.· error)
    ≡ (b Group.- a) Mul.· error
  total-bound =
    sym (mul-distrib-over-add-left
      (midpoint a b Group.- a)
      (b Group.- midpoint a b) error)
    ∙ cong (Mul._· error) (midpoint-widths a b)


-- Oscillation is recorded at the cells of one fixed dyadic depth.  This
-- proposition is structural: its two branches are precisely the cells in
-- the left and right halves.  It avoids selecting or enumerating those cells.

DyadicLeftOscillation :
  (Real.ℝ → Real.ℝ) → Real.ℝ →
  Real.ℝ → Real.ℝ → ℕ → Type₀
DyadicLeftOscillation f error a b zero =
  ∀ x → a ≤ℝ x → x ≤ℝ b →
    Abs.absℝ (f x Group.- f a) ≤ℝ error
DyadicLeftOscillation f error a b (suc n) =
  DyadicLeftOscillation f error a (midpoint a b) n ×
  DyadicLeftOscillation f error (midpoint a b) b n


-- The matching recursive mesh predicate says that every depth-`n` cell is
-- below one rational radius.  This is deliberately a proposition rather than
-- a maximum-width operation, so its use never chooses a distinguished cell.

DyadicCellsBelow :
  Real.ℝ → Real.ℝ → ℕ → ℚ₊ → Type₀
DyadicCellsBelow a b zero δ =
  b Group.- a <ℝ Real.ιℚ (fst δ)
DyadicCellsBelow a b (suc n) δ =
  DyadicCellsBelow a (midpoint a b) n δ ×
  DyadicCellsBelow (midpoint a b) b n δ


iteratedHalfWidth : ℕ → Real.ℝ → Real.ℝ
iteratedHalfWidth zero width₀ = width₀
iteratedHalfWidth (suc n) width₀ =
  iteratedHalfWidth n (rationalHalf Scalar.⋆ width₀)


iteratedHalfWidth-dyadic : ∀ n width₀ →
  iteratedHalfWidth n width₀ ≡
  fst (dyadicRadius n) Scalar.⋆ width₀
iteratedHalfWidth-dyadic zero width₀ =
  sym (scalar-id width₀)
iteratedHalfWidth-dyadic (suc n) width₀ =
  iteratedHalfWidth-dyadic n
    (rationalHalf Scalar.⋆ width₀)
  ∙ sym (scalar-assoc
      (fst (dyadicRadius n)) rationalHalf width₀)
  ∙ cong (Scalar._⋆ width₀)
      (ℚComm.·Comm (fst (dyadicRadius n)) rationalHalf)


iteratedHalfWidth-as-dyadicWidth : ∀ a b n →
  iteratedHalfWidth n (b Group.- a) ≡
  dyadicWidthSequence a b n
iteratedHalfWidth-as-dyadicWidth a b n =
  iteratedHalfWidth-dyadic n (b Group.- a)
  ∙ sym (mul-rational-right-as-scalar
      (b Group.- a) (fst (dyadicRadius n)))


iteratedHalfWidthBound→dyadicCellsBelow : ∀ a b n δ →
  iteratedHalfWidth n (b Group.- a) <ℝ Real.ιℚ (fst δ) →
  DyadicCellsBelow a b n δ
iteratedHalfWidthBound→dyadicCellsBelow
  a b zero δ small = small
iteratedHalfWidthBound→dyadicCellsBelow
  a b (suc n) δ small =
  iteratedHalfWidthBound→dyadicCellsBelow
    a (midpoint a b) n δ
    (subst
      (λ width₀ →
        iteratedHalfWidth n width₀ <ℝ Real.ιℚ (fst δ))
      (sym (midpoint-left-width a b)) small)
  ,
  iteratedHalfWidthBound→dyadicCellsBelow
    (midpoint a b) b n δ
    (subst
      (λ width₀ →
        iteratedHalfWidth n width₀ <ℝ Real.ιℚ (fst δ))
      (sym (midpoint-right-width a b)) small)


-- The recursive mesh tends to zero.  The proof reuses the established
-- dyadic-width limit only after proving that the binary and flat geometries
-- have exactly the same width; it does not identify their sums or tags.

dyadicCellsEventuallyBelow : ∀ a b δ →
  ∃[ N ∈ ℕ ]
    (∀ n → N ℕ.≤ n → DyadicCellsBelow a b n δ)
dyadicCellsEventuallyBelow a b δ =
  PT.map
    (λ { (N , close) →
      N , λ n N≤n →
        iteratedHalfWidthBound→dyadicCellsBelow a b n δ
          (subst
            (λ z → z <ℝ Real.ιℚ (fst δ))
            (sym (iteratedHalfWidth-as-dyadicWidth a b n))
            (≤<ℝ-trans
              (dyadicWidthSequence a b n)
              (Abs.absℝ (dyadicWidthSequence a b n))
              (Real.ιℚ (fst δ))
              (x≤abs (dyadicWidthSequence a b n))
              (subst
                (λ z → z <ℝ Real.ιℚ (fst δ))
                (cong Abs.absℝ
                  (sub-zero-right (dyadicWidthSequence a b n)))
                (closeness→absDifference<
                  (dyadicWidthSequence a b n)
                  (Real.ιℚ 0) δ (close n N≤n))))) })
    (dyadicWidthIsLimitZero a b δ)


-- One radiuswise continuity witness controls all cells simultaneously once
-- their recursive mesh is below its input radius.  In particular, there is
-- no selection of one modulus per cell or per subdivision depth here.

dyadicCellsBelow→leftOscillation :
  ∀ f ε δ →
  (∀ x y →
    x Real.Base.≈ᶜ[ δ ] y →
    f x Real.Base.≈ᶜ[ ε ] f y) →
  ∀ a b n →
  (a≤b : a ≤ℝ b) →
  DyadicCellsBelow a b n δ →
  DyadicLeftOscillation f (Real.ιℚ (fst ε)) a b n
dyadicCellsBelow→leftOscillation
  f ε δ close a b zero a≤b cells x a≤x x≤b =
  <ℝ-weaken
    (Abs.absℝ (f x Group.- f a))
    (Real.ιℚ (fst ε))
    (closeness→absDifference< (f x) (f a) ε
      (close x a
        (absDifference<→closeness x a δ
          (≤<ℝ-trans
            (Abs.absℝ (x Group.- a))
            (b Group.- a)
            (Real.ιℚ (fst δ))
            (pointsInIntervalDistanceBound
              a b x a a≤x x≤b (≤ℝ-refl a) a≤b)
            cells))))
dyadicCellsBelow→leftOscillation
  f ε δ close a b (suc n) a≤b cells =
  dyadicCellsBelow→leftOscillation
    f ε δ close a (midpoint a b) n
    (midpoint-lower a b a≤b) (fst cells)
  ,
  dyadicCellsBelow→leftOscillation
    f ε δ close (midpoint a b) b n
    (midpoint-upper a b a≤b) (snd cells)


radiuswiseUCControlsDyadicLeftOscillation :
  ∀ f → IsRadiuswiseUniformlyContinuousℝ f →
  ∀ ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ a b n → a ≤ℝ b →
      DyadicCellsBelow a b n δ →
      DyadicLeftOscillation f (Real.ιℚ (fst ε)) a b n)
radiuswiseUCControlsDyadicLeftOscillation f f-uc ε =
  PT.map
    (λ { (δ , close) →
      δ , λ a b n a≤b cells →
        dyadicCellsBelow→leftOscillation
          f ε δ close a b n a≤b cells })
    (f-uc ε)


-- Radius selection and the eventual mesh index remain under one truncation.
-- This is exactly the amount of choice needed for a single requested output
-- radius and is therefore compatible with the Cauchy-completion interface.

radiuswiseUCEventuallyControlsDyadicLeftOscillation :
  ∀ f → IsRadiuswiseUniformlyContinuousℝ f →
  ∀ ε a b → a ≤ℝ b →
  ∃[ N ∈ ℕ ]
    (∀ n → N ℕ.≤ n →
      DyadicLeftOscillation
        f (Real.ιℚ (fst ε)) a b n)
radiuswiseUCEventuallyControlsDyadicLeftOscillation
  f f-uc ε a b a≤b =
  PT.rec squash₁
    (λ { (δ , controls) →
      PT.map
        (λ { (N , fine) →
          N , λ n N≤n →
            controls a b n a≤b (fine n N≤n) })
        (dyadicCellsEventuallyBelow a b δ) })
    (radiuswiseUCControlsDyadicLeftOscillation f f-uc ε)


-- A level `n + k` refines level `n` by `k` further binary subdivisions.
-- The estimate compares those levels directly, so it is uniform in `k` and
-- is strong enough for a Cauchy tail (unlike an adjacent-level estimate).

dyadicRecursiveSum-refinementAbsBound :
  ∀ f a b error n k →
  (a≤b : a ≤ℝ b) →
  DyadicLeftOscillation f error a b n →
  Abs.absℝ
    (dyadicRecursiveSum f a b (n + k) Group.-
      dyadicRecursiveSum f a b n)
  ≤ℝ (b Group.- a) Mul.· error
dyadicRecursiveSum-refinementAbsBound
  f a b error zero k a≤b oscillation =
  dyadicRecursiveSum-constantAbsBound
    f a b (f a) error k a≤b oscillation
dyadicRecursiveSum-refinementAbsBound
  f a b error (suc n) k a≤b oscillation =
  subst
    (λ z →
      Abs.absℝ
        (dyadicRecursiveSum f a b (suc n + k) Group.-
          dyadicRecursiveSum f a b (suc n))
      ≤ℝ z)
    total-bound
    (subst
      (λ z → Abs.absℝ z ≤ℝ left-bound Add.+ right-bound)
      (sym difference-split)
      combined-bound)
  where
  left-fine : Real.ℝ
  left-fine = dyadicRecursiveSum f a (midpoint a b) (n + k)

  right-fine : Real.ℝ
  right-fine = dyadicRecursiveSum f (midpoint a b) b (n + k)

  left-coarse : Real.ℝ
  left-coarse = dyadicRecursiveSum f a (midpoint a b) n

  right-coarse : Real.ℝ
  right-coarse = dyadicRecursiveSum f (midpoint a b) b n

  left-difference : Real.ℝ
  left-difference = left-fine Group.- left-coarse

  right-difference : Real.ℝ
  right-difference = right-fine Group.- right-coarse

  left-bound : Real.ℝ
  left-bound = (midpoint a b Group.- a) Mul.· error

  right-bound : Real.ℝ
  right-bound = (b Group.- midpoint a b) Mul.· error

  left-estimate : Abs.absℝ left-difference ≤ℝ left-bound
  left-estimate =
    dyadicRecursiveSum-refinementAbsBound
      f a (midpoint a b) error n k
      (midpoint-lower a b a≤b) (fst oscillation)

  right-estimate : Abs.absℝ right-difference ≤ℝ right-bound
  right-estimate =
    dyadicRecursiveSum-refinementAbsBound
      f (midpoint a b) b error n k
      (midpoint-upper a b a≤b) (snd oscillation)

  combined-bound :
    Abs.absℝ (left-difference Add.+ right-difference) ≤ℝ
    left-bound Add.+ right-bound
  combined-bound =
    ≤ℝ-trans
      (Abs.absℝ (left-difference Add.+ right-difference))
      (Abs.absℝ left-difference Add.+ Abs.absℝ right-difference)
      (left-bound Add.+ right-bound)
      (abs-triangle left-difference right-difference)
      (add-monotone
        (Abs.absℝ left-difference) left-bound
        (Abs.absℝ right-difference) right-bound
        left-estimate right-estimate)

  difference-split :
    (left-fine Add.+ right-fine) Group.-
      (left-coarse Add.+ right-coarse)
    ≡ left-difference Add.+ right-difference
  difference-split =
    sum-difference-split left-fine right-fine left-coarse right-coarse

  total-bound : left-bound Add.+ right-bound ≡
    (b Group.- a) Mul.· error
  total-bound =
    sym (mul-distrib-over-add-left
      (midpoint a b Group.- a)
      (b Group.- midpoint a b) error)
    ∙ cong (Mul._· error) (midpoint-widths a b)


-- A rational bound on the interval width turns the real-valued refinement
-- estimate into a metric estimate.  Two halvings leave strict room after the
-- non-strict order bounds, while division by `B` exactly cancels the chosen
-- rational width bound.

dyadicRecursiveSum-refinementClose :
  ∀ f a b ε B n k →
  Abs.absℝ (b Group.- a) ≤ℝ Real.ιℚ (fst B) →
  (a≤b : a ≤ℝ b) →
  DyadicLeftOscillation f
    (Real.ιℚ
      (fst (((ε /2₊) /2₊) ₊／₊ B))) a b n →
  dyadicRecursiveSum f a b (n + k)
    Real.Base.≈ᶜ[ ε /2₊ ]
  dyadicRecursiveSum f a b n
dyadicRecursiveSum-refinementClose
  f a b ε B n k width-bound a≤b oscillation =
  absDifference<→closeness
    (dyadicRecursiveSum f a b (n + k))
    (dyadicRecursiveSum f a b n) (ε /2₊)
    (≤<ℝ-trans
      (Abs.absℝ
        (dyadicRecursiveSum f a b (n + k) Group.-
          dyadicRecursiveSum f a b n))
      ((b Group.- a) Mul.· Real.ιℚ (fst output-radius))
      (Real.ιℚ (fst (ε /2₊)))
      (dyadicRecursiveSum-refinementAbsBound
        f a b (Real.ιℚ (fst output-radius)) n k
        a≤b oscillation)
      product-small)
  where
  quarter-radius : ℚ₊
  quarter-radius = (ε /2₊) /2₊

  output-radius : ℚ₊
  output-radius = quarter-radius ₊／₊ B

  width≤B : b Group.- a ≤ℝ Real.ιℚ (fst B)
  width≤B =
    ≤ℝ-trans
      (b Group.- a) (Abs.absℝ (b Group.- a))
      (Real.ιℚ (fst B))
      (x≤abs (b Group.- a)) width-bound

  zero≤output :
    Real.ιℚ 0 ≤ℝ Real.ιℚ (fst output-radius)
  zero≤output =
    ≤ℚ→≤ℝ 0 (fst output-radius)
      (ℚ.<Weaken≤ 0 (fst output-radius) (snd output-radius))

  product-upper :
    (b Group.- a) Mul.· Real.ιℚ (fst output-radius)
    ≤ℝ
    Real.ιℚ (fst B) Mul.· Real.ιℚ (fst output-radius)
  product-upper =
    mul-preserves≤-right-nonnegative
      (b Group.- a) (Real.ιℚ (fst B))
      (Real.ιℚ (fst output-radius))
      width≤B zero≤output

  rational-product :
    Real.ιℚ (fst B) Mul.· Real.ιℚ (fst output-radius)
    ≡ Real.ιℚ (fst quarter-radius)
  rational-product =
    Mul.mul-ι-ι (fst B) (fst output-radius)
    ∙ cong Real.ιℚ (·／ B quarter-radius)

  rational-quarter-small :
    Real.ιℚ (fst quarter-radius) <ℝ
    Real.ιℚ (fst (ε /2₊))
  rational-quarter-small =
    <ℚ→<ℝ (fst quarter-radius) (fst (ε /2₊))
      (/2₊<id (ε /2₊))

  product-small :
    (b Group.- a) Mul.· Real.ιℚ (fst output-radius)
    <ℝ Real.ιℚ (fst (ε /2₊))
  product-small =
    ≤<ℝ-trans
      ((b Group.- a) Mul.· Real.ιℚ (fst output-radius))
      (Real.ιℚ (fst B) Mul.· Real.ιℚ (fst output-radius))
      (Real.ιℚ (fst (ε /2₊)))
      product-upper
      (subst (_<ℝ Real.ιℚ (fst (ε /2₊)))
        (sym rational-product) rational-quarter-small)


-- Radiuswise uniform continuity on a fixed ordered interval is sufficient
-- for the recursive left dyadic sums to be Cauchy.  Every choice made in the
-- proof (a width bound, one continuity radius, one tail index) is eliminated
-- into the proposition-valued Cauchy witness at the same requested radius.

radiuswiseUCDyadicRecursiveSumIsCauchy :
  ∀ f a b → a ≤ℝ b →
  IsRadiuswiseUniformlyContinuousℝ f →
  Real.Base.IsCauchySequence (dyadicRecursiveSum f a b)
radiuswiseUCDyadicRecursiveSumIsCauchy f a b a≤b f-uc ε =
  PT.rec squash₁ withWidthBound
    (∃rationalBound (b Group.- a))
  where
  withWidthBound :
    RationalBound (b Group.- a) →
    ∃[ N ∈ ℕ ]
      (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        dyadicRecursiveSum f a b m
          Real.Base.≈ᶜ[ ε ]
        dyadicRecursiveSum f a b n)
  withWidthBound bound@(B , _) =
    PT.map
      (λ { (N , oscillation) →
        N , λ m n N≤m N≤n →
          subst
            (λ ρ →
              dyadicRecursiveSum f a b m
                Real.Base.≈ᶜ[ ρ ]
              dyadicRecursiveSum f a b n)
            (ℚ₊≡ (/2+/2≡id (fst ε)))
            (Real.Premetric.tri≈ᶜ
              (dyadicRecursiveSum f a b m)
              (dyadicRecursiveSum f a b N)
              (dyadicRecursiveSum f a b n)
              (ε /2₊) (ε /2₊)
              (close-to-base N oscillation m N≤m)
              (Real.Base.sym≈ᶜ
                (dyadicRecursiveSum f a b n)
                (dyadicRecursiveSum f a b N)
                (ε /2₊)
                (close-to-base N oscillation n N≤n))) })
      (radiuswiseUCEventuallyControlsDyadicLeftOscillation
        f f-uc output-radius a b a≤b)
    where
    quarter-radius : ℚ₊
    quarter-radius = (ε /2₊) /2₊

    output-radius : ℚ₊
    output-radius = quarter-radius ₊／₊ B

    close-to-base :
      ∀ N →
      (∀ n → N ℕ.≤ n →
        DyadicLeftOscillation
          f (Real.ιℚ (fst output-radius)) a b n) →
      ∀ m → N ℕ.≤ m →
      dyadicRecursiveSum f a b m
        Real.Base.≈ᶜ[ ε /2₊ ]
      dyadicRecursiveSum f a b N
    close-to-base N oscillation m (k , k+N≡m) =
      subst
        (λ level →
          dyadicRecursiveSum f a b level
            Real.Base.≈ᶜ[ ε /2₊ ]
          dyadicRecursiveSum f a b N)
        (+-comm N k ∙ k+N≡m)
        (dyadicRecursiveSum-refinementClose
          f a b ε B N k (snd bound) a≤b
          (oscillation N (ℕ.≤-refl {m = N})))
