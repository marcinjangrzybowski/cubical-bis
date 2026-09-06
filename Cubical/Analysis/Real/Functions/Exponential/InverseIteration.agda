module Cubical.Analysis.Real.Functions.Exponential.InverseIteration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

  opaque
    productNonnegative : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → 0ℝ ≤ℝ x · y
    productNonnegative x y px py =
      isNonnegative→0≤ (x · y)
        (mulPresIsNonnegative x y
          (0≤→isNonnegative x px) (0≤→isNonnegative y py))

    subtractSameRight : ∀ x y z → (x - z) - (y - z) ≡ x - y
    subtractSameRight x y z =
      cong ((x - z) +_) (negSub y z)
      ∙ sym (addAssoc x (- z) (z - y))
      ∙ cong (x +_)
          (addAssoc (- z) z (- y)
          ∙ cong (_+ (- y)) (addInvL z)
          ∙ addIdL (- y))

-- Every step uses continuous arithmetic. In particular no branch or family
-- of approximate preimages needs to be selected.
module DampedIteration (a b target : ℝ)
  (a≤b : a ≤ℝ b)
  (lower : exponentialEntireValue a ≤ℝ target)
  (upper : target ≤ℝ exponentialEntireValue b) where

  radius : ℝ
  radius = absℝ a + absℝ b

  damping : ℝ
  damping = exponentialEntireValue (- radius)

  contraction : ℝ
  contraction = 1ℝ - damping · exponentialEntireValue a

  residual : ℝ → ℝ
  residual x = target - exponentialEntireValue x

  step : ℝ → ℝ
  step x = x + damping · residual x

  Invariant : ℝ → Type₀
  Invariant x = (a ≤ℝ x) × (x ≤ℝ b) × (exponentialEntireValue x ≤ℝ target)

  initial-invariant : Invariant a
  initial-invariant = ≤ℝ-refl a , a≤b , lower

  opaque
    absLeft≤radius : absℝ a ≤ℝ radius
    absLeft≤radius =
      subst (_≤ℝ radius) (addIdR (absℝ a))
        (addPres≤L 0ℝ (absℝ b) (absℝ a) (absNonnegative b))

    absRight≤radius : absℝ b ≤ℝ radius
    absRight≤radius =
      subst (_≤ℝ radius) (addIdL (absℝ b))
        (addPres≤R 0ℝ (absℝ a) (absℝ b) (absNonnegative a))

    radius-nonnegative : 0ℝ ≤ℝ radius
    radius-nonnegative =
      ≤ℝ-trans 0ℝ (absℝ a) radius (absNonnegative a) absLeft≤radius

    interval-abs-bound : ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ x ≤ℝ radius
    interval-abs-bound x left right =
      absLeastUpperBound x radius
        (≤ℝ-trans x b radius right
          (≤ℝ-trans b (absℝ b) radius (leAbs b) absRight≤radius))
        (≤ℝ-trans (- x) (- a) radius (negPres≤ a x left)
          (≤ℝ-trans (- a) (absℝ a) radius (negLeAbs a) absLeft≤radius))

    damping-positive : 0ℝ <ℝ damping
    damping-positive = exponentialEntireValue-positive (- radius)

    damping-nonnegative : 0ℝ ≤ℝ damping
    damping-nonnegative = exponentialEntireValue-nonnegative (- radius)

    damping-cancels : damping · exponentialEntireValue radius ≡ 1ℝ
    damping-cancels =
      mulComm damping (exponentialEntireValue radius)
      ∙ exponentialEntireValue-mul-negative radius

    contraction-nonnegative : 0ℝ ≤ℝ contraction
    contraction-nonnegative =
      nonnegativeSub (damping · exponentialEntireValue a) 1ℝ
        (subst (damping · exponentialEntireValue a ≤ℝ_) damping-cancels
          (mulPres≤L (exponentialEntireValue a) (exponentialEntireValue radius)
            damping (0≤→isNonnegative damping damping-nonnegative)
            (exponentialEntireValue-preserves≤ a radius
              (≤ℝ-trans a (absℝ a) radius (leAbs a) absLeft≤radius))))

    contraction<one : contraction <ℝ 1ℝ
    contraction<one =
      subst (_<ℝ 1ℝ) (addComm (- (damping · exponentialEntireValue a)) 1ℝ)
        (subst ((- (damping · exponentialEntireValue a)) + 1ℝ <ℝ_) (addIdL 1ℝ)
          (<ℝ-addR (- (damping · exponentialEntireValue a)) 0ℝ 1ℝ
            (subst ((- (damping · exponentialEntireValue a)) <ℝ_) negZero
              (<ℝ-neg 0ℝ (damping · exponentialEntireValue a)
                (mulPositive damping (exponentialEntireValue a)
                  damping-positive (exponentialEntireValue-positive a))))))

    residual-nonnegative : ∀ x → Invariant x → 0ℝ ≤ℝ residual x
    residual-nonnegative x invariant =
      nonnegativeSub (exponentialEntireValue x) target (snd (snd invariant))

    step-increasing : ∀ x → Invariant x → x ≤ℝ step x
    step-increasing x invariant =
      subst (_≤ℝ step x) (addIdR x)
        (addPres≤L 0ℝ (damping · residual x) x
          (productNonnegative damping (residual x)
            damping-nonnegative (residual-nonnegative x invariant)))

    step-difference : ∀ x → step x - x ≡ damping · residual x
    step-difference x =
      cong (_- x) (addComm x (damping · residual x))
      ∙ R.plusMinus (damping · residual x) x

  private
    opaque
      cancelDampedBound : ∀ z → damping · (z · exponentialEntireValue radius) ≡ z
      cancelDampedBound z =
        cong (damping ·_) (mulComm z (exponentialEntireValue radius))
        ∙ mulAssoc damping (exponentialEntireValue radius) z
        ∙ cong (_· z) damping-cancels ∙ mulIdL z

      cancelUpperBound : ∀ z → (damping · z) · exponentialEntireValue radius ≡ z
      cancelUpperBound z =
        sym (mulAssoc damping z (exponentialEntireValue radius))
        ∙ cancelDampedBound z

      directed-upper-bound : ∀ x y → a ≤ℝ x → y ≤ℝ b → x ≤ℝ y →
        exponentialEntireValue y - exponentialEntireValue x ≤ℝ
        (y - x) · exponentialEntireValue radius
      directed-upper-bound x y left right ordered =
        ≤ℝ-trans (exponentialEntireValue y - exponentialEntireValue x)
          (absℝ (exponentialEntireValue y - exponentialEntireValue x))
          ((y - x) · exponentialEntireValue radius)
          (leAbs (exponentialEntireValue y - exponentialEntireValue x))
          (subst (absℝ (exponentialEntireValue y - exponentialEntireValue x) ≤ℝ_)
            (cong (_· exponentialEntireValue radius)
              (absOfNonnegative (y - x) (nonnegativeSub x y ordered)))
            (exponentialEntireValue-absoluteDifferenceBoundOnRadius
              x y radius radius-nonnegative
              (interval-abs-bound x left (≤ℝ-trans x y b ordered right))
              (interval-abs-bound y (≤ℝ-trans a x y left ordered) right)))

  opaque
    step-upper-bound : ∀ x → Invariant x → step x ≤ℝ b
    step-upper-bound x invariant =
      subst (step x ≤ℝ_) (addComm x (b - x) ∙ subAddCancel b x)
        (addPres≤L (damping · residual x) (b - x) x
          (subst (damping · residual x ≤ℝ_) (cancelDampedBound (b - x))
            (mulPres≤L (residual x)
              ((b - x) · exponentialEntireValue radius) damping
              (0≤→isNonnegative damping damping-nonnegative)
              (≤ℝ-trans (residual x)
                (exponentialEntireValue b - exponentialEntireValue x)
                ((b - x) · exponentialEntireValue radius)
                (addPres≤R target (exponentialEntireValue b)
                  (- exponentialEntireValue x) upper)
                (directed-upper-bound x b (fst invariant) (≤ℝ-refl b)
                  (fst (snd invariant)))))))

    step-image-upper-bound : ∀ x → Invariant x →
      exponentialEntireValue (step x) ≤ℝ target
    step-image-upper-bound x invariant =
      subst2 _≤ℝ_
        (subAddCancel (exponentialEntireValue (step x)) (exponentialEntireValue x))
        (subAddCancel target (exponentialEntireValue x))
        (addPres≤R
          (exponentialEntireValue (step x) - exponentialEntireValue x)
          (residual x) (exponentialEntireValue x)
          (subst ((exponentialEntireValue (step x) - exponentialEntireValue x) ≤ℝ_)
            (cong (_· exponentialEntireValue radius) (step-difference x)
              ∙ cancelUpperBound (residual x))
            (directed-upper-bound x (step x) (fst invariant)
              (step-upper-bound x invariant) (step-increasing x invariant))))

    step-preserves : ∀ x → Invariant x → Invariant (step x)
    step-preserves x invariant =
      ≤ℝ-trans a x (step x) (fst invariant) (step-increasing x invariant)
      , step-upper-bound x invariant
      , step-image-upper-bound x invariant

    residual-contracts : ∀ x → Invariant x →
      residual (step x) ≤ℝ contraction · residual x
    residual-contracts x invariant =
      subst2 _≤ℝ_
        (subtractSameRight target (exponentialEntireValue (step x))
          (exponentialEntireValue x))
        factorization
        (addPres≤L
          (- (exponentialEntireValue (step x) - exponentialEntireValue x))
          (- (exponentialEntireValue a · (step x - x))) (residual x)
          (negPres≤ (exponentialEntireValue a · (step x - x))
            (exponentialEntireValue (step x) - exponentialEntireValue x)
            (≤ℝ-trans (exponentialEntireValue a · (step x - x))
              (exponentialEntireValue x · (step x - x))
              (exponentialEntireValue (step x) - exponentialEntireValue x)
              (mulPres≤R-0≤ (exponentialEntireValue a) (exponentialEntireValue x)
                (step x - x) (nonnegativeSub x (step x) (step-increasing x invariant))
                (exponentialEntireValue-preserves≤ a x (fst invariant)))
              (exponentialEntireValue-lowerDifferenceBound x (step x)
                (step-increasing x invariant)))))
      where
      factorization : residual x - exponentialEntireValue a · (step x - x)
        ≡ contraction · residual x
      factorization =
        cong (λ value → residual x - value)
          (cong (exponentialEntireValue a ·_) (step-difference x)
          ∙ mulAssoc (exponentialEntireValue a) damping (residual x)
          ∙ cong (_· residual x) (mulComm (exponentialEntireValue a) damping))
        ∙ sym (cong (_- ((damping · exponentialEntireValue a) · residual x))
            (mulIdL (residual x)))
        ∙ sym (R.·DistL- 1ℝ (damping · exponentialEntireValue a) (residual x))

  -- Keep recursive values opaque under exponential and lattice operations.
  -- Clients rewrite using these small paths instead of normalizing the
  -- completed-real representation of a growing arithmetic expression.
  opaque
    iteration-state : ℕ → Σ[ x ∈ ℝ ] Invariant x
    iteration-state zero = a , initial-invariant
    iteration-state (suc n) =
      step (fst (iteration-state n))
      , step-preserves (fst (iteration-state n)) (snd (iteration-state n))

    iteration : ℕ → ℝ
    iteration n = fst (iteration-state n)

    iteration-value : ∀ n → iteration n ≡ fst (iteration-state n)
    iteration-value n = refl

    iteration-zero : iteration zero ≡ a
    iteration-zero = refl

    iteration-step : ∀ n → iteration (suc n) ≡ step (iteration n)
    iteration-step n = refl

    iteration-invariant : ∀ n → Invariant (iteration n)
    iteration-invariant n =
      subst Invariant (sym (iteration-value n)) (snd (iteration-state n))

  opaque
    iteration-contracts : ∀ n →
      residual (iteration (suc n)) ≤ℝ contraction · residual (iteration n)
    iteration-contracts n =
      subst (λ point → residual point ≤ℝ contraction · residual (iteration n))
        (sym (iteration-step n))
        (residual-contracts (iteration n) (iteration-invariant n))

    iteration-increasing : ∀ n → iteration n ≤ℝ iteration (suc n)
    iteration-increasing n =
      subst (iteration n ≤ℝ_) (sym (iteration-step n))
        (step-increasing (iteration n) (iteration-invariant n))

    iteration-difference : ∀ n →
      iteration (suc n) - iteration n ≡ damping · residual (iteration n)
    iteration-difference n =
      cong (_- iteration n) (iteration-step n) ∙ step-difference (iteration n)

    residual-geometric-bound : ∀ n →
      residual (iteration n) ≤ℝ residual (iteration zero) · powℝ contraction n
    residual-geometric-bound =
      contractionGeometricBound (λ n → residual (iteration n))
        contraction contraction-nonnegative iteration-contracts

    increment-geometric-bound : ∀ n →
      absℝ (successiveIncrements iteration n) ≤ℝ
      (damping · residual (iteration zero)) · powℝ contraction n
    increment-geometric-bound n =
      subst2 _≤ℝ_
        (sym (absOfNonnegative (iteration (suc n) - iteration n)
            (nonnegativeSub (iteration n) (iteration (suc n))
              (iteration-increasing n))
          ∙ iteration-difference n))
        (mulAssoc damping (residual (iteration zero)) (powℝ contraction n))
        (mulPres≤L (residual (iteration n))
          (residual (iteration zero) · powℝ contraction n) damping
          (0≤→isNonnegative damping damping-nonnegative)
          (residual-geometric-bound n))

    iteration-cauchy : SeqWitness iteration
    iteration-cauchy =
      geometricallyBoundedIncrementsCauchy
        iteration contraction (damping · residual (iteration zero))
        contraction-nonnegative contraction<one increment-geometric-bound

    iteration-residual-nonnegative : ∀ n → 0ℝ ≤ℝ residual (iteration n)
    iteration-residual-nonnegative n =
      residual-nonnegative (iteration n) (iteration-invariant n)

  opaque
    value : ℝ
    value = limitOfSequence iteration iteration-cauchy

    iteration-limit : isLimitSequence iteration value
    iteration-limit = limitOfSequenceIsLimit iteration iteration-cauchy

    residual-limit :
      isLimitSequence (λ n → residual (iteration n)) (residual value)
    residual-limit =
      subPresIsLimitSequence
        {x = λ _ → target} {y = λ n → exponentialEntireValue (iteration n)}
        {l = target} {m = exponentialEntireValue value}
        (constantIsLimitSequence target)
        (continuousRealMapPreservesLimit
          exponentialEntireValue exponentialEntireValueIsContinuous
          {sequence = iteration} {limit = value} iteration-limit)

    residual-zero : residual value ≡ 0ℝ
    residual-zero =
      geometricallyBoundedNonnegativeLimitZero
        (λ n → residual (iteration n)) (residual value)
        contraction (residual (iteration zero))
        contraction-nonnegative contraction<one residual-limit
        iteration-residual-nonnegative residual-geometric-bound

    value-preimage : exponentialEntireValue value ≡ target
    value-preimage = sym
      (sym (subAddCancel target (exponentialEntireValue value))
      ∙ cong (_+ exponentialEntireValue value) residual-zero
      ∙ addIdL (exponentialEntireValue value))
