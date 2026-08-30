module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (zero ; suc)

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Base

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  as Lattice
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


-- Cauchy preservation ----------------------------------------------------
--
-- These statements strengthen the corresponding chosen-modulus sequence
-- results: every operation consumes only radiuswise truncated Cauchy tails.
-- For nonexpanding unary operations they are instances of the generic
-- continuity theorem.  The binary operations below still reuse their
-- constructor-level graph proofs until a public continuity package for each
-- binary operation is available.

negPresIsCauchySequence : ∀ {x} →
  IsCauchySequence x →
  IsCauchySequence (Neg.-_ ∘ x)
negPresIsCauchySequence {x} =
  nonExpandingPresIsCauchySequence Neg.negationⁿ x


absPresIsCauchySequence : ∀ {x} →
  IsCauchySequence x →
  IsCauchySequence (Abs.absℝ ∘ x)
absPresIsCauchySequence {x} =
  nonExpandingPresIsCauchySequence Abs.absoluteValueⁿ x


addPresIsCauchySequence : ∀ {x y} →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → x n Add.+ y n)
addPresIsCauchySequence = Add.add-diagonalIsCauchySequence


mulPresIsCauchySequence : ∀ {x y} →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → x n Mul.· y n)
mulPresIsCauchySequence = Mul.mul-diagonalIsCauchySequence


maxPresIsCauchySequence : ∀ {x y} →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → x n Lattice.⊔ℝ y n)
maxPresIsCauchySequence = Lattice.max-diagonalIsCauchySequence


scalarPresIsCauchySequence : ∀ c {x} →
  IsCauchySequence x →
  IsCauchySequence (Scalar._⋆_ c ∘ x)
scalarPresIsCauchySequence c {x} =
  continuousPreservesIsCauchySequence
    (Scalar._⋆_ c) (Scalar.scalar-isContinuous c) x


subPresIsCauchySequence : ∀ {x y} →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → x n Group.- y n)
subPresIsCauchySequence gx gy =
  addPresIsCauchySequence gx (negPresIsCauchySequence gy)


minPresIsCauchySequence : ∀ {x y} →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → x n Lattice.⊓ℝ y n)
minPresIsCauchySequence gx gy =
  negPresIsCauchySequence
    (maxPresIsCauchySequence
      (negPresIsCauchySequence gx)
      (negPresIsCauchySequence gy))


powerPresIsCauchySequence : ∀ n {x} →
  IsCauchySequence x →
  IsCauchySequence (λ k → x k ^ⁿ n)
powerPresIsCauchySequence zero {x} gx =
  constantIsCauchySequence oneℝ
powerPresIsCauchySequence (suc n) {x} gx =
  mulPresIsCauchySequence gx
    (powerPresIsCauchySequence n gx)


-- Limit preservation -----------------------------------------------------
--
-- Unary limit preservation is purely the generic continuity theorem.  For
-- binary operations, a convergence proof is turned into radiuswise
-- Cauchyness, never into a chosen modulus.  Their native `lim` computation
-- rules then identify the canonical output limit.

negPresIsLimitSequence : ∀ {x l} →
  isLimitSequence x l →
  isLimitSequence (Neg.-_ ∘ x) (Neg.- l)
negPresIsLimitSequence =
  nonExpandingPresIsLimitSequence Neg.negationⁿ


absPresIsLimitSequence : ∀ {x l} →
  isLimitSequence x l →
  isLimitSequence (Abs.absℝ ∘ x) (Abs.absℝ l)
absPresIsLimitSequence =
  nonExpandingPresIsLimitSequence Abs.absoluteValueⁿ


scalarPresIsLimitSequence : ∀ c {x l} →
  isLimitSequence x l →
  isLimitSequence (Scalar._⋆_ c ∘ x) (c Scalar.⋆ l)
scalarPresIsLimitSequence c =
  continuousPreservesIsLimitSequence
    (Scalar._⋆_ c) (Scalar.scalar-isContinuous c)


addPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n Add.+ y n) (l Add.+ m)
addPresIsLimitSequence {x} {y} {l} {m} x→l y→m =
  subst (isLimitSequence (λ n → x n Add.+ y n)) output-limit-path
    (limitOfCauchySequenceIsLimit _ output-cauchy)
  where
  x-cauchy = isLimitSequence→isCauchySequence x→l
  y-cauchy = isLimitSequence→isCauchySequence y→m
  output-cauchy = addPresIsCauchySequence x-cauchy y-cauchy

  output-limit-path :
    limitOfCauchySequence (λ n → x n Add.+ y n) output-cauchy ≡
    l Add.+ m
  output-limit-path =
    sym (Add.add-lim-lim x x-cauchy y y-cauchy)
    ∙ cong₂ Add._+_
        (canonicalLimit≡ x x-cauchy l x→l)
        (canonicalLimit≡ y y-cauchy m y→m)


mulPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n Mul.· y n) (l Mul.· m)
mulPresIsLimitSequence {x} {y} {l} {m} x→l y→m =
  subst (isLimitSequence (λ n → x n Mul.· y n)) output-limit-path
    (limitOfCauchySequenceIsLimit _ output-cauchy)
  where
  x-cauchy = isLimitSequence→isCauchySequence x→l
  y-cauchy = isLimitSequence→isCauchySequence y→m
  output-cauchy = mulPresIsCauchySequence x-cauchy y-cauchy

  output-limit-path :
    limitOfCauchySequence (λ n → x n Mul.· y n) output-cauchy ≡
    l Mul.· m
  output-limit-path =
    sym (Mul.mul-lim-lim x x-cauchy y y-cauchy)
    ∙ cong₂ Mul._·_
        (canonicalLimit≡ x x-cauchy l x→l)
        (canonicalLimit≡ y y-cauchy m y→m)


maxPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence
    (λ n → x n Lattice.⊔ℝ y n)
    (l Lattice.⊔ℝ m)
maxPresIsLimitSequence {x} {y} {l} {m} x→l y→m =
  subst
    (isLimitSequence (λ n → x n Lattice.⊔ℝ y n))
    output-limit-path
    (limitOfCauchySequenceIsLimit _ output-cauchy)
  where
  x-cauchy = isLimitSequence→isCauchySequence x→l
  y-cauchy = isLimitSequence→isCauchySequence y→m
  output-cauchy = maxPresIsCauchySequence x-cauchy y-cauchy

  output-limit-path :
    limitOfCauchySequence
      (λ n → x n Lattice.⊔ℝ y n) output-cauchy ≡
    l Lattice.⊔ℝ m
  output-limit-path =
    sym (Lattice.max-lim-lim x x-cauchy y y-cauchy)
    ∙ cong₂ Lattice._⊔ℝ_
        (canonicalLimit≡ x x-cauchy l x→l)
        (canonicalLimit≡ y y-cauchy m y→m)


subPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n Group.- y n) (l Group.- m)
subPresIsLimitSequence x→l y→m =
  addPresIsLimitSequence x→l (negPresIsLimitSequence y→m)


minPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence
    (λ n → x n Lattice.⊓ℝ y n)
    (l Lattice.⊓ℝ m)
minPresIsLimitSequence x→l y→m =
  negPresIsLimitSequence
    (maxPresIsLimitSequence
      (negPresIsLimitSequence x→l)
      (negPresIsLimitSequence y→m))


powerPresIsLimitSequence : ∀ n {x l} →
  isLimitSequence x l →
  isLimitSequence (λ k → x k ^ⁿ n) (l ^ⁿ n)
powerPresIsLimitSequence zero {x} {l} x→l =
  constantIsLimitSequence oneℝ
powerPresIsLimitSequence (suc n) {x} {l} x→l =
  mulPresIsLimitSequence x→l
    (powerPresIsLimitSequence n x→l)
