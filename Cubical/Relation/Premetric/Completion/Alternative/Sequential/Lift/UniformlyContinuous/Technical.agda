open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous.Technical
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as RegularComparisonDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition

module S = SequentialDefinition M'
module T = SequentialDefinition N'
module Comparison = RegularComparisonDefinition M'
module C = CauchyContinuousDefinition M' N'

private
  M = M' .fst
  N = N' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')
  module PM = PremetricStr (M' .snd)
  module PN = PremetricStr (N' .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


JointlyApproximableFor :
  (M → N) → S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
JointlyApproximableFor f = C.JointlyApproximableFor (T.ι ∘ f)

isPropJointlyApproximableFor : ∀ f x y →
  isProp (JointlyApproximableFor f x y)
isPropJointlyApproximableFor f =
  C.isPropJointlyApproximableFor (T.ι ∘ f)


private
  tripleQuarter< : ∀ ε → ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


module WithModulus
  (f : M → N)
  (μ : ℚ₊ → ℚ₊)
  (f-uc : IsUniformlyContinuousWith (M' .snd) f (N' .snd) μ) where

  inputBudget : ℚ₊ → ℚ₊
  inputBudget ε = μ (ε /4₊) /4₊

  JointlyApproximable : S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
  JointlyApproximable = JointlyApproximableFor f

  jointlyApproximable-pres∼ : ∀ x x' y y' ε →
    JointlyApproximable x y →
    JointlyApproximable x' y' →
    x S.∼̂ₛ[ inputBudget ε ] x' →
    y T.∼̂ₛ[ ε ] y'
  jointlyApproximable-pres∼ x x' y y' ε xy x'y' x∼x' =
    PT.rec2 (T.isProp∼ y ε y') step
      (xy sourceRadius outputRadius)
      (x'y' sourceRadius outputRadius)
    where
    outputRadius = ε /4₊
    sourceRadius = inputBudget ε

    step :
      (Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x) ×
        (T.ι (f q) T.∼̂ₛ[ outputRadius ] y)) →
      (Σ[ r ∈ M ]
        (S.ι r S.∼̂ₛ[ sourceRadius ] x') ×
        (T.ι (f r) T.∼̂ₛ[ outputRadius ] y')) →
      y T.∼̂ₛ[ ε ] y'
    step (q , ιq∼x , ιfq∼y) (r , ιr∼x' , ιfr∼y') =
      T.isMonotone∼̂ₛ< y y' _ ε (tripleQuarter< ε)
        (T.tri∼ y (T.ι (f r)) y'
          (outputRadius +₊ outputRadius) outputRadius
          (T.tri∼ y (T.ι (f q)) (T.ι (f r))
            outputRadius outputRadius
            (T.sym∼ _ _ outputRadius ιfq∼y)
            (T.ι-ι (f q) (f r) outputRadius f-q∼f-r))
          ιfr∼y')
      where
      q∼r-small : S.ι q S.∼̂ₛ[
          (sourceRadius +₊ sourceRadius) +₊ sourceRadius
        ] S.ι r
      q∼r-small =
        S.tri∼ (S.ι q) x' (S.ι r)
          (sourceRadius +₊ sourceRadius) sourceRadius
          (S.tri∼ (S.ι q) x x'
            sourceRadius sourceRadius ιq∼x x∼x')
          (S.sym∼ _ _ sourceRadius ιr∼x')

      q∼r : q PM.≈[ μ outputRadius ] r
      q∼r = Comparison.ι-reflects∼ q r (μ outputRadius)
        (S.isMonotone∼̂ₛ< _ _ _ (μ outputRadius)
          (tripleQuarter< (μ outputRadius)) q∼r-small)

      f-q∼f-r : f q PN.≈[ outputRadius ] f r
      f-q∼f-r =
        f-uc .IsUniformlyContinuousWith.pres≈ q r outputRadius q∼r


  jointlyApproximable-equal : ∀ x y y' →
    JointlyApproximable x y →
    JointlyApproximable x y' → y ≡ y'
  jointlyApproximable-equal x y y' xy xy' =
    T.eqℭ y y' λ ε →
      jointlyApproximable-pres∼ x x y y' ε xy xy'
        (S.isRefl∼̂ₛ x (inputBudget ε))


  imageCauchySeq : ∀ x y →
    (∀ n → JointlyApproximable (x n) (y n)) →
    S.CauchySeq x → T.CauchySeq y
  imageCauchySeq x y joint (N , xc) .fst ε = N (inputBudget ε)
  imageCauchySeq x y joint (N , xc) .snd ε m n Nε≤m Nε≤n =
    jointlyApproximable-pres∼ (x m) (x n) (y m) (y n) ε
      (joint m) (joint n)
      (xc (inputBudget ε) m n Nε≤m Nε≤n)


  isCauchyContinuousWith : C.IsCauchyContinuous (T.ι ∘ f)
  isCauchyContinuousWith = C.cauchyContinuous preserve
    where
    preserve : ∀ x y →
      (∀ n → JointlyApproximable (x n) (y n)) →
      S.SeqWitness x → T.SeqWitness y
    preserve x y joint = PT.map (imageCauchySeq x y joint)
