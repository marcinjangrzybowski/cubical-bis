module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Transfer where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base


open PositiveRationals using (ℚ₊)


ChosenClosenessReflection : (ℕ → ℝ) → (ℕ → ℝ) → Type₀
ChosenClosenessReflection source image =
  ∀ input →
  Σ[ output ∈ ℚ₊ ]
    (∀ m n → image m ∼[ output ] image n →
      source m ∼[ input ] source n)


opaque
  chosenClosenessReflection-presCauchySeq :
    ∀ source image →
    ChosenClosenessReflection source image →
    CauchySeq image → CauchySeq source
  chosenClosenessReflection-presCauchySeq
      source image reflect (N , image-cauchy) =
    (λ input → N (fst (reflect input)))
    , λ input m n Nε≤m Nε≤n →
        snd (reflect input) m n
          (image-cauchy
            (fst (reflect input)) m n Nε≤m Nε≤n)


  chosenClosenessReflection-presSeqWitness :
    ∀ source image →
    ChosenClosenessReflection source image →
    SeqWitness image → SeqWitness source
  chosenClosenessReflection-presSeqWitness source image reflect =
    PT.map
      (chosenClosenessReflection-presCauchySeq source image reflect)
