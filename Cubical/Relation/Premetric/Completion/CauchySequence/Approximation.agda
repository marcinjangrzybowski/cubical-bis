open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Approximation
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Properties as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ

import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as OrdinaryCloseness
import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Elimination
  as CauchyCompletionElimination

module C = OrdinaryCloseness M'
module S = CauchyCompletion M'
module E = CauchyCompletionElimination M'
module PM = PremetricStr (M' .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

private
  M = M' .fst
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


Tailᵁ : (ℕ → C.UpperCuts) → ℚ₊ → ℕ → Type (ℓ-max ℓ ℓ')
Tailᵁ x ε N = ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
  x m C.≈ᵁ[ ε ] x n

SeqUpperCutWitness : (ℕ → C.UpperCuts) → Type (ℓ-max ℓ ℓ')
SeqUpperCutWitness x = ∀ ε → ∥ Σ[ N ∈ ℕ ] Tailᵁ x ε N ∥₁


-- This is the Cauchy-sequence analogue of OrdinaryCloseness's
-- UpperCut∃<.  Besides a radius and an index, a representative stores the
-- radius-specific tail which certifies that the chosen index is genuinely
-- late.  The whole package is merely truncated.

UpperCutSeq : (x : ℕ → C.UpperCuts) →
  SeqUpperCutWitness x → C.UpperCuts
fst (UpperCutSeq x gx) ε =
  ∥ Σ[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ]
      Σ[ N ∈ ℕ ]
        Tailᵁ x δ N ×
        fst (x N) [ ε -₊ δ ]⟨ δ<ε ⟩ ∥₁
snd (UpperCutSeq x gx) = upperCut
  where
  open C.IsUpperCut

  upperCut : C.IsUpperCut (fst (UpperCutSeq x gx))
  upperCut .isPropUpperCut ε = squash₁
  upperCut .isRoundedUpperCut ε = PT.rec squash₁ rounded
    where
    rounded :
      (Σ[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ]
        Σ[ N ∈ ℕ ]
          Tailᵁ x δ N ×
          fst (x N) [ ε -₊ δ ]⟨ δ<ε ⟩) →
      ∃[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × fst (UpperCutSeq x gx) ρ
    rounded (δ , δ<ε , N , tail , xN-close) =
      PT.map tighten
        (C.IsUpperCut.isRoundedUpperCut (snd (x N))
          [ ε -₊ δ ]⟨ δ<ε ⟩ xN-close)
      where
      tighten :
        (Σ[ κ ∈ ℚ₊ ]
          (κ <₊ [ ε -₊ δ ]⟨ δ<ε ⟩) × fst (x N) κ) →
        Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × fst (UpperCutSeq x gx) ρ
      tighten (κ , κ<ε-δ , xN-closeκ) =
        (κ +₊ δ) , (<≤ℚ![ κ<ε-δ ]) ,
        (∣ δ , (<₊SumRight δ κ) , N , tail ,
          subst (fst (x N)) (ℚ₊≡ (sym (ℚRing.plusMinus (fst κ) (fst δ))))
            xN-closeκ ∣₁)


substUpperCut : ∀ {U : C.UpperCuts} {ε ε'} →
  fst ε ≡ fst ε' → fst U ε → fst U ε'
substUpperCut {U = U} p = subst (fst U) (ℚ₊≡ p)


isTriangular≈ᵁ : ∀ U V W ε δ →
  U C.≈ᵁ[ ε ] V → V C.≈ᵁ[ δ ] W →
  U C.≈ᵁ[ ε +₊ δ ] W
isTriangular≈ᵁ U V W ε δ U≈V V≈W θ .fst u =
  substUpperCut {U = W} (sym (ℚ.+Assoc (fst θ) (fst ε) (fst δ)))
    (fst (V≈W (θ +₊ ε)) (fst (U≈V θ) u))
isTriangular≈ᵁ U V W ε δ U≈V V≈W θ .snd w =
  substUpperCut {U = U} ℚ!!
    (snd (U≈V (θ +₊ δ)) (snd (V≈W θ) w))


upperCut≈ : M → M → C.UpperCuts
upperCut≈ = C.UpperCut≈

upperCut≈-pres≈ : ∀ x y z ε → y PM.≈[ ε ] z →
  upperCut≈ x y C.≈ᵁ[ ε ] upperCut≈ x z
upperCut≈-pres≈ x y z ε y≈z θ .fst (lift x≈y) =
  lift (PM.isTriangular≈ x y z θ ε x≈y y≈z)
upperCut≈-pres≈ x y z ε y≈z θ .snd (lift x≈z) =
  lift (PM.isTriangular≈ x z y θ ε x≈z (PM.isSym≈ y z ε y≈z))


module _
  (U : C.UpperCuts) (y : ℕ → C.UpperCuts)
  (gy : SeqUpperCutWitness y)
  (N : ℕ) (ε δ : ℚ₊) (yc : Tailᵁ y δ N)
  (Δ : 0 <ℚ ε -₊ δ)
  (U≈yN : U C.≈ᵁ[ ε -₊ δ , Δ ] y N)
  where

  upperCut→seq : ∀ θ → fst U θ →
    fst (UpperCutSeq y gy) (θ +₊ ε)
  upperCut→seq θ Uθ =
    ∣ δ , (<≤ℚ![ Δ ]) , N , yc ,
      substUpperCut {U = y N} ℚ!! (fst (U≈yN θ) Uθ) ∣₁

  seq→upperCut : ∀ θ → fst (UpperCutSeq y gy) θ →
    fst U (θ +₊ ε)
  seq→upperCut θ = PT.rec (C.IsUpperCut.isPropUpperCut (snd U) (θ +₊ ε))
    λ (α , α<θ , K , yca , yK-close) →
      let
        L = ℕ.max K N

        K≤L : K ℕ.≤ L
        K≤L = ℕ.left-≤-max {K} {N}

        N≤L : N ℕ.≤ L
        N≤L = ℕ.right-≤-max {N} {K}

        yK≈yL : y K C.≈ᵁ[ α ] y L
        yK≈yL = yca K L ℕ.≤-refl K≤L

        yL≈yN : y L C.≈ᵁ[ δ ] y N
        yL≈yN = yc L N N≤L ℕ.≤-refl

        yK≈yN : y K C.≈ᵁ[ α +₊ δ ] y N
        yK≈yN = isTriangular≈ᵁ (y K) (y L) (y N) α δ yK≈yL yL≈yN

        yN-close : fst (y N) (θ +₊ δ)
        yN-close = substUpperCut {U = y N} ℚ!!
          (fst (yK≈yN [ θ -₊ α ]⟨ α<θ ⟩) yK-close)

        U-close : fst U ((θ +₊ δ) +₊ (ε -₊ δ , Δ))
        U-close = snd (U≈yN (θ +₊ δ)) yN-close
      in
        substUpperCut {U = U} ℚ!! U-close

  upperCut≈seq : U C.≈ᵁ[ ε ] UpperCutSeq y gy
  upperCut≈seq θ .fst = upperCut→seq θ
  upperCut≈seq θ .snd = seq→upperCut θ


seqUpperCut→seqUpperCut :
  ∀ (x : ℕ → C.UpperCuts) (gx : SeqUpperCutWitness x) N
    (y : ℕ → C.UpperCuts) (gy : SeqUpperCutWitness y) K
    ε δ η (xc : Tailᵁ x δ N) (yc : Tailᵁ y η K)
    (Δ : 0 <ℚ ε -₊ (δ +₊ η)) →
    x N C.≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] y K →
    ∀ θ → fst (UpperCutSeq x gx) θ →
      fst (UpperCutSeq y gy) (θ +₊ ε)
seqUpperCut→seqUpperCut x gx N y gy K ε δ η xc yc Δ xN≈yK θ =
  PT.map forward
  where
  forward :
    (Σ[ α ∈ ℚ₊ ] Σ[ α<θ ∈ (α <₊ θ) ]
      Σ[ I ∈ ℕ ]
        Tailᵁ x α I × fst (x I) [ θ -₊ α ]⟨ α<θ ⟩) →
    Σ[ η' ∈ ℚ₊ ] Σ[ η'<θ+ε ∈ (η' <₊ (θ +₊ ε)) ]
      Σ[ J ∈ ℕ ]
        Tailᵁ y η' J ×
        fst (y J) [ (θ +₊ ε) -₊ η' ]⟨ η'<θ+ε ⟩
  forward (α , α<θ , I , xca , xI-close) =
    η , η<θ+ε , K , yc , yK-close
    where
    L = ℕ.max I N

    I≤L : I ℕ.≤ L
    I≤L = ℕ.left-≤-max {I} {N}

    N≤L : N ℕ.≤ L
    N≤L = ℕ.right-≤-max {N} {I}

    xI≈xL : x I C.≈ᵁ[ α ] x L
    xI≈xL = xca I L ℕ.≤-refl I≤L

    xL≈xN : x L C.≈ᵁ[ δ ] x N
    xL≈xN = xc L N N≤L ℕ.≤-refl

    xI≈xN : x I C.≈ᵁ[ α +₊ δ ] x N
    xI≈xN = isTriangular≈ᵁ (x I) (x L) (x N) α δ xI≈xL xL≈xN

    xN-close : fst (x N) (θ +₊ δ)
    xN-close = substUpperCut {U = x N} ℚ!!
      (fst (xI≈xN [ θ -₊ α ]⟨ α<θ ⟩) xI-close)

    yK-close-raw :
      fst (y K) ((θ +₊ δ) +₊ (ε -₊ (δ +₊ η) , Δ))
    yK-close-raw = fst (xN≈yK (θ +₊ δ)) xN-close

    η<θ+ε : η <₊ (θ +₊ ε)
    η<θ+ε = <≤ℚ![ Δ ]

    yK-close : fst (y K) [ (θ +₊ ε) -₊ η ]⟨ η<θ+ε ⟩
    yK-close = substUpperCut {U = y K} ℚ!! yK-close-raw


upperCutSeq≈ :
  ∀ (x : ℕ → C.UpperCuts) (gx : SeqUpperCutWitness x) N
    (y : ℕ → C.UpperCuts) (gy : SeqUpperCutWitness y) K
    ε δ η (xc : Tailᵁ x δ N) (yc : Tailᵁ y η K)
    (Δ : 0 <ℚ ε -₊ (δ +₊ η)) →
    x N C.≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] y K →
    UpperCutSeq x gx C.≈ᵁ[ ε ] UpperCutSeq y gy
upperCutSeq≈ x gx N y gy K ε δ η xc yc Δ xN≈yK θ .fst =
  seqUpperCut→seqUpperCut x gx N y gy K ε δ η xc yc Δ xN≈yK θ
upperCutSeq≈ x gx N y gy K ε δ η xc yc Δ xN≈yK θ .snd =
  seqUpperCut→seqUpperCut y gy K x gx N ε η δ yc xc Δ' yK≈xN θ
  where
  Δ' : 0 <ℚ ε -₊ (η +₊ δ)
  Δ' = <≤ℚ![ Δ ]

  yK≈xN : y K C.≈ᵁ[ ε -₊ (η +₊ δ) , Δ' ] x N
  yK≈xN = subst (y K C.≈ᵁ[_] x N) (ℚ₊≡ ℚ!!)
    (C.isSym≈ᵁ (x N) (y K) _ xN≈yK)


upperCutsAtιRec : M →
  E.RecCompletionSym C.UpperCuts (λ U V ε → U C.≈ᵁ[ ε ] V)
upperCutsAtιRec q .E.RecCompletionSym.ιA = upperCut≈ q
upperCutsAtιRec q .E.RecCompletionSym.limA = UpperCutSeq
upperCutsAtιRec q .E.RecCompletionSym.eqA = C.isSeparated≈ᵁ
upperCutsAtιRec q .E.RecCompletionSym.ι-ι-B = upperCut≈-pres≈ q
upperCutsAtιRec q .E.RecCompletionSym.ι-lim-B =
  λ x y gy N ε δ yc Δ → upperCut≈seq (upperCut≈ q x) y gy N ε δ yc Δ
upperCutsAtιRec q .E.RecCompletionSym.lim-lim-B = upperCutSeq≈
upperCutsAtιRec q .E.RecCompletionSym.isSymB = C.isSym≈ᵁ
upperCutsAtιRec q .E.RecCompletionSym.isPropB = C.isProp≈ᵁ


B⟨ι_,_⟩ : M → S.Completion → C.UpperCuts
B⟨ι q , x ⟩ = E.RecCompletionSym.go (upperCutsAtιRec q) x

B[_]⟨ι_,_⟩ : ℚ₊ → M → S.Completion → Type (ℓ-max ℓ ℓ')
B[ ε ]⟨ι q , x ⟩ = fst B⟨ι q , x ⟩ ε

B⟨ι_,⟩-pres≈ᶜ : ∀ q x y ε → x S.≈ᶜ[ ε ] y →
  B⟨ι q , x ⟩ C.≈ᵁ[ ε ] B⟨ι q , y ⟩
B⟨ι q ,⟩-pres≈ᶜ x y ε = E.RecCompletionSym.go≈ᶜ (upperCutsAtιRec q)


-- A decorated variant retains the actual HIIT tail proofs.  The one-sided
-- semantics above was sufficient for injectivity; retaining these proofs is
-- what makes the eventual semantic ball relation decodable back to HIIT
-- closeness.

Tailᵁᵈ : (x : ℕ → S.Completion) → (ℕ → C.UpperCuts) →
  ℚ₊ → ℕ → Type (ℓ-max ℓ ℓ')
Tailᵁᵈ x U ε N = ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
  Σ[ r ∈ x m S.≈ᶜ[ ε ] x n ] U m C.≈ᵁ[ ε ] U n

SeqUpperCutWitnessᵈ : (x : ℕ → S.Completion) →
  (ℕ → C.UpperCuts) → Type (ℓ-max ℓ ℓ')
SeqUpperCutWitnessᵈ x U = ∀ ε → ∥ Σ[ N ∈ ℕ ] Tailᵁᵈ x U ε N ∥₁

UpperCutSeqᵈ : ∀ (x : ℕ → S.Completion) (U : ℕ → C.UpperCuts) →
  SeqUpperCutWitnessᵈ x U → C.UpperCuts
fst (UpperCutSeqᵈ x U gx) ε =
  ∥ Σ[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ]
      Σ[ N ∈ ℕ ] Tailᵁᵈ x U δ N ×
        fst (U N) [ ε -₊ δ ]⟨ δ<ε ⟩ ∥₁
snd (UpperCutSeqᵈ x U gx) = upperCut
  where
  open C.IsUpperCut

  upperCut : C.IsUpperCut (fst (UpperCutSeqᵈ x U gx))
  upperCut .isPropUpperCut ε = squash₁
  upperCut .isRoundedUpperCut ε = PT.rec squash₁ λ (δ , δ<ε , N , tail , UN) →
    PT.map
      (λ { (κ , κ<ε-δ , UNκ) →
        (κ +₊ δ) , (<≤ℚ![ κ<ε-δ ]) ,
        ∣ δ , (<₊SumRight δ κ) , N , tail ,
          subst (fst (U N))
            (ℚ₊≡ (sym (ℚRing.plusMinus (fst κ) (fst δ)))) UNκ ∣₁ })
      (C.IsUpperCut.isRoundedUpperCut (snd (U N))
        [ ε -₊ δ ]⟨ δ<ε ⟩ UN)


module _
  (V : C.UpperCuts) (y : ℕ → S.Completion) (U : ℕ → C.UpperCuts)
  (gy : SeqUpperCutWitnessᵈ y U)
  (N : ℕ) (ε δ : ℚ₊) (yc : Tailᵁᵈ y U δ N)
  (Δ : 0 <ℚ ε -₊ δ)
  (V≈UN : V C.≈ᵁ[ ε -₊ δ , Δ ] U N)
  where

  upperCut→seqᵈ : ∀ θ → fst V θ → fst (UpperCutSeqᵈ y U gy) (θ +₊ ε)
  upperCut→seqᵈ θ Vθ =
    ∣ δ , (<≤ℚ![ Δ ]) , N , yc ,
      substUpperCut {U = U N} ℚ!! (fst (V≈UN θ) Vθ) ∣₁

  seqᵈ→upperCut : ∀ θ → fst (UpperCutSeqᵈ y U gy) θ → fst V (θ +₊ ε)
  seqᵈ→upperCut θ = PT.rec (C.IsUpperCut.isPropUpperCut (snd V) (θ +₊ ε))
    λ (α , α<θ , K , yca , UK-close) →
      let
        L = ℕ.max K N
        K≤L : K ℕ.≤ L
        K≤L = ℕ.left-≤-max {K} {N}
        N≤L : N ℕ.≤ L
        N≤L = ℕ.right-≤-max {N} {K}
        UK≈UL = snd (yca K L ℕ.≤-refl K≤L)
        UL≈UN = snd (yc L N N≤L ℕ.≤-refl)
        UN-close = substUpperCut {U = U N} ℚ!!
          (fst (UL≈UN ([ θ -₊ α ]⟨ α<θ ⟩ +₊ α))
            (fst (UK≈UL [ θ -₊ α ]⟨ α<θ ⟩) UK-close))
        V-close = snd (V≈UN (θ +₊ δ)) UN-close
      in substUpperCut {U = V} ℚ!! V-close

  upperCut≈seqᵈ : V C.≈ᵁ[ ε ] UpperCutSeqᵈ y U gy
  upperCut≈seqᵈ θ .fst = upperCut→seqᵈ θ
  upperCut≈seqᵈ θ .snd = seqᵈ→upperCut θ


seqUpperCutᵈ→seqUpperCutᵈ :
  ∀ (x : ℕ → S.Completion) (U : ℕ → C.UpperCuts)
    (gx : SeqUpperCutWitnessᵈ x U) N
    (y : ℕ → S.Completion) (V : ℕ → C.UpperCuts)
    (gy : SeqUpperCutWitnessᵈ y V) K
    ε δ η (xc : Tailᵁᵈ x U δ N) (yc : Tailᵁᵈ y V η K)
    (Δ : 0 <ℚ ε -₊ (δ +₊ η)) →
    U N C.≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] V K →
    ∀ θ → fst (UpperCutSeqᵈ x U gx) θ →
      fst (UpperCutSeqᵈ y V gy) (θ +₊ ε)
seqUpperCutᵈ→seqUpperCutᵈ x U gx N y V gy K ε δ η xc yc Δ UN≈VK θ =
  PT.map forward
  where
  forward :
    (Σ[ α ∈ ℚ₊ ] Σ[ α<θ ∈ (α <₊ θ) ]
      Σ[ I ∈ ℕ ] Tailᵁᵈ x U α I × fst (U I) [ θ -₊ α ]⟨ α<θ ⟩) →
    Σ[ η' ∈ ℚ₊ ] Σ[ η'<θ+ε ∈ (η' <₊ (θ +₊ ε)) ]
      Σ[ J ∈ ℕ ] Tailᵁᵈ y V η' J ×
        fst (V J) [ (θ +₊ ε) -₊ η' ]⟨ η'<θ+ε ⟩
  forward (α , α<θ , I , xca , UI-close) = η , η<θ+ε , K , yc , VK-close
    where
    L = ℕ.max I N
    I≤L : I ℕ.≤ L
    I≤L = ℕ.left-≤-max {I} {N}
    N≤L : N ℕ.≤ L
    N≤L = ℕ.right-≤-max {N} {I}
    UI≈UL = snd (xca I L ℕ.≤-refl I≤L)
    UL≈UN = snd (xc L N N≤L ℕ.≤-refl)
    UN-close = substUpperCut {U = U N} ℚ!!
      (fst (UL≈UN ([ θ -₊ α ]⟨ α<θ ⟩ +₊ α))
        (fst (UI≈UL [ θ -₊ α ]⟨ α<θ ⟩) UI-close))
    VK-raw = fst (UN≈VK (θ +₊ δ)) UN-close
    η<θ+ε : η <₊ (θ +₊ ε)
    η<θ+ε = <≤ℚ![ Δ ]
    VK-close = substUpperCut {U = V K} ℚ!! VK-raw


upperCutSeqᵈ≈ :
  ∀ (x : ℕ → S.Completion) (U : ℕ → C.UpperCuts)
    (gx : SeqUpperCutWitnessᵈ x U) N
    (y : ℕ → S.Completion) (V : ℕ → C.UpperCuts)
    (gy : SeqUpperCutWitnessᵈ y V) K
    ε δ η (xc : Tailᵁᵈ x U δ N) (yc : Tailᵁᵈ y V η K)
    (Δ : 0 <ℚ ε -₊ (δ +₊ η)) →
    U N C.≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] V K →
    UpperCutSeqᵈ x U gx C.≈ᵁ[ ε ] UpperCutSeqᵈ y V gy
upperCutSeqᵈ≈ x U gx N y V gy K ε δ η xc yc Δ UN≈VK θ .fst =
  seqUpperCutᵈ→seqUpperCutᵈ x U gx N y V gy K ε δ η xc yc Δ UN≈VK θ
upperCutSeqᵈ≈ x U gx N y V gy K ε δ η xc yc Δ UN≈VK θ .snd =
  seqUpperCutᵈ→seqUpperCutᵈ y V gy K x U gx N ε η δ yc xc Δ' VK≈UN θ
  where
  Δ' : 0 <ℚ ε -₊ (η +₊ δ)
  Δ' = <≤ℚ![ Δ ]
  VK≈UN = subst (V K C.≈ᵁ[_] U N) (ℚ₊≡ ℚ!!)
    (C.isSym≈ᵁ (U N) (V K) _ UN≈VK)


upperCutsAtιElim : M →
  E.ElimCompletion (λ _ → C.UpperCuts)
    (λ U V ε _ → U C.≈ᵁ[ ε ] V)
upperCutsAtιElim q .E.ElimCompletion.ιA = upperCut≈ q
upperCutsAtιElim q .E.ElimCompletion.limA =
  λ x gx U gxU → UpperCutSeqᵈ x U gxU
upperCutsAtιElim q .E.ElimCompletion.eqA p U V coarse all =
  C.isSeparated≈ᵁ U V all
upperCutsAtιElim q .E.ElimCompletion.ι-ι-B = upperCut≈-pres≈ q
upperCutsAtιElim q .E.ElimCompletion.ι-lim-B =
  λ x y gy N ε δ yc Δ r U gyU ycU →
    upperCut≈seqᵈ (upperCut≈ q x) y U gyU N ε δ
      (λ m n N≤m N≤n → yc m n N≤m N≤n , ycU m n N≤m N≤n) Δ
upperCutsAtιElim q .E.ElimCompletion.lim-ι-B =
  λ x gx N y ε δ xc Δ r U gxU xcU inner →
    C.isSym≈ᵁ (upperCut≈ q y) (UpperCutSeqᵈ x U gxU) ε
      (upperCut≈seqᵈ (upperCut≈ q y) x U gxU N ε δ
        (λ m n N≤m N≤n → xc m n N≤m N≤n , xcU m n N≤m N≤n) Δ
        (C.isSym≈ᵁ (U N) (upperCut≈ q y) _ inner))
upperCutsAtιElim q .E.ElimCompletion.lim-lim-B =
  λ x gx N y gy K ε δ η xc yc Δ r U gxU xcU V gyV ycV →
    upperCutSeqᵈ≈ x U gxU N y V gyV K ε δ η
      (λ m n N≤m N≤n → xc m n N≤m N≤n , xcU m n N≤m N≤n)
      (λ m n K≤m K≤n → yc m n K≤m K≤n , ycV m n K≤m K≤n) Δ
upperCutsAtιElim q .E.ElimCompletion.isPropB U V ε r = C.isProp≈ᵁ U V ε


D⟨ι_,_⟩ : M → S.Completion → C.UpperCuts
D⟨ι q , x ⟩ = E.ElimCompletion.go (upperCutsAtιElim q) x

D[_]⟨ι_,_⟩ : ℚ₊ → M → S.Completion → Type (ℓ-max ℓ ℓ')
D[ ε ]⟨ι q , x ⟩ = fst D⟨ι q , x ⟩ ε

D⟨ι_,⟩-pres≈ᶜ : ∀ q x y ε → x S.≈ᶜ[ ε ] y →
  D⟨ι q , x ⟩ C.≈ᵁ[ ε ] D⟨ι q , y ⟩
D⟨ι q ,⟩-pres≈ᶜ x y ε = E.ElimCompletion.go≈ᶜ (upperCutsAtιElim q)


private
  tightenLimitRadius : ∀ (ε δ κ gap : ℚ₊) →
    fst gap ≡ fst ε ℚ.- fst δ → κ <₊ gap →
    (κ +₊ δ) <₊ ε
  tightenLimitRadius ε δ κ gap gap≡ε-δ κ<gap = begin<
    fst (κ +₊ δ)
      <⟨ +MonoR< (fst κ) (fst gap) (fst δ) κ<gap ⟩
    fst (gap +₊ δ)
      ≡→≤⟨ cong (ℚ._+ fst δ) gap≡ε-δ ⟩
    (fst ε ℚ.- fst δ) ℚ.+ fst δ
      ≡→≤⟨ minusPlus₊ ε δ ⟩
    fst ε ◾

  restoredDifference : ∀ (κ δ : ℚ₊) →
    (κ +₊ δ) -₊ δ ≡ fst κ
  restoredDifference κ δ = ℚRing.plusMinus (fst κ) (fst δ)


-- Roundedness is structural for the reduced HIIT relation: every remaining
-- constructor already contains strict radius slack.  It needs no triangle
-- law and is therefore available before the semantic ball equivalence.

isRounded≈ᶜ : ∀ x y ε →
  x S.≈ᶜ[ ε ] y →
  ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x S.≈ᶜ[ δ ] y)
isRounded≈ᶜ .(S.ι x) .(S.ι y) ε (S.ι-ι x y .ε x≈y) =
  PT.map (λ { (δ , δ<ε , x≈δy) → δ , δ<ε , S.ι-ι x y δ x≈δy })
    (PM.isRounded≈ x y ε x≈y)
isRounded≈ᶜ .(S.ι x) .(S.lim y gy) ε
  (S.ι-lim x y gy N .ε δ yc Δ inner) =
  PT.map tighten (isRounded≈ᶜ _ _ (ε -₊ δ , Δ) inner)
  where
  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ δ , Δ)) × (S.ι x S.≈ᶜ[ κ ] y N) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × (S.ι x S.≈ᶜ[ ρ ] S.lim y gy)
  tighten (κ , κ<ε-δ , innerκ) = ρ , ρ<ε ,
    S.ι-lim x y gy N ρ δ yc Δρ innerρ
    where
    ρ = κ +₊ δ
    ρ<ε = tightenLimitRadius ε δ κ (ε -₊ δ , Δ) refl κ<ε-δ
    difference≡κ = restoredDifference κ δ
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)
    innerρ = subst (S.ι x S.≈ᶜ[_] y N) (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded≈ᶜ .(S.lim x gx) .(S.ι y) ε
  (S.lim-ι x gx N y .ε δ xc Δ inner) =
  PT.map tighten (isRounded≈ᶜ _ _ (ε -₊ δ , Δ) inner)
  where
  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ δ , Δ)) × (x N S.≈ᶜ[ κ ] S.ι y) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × (S.lim x gx S.≈ᶜ[ ρ ] S.ι y)
  tighten (κ , κ<ε-δ , innerκ) = ρ , ρ<ε ,
    S.lim-ι x gx N y ρ δ xc Δρ innerρ
    where
    ρ = κ +₊ δ
    ρ<ε = tightenLimitRadius ε δ κ (ε -₊ δ , Δ) refl κ<ε-δ
    difference≡κ = restoredDifference κ δ
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)
    innerρ = subst (x N S.≈ᶜ[_] S.ι y) (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded≈ᶜ .(S.lim x gx) .(S.lim y gy) ε
  (S.lim-lim x gx N y gy K .ε δ η xc yc Δ inner) =
  PT.map tighten (isRounded≈ᶜ _ _ (ε -₊ (δ +₊ η) , Δ) inner)
  where
  outer = δ +₊ η
  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ outer , Δ)) × (x N S.≈ᶜ[ κ ] y K) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × (S.lim x gx S.≈ᶜ[ ρ ] S.lim y gy)
  tighten (κ , κ<ε-outer , innerκ) = ρ , ρ<ε ,
    S.lim-lim x gx N y gy K ρ δ η xc yc Δρ innerρ
    where
    ρ = κ +₊ outer
    ρ<ε = tightenLimitRadius ε outer κ (ε -₊ outer , Δ) refl κ<ε-outer
    difference≡κ = restoredDifference κ outer
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)
    innerρ = subst (x N S.≈ᶜ[_] y K) (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded≈ᶜ x y ε (S.isProp≈ᶜ .x .ε .y p q i) =
  isProp→PathP (λ _ → squash₁)
    (isRounded≈ᶜ x y ε p) (isRounded≈ᶜ x y ε q) i


-- The first decisive application of the semantic relation: an HIIT proof
-- between embedded base points reflects to the original premetric.  The
-- rounded proof supplies the strict slack which lets the upper-cut action
-- recover radius ε itself rather than only every radius above ε.

ι-ι→≈ : ∀ x y ε →
  S.ι x S.≈ᶜ[ ε ] S.ι y → x PM.≈[ ε ] y
ι-ι→≈ x y ε p = PT.rec (PM.isProp≈ x y ε) reflect (isRounded≈ᶜ _ _ ε p)
  where
  reflect :
    (Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) × (S.ι x S.≈ᶜ[ ρ ] S.ι y)) →
    x PM.≈[ ε ] y
  reflect (ρ , ρ<ε , pρ) =
    subst (x PM.≈[_] y) (ℚ₊≡ (minusPlus₊ ε ρ)) result
    where
    gap : ℚ₊
    gap = [ ε -₊ ρ ]⟨ ρ<ε ⟩

    semantic : upperCut≈ x x C.≈ᵁ[ ρ ] upperCut≈ x y
    semantic = B⟨ι x ,⟩-pres≈ᶜ (S.ι x) (S.ι y) ρ pρ

    result : x PM.≈[ gap +₊ ρ ] y
    result = lower (fst (semantic gap) (lift (PM.isRefl≈ x gap)))


isInjectiveι : ∀ x y → S.ι x ≡ S.ι y → x ≡ y
isInjectiveι x y ιx≡ιy = PM.isSeparated≈ x y λ ε →
  ι-ι→≈ x y ε
    (subst (S.ι x S.≈ᶜ[ ε ]_) ιx≡ιy (S.isRefl≈ᶜ (S.ι x) ε))


-- For an embedded centre, the decorated upper cut is not merely preserved
-- by HIIT closeness: it classifies that closeness exactly.  This is the
-- Cauchy-sequence counterpart of the first computation rules for the
-- ordinary completion's semantic balls.

ι≈ᶜ→D : ∀ q y ε → S.ι q S.≈ᶜ[ ε ] y → D[ ε ]⟨ι q , y ⟩
ι≈ᶜ→D q y ε p = PT.rec
  (C.IsUpperCut.isPropUpperCut (snd D⟨ι q , y ⟩) ε)
  reflect (isRounded≈ᶜ (S.ι q) y ε p)
  where
  reflect : Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) ×
      (S.ι q S.≈ᶜ[ ρ ] y) →
    D[ ε ]⟨ι q , y ⟩
  reflect (ρ , ρ<ε , pρ) =
    subst (D[_]⟨ι q , y ⟩) (ℚ₊≡ (minusPlus₊ ε ρ))
      (fst (D⟨ι q ,⟩-pres≈ᶜ (S.ι q) y ρ pρ
        [ ε -₊ ρ ]⟨ ρ<ε ⟩)
        (lift (PM.isRefl≈ q [ ε -₊ ρ ]⟨ ρ<ε ⟩)))


D→ι≈ᶜ : ∀ q y ε → D[ ε ]⟨ι q , y ⟩ → S.ι q S.≈ᶜ[ ε ] y
D→ι≈ᶜ q = S.ElimCompletion-Prop.go e
  where
  e : S.ElimCompletion-Prop
    (λ y → ∀ ε → D[ ε ]⟨ι q , y ⟩ → S.ι q S.≈ᶜ[ ε ] y)
  e .S.ElimCompletion-Prop.ιA y ε (lift q≈y) = S.ι-ι q y ε q≈y
  e .S.ElimCompletion-Prop.limA y gy IH ε =
    PT.rec (S.isProp≈ᶜ (S.ι q) ε (S.lim y gy)) λ where
      (δ , δ<ε , N , tail , inner) →
        S.ι-lim q y gy N ε δ
          (λ m n N≤m N≤n → fst (tail m n N≤m N≤n))
          (<→0<Δ (fst δ) (fst ε) δ<ε)
          (IH N [ ε -₊ δ ]⟨ δ<ε ⟩ inner)
  e .S.ElimCompletion-Prop.isPropA y = isPropΠ λ ε →
    isProp→ (S.isProp≈ᶜ (S.ι q) ε y)


ι≈ᶜ≃D : ∀ {q y ε} →
  (S.ι q S.≈ᶜ[ ε ] y) ≃ D[ ε ]⟨ι q , y ⟩
ι≈ᶜ≃D {q} {y} {ε} = propBiimpl→Equiv
  (S.isProp≈ᶜ (S.ι q) ε y)
  (C.IsUpperCut.isPropUpperCut (snd D⟨ι q , y ⟩) ε)
  (ι≈ᶜ→D q y ε) (D→ι≈ᶜ q y ε)


-- Two decorated balls with a common embedded centre compose.  This is where
-- the direct computations of D are especially useful: in the limit-limit
-- case the two independently truncated tails are opened only inside the
-- proposition-valued target and their chosen components are handled by the
-- component-component induction hypothesis.

D-pair→≈ᶜ : ∀ q x z α β →
  D[ α ]⟨ι q , x ⟩ → D[ β ]⟨ι q , z ⟩ →
  x S.≈ᶜ[ α +₊ β ] z
D-pair→≈ᶜ q = E.ElimCompletion-Prop2.go e
  where
  e : E.ElimCompletion-Prop2
    (λ x z → ∀ α β →
      D[ α ]⟨ι q , x ⟩ → D[ β ]⟨ι q , z ⟩ →
      x S.≈ᶜ[ α +₊ β ] z)

  e .E.ElimCompletion-Prop2.ι-ιA x z α β
    (lift q≈x) (lift q≈z) =
    S.ι-ι x z (α +₊ β)
      (PM.isTriangular≈ x q z α β
        (PM.isSym≈ q x α q≈x) q≈z)

  e .E.ElimCompletion-Prop2.ι-limA x z gz IH α β Dx =
    PT.rec (S.isProp≈ᶜ (S.ι x) (α +₊ β) (S.lim z gz)) λ where
      (η , η<β , K , tail , DzK) →
        let
          η<α+β : η <₊ (α +₊ β)
          η<α+β = <≤ℚ![ η<β ]

          Δ : 0 <ℚ (α +₊ β) -₊ η
          Δ = <→0<Δ (fst η) (fst (α +₊ β)) η<α+β

          inner : S.ι x S.≈ᶜ[ (α +₊ β) -₊ η , Δ ] z K
          inner = subst (S.ι x S.≈ᶜ[_] z K) (ℚ₊≡ ℚ!!)
            (IH K α [ β -₊ η ]⟨ η<β ⟩ Dx DzK)
        in
          S.ι-lim x z gz K (α +₊ β) η
            (λ m n K≤m K≤n → fst (tail m n K≤m K≤n))
            Δ inner

  e .E.ElimCompletion-Prop2.lim-ιA x gx z IH α β Dx (lift q≈z) =
    PT.rec (S.isProp≈ᶜ (S.lim x gx) (α +₊ β) (S.ι z))
      (λ where
        (δ , δ<α , N , tail , DxN) →
          let
            δ<α+β : δ <₊ (α +₊ β)
            δ<α+β = <≤ℚ![ δ<α ]

            Δ : 0 <ℚ (α +₊ β) -₊ δ
            Δ = <→0<Δ (fst δ) (fst (α +₊ β)) δ<α+β

            inner : x N S.≈ᶜ[ (α +₊ β) -₊ δ , Δ ] S.ι z
            inner = subst (x N S.≈ᶜ[_] S.ι z) (ℚ₊≡ ℚ!!)
              (IH N [ α -₊ δ ]⟨ δ<α ⟩ β DxN (lift q≈z))
          in
            S.lim-ι x gx N z (α +₊ β) δ
              (λ m n N≤m N≤n → fst (tail m n N≤m N≤n))
              Δ inner)
      Dx

  e .E.ElimCompletion-Prop2.lim-limA x gx z gz IH α β Dx =
    PT.rec (isProp→ (S.isProp≈ᶜ (S.lim x gx) (α +₊ β) (S.lim z gz)))
      (λ where
        (δ , δ<α , N , xtail , DxN) Dz →
          PT.rec (S.isProp≈ᶜ (S.lim x gx) (α +₊ β) (S.lim z gz))
            (λ where
              (η , η<β , K , ztail , DzK) →
                let
                  δη<αβ : (δ +₊ η) <₊ (α +₊ β)
                  δη<αβ = +Mono< (fst δ) (fst α)
                    (fst η) (fst β) δ<α η<β

                  Δ : 0 <ℚ (α +₊ β) -₊ (δ +₊ η)
                  Δ = <→0<Δ (fst (δ +₊ η))
                    (fst (α +₊ β)) δη<αβ

                  inner : x N S.≈ᶜ[
                      (α +₊ β) -₊ (δ +₊ η) , Δ ] z K
                  inner = subst (x N S.≈ᶜ[_] z K) (ℚ₊≡ ℚ!!)
                    (IH N K
                      [ α -₊ δ ]⟨ δ<α ⟩
                      [ β -₊ η ]⟨ η<β ⟩
                      DxN DzK)
                in
                  S.lim-lim x gx N z gz K (α +₊ β) δ η
                    (λ m n N≤m N≤n → fst (xtail m n N≤m N≤n))
                    (λ m n K≤m K≤n → fst (ztail m n K≤m K≤n))
                    Δ inner)
            Dz)
      Dx

  e .E.ElimCompletion-Prop2.isPropA x z = isPropΠ2 λ α β →
    isProp→ (isProp→ (S.isProp≈ᶜ x (α +₊ β) z))


-- Density does not use triangle.  Only the tail at ε/4 is opened, and the
-- recursively obtained base approximation of its selected component fits
-- directly into the ι-lim constructor.

∃approx : ∀ x ε → ∃[ q ∈ M ] (S.ι q S.≈ᶜ[ ε ] x)
∃approx = S.ElimCompletion-Prop.go e
  where
  e : S.ElimCompletion-Prop
    (λ x → ∀ ε → ∃[ q ∈ M ] (S.ι q S.≈ᶜ[ ε ] x))
  e .S.ElimCompletion-Prop.ιA q ε =
    ∣ q , S.isRefl≈ᶜ (S.ι q) ε ∣₁
  e .S.ElimCompletion-Prop.limA x gx IH ε =
    PT.rec squash₁ withTail (gx quarter)
    where
    quarter = ε /4₊

    quarter+quarter<ε : (quarter +₊ quarter) <₊ ε
    quarter+quarter<ε = begin<
      fst (quarter +₊ quarter)
        ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
      fst (ε /2₊)
        <⟨ /2₊<id ε ⟩
      fst ε ◾

    quarter<ε : quarter <₊ ε
    quarter<ε = ℚ.isTrans< _ _ _
      (/4₊</2₊ ε) (/2₊<id ε)

    Δ : 0 <ℚ ε -₊ quarter
    Δ = <→0<Δ (fst quarter) (fst ε) quarter<ε

    quarter<gap : quarter <₊ (ε -₊ quarter , Δ)
    quarter<gap = +CancelR<
      (fst quarter) (ε -₊ quarter) (fst quarter)
      (subst (fst (quarter +₊ quarter) <ℚ_)
        (sym (minusPlus₊ ε quarter)) quarter+quarter<ε)

    withTail : S.CauchyTail x quarter →
      ∃[ q ∈ M ] (S.ι q S.≈ᶜ[ ε ] S.lim x gx)
    withTail (N , xc) = PT.map
      (λ { (q , q∼xN) → q ,
        S.ι-lim q x gx N ε quarter xc Δ
          (S.isMonotone≈ᶜ< (S.ι q) (x N)
            quarter (ε -₊ quarter , Δ) quarter<gap q∼xN) })
      (IH N quarter)
  e .S.ElimCompletion-Prop.isPropA x = isPropΠ λ _ → squash₁


-- Triangle is now derived rather than postulated by the HIIT.  Roundedness
-- supplies strict slack in both input radii.  A sufficiently close embedded
-- approximation of the left endpoint becomes a common semantic centre;
-- D-pair→≈ᶜ composes the two decorated balls, and the remaining slack absorbs
-- the approximation twice.

tri≈ᶜ : ∀ x y z ε δ →
  x S.≈ᶜ[ ε ] y → y S.≈ᶜ[ δ ] z →
  x S.≈ᶜ[ ε +₊ δ ] z
tri≈ᶜ x y z ε δ x∼y y∼z =
  PT.rec targetProp withLeft (isRounded≈ᶜ x y ε x∼y)
  where
  targetProp = S.isProp≈ᶜ x (ε +₊ δ) z

  withLeft : Σ[ ε' ∈ ℚ₊ ] (ε' <₊ ε) ×
      (x S.≈ᶜ[ ε' ] y) →
    x S.≈ᶜ[ ε +₊ δ ] z
  withLeft (ε' , ε'<ε , x∼y') =
    PT.rec targetProp withRight (isRounded≈ᶜ y z δ y∼z)
    where
    withRight : Σ[ δ' ∈ ℚ₊ ] (δ' <₊ δ) ×
        (y S.≈ᶜ[ δ' ] z) →
      x S.≈ᶜ[ ε +₊ δ ] z
    withRight (δ' , δ'<δ , y∼z') =
      PT.rec targetProp withCenter (∃approx x α)
      where
      inner = ε' +₊ δ'

      inner<target : inner <₊ (ε +₊ δ)
      inner<target = +Mono< (fst ε') (fst ε)
        (fst δ') (fst δ) ε'<ε δ'<δ

      gap = [ (ε +₊ δ) -₊ inner ]⟨ inner<target ⟩
      α = gap /4₊
      β = (α +₊ ε') +₊ δ'
      ρ = α +₊ β

      ρ<target : ρ <₊ (ε +₊ δ)
      ρ<target = <≤ℚ![ inner<target ]

      withCenter : Σ[ q ∈ M ] (S.ι q S.≈ᶜ[ α ] x) →
        x S.≈ᶜ[ ε +₊ δ ] z
      withCenter (q , q∼x) =
        S.isMonotone≈ᶜ< x z ρ (ε +₊ δ) ρ<target
          (D-pair→≈ᶜ q x z α β Dx Dz)
        where
        Dx : D[ α ]⟨ι q , x ⟩
        Dx = ι≈ᶜ→D q x α q∼x

        Dy : D[ α +₊ ε' ]⟨ι q , y ⟩
        Dy = fst (D⟨ι q ,⟩-pres≈ᶜ x y ε' x∼y' α) Dx

        Dz : D[ β ]⟨ι q , z ⟩
        Dz = fst (D⟨ι q ,⟩-pres≈ᶜ y z δ' y∼z' (α +₊ ε')) Dy


-- The resulting semantic relation.  A witness is a common embedded centre
-- together with two decorated balls whose radii have sum strictly below the
-- requested radius.  All choices, including the centre, remain under one
-- propositional truncation.

_≈ᴰ[_]_ : S.Completion → ℚ₊ → S.Completion → Type (ℓ-max ℓ ℓ')
x ≈ᴰ[ ε ] y =
  ∃[ q ∈ M ] Σ[ α ∈ ℚ₊ ] Σ[ β ∈ ℚ₊ ]
    ((α +₊ β) <₊ ε) ×
    D[ α ]⟨ι q , x ⟩ × D[ β ]⟨ι q , y ⟩

isProp≈ᴰ : ∀ x y ε → isProp (x ≈ᴰ[ ε ] y)
isProp≈ᴰ x y ε = squash₁


≈ᴰ→≈ᶜ : ∀ {x y ε} → x ≈ᴰ[ ε ] y → x S.≈ᶜ[ ε ] y
≈ᴰ→≈ᶜ {x} {y} {ε} = PT.rec (S.isProp≈ᶜ x ε y) λ where
  (q , α , β , αβ<ε , Dx , Dy) →
    S.isMonotone≈ᶜ< x y (α +₊ β) ε αβ<ε
      (D-pair→≈ᶜ q x y α β Dx Dy)


≈ᶜ→≈ᴰ : ∀ {x y ε} → x S.≈ᶜ[ ε ] y → x ≈ᴰ[ ε ] y
≈ᶜ→≈ᴰ {x} {y} {ε} x∼y =
  PT.rec squash₁ withRounded (isRounded≈ᶜ x y ε x∼y)
  where
  withRounded : Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) ×
      (x S.≈ᶜ[ ρ ] y) →
    x ≈ᴰ[ ε ] y
  withRounded (ρ , ρ<ε , x∼yρ) = PT.map withCenter (∃approx x α)
    where
    gap = [ ε -₊ ρ ]⟨ ρ<ε ⟩
    α = gap /4₊
    β = α +₊ ρ

    αβ<ε : (α +₊ β) <₊ ε
    αβ<ε = <≤ℚ![ ρ<ε ]

    withCenter : Σ[ q ∈ M ] (S.ι q S.≈ᶜ[ α ] x) →
      Σ[ q ∈ M ] Σ[ α' ∈ ℚ₊ ] Σ[ β' ∈ ℚ₊ ]
        ((α' +₊ β') <₊ ε) ×
        D[ α' ]⟨ι q , x ⟩ × D[ β' ]⟨ι q , y ⟩
    withCenter (q , q∼x) = q , α , β , αβ<ε , Dx , Dy
      where
      Dx : D[ α ]⟨ι q , x ⟩
      Dx = ι≈ᶜ→D q x α q∼x

      Dy : D[ β ]⟨ι q , y ⟩
      Dy = fst (D⟨ι q ,⟩-pres≈ᶜ x y ρ x∼yρ α) Dx


≈ᶜ≃≈ᴰ : ∀ {x y ε} → (x S.≈ᶜ[ ε ] y) ≃ (x ≈ᴰ[ ε ] y)
≈ᶜ≃≈ᴰ {x} {y} {ε} = propBiimpl→Equiv
  (S.isProp≈ᶜ x ε y) (isProp≈ᴰ x y ε) ≈ᶜ→≈ᴰ ≈ᴰ→≈ᶜ
