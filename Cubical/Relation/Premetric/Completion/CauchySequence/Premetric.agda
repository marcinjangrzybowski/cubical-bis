open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Relation.Premetric.Properties

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Approximation
  as CompletionApproximation
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as CauchySequenceLimits

module S = CauchyCompletion M'
module SC = CompletionApproximation M'
module PM = PremetricStr (M' .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

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

  dyadic : ℕ → ℚ₊
  dyadic n = [ 1 / 2 ]₊ ℚ₊^ⁿ n

  half<one : fst [ 1 / 2 ]₊ <ℚ 1
  half<one = subst (fst [ 1 / 2 ]₊ <ℚ_)
    (/2+/2≡id 1) (<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  dyadicAntitone : ∀ m n → m ℕ.≤ n →
    fst (dyadic n) ≤ℚ fst (dyadic m)
  dyadicAntitone m n m≤n =
    powExponentAntitone (fst [ 1 / 2 ]₊)
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ (snd [ 1 / 2 ]₊))
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ half<one)
      m n m≤n

  dyadicModulus : ℚ₊ → ℕ
  dyadicModulus ε = fst (1/2ⁿ<ε (ε /4₊))

  dyadicModulus-small : ∀ ε →
    fst (dyadic (dyadicModulus ε)) <ℚ fst (ε /4₊)
  dyadicModulus-small ε = snd (1/2ⁿ<ε (ε /4₊))


-- Only the tail witness at ε/4 is exposed here.  In particular this lemma
-- never asks for, or constructs, a modulus at every radius simultaneously.

ι-close-lim-from-late : ∀ q x gx ε N
  (xc : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
    x m S.≈ᶜ[ ε /4₊ ] x n)
  n →
  N ℕ.≤ n →
  S.ι q S.≈ᶜ[ ε /4₊ ] x n →
  S.ι q S.≈ᶜ[ ε ] S.lim x gx
ι-close-lim-from-late q x gx ε N xc n N≤n ιq∼xn =
  S.ι-lim q x gx N ε δ xc Δ
    (S.isMonotone≈ᶜ< _ _ _ target small<target small)
  where
  δ = ε /4₊

  x-n∼x-N : x n S.≈ᶜ[ δ ] x N
  x-n∼x-N = xc n N N≤n ℕ.≤-refl

  small : S.ι q S.≈ᶜ[ δ +₊ δ ] x N
  small = SC.tri≈ᶜ (S.ι q) (x n) (x N) δ δ ιq∼xn x-n∼x-N

  Δ : 0 ℚ.< ε -₊ δ
  Δ = <→0<Δ (fst δ) (fst ε) (/4₊<id ε)

  target = (ε -₊ δ , Δ)

  small<target : (δ +₊ δ) <₊ target
  small<target = +CancelR<
    (fst (δ +₊ δ)) (fst target) (fst δ)
    (subst (fst (δ +₊ δ) ℚ.+ fst δ <ℚ_)
      (sym (minusPlus₊ ε δ)) (tripleQuarter< ε))


-- Density still only makes one truncated choice for the requested radius.

∃approx : ∀ x ε → ∃[ q ∈ M' .fst ] (S.ι q S.≈ᶜ[ ε ] x)
∃approx = S.ElimCompletion-Prop.go e
  where
  e : S.ElimCompletion-Prop
    (λ x → ∀ ε → ∃[ q ∈ M' .fst ] (S.ι q S.≈ᶜ[ ε ] x))
  e .S.ElimCompletion-Prop.ιA q ε =
    ∣ q , S.isRefl≈ᶜ (S.ι q) ε ∣₁
  e .S.ElimCompletion-Prop.limA x gx IH ε =
    PT.rec squash₁ withTail (gx (ε /4₊))
    where
    withTail : S.CauchyTail x (ε /4₊) →
      ∃[ q ∈ M' .fst ] (S.ι q S.≈ᶜ[ ε ] S.lim x gx)
    withTail (N , xc) = PT.map
      (λ { (q , ιq∼xN) → q ,
        ι-close-lim-from-late q x gx ε N xc N ℕ.≤-refl ιq∼xN })
      (IH N (ε /4₊))
  e .S.ElimCompletion-Prop.isPropA x = isPropΠ λ _ → squash₁


close-lim-from-late :
  ∀ (z : S.Completion) (y : ℕ → S.Completion) (gy : S.IsCauchySequence y)
    ε (N : ℕ)
    (yc : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      y m S.≈ᶜ[ (ε /4₊) /4₊ ] y n)
    n →
  N ℕ.≤ n →
  z S.≈ᶜ[ (((ε /4₊) /4₊) /4₊) ] y n →
  z S.≈ᶜ[ ε ] S.lim y gy
close-lim-from-late z y gy ε N yc n late z∼yn =
  PT.rec (S.isProp≈ᶜ z ε (S.lim y gy)) withApprox
    (∃approx z small)
  where
  outer = ε /4₊
  required = outer /4₊
  small = required /4₊

  twiceSmall<required : (small +₊ small) <₊ required
  twiceSmall<required = begin<
    fst (small +₊ small)
      ≡→≤⟨ /4+/4≡/2 (fst required) ⟩
    fst (required /2₊)
      <⟨ /2₊<id required ⟩
    fst required ◾

  small<outer : small <₊ outer
  small<outer = ℚ.isTrans< _ _ _
    (/4₊<id required) (/4₊<id outer)

  smallPlusOuter<ε : (small +₊ outer) <₊ ε
  smallPlusOuter<ε = begin<
    fst (small +₊ outer)
      <⟨ +MonoR< (fst small) (fst outer) (fst outer) small<outer ⟩
    fst (outer +₊ outer)
      ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
    fst (ε /2₊)
      <⟨ /2₊<id ε ⟩
    fst ε ◾

  withApprox :
    (Σ[ q ∈ M' .fst ] (S.ι q S.≈ᶜ[ small ] z)) →
    z S.≈ᶜ[ ε ] S.lim y gy
  withApprox (q , ιq∼z) =
    S.isMonotone≈ᶜ< z (S.lim y gy)
      (small +₊ outer) ε smallPlusOuter<ε
      (SC.tri≈ᶜ z (S.ι q) (S.lim y gy) small outer
        (S.sym≈ᶜ (S.ι q) z small ιq∼z)
        (ι-close-lim-from-late q y gy outer N yc n late
          (S.isMonotone≈ᶜ< (S.ι q) (y n)
            (small +₊ small) required twiceSmall<required
            (SC.tri≈ᶜ (S.ι q) z (y n) small small
              ιq∼z z∼yn))))


isRounded≈ᶜ : ∀ x y ε →
  x S.≈ᶜ[ ε ] y →
  ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x S.≈ᶜ[ δ ] y)
isRounded≈ᶜ = SC.isRounded≈ᶜ

tri≈ᶜ : ∀ x y z ε δ →
  x S.≈ᶜ[ ε ] y → y S.≈ᶜ[ δ ] z →
  x S.≈ᶜ[ ε +₊ δ ] z
tri≈ᶜ = SC.tri≈ᶜ


CompletionPremetricSpace : PremetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
CompletionPremetricSpace .fst = S.Completion
PremetricStr._≈[_]_ (CompletionPremetricSpace .snd) = S._≈ᶜ[_]_
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isSetM = S.isSetCompletion
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isProp≈ =
  λ x y ε → S.isProp≈ᶜ x ε y
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isRefl≈ = S.isRefl≈ᶜ
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isSym≈ = S.sym≈ᶜ
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isSeparated≈ = S.eqCompletion
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isTriangular≈ = SC.tri≈ᶜ
PremetricStr.isPremetric (CompletionPremetricSpace .snd) .IsPremetric.isRounded≈ = isRounded≈ᶜ


lim-isLimitSeq : ∀ z gz →
  PremetricTheory.isLimitSeq CompletionPremetricSpace z (S.lim z gz)
lim-isLimitSeq z gz ε =
  PT.rec squash₁ withTail (gz required)
  where
  required = (ε /4₊) /4₊

  withTail : S.CauchyTail z required →
    ∃[ K ∈ ℕ ] (∀ n → K ℕ.≤ n →
      z n S.≈ᶜ[ ε ] S.lim z gz)
  withTail (N , nc) =
    ∣ N , (λ n late →
      close-lim-from-late (z n) z gz ε N nc n late
        (S.isRefl≈ᶜ (z n) (required /4₊))) ∣₁


-- The constructor `lim`, together with the preceding convergence theorem,
-- supplies exactly the radiuswise sequential completeness notion used by
-- extension theorems.  No simultaneous choice of tail indices is made.

module CompletionLimits =
  CauchySequenceLimits CompletionPremetricSpace

hasCauchySequenceLimitsCompletion :
  CompletionLimits.HasCauchySequenceLimits
hasCauchySequenceLimitsCompletion z gz =
  S.lim z gz , lim-isLimitSeq z gz


-- A usual ℚ₊-indexed Cauchy approximation has a canonical dyadic
-- subsequence.  Its tail bound is constructed separately for the requested
-- radius, exactly matching IsCauchySequence.

dyadicIsCauchySequence : ∀ (x : ℚ₊ → S.Completion) →
  (∀ ε δ → x ε S.≈ᶜ[ ε +₊ δ ] x δ) →
  S.IsCauchySequence (x ∘ dyadic)
dyadicIsCauchySequence x xc ε = ∣ dyadicModulus ε , close ∣₁
  where
  close : ∀ m n →
    dyadicModulus ε ℕ.≤ m →
    dyadicModulus ε ℕ.≤ n →
    x (dyadic m) S.≈ᶜ[ ε ] x (dyadic n)
  close m n N≤m N≤n =
    S.isMonotone≈ᶜ< _ _ (dyadic m +₊ dyadic n) ε
      sum<ε (xc (dyadic m) (dyadic n))
    where
    q = ε /4₊

    dm<q : fst (dyadic m) <ℚ fst q
    dm<q = begin<
      fst (dyadic m)
        ≤⟨ dyadicAntitone (dyadicModulus ε) m N≤m ⟩
      fst (dyadic (dyadicModulus ε))
        <⟨ dyadicModulus-small ε ⟩
      fst q ◾

    dn<q : fst (dyadic n) <ℚ fst q
    dn<q = begin<
      fst (dyadic n)
        ≤⟨ dyadicAntitone (dyadicModulus ε) n N≤n ⟩
      fst (dyadic (dyadicModulus ε))
        <⟨ dyadicModulus-small ε ⟩
      fst q ◾

    sum<ε : (dyadic m +₊ dyadic n) <₊ ε
    sum<ε = begin<
      fst (dyadic m +₊ dyadic n)
        <⟨ +Mono< _ _ _ _ dm<q dn<q ⟩
      fst (q +₊ q)
        ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
      fst (ε /2₊)
        <⟨ /2₊<id ε ⟩
      fst ε ◾


module CompletionTheory = PremetricTheory CompletionPremetricSpace

-- Completeness in the library's ordinary sense: every ℚ₊-indexed
-- Cauchy approximation has a limit.  The proof samples dyadically, applies
-- the sequential limit constructor, and compares the original approximation
-- with that subsequence.

isCompleteCompletion : CompletionTheory.isComplete
isCompleteCompletion x xc = S.lim z gz , isLimit
  where
  z : ℕ → S.Completion
  z = x ∘ dyadic

  gz : S.IsCauchySequence z
  gz = dyadicIsCauchySequence x xc

  isLimit : CompletionTheory.isLimit x (S.lim z gz)
  isLimit ε θ =
    PT.rec (S.isProp≈ᶜ (x ε) (ε +₊ θ) (S.lim z gz))
      withSequentialLimit
      (lim-isLimitSeq z gz (θ /4₊))
    where
    withSequentialLimit :
      (Σ[ K ∈ ℕ ] (∀ n → K ℕ.≤ n →
        z n S.≈ᶜ[ θ /4₊ ] S.lim z gz)) →
      x ε S.≈ᶜ[ ε +₊ θ ] S.lim z gz
    withSequentialLimit (K , closeToLimit) =
      S.isMonotone≈ᶜ< _ _
        ((ε +₊ dyadic n) +₊ θ /4₊) (ε +₊ θ)
        total<target
        (SC.tri≈ᶜ (x ε) (z n) (S.lim z gz)
          (ε +₊ dyadic n) (θ /4₊)
          (xc ε (dyadic n))
          (closeToLimit n K≤n))
      where
      n = K ℕ.+ dyadicModulus θ

      K≤n : K ℕ.≤ n
      K≤n = ℕ.≤SumLeft

      modulus≤n : dyadicModulus θ ℕ.≤ n
      modulus≤n = ℕ.≤SumRight

      dn<quarter : fst (dyadic n) <ℚ fst (θ /4₊)
      dn<quarter = begin<
        fst (dyadic n)
          ≤⟨ dyadicAntitone (dyadicModulus θ) n modulus≤n ⟩
        fst (dyadic (dyadicModulus θ))
          <⟨ dyadicModulus-small θ ⟩
        fst (θ /4₊) ◾

      dyadicPlusQuarter<θ : (dyadic n +₊ θ /4₊) <₊ θ
      dyadicPlusQuarter<θ = begin<
        fst (dyadic n +₊ θ /4₊)
          <⟨ +MonoR< (fst (dyadic n)) (fst (θ /4₊))
               (fst (θ /4₊)) dn<quarter ⟩
        fst (θ /4₊ +₊ θ /4₊)
          ≡→≤⟨ /4+/4≡/2 (fst θ) ⟩
        fst (θ /2₊)
          <⟨ /2₊<id θ ⟩
        fst θ ◾

      total<target : ((ε +₊ dyadic n) +₊ θ /4₊) <₊ (ε +₊ θ)
      total<target = begin<
        fst ((ε +₊ dyadic n) +₊ θ /4₊)
          ≡→≤⟨ sym (ℚ.+Assoc (fst ε) (fst (dyadic n)) (fst (θ /4₊))) ⟩
        fst (ε +₊ (dyadic n +₊ θ /4₊))
          <⟨ +MonoL< (fst (dyadic n +₊ θ /4₊)) (fst θ)
               (fst ε) dyadicPlusQuarter<θ ⟩
        fst (ε +₊ θ) ◾
