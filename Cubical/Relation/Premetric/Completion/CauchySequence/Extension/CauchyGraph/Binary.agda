open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  {ℓM} {ℓM'} {ℓN} {ℓN'} {ℓO} {ℓO'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (O' : PremetricSpace ℓO ℓO') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels hiding (extend)

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric

module S = CauchyCompletion M'
module U = CauchyCompletion N'
module T = CauchyCompletion O'
module SP = CompletionPremetric M'
module UP = CompletionPremetric N'
module TP = CompletionPremetric O'

private
  M = M' .fst
  N = N' .fst
  O = O' .fst
  ℓₘ = ℓ-max (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN'))
    (ℓ-max ℓO ℓO')

open PositiveRationals
open PositiveHalvesℚ


-- This is a genuinely binary graph condition: no product premetric or
-- completion of a product is involved.  The two source approximations are
-- chosen together with one approximation in the target graph.

GraphClosure :
  (M → N → T.Completion) → S.Completion → U.Completion → T.Completion → Type ℓₘ
GraphClosure f x y z = ∀ α β γ →
  ∃[ p ∈ M ]
    Σ[ q ∈ N ]
      (S.ι p S.≈ᶜ[ α ] x) ×
      (U.ι q U.≈ᶜ[ β ] y) ×
      (f p q T.≈ᶜ[ γ ] z)

isPropGraphClosure : ∀ f x y z →
  isProp (GraphClosure f x y z)
isPropGraphClosure f x y z =
  isPropΠ3 λ _ _ _ → squash₁


record PreservesCauchyGraphs (f : M → N → T.Completion) : Type ℓₘ where
  no-eta-equality
  pattern
  constructor preservesCauchyGraphs
  field
    presCauchyGraphs :
      ∀ (x : ℕ → S.Completion) (y : ℕ → U.Completion) (z : ℕ → T.Completion) →
      (∀ n → GraphClosure f (x n) (y n) (z n)) →
      S.IsCauchySequence x → U.IsCauchySequence y → T.IsCauchySequence z

open PreservesCauchyGraphs

isPropPreservesCauchyGraphs : ∀ f → isProp (PreservesCauchyGraphs f)
isPropPreservesCauchyGraphs f
  (preservesCauchyGraphs preserve)
  (preservesCauchyGraphs preserve') =
  cong preservesCauchyGraphs
    ((isPropΠ3 λ _ _ z →
        isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
        T.isPropIsCauchySequence z)
      preserve preserve')


BaseGraphClosure :
  (M → N → O) → S.Completion → U.Completion → T.Completion → Type ℓₘ
BaseGraphClosure f =
  GraphClosure (λ p q → T.ι (f p q))

PreservesBaseCauchyGraphs : (M → N → O) → Type ℓₘ
PreservesBaseCauchyGraphs f =
  PreservesCauchyGraphs (λ p q → T.ι (f p q))

isPropPreservesBaseCauchyGraphs : ∀ f →
  isProp (PreservesBaseCauchyGraphs f)
isPropPreservesBaseCauchyGraphs f =
  isPropPreservesCauchyGraphs (λ p q → T.ι (f p q))


private
  constantIsCauchySequenceS : ∀ x → S.IsCauchySequence (λ _ → x)
  constantIsCauchySequenceS x ε =
    ∣ zero , (λ m n _ _ → S.isRefl≈ᶜ x ε) ∣₁

  constantIsCauchySequenceU : ∀ y → U.IsCauchySequence (λ _ → y)
  constantIsCauchySequenceU y ε =
    ∣ zero , (λ m n _ _ → U.isRefl≈ᶜ y ε) ∣₁

  alternate : T.Completion → T.Completion → ℕ → T.Completion
  alternate z z' zero = z
  alternate z z' (suc zero) = z'
  alternate z z' (suc (suc n)) = alternate z z' n

  alternate-even : ∀ z z' n →
    alternate z z' (ℕ.doubleℕ n) ≡ z
  alternate-even z z' zero = refl
  alternate-even z z' (suc n) = alternate-even z z' n

  alternate-odd : ∀ z z' n →
    alternate z z' (suc (ℕ.doubleℕ n)) ≡ z'
  alternate-odd z z' zero = refl
  alternate-odd z z' (suc n) = alternate-odd z z' n

  n≤double : ∀ n → n ℕ.≤ ℕ.doubleℕ n
  n≤double zero = ℕ.≤-refl
  n≤double (suc n) =
    ℕ.suc-≤-suc (ℕ.≤-trans (n≤double n) ℕ.≤-sucℕ)


opaque
  graphClosureUnique : ∀ (f : M → N → T.Completion) →
    PreservesCauchyGraphs f →
    ∀ x y z z' →
    GraphClosure f x y z →
    GraphClosure f x y z' →
    z ≡ z'
  graphClosureUnique f f-cc x y z z' xyz xyz' =
    T.eqCompletion z z' close
    where
    alternatingJoint : ∀ n →
      GraphClosure f x y (alternate z z' n)
    alternatingJoint zero = xyz
    alternatingJoint (suc zero) = xyz'
    alternatingJoint (suc (suc n)) = alternatingJoint n

    alternatingWitness : T.IsCauchySequence (alternate z z')
    alternatingWitness = f-cc .presCauchyGraphs
      (λ _ → x) (λ _ → y) (alternate z z') alternatingJoint
      (constantIsCauchySequenceS x) (constantIsCauchySequenceU y)

    close : ∀ ε → z T.≈ᶜ[ ε ] z'
    close ε = PT.rec (T.isProp≈ᶜ z ε z') withCauchy
      (alternatingWitness ε)
      where
      withCauchy : T.CauchyTail (alternate z z') ε →
        z T.≈ᶜ[ ε ] z'
      withCauchy (K , zc) =
        subst2 (T._≈ᶜ[ ε ]_)
          (alternate-even z z' K)
          (alternate-odd z z' K)
          (zc (ℕ.doubleℕ K) (suc (ℕ.doubleℕ K))
            (n≤double K)
            (ℕ.≤-trans (n≤double K) ℕ.≤-sucℕ))


ExtensionFiber :
  (M → N → T.Completion) → S.Completion → U.Completion → Type ℓₘ
ExtensionFiber f x y =
  Σ[ z ∈ T.Completion ] GraphClosure f x y z

isPropExtensionFiber : ∀ (f : M → N → T.Completion) →
  PreservesCauchyGraphs f → ∀ x y → isProp (ExtensionFiber f x y)
isPropExtensionFiber f f-cc x y (z , xyz) (z' , xyz') =
  Σ≡Prop (isPropGraphClosure f x y)
    (graphClosureUnique f f-cc x y z z' xyz xyz')


private
  baseFiber : ∀ f p q → ExtensionFiber f (S.ι p) (U.ι q)
  baseFiber f p q .fst = f p q
  baseFiber f p q .snd α β γ =
    ∣ p , q
      , S.isRefl≈ᶜ (S.ι p) α
      , U.isRefl≈ᶜ (U.ι q) β
      , T.isRefl≈ᶜ (f p q) γ ∣₁


opaque
  limitRightGraphClosure :
    ∀ f x y gy z gz →
    (∀ n → GraphClosure f x (y n) (z n)) →
    GraphClosure f x (U.lim y gy) (T.lim z gz)
  limitRightGraphClosure f x y gy z gz joint α β γ =
    PT.rec squash₁ withSource (gy (β /4₊))
    where
    targetRequired : ℚ₊
    targetRequired = (γ /4₊) /4₊

    withSource : U.CauchyTail y (β /4₊) →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.≈ᶜ[ α ] x) ×
          (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
          (f p q T.≈ᶜ[ γ ] T.lim z gz)
    withSource (L , yc) =
      PT.rec squash₁ (withTarget L yc) (gz targetRequired)
      where
      withTarget :
        (L : ℕ) →
        (∀ m n → L ℕ.≤ m → L ℕ.≤ n →
          y m U.≈ᶜ[ β /4₊ ] y n) →
        T.CauchyTail z targetRequired →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.≈ᶜ[ α ] x) ×
            (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
            (f p q T.≈ᶜ[ γ ] T.lim z gz)
      withTarget L yc (K , zc) =
        PT.map makeLateApproximation
          (joint n α (β /4₊) targetSmall)
        where
        targetSmall : ℚ₊
        targetSmall = targetRequired /4₊

        n : ℕ
        n = ℕ.max L K

        makeLateApproximation :
          (Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.≈ᶜ[ α ] x) ×
              (U.ι q U.≈ᶜ[ β /4₊ ] y n) ×
              (f p q T.≈ᶜ[ targetSmall ] z n)) →
          Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.≈ᶜ[ α ] x) ×
              (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
              (f p q T.≈ᶜ[ γ ] T.lim z gz)
        makeLateApproximation (p , q , p-close , q-close , f-close) =
          p , q , p-close
          , UP.ι-close-lim-from-late q y gy β L yc n
              (ℕ.left-≤-max {m = L} {n = K}) q-close
          , TP.close-lim-from-late (f p q) z gz γ K zc n
              (ℕ.right-≤-max {n = K} {m = L}) f-close


  limitLeftGraphClosure :
    ∀ f x gx y z gz →
    (∀ n → GraphClosure f (x n) y (z n)) →
    GraphClosure f (S.lim x gx) y (T.lim z gz)
  limitLeftGraphClosure f x gx y z gz joint α β γ =
    PT.rec squash₁ withSource (gx (α /4₊))
    where
    targetRequired : ℚ₊
    targetRequired = (γ /4₊) /4₊

    withSource : S.CauchyTail x (α /4₊) →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
          (U.ι q U.≈ᶜ[ β ] y) ×
          (f p q T.≈ᶜ[ γ ] T.lim z gz)
    withSource (K , xc) =
      PT.rec squash₁ (withTarget K xc) (gz targetRequired)
      where
      withTarget :
        (K : ℕ) →
        (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
          x m S.≈ᶜ[ α /4₊ ] x n) →
        T.CauchyTail z targetRequired →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
            (U.ι q U.≈ᶜ[ β ] y) ×
            (f p q T.≈ᶜ[ γ ] T.lim z gz)
      withTarget K xc (L , zc) =
        PT.map makeLateApproximation
          (joint n (α /4₊) β targetSmall)
        where
        targetSmall : ℚ₊
        targetSmall = targetRequired /4₊

        n : ℕ
        n = ℕ.max K L

        makeLateApproximation :
          (Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.≈ᶜ[ α /4₊ ] x n) ×
              (U.ι q U.≈ᶜ[ β ] y) ×
              (f p q T.≈ᶜ[ targetSmall ] z n)) →
          Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
              (U.ι q U.≈ᶜ[ β ] y) ×
              (f p q T.≈ᶜ[ γ ] T.lim z gz)
        makeLateApproximation (p , q , p-close , q-close , f-close) =
          p , q
          , SP.ι-close-lim-from-late p x gx α K xc n
              (ℕ.left-≤-max {m = K} {n = L}) p-close
          , q-close
          , TP.close-lim-from-late (f p q) z gz γ L zc n
              (ℕ.right-≤-max {n = L} {m = K}) f-close


  limitBothGraphClosure :
    ∀ f x gx y gy z gz →
    (∀ n → GraphClosure f (x n) (y n) (z n)) →
    GraphClosure f
      (S.lim x gx) (U.lim y gy) (T.lim z gz)
  limitBothGraphClosure f x gx y gy z gz joint α β γ =
    PT.rec squash₁ withLeft (gx (α /4₊))
    where
    targetRequired : ℚ₊
    targetRequired = (γ /4₊) /4₊

    withLeft : S.CauchyTail x (α /4₊) →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
          (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
          (f p q T.≈ᶜ[ γ ] T.lim z gz)
    withLeft (K , xc) =
      PT.rec squash₁ (withRight K xc) (gy (β /4₊))
      where
      withRight :
        (K : ℕ) →
        (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
          x m S.≈ᶜ[ α /4₊ ] x n) →
        U.CauchyTail y (β /4₊) →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
            (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
            (f p q T.≈ᶜ[ γ ] T.lim z gz)
      withRight K xc (L , yc) =
        PT.rec squash₁ (withTarget K xc L yc)
          (gz targetRequired)
        where
        withTarget :
          (K : ℕ) →
          (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
            x m S.≈ᶜ[ α /4₊ ] x n) →
          (L : ℕ) →
          (∀ m n → L ℕ.≤ m → L ℕ.≤ n →
            y m U.≈ᶜ[ β /4₊ ] y n) →
          T.CauchyTail z targetRequired →
          ∃[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
              (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
              (f p q T.≈ᶜ[ γ ] T.lim z gz)
        withTarget K xc L yc (H , zc) =
          PT.map makeLateApproximation
            (joint n (α /4₊) (β /4₊) targetSmall)
          where
          targetSmall : ℚ₊
          targetSmall = targetRequired /4₊

          leftIndex rightIndex targetIndex : ℕ
          leftIndex = K
          rightIndex = L
          targetIndex = H

          n : ℕ
          n = ℕ.max leftIndex (ℕ.max rightIndex targetIndex)

          leftLate : leftIndex ℕ.≤ n
          leftLate = ℕ.left-≤-max

          rightLate : rightIndex ℕ.≤ n
          rightLate = ℕ.≤-trans
            (ℕ.left-≤-max {m = rightIndex} {n = targetIndex})
            (ℕ.right-≤-max
              {n = ℕ.max rightIndex targetIndex} {m = leftIndex})

          targetLate : targetIndex ℕ.≤ n
          targetLate = ℕ.≤-trans
            (ℕ.right-≤-max {n = targetIndex} {m = rightIndex})
            (ℕ.right-≤-max
              {n = ℕ.max rightIndex targetIndex} {m = leftIndex})

          makeLateApproximation :
            (Σ[ p ∈ M ]
              Σ[ q ∈ N ]
                (S.ι p S.≈ᶜ[ α /4₊ ] x n) ×
                (U.ι q U.≈ᶜ[ β /4₊ ] y n) ×
                (f p q T.≈ᶜ[ targetSmall ] z n)) →
            Σ[ p ∈ M ]
              Σ[ q ∈ N ]
                (S.ι p S.≈ᶜ[ α ] S.lim x gx) ×
                (U.ι q U.≈ᶜ[ β ] U.lim y gy) ×
                (f p q T.≈ᶜ[ γ ] T.lim z gz)
          makeLateApproximation
              (p , q , p-close , q-close , f-close) =
            p , q
            , SP.ι-close-lim-from-late p x gx α K xc n
                leftLate p-close
            , UP.ι-close-lim-from-late q y gy β L yc n
                rightLate q-close
            , TP.close-lim-from-late (f p q) z gz γ H zc n
                targetLate f-close


private
  limitRightFiber : ∀ (f : M → N → T.Completion)
    (f-cc : PreservesCauchyGraphs f) p
    (y : ℕ → U.Completion) (gy : U.IsCauchySequence y) →
    (∀ n → ExtensionFiber f (S.ι p) (y n)) →
    ExtensionFiber f (S.ι p) (U.lim y gy)
  limitRightFiber f f-cc p y gy IH =
    T.lim z gz ,
    limitRightGraphClosure f (S.ι p) y gy z gz joint
    where
    z : ℕ → T.Completion
    z n = IH n .fst

    joint : ∀ n → GraphClosure f (S.ι p) (y n) (z n)
    joint n = IH n .snd

    gz : T.IsCauchySequence z
    gz = f-cc .presCauchyGraphs
      (λ _ → S.ι p) y z joint
      (constantIsCauchySequenceS (S.ι p)) gy


  rightFiberElimAtBase : ∀ (f : M → N → T.Completion)
    (f-cc : PreservesCauchyGraphs f) p →
    U.ElimCompletion-Prop (ExtensionFiber f (S.ι p))
  rightFiberElimAtBase f f-cc p .U.ElimCompletion-Prop.ιA =
    baseFiber f p
  rightFiberElimAtBase f f-cc p .U.ElimCompletion-Prop.limA =
    limitRightFiber f f-cc p
  rightFiberElimAtBase f f-cc p .U.ElimCompletion-Prop.isPropA =
    isPropExtensionFiber f f-cc (S.ι p)


  limitLeftFiber : ∀ (f : M → N → T.Completion)
    (f-cc : PreservesCauchyGraphs f)
    (x : ℕ → S.Completion) (gx : S.IsCauchySequence x) →
    (∀ n y → ExtensionFiber f (x n) y) →
    ∀ y → ExtensionFiber f (S.lim x gx) y
  limitLeftFiber f f-cc x gx IH y =
    T.lim z gz ,
    limitLeftGraphClosure f x gx y z gz joint
    where
    z : ℕ → T.Completion
    z n = IH n y .fst

    joint : ∀ n → GraphClosure f (x n) y (z n)
    joint n = IH n y .snd

    gz : T.IsCauchySequence z
    gz = f-cc .presCauchyGraphs
      x (λ _ → y) z joint gx (constantIsCauchySequenceU y)


  fiberElim : ∀ (f : M → N → T.Completion)
    (f-cc : PreservesCauchyGraphs f) →
    S.ElimCompletion-Prop (λ x → ∀ y → ExtensionFiber f x y)
  fiberElim f f-cc .S.ElimCompletion-Prop.ιA p =
    U.ElimCompletion-Prop.go (rightFiberElimAtBase f f-cc p)
  fiberElim f f-cc .S.ElimCompletion-Prop.limA =
    limitLeftFiber f f-cc
  fiberElim f f-cc .S.ElimCompletion-Prop.isPropA x =
    isPropΠ (isPropExtensionFiber f f-cc x)


extensionFiber : ∀ (f : M → N → T.Completion) →
  PreservesCauchyGraphs f → ∀ x y → ExtensionFiber f x y
extensionFiber f f-cc = S.ElimCompletion-Prop.go (fiberElim f f-cc)

extend :
  (f : M → N → T.Completion) →
  PreservesCauchyGraphs f →
  S.Completion → U.Completion → T.Completion
extend f f-cc x y = extensionFiber f f-cc x y .fst

extend-graph :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f) x y →
  GraphClosure f x y
    (extend f f-cc x y)
extend-graph f f-cc x y =
  extensionFiber f f-cc x y .snd


extend-preservesDiagonalCauchy :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
    (x : ℕ → S.Completion) (y : ℕ → U.Completion) →
  S.IsCauchySequence x → U.IsCauchySequence y →
  T.IsCauchySequence (λ n → extend f f-cc (x n) (y n))
extend-preservesDiagonalCauchy f f-cc x y gx gy =
  f-cc .presCauchyGraphs x y
    (λ n → extend f f-cc (x n) (y n))
    (λ n → extend-graph f f-cc (x n) (y n))
    gx gy


-- All four constructor pairs have small computation rules.  The first
-- three, and the nested form of lim/lim, are judgmental consequences of the
-- construction; keeping these proofs as refl protects that computation.

extend-ι-ι :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f) p q →
  extend f f-cc (S.ι p) (U.ι q) ≡ f p q
extend-ι-ι f f-cc p q = refl

extend-ι-lim :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
    p y gy →
  extend f f-cc (S.ι p) (U.lim y gy) ≡
    T.lim (λ n → extend f f-cc (S.ι p) (y n)) _
extend-ι-lim f f-cc p y gy = refl

extend-lim-ι :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
    x gx q →
  extend f f-cc (S.lim x gx) (U.ι q) ≡
    T.lim (λ n → extend f f-cc (x n) (U.ι q)) _
extend-lim-ι f f-cc x gx q = refl

extend-lim-lim-nested :
  ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
    x gx y gy →
  extend f f-cc (S.lim x gx) (U.lim y gy) ≡
    T.lim
      (λ n → extend f f-cc (x n) (U.lim y gy)) _
extend-lim-lim-nested f f-cc x gx y gy = refl


-- Unlike the nested rule, this synchronized rule is propositional: it says
-- that the two source sequences may advance together.  The `-with` form
-- accepts any independently obtained Cauchy witness for the diagonal image.

opaque
  extend-lim-lim-with :
    ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
      x gx y gy
      (gz : T.IsCauchySequence
        (λ n → extend f f-cc (x n) (y n))) →
    extend f f-cc (S.lim x gx) (U.lim y gy) ≡
      T.lim
        (λ n → extend f f-cc (x n) (y n)) gz
  extend-lim-lim-with f f-cc x gx y gy gz =
    graphClosureUnique f f-cc
      (S.lim x gx) (U.lim y gy) _ _
      (extend-graph f f-cc
        (S.lim x gx) (U.lim y gy))
      (limitBothGraphClosure f x gx y gy _ gz
        (λ n → extend-graph f f-cc (x n) (y n)))

  extend-lim-lim :
    ∀ (f : M → N → T.Completion) (f-cc : PreservesCauchyGraphs f)
      x gx y gy →
    extend f f-cc (S.lim x gx) (U.lim y gy) ≡
      T.lim
        (λ n → extend f f-cc (x n) (y n))
        (extend-preservesDiagonalCauchy
          f f-cc x y gx gy)
  extend-lim-lim f f-cc x gx y gy =
    extend-lim-lim-with f f-cc x gx y gy
      (extend-preservesDiagonalCauchy
        f f-cc x y gx gy)


extendBase :
  (f : M → N → O) →
  PreservesBaseCauchyGraphs f →
  S.Completion → U.Completion → T.Completion
extendBase f =
  extend (λ p q → T.ι (f p q))

extendBase-ι-ι :
  ∀ (f : M → N → O) (f-cc : PreservesBaseCauchyGraphs f) p q →
  extendBase f f-cc (S.ι p) (U.ι q) ≡
    T.ι (f p q)
extendBase-ι-ι f f-cc p q = refl
