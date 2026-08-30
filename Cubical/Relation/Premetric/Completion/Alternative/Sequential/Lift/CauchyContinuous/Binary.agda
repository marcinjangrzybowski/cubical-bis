open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous.Binary
  {ℓM} {ℓM'} {ℓN} {ℓN'} {ℓO} {ℓO'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (O' : PremetricSpace ℓO ℓO') where

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

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition

module S = SequentialDefinition M'
module U = SequentialDefinition N'
module T = SequentialDefinition O'
module SP = SequentialPropertiesDefinition M'
module UP = SequentialPropertiesDefinition N'
module TP = SequentialPropertiesDefinition O'

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

JointlyApproximableFor :
  (M → N → T.ℭ̂ₛ) → S.ℭ̂ₛ → U.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
JointlyApproximableFor f x y z = ∀ α β γ →
  ∃[ p ∈ M ]
    Σ[ q ∈ N ]
      (S.ι p S.∼̂ₛ[ α ] x) ×
      (U.ι q U.∼̂ₛ[ β ] y) ×
      (f p q T.∼̂ₛ[ γ ] z)

isPropJointlyApproximableFor : ∀ f x y z →
  isProp (JointlyApproximableFor f x y z)
isPropJointlyApproximableFor f x y z =
  isPropΠ3 λ _ _ _ → squash₁


record IsCauchyContinuous (f : M → N → T.ℭ̂ₛ) : Type ℓₘ where
  no-eta-equality
  pattern
  constructor cauchyContinuous
  field
    presCauchyGraph :
      ∀ (x : ℕ → S.ℭ̂ₛ) (y : ℕ → U.ℭ̂ₛ) (z : ℕ → T.ℭ̂ₛ) →
      (∀ n → JointlyApproximableFor f (x n) (y n) (z n)) →
      S.SeqWitness x → U.SeqWitness y → T.SeqWitness z

open IsCauchyContinuous

isPropIsCauchyContinuous : ∀ f → isProp (IsCauchyContinuous f)
isPropIsCauchyContinuous f
  (cauchyContinuous preserve)
  (cauchyContinuous preserve') =
  cong cauchyContinuous
    ((isPropΠ λ _ → isPropΠ2 λ _ _ →
        isPropΠ λ _ → isPropΠ λ _ →
        isPropΠ λ _ → squash₁)
      preserve preserve')


BaseJointlyApproximableFor :
  (M → N → O) → S.ℭ̂ₛ → U.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
BaseJointlyApproximableFor f =
  JointlyApproximableFor (λ p q → T.ι (f p q))

IsCauchyContinuousBase : (M → N → O) → Type ℓₘ
IsCauchyContinuousBase f =
  IsCauchyContinuous (λ p q → T.ι (f p q))

isPropIsCauchyContinuousBase : ∀ f →
  isProp (IsCauchyContinuousBase f)
isPropIsCauchyContinuousBase f =
  isPropIsCauchyContinuous (λ p q → T.ι (f p q))


private
  constantSeqWitnessS : ∀ x → S.SeqWitness (λ _ → x)
  constantSeqWitnessS x =
    ∣ (λ _ → zero) ,
      (λ ε m n _ _ → S.isRefl∼̂ₛ x ε) ∣₁

  constantSeqWitnessU : ∀ y → U.SeqWitness (λ _ → y)
  constantSeqWitnessU y =
    ∣ (λ _ → zero) ,
      (λ ε m n _ _ → U.isRefl∼̂ₛ y ε) ∣₁

  alternate : T.ℭ̂ₛ → T.ℭ̂ₛ → ℕ → T.ℭ̂ₛ
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
  jointlyApproximable-equal : ∀ (f : M → N → T.ℭ̂ₛ) →
    IsCauchyContinuous f →
    ∀ x y z z' →
    JointlyApproximableFor f x y z →
    JointlyApproximableFor f x y z' →
    z ≡ z'
  jointlyApproximable-equal f f-cc x y z z' xyz xyz' =
    T.eqℭ z z' close
    where
    alternatingJoint : ∀ n →
      JointlyApproximableFor f x y (alternate z z' n)
    alternatingJoint zero = xyz
    alternatingJoint (suc zero) = xyz'
    alternatingJoint (suc (suc n)) = alternatingJoint n

    alternatingWitness : T.SeqWitness (alternate z z')
    alternatingWitness = f-cc .presCauchyGraph
      (λ _ → x) (λ _ → y) (alternate z z') alternatingJoint
      (constantSeqWitnessS x) (constantSeqWitnessU y)

    close : ∀ ε → z T.∼̂ₛ[ ε ] z'
    close ε = PT.rec (T.isProp∼ z ε z') withCauchy
      alternatingWitness
      where
      withCauchy : T.CauchySeq (alternate z z') → z T.∼̂ₛ[ ε ] z'
      withCauchy (K , zc) =
        subst2 (T._∼̂ₛ[ ε ]_)
          (alternate-even z z' (K ε))
          (alternate-odd z z' (K ε))
          (zc ε (ℕ.doubleℕ (K ε)) (suc (ℕ.doubleℕ (K ε)))
            (n≤double (K ε))
            (ℕ.≤-trans (n≤double (K ε)) ℕ.≤-sucℕ))


LiftFiber :
  (M → N → T.ℭ̂ₛ) → S.ℭ̂ₛ → U.ℭ̂ₛ → Type ℓₘ
LiftFiber f x y =
  Σ[ z ∈ T.ℭ̂ₛ ] JointlyApproximableFor f x y z

isPropLiftFiber : ∀ (f : M → N → T.ℭ̂ₛ) →
  IsCauchyContinuous f → ∀ x y → isProp (LiftFiber f x y)
isPropLiftFiber f f-cc x y (z , xyz) (z' , xyz') =
  Σ≡Prop (isPropJointlyApproximableFor f x y)
    (jointlyApproximable-equal f f-cc x y z z' xyz xyz')


private
  baseFiber : ∀ f p q → LiftFiber f (S.ι p) (U.ι q)
  baseFiber f p q .fst = f p q
  baseFiber f p q .snd α β γ =
    ∣ p , q
      , S.isRefl∼̂ₛ (S.ι p) α
      , U.isRefl∼̂ₛ (U.ι q) β
      , T.isRefl∼̂ₛ (f p q) γ ∣₁


opaque
  limitRightJointlyApproximable :
    ∀ f x y gy z gz →
    (∀ n → JointlyApproximableFor f x (y n) (z n)) →
    JointlyApproximableFor f x (U.lim y gy) (T.lim z gz)
  limitRightJointlyApproximable f x y gy z gz joint α β γ =
    PT.rec squash₁ withSource gy
    where
    withSource : U.CauchySeq y →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.∼̂ₛ[ α ] x) ×
          (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
          (f p q T.∼̂ₛ[ γ ] T.lim z gz)
    withSource (L , yc) = PT.rec squash₁ (withTarget L yc) gz
      where
      withTarget :
        (L : ℚ₊ → ℕ) →
        (∀ ε m n → L ε ℕ.≤ m → L ε ℕ.≤ n →
          y m U.∼̂ₛ[ ε ] y n) →
        T.CauchySeq z →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.∼̂ₛ[ α ] x) ×
            (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
            (f p q T.∼̂ₛ[ γ ] T.lim z gz)
      withTarget L yc (K , zc) =
        PT.map makeLateApproximation
          (joint n α (β /4₊) targetSmall)
        where
        targetRequired : ℚ₊
        targetRequired = (γ /4₊) /4₊

        targetSmall : ℚ₊
        targetSmall = targetRequired /4₊

        n : ℕ
        n = ℕ.max (L (β /4₊)) (K targetRequired)

        makeLateApproximation :
          (Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.∼̂ₛ[ α ] x) ×
              (U.ι q U.∼̂ₛ[ β /4₊ ] y n) ×
              (f p q T.∼̂ₛ[ targetSmall ] z n)) →
          Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.∼̂ₛ[ α ] x) ×
              (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
              (f p q T.∼̂ₛ[ γ ] T.lim z gz)
        makeLateApproximation (p , q , p-close , q-close , f-close) =
          p , q , p-close
          , UP.ι-close-lim-from-late q y gy L yc β n
              (ℕ.left-≤-max
                {m = L (β /4₊)} {n = K targetRequired}) q-close
          , TP.close-lim-from-late (f p q) z gz K zc γ n
              (ℕ.right-≤-max
                {n = K targetRequired} {m = L (β /4₊)}) f-close


  limitLeftJointlyApproximable :
    ∀ f x gx y z gz →
    (∀ n → JointlyApproximableFor f (x n) y (z n)) →
    JointlyApproximableFor f (S.lim x gx) y (T.lim z gz)
  limitLeftJointlyApproximable f x gx y z gz joint α β γ =
    PT.rec squash₁ withSource gx
    where
    withSource : S.CauchySeq x →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
          (U.ι q U.∼̂ₛ[ β ] y) ×
          (f p q T.∼̂ₛ[ γ ] T.lim z gz)
    withSource (K , xc) = PT.rec squash₁ (withTarget K xc) gz
      where
      withTarget :
        (K : ℚ₊ → ℕ) →
        (∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
          x m S.∼̂ₛ[ ε ] x n) →
        T.CauchySeq z →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
            (U.ι q U.∼̂ₛ[ β ] y) ×
            (f p q T.∼̂ₛ[ γ ] T.lim z gz)
      withTarget K xc (L , zc) =
        PT.map makeLateApproximation
          (joint n (α /4₊) β targetSmall)
        where
        targetRequired : ℚ₊
        targetRequired = (γ /4₊) /4₊

        targetSmall : ℚ₊
        targetSmall = targetRequired /4₊

        n : ℕ
        n = ℕ.max (K (α /4₊)) (L targetRequired)

        makeLateApproximation :
          (Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.∼̂ₛ[ α /4₊ ] x n) ×
              (U.ι q U.∼̂ₛ[ β ] y) ×
              (f p q T.∼̂ₛ[ targetSmall ] z n)) →
          Σ[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
              (U.ι q U.∼̂ₛ[ β ] y) ×
              (f p q T.∼̂ₛ[ γ ] T.lim z gz)
        makeLateApproximation (p , q , p-close , q-close , f-close) =
          p , q
          , SP.ι-close-lim-from-late p x gx K xc α n
              (ℕ.left-≤-max
                {m = K (α /4₊)} {n = L targetRequired}) p-close
          , q-close
          , TP.close-lim-from-late (f p q) z gz L zc γ n
              (ℕ.right-≤-max
                {n = L targetRequired} {m = K (α /4₊)}) f-close


  limitBothJointlyApproximable :
    ∀ f x gx y gy z gz →
    (∀ n → JointlyApproximableFor f (x n) (y n) (z n)) →
    JointlyApproximableFor f
      (S.lim x gx) (U.lim y gy) (T.lim z gz)
  limitBothJointlyApproximable f x gx y gy z gz joint α β γ =
    PT.rec squash₁ withLeft gx
    where
    withLeft : S.CauchySeq x →
      ∃[ p ∈ M ]
        Σ[ q ∈ N ]
          (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
          (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
          (f p q T.∼̂ₛ[ γ ] T.lim z gz)
    withLeft (K , xc) = PT.rec squash₁ (withRight K xc) gy
      where
      withRight :
        (K : ℚ₊ → ℕ) →
        (∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
          x m S.∼̂ₛ[ ε ] x n) →
        U.CauchySeq y →
        ∃[ p ∈ M ]
          Σ[ q ∈ N ]
            (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
            (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
            (f p q T.∼̂ₛ[ γ ] T.lim z gz)
      withRight K xc (L , yc) =
        PT.rec squash₁ (withTarget K xc L yc) gz
        where
        withTarget :
          (K : ℚ₊ → ℕ) →
          (∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
            x m S.∼̂ₛ[ ε ] x n) →
          (L : ℚ₊ → ℕ) →
          (∀ ε m n → L ε ℕ.≤ m → L ε ℕ.≤ n →
            y m U.∼̂ₛ[ ε ] y n) →
          T.CauchySeq z →
          ∃[ p ∈ M ]
            Σ[ q ∈ N ]
              (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
              (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
              (f p q T.∼̂ₛ[ γ ] T.lim z gz)
        withTarget K xc L yc (H , zc) =
          PT.map makeLateApproximation
            (joint n (α /4₊) (β /4₊) targetSmall)
          where
          targetRequired : ℚ₊
          targetRequired = (γ /4₊) /4₊

          targetSmall : ℚ₊
          targetSmall = targetRequired /4₊

          leftIndex rightIndex targetIndex : ℕ
          leftIndex = K (α /4₊)
          rightIndex = L (β /4₊)
          targetIndex = H targetRequired

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
                (S.ι p S.∼̂ₛ[ α /4₊ ] x n) ×
                (U.ι q U.∼̂ₛ[ β /4₊ ] y n) ×
                (f p q T.∼̂ₛ[ targetSmall ] z n)) →
            Σ[ p ∈ M ]
              Σ[ q ∈ N ]
                (S.ι p S.∼̂ₛ[ α ] S.lim x gx) ×
                (U.ι q U.∼̂ₛ[ β ] U.lim y gy) ×
                (f p q T.∼̂ₛ[ γ ] T.lim z gz)
          makeLateApproximation
              (p , q , p-close , q-close , f-close) =
            p , q
            , SP.ι-close-lim-from-late p x gx K xc α n
                leftLate p-close
            , UP.ι-close-lim-from-late q y gy L yc β n
                rightLate q-close
            , TP.close-lim-from-late (f p q) z gz H zc γ n
                targetLate f-close


private
  limitRightFiber : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) p
    (y : ℕ → U.ℭ̂ₛ) (gy : U.SeqWitness y) →
    (∀ n → LiftFiber f (S.ι p) (y n)) →
    LiftFiber f (S.ι p) (U.lim y gy)
  limitRightFiber f f-cc p y gy IH =
    T.lim z gz ,
    limitRightJointlyApproximable f (S.ι p) y gy z gz joint
    where
    z : ℕ → T.ℭ̂ₛ
    z n = IH n .fst

    joint : ∀ n → JointlyApproximableFor f (S.ι p) (y n) (z n)
    joint n = IH n .snd

    gz : T.SeqWitness z
    gz = f-cc .presCauchyGraph
      (λ _ → S.ι p) y z joint
      (constantSeqWitnessS (S.ι p)) gy


  rightFiberElimAtBase : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) p →
    U.Elimℭ̂ₛ-Prop (LiftFiber f (S.ι p))
  rightFiberElimAtBase f f-cc p .U.Elimℭ̂ₛ-Prop.ιA =
    baseFiber f p
  rightFiberElimAtBase f f-cc p .U.Elimℭ̂ₛ-Prop.limA =
    limitRightFiber f f-cc p
  rightFiberElimAtBase f f-cc p .U.Elimℭ̂ₛ-Prop.isPropA =
    isPropLiftFiber f f-cc (S.ι p)


  limitLeftFiber : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x) →
    (∀ n y → LiftFiber f (x n) y) →
    ∀ y → LiftFiber f (S.lim x gx) y
  limitLeftFiber f f-cc x gx IH y =
    T.lim z gz ,
    limitLeftJointlyApproximable f x gx y z gz joint
    where
    z : ℕ → T.ℭ̂ₛ
    z n = IH n y .fst

    joint : ∀ n → JointlyApproximableFor f (x n) y (z n)
    joint n = IH n y .snd

    gz : T.SeqWitness z
    gz = f-cc .presCauchyGraph
      x (λ _ → y) z joint gx (constantSeqWitnessU y)


  fiberElim : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) →
    S.Elimℭ̂ₛ-Prop (λ x → ∀ y → LiftFiber f x y)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.ιA p =
    U.Elimℭ̂ₛ-Prop.go (rightFiberElimAtBase f f-cc p)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.limA =
    limitLeftFiber f f-cc
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.isPropA x =
    isPropΠ (isPropLiftFiber f f-cc x)


liftFiber : ∀ (f : M → N → T.ℭ̂ₛ) →
  IsCauchyContinuous f → ∀ x y → LiftFiber f x y
liftFiber f f-cc = S.Elimℭ̂ₛ-Prop.go (fiberElim f f-cc)

liftCauchyContinuous :
  (f : M → N → T.ℭ̂ₛ) →
  IsCauchyContinuous f →
  S.ℭ̂ₛ → U.ℭ̂ₛ → T.ℭ̂ₛ
liftCauchyContinuous f f-cc x y = liftFiber f f-cc x y .fst

liftCauchyContinuous-joint :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) x y →
  JointlyApproximableFor f x y
    (liftCauchyContinuous f f-cc x y)
liftCauchyContinuous-joint f f-cc x y =
  liftFiber f f-cc x y .snd


liftCauchyContinuous-diagonalSeqWitness :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (y : ℕ → U.ℭ̂ₛ) →
  S.SeqWitness x → U.SeqWitness y →
  T.SeqWitness (λ n → liftCauchyContinuous f f-cc (x n) (y n))
liftCauchyContinuous-diagonalSeqWitness f f-cc x y gx gy =
  f-cc .presCauchyGraph x y
    (λ n → liftCauchyContinuous f f-cc (x n) (y n))
    (λ n → liftCauchyContinuous-joint f f-cc (x n) (y n))
    gx gy


-- All four constructor pairs have small computation rules.  The first
-- three, and the nested form of lim/lim, are judgmental consequences of the
-- construction; keeping these proofs as refl protects that computation.

liftCauchyContinuous-ι-ι :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) p q →
  liftCauchyContinuous f f-cc (S.ι p) (U.ι q) ≡ f p q
liftCauchyContinuous-ι-ι f f-cc p q = refl

liftCauchyContinuous-ι-lim :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    p y gy →
  liftCauchyContinuous f f-cc (S.ι p) (U.lim y gy) ≡
    T.lim (λ n → liftCauchyContinuous f f-cc (S.ι p) (y n)) _
liftCauchyContinuous-ι-lim f f-cc p y gy = refl

liftCauchyContinuous-lim-ι :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    x gx q →
  liftCauchyContinuous f f-cc (S.lim x gx) (U.ι q) ≡
    T.lim (λ n → liftCauchyContinuous f f-cc (x n) (U.ι q)) _
liftCauchyContinuous-lim-ι f f-cc x gx q = refl

liftCauchyContinuous-lim-lim-nested :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    x gx y gy →
  liftCauchyContinuous f f-cc (S.lim x gx) (U.lim y gy) ≡
    T.lim
      (λ n → liftCauchyContinuous f f-cc (x n) (U.lim y gy)) _
liftCauchyContinuous-lim-lim-nested f f-cc x gx y gy = refl


-- Unlike the nested rule, this synchronized rule is propositional: it says
-- that the two source sequences may advance together.  The `-with` form
-- accepts any independently obtained Cauchy witness for the diagonal image.

opaque
  liftCauchyContinuous-lim-lim-with :
    ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
      x gx y gy
      (gz : T.SeqWitness
        (λ n → liftCauchyContinuous f f-cc (x n) (y n))) →
    liftCauchyContinuous f f-cc (S.lim x gx) (U.lim y gy) ≡
      T.lim
        (λ n → liftCauchyContinuous f f-cc (x n) (y n)) gz
  liftCauchyContinuous-lim-lim-with f f-cc x gx y gy gz =
    jointlyApproximable-equal f f-cc
      (S.lim x gx) (U.lim y gy) _ _
      (liftCauchyContinuous-joint f f-cc
        (S.lim x gx) (U.lim y gy))
      (limitBothJointlyApproximable f x gx y gy _ gz
        (λ n → liftCauchyContinuous-joint f f-cc (x n) (y n)))

  liftCauchyContinuous-lim-lim :
    ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
      x gx y gy →
    liftCauchyContinuous f f-cc (S.lim x gx) (U.lim y gy) ≡
      T.lim
        (λ n → liftCauchyContinuous f f-cc (x n) (y n))
        (liftCauchyContinuous-diagonalSeqWitness
          f f-cc x y gx gy)
  liftCauchyContinuous-lim-lim f f-cc x gx y gy =
    liftCauchyContinuous-lim-lim-with f f-cc x gx y gy
      (liftCauchyContinuous-diagonalSeqWitness
        f f-cc x y gx gy)


liftCauchyContinuousBase :
  (f : M → N → O) →
  IsCauchyContinuousBase f →
  S.ℭ̂ₛ → U.ℭ̂ₛ → T.ℭ̂ₛ
liftCauchyContinuousBase f =
  liftCauchyContinuous (λ p q → T.ι (f p q))

liftCauchyContinuousBase-ι-ι :
  ∀ (f : M → N → O) (f-cc : IsCauchyContinuousBase f) p q →
  liftCauchyContinuousBase f f-cc (S.ι p) (U.ι q) ≡
    T.ι (f p q)
liftCauchyContinuousBase-ι-ι f f-cc p q = refl
