open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous.Synchronized
  {ℓM} {ℓM'} {ℓN} {ℓN'} {ℓO} {ℓO'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (O' : PremetricSpace ℓO ℓO') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous.Binary
  as BinaryDefinition

module S = SequentialDefinition M'
module U = SequentialDefinition N'
module T = SequentialDefinition O'
module B = BinaryDefinition M' N' O'

private
  M = M' .fst
  N = N' .fst
  O = O' .fst


-- The synchronized lift uses exactly the same intrinsic binary condition as
-- Binary.  Only its proposition-valued elimination program is different.

open B public using
  ( JointlyApproximableFor
  ; isPropJointlyApproximableFor
  ; IsCauchyContinuous
  ; cauchyContinuous
  ; isPropIsCauchyContinuous
  ; BaseJointlyApproximableFor
  ; IsCauchyContinuousBase
  ; isPropIsCauchyContinuousBase
  ; LiftFiber
  ; isPropLiftFiber
  )

open IsCauchyContinuous public


private
  constantSeqWitnessS : ∀ x → S.SeqWitness (λ _ → x)
  constantSeqWitnessS x =
    ∣ (λ _ → zero) ,
      (λ ε m n _ _ → S.isRefl∼̂ₛ x ε) ∣₁

  constantSeqWitnessU : ∀ y → U.SeqWitness (λ _ → y)
  constantSeqWitnessU y =
    ∣ (λ _ → zero) ,
      (λ ε m n _ _ → U.isRefl∼̂ₛ y ε) ∣₁


  baseFiber : ∀ f p q → LiftFiber f (S.ι p) (U.ι q)
  baseFiber f p q .fst = f p q
  baseFiber f p q .snd α β γ =
    ∣ p , q
      , S.isRefl∼̂ₛ (S.ι p) α
      , U.isRefl∼̂ₛ (U.ι q) β
      , T.isRefl∼̂ₛ (f p q) γ ∣₁


  limitRightFiber : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) p
    (y : ℕ → U.ℭ̂ₛ) (gy : U.SeqWitness y) →
    (∀ n → LiftFiber f (S.ι p) (y n)) →
    LiftFiber f (S.ι p) (U.lim y gy)
  limitRightFiber f f-cc p y gy IH =
    T.lim z gz ,
    B.limitRightJointlyApproximable f (S.ι p) y gy z gz joint
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


  limitLeftAtBase : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x)
    (IH : ∀ n y → LiftFiber f (x n) y) q →
    LiftFiber f (S.lim x gx) (U.ι q)
  limitLeftAtBase f f-cc x gx IH q =
    T.lim z gz ,
    B.limitLeftJointlyApproximable f x gx (U.ι q) z gz joint
    where
    z : ℕ → T.ℭ̂ₛ
    z n = IH n (U.ι q) .fst

    joint : ∀ n → JointlyApproximableFor f (x n) (U.ι q) (z n)
    joint n = IH n (U.ι q) .snd

    gz : T.SeqWitness z
    gz = f-cc .presCauchyGraph
      x (λ _ → U.ι q) z joint gx
      (constantSeqWitnessU (U.ι q))


  limitBothFiber : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x)
    (IH : ∀ n y → LiftFiber f (x n) y)
    (y : ℕ → U.ℭ̂ₛ) (gy : U.SeqWitness y) →
    (∀ n → LiftFiber f (S.lim x gx) (y n)) →
    LiftFiber f (S.lim x gx) (U.lim y gy)
  limitBothFiber f f-cc x gx IH y gy _ =
    T.lim z gz ,
    B.limitBothJointlyApproximable f x gx y gy z gz joint
    where
    -- Crucially, this is diagonal in the two source sequences.  The recursive
    -- results for (lim x , y n) are deliberately not used.
    z : ℕ → T.ℭ̂ₛ
    z n = IH n (y n) .fst

    joint : ∀ n → JointlyApproximableFor f (x n) (y n) (z n)
    joint n = IH n (y n) .snd

    gz : T.SeqWitness z
    gz = f-cc .presCauchyGraph x y z joint gx gy


  synchronizedLimitElim : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x)
    (IH : ∀ n y → LiftFiber f (x n) y) →
    U.Elimℭ̂ₛ-Prop (LiftFiber f (S.lim x gx))
  synchronizedLimitElim f f-cc x gx IH
    .U.Elimℭ̂ₛ-Prop.ιA =
      limitLeftAtBase f f-cc x gx IH
  synchronizedLimitElim f f-cc x gx IH
    .U.Elimℭ̂ₛ-Prop.limA =
      limitBothFiber f f-cc x gx IH
  synchronizedLimitElim f f-cc x gx IH
    .U.Elimℭ̂ₛ-Prop.isPropA =
      isPropLiftFiber f f-cc (S.lim x gx)


  fiberElim : ∀ (f : M → N → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) →
    S.Elimℭ̂ₛ-Prop (λ x → ∀ y → LiftFiber f x y)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.ιA p =
    U.Elimℭ̂ₛ-Prop.go (rightFiberElimAtBase f f-cc p)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.limA x gx IH =
    U.Elimℭ̂ₛ-Prop.go (synchronizedLimitElim f f-cc x gx IH)
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


-- Every pair of point constructors computes judgmentally.  In particular,
-- the lim/lim rule below is diagonal rather than nested.

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

liftCauchyContinuous-lim-lim :
  ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    x gx y gy →
  liftCauchyContinuous f f-cc (S.lim x gx) (U.lim y gy) ≡
    T.lim
      (λ n → liftCauchyContinuous f f-cc (x n) (y n)) _
liftCauchyContinuous-lim-lim f f-cc x gx y gy = refl


-- The change is computational, not extensional: uniqueness of the binary
-- graph fiber identifies this synchronized lift with Binary's nested lift.

opaque
  liftCauchyContinuous≡binary :
    ∀ (f : M → N → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) →
    liftCauchyContinuous f f-cc ≡ B.liftCauchyContinuous f f-cc
  liftCauchyContinuous≡binary f f-cc =
    funExt λ x → funExt λ y →
      B.jointlyApproximable-equal f f-cc x y _ _
        (liftCauchyContinuous-joint f f-cc x y)
        (B.liftCauchyContinuous-joint f f-cc x y)


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
