module Cubical.HITs.CauchyReals.AproxDemo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
import Cubical.Data.Fin as F
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Instances.Int.Fast
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Algebra.Ring.BigOps
import Cubical.Data.FinData as FD

open import Cubical.HITs.PropositionalTruncation.MagicTrick
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.HITs.CauchyReals.RationalsImports 
open import Cubical.HITs.CauchyReals.Sequence 
-- open import Cubical.HITs.CauchyReals.TrigBase

open ℚ using (_⁻¹₊)


open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.Aproximations

open import Cubical.Data.Rationals.Bisection


module Sqrt2 where
 open ℚIncrFunBisect 1 2 ℚ.decℚ<? (λ x → x ℚ.· x) 2
 
 -- opaque
 icsSqrt2 : IsCauchySequence' (λ x → rat (bs x))
 icsSqrt2 ε =
   let N , pp = isCauchySequenceSolve ε
   in N , λ m n <m <n → isTrans≡<ᵣ _ _ _
          (cong absᵣ ℚℝ! ∙ absᵣ-rat (bs n ℚ.- bs m) ) (<ℚ→<ᵣ _ _ (pp m n <m <n))
 
 sqrt2 : ℝ
 sqrt2 = fromCauchySequence' (rat ∘ bs) icsSqrt2

 
 module _ where
  opaque
   unfolding _+ᵣ_ _·ᵣ_ -ᵣ_ NonExpanding₂.go
   
   sqrt2-val : ℚ
   sqrt2-val = getApproxVal (sqrt2 ·ᵣ (rat 3)) [ 1 / 255 ]₊

   sqrt2-val' : Bool × ℚ
   sqrt2-val' = getApproxVal⊎ (sqrt2 ·ᵣ (rat 3)) [ 1 / 255 ]₊

module NthRoot (pow : ℕ₊₁) (q : ℚ₊) where
 fQ : Σ ℕ₊₁ (λ k → fst q ℚ.< fromNat (ℕ₊₁→ℕ k))
 fQ = ℚ.ceilℚ₊ q
 n' = (ℤ.ℕ₊₁→ℤ (fst fQ))



 open ℚIncrFunBisect [ 1 / 2 ] [ n' / 1 ] (ℚ.pos<pos _)
   (λ x → x ℚ.^ⁿ ℕ₊₁→ℕ pow) (fst q)

 icsNthRoot : IsCauchySequence' (λ x → rat (bs x))
 icsNthRoot ε =
   let N , pp = isCauchySequenceSolve ε
   in N , λ m n <m <n → isTrans≡<ᵣ _ _ _
          (cong absᵣ ℚℝ! ∙ absᵣ-rat (bs n ℚ.- bs m) ) (<ℚ→<ᵣ _ _ (pp m n <m <n))

 nthRootℚ₊ : ℝ
 nthRootℚ₊ = fromCauchySequence' (rat ∘ bs) icsNthRoot

 

 val : _
 val = getApproxVal nthRootℚ₊ 


fromConstSeq : ℝ
fromConstSeq =
 fromCauchySequence'₁ (λ _ → 0) ∣ (λ ε → 0 , λ _ _ _ _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (-ᵣ-rat₂ 0 0 ) ∙ absᵣ-rat 0) (<ℚ→<ᵣ _ _ (snd ε))) ∣₁


module _ where
 open NthRoot
 
 realNum : ℝ
 realNum = nthRootℚ₊ 7 13

 realNum' : ℝ
 realNum' = nthRootℚ₊ 3 11

 _ : ℕ × ℕ
 _ = digitsℝ realNum' 50


 -- c1 : ℤ.ℤ × ℕ
 -- c1 = map-snd ℕ₊₁→ℕ (fst (ℚ.reduced (val 5 31 [ 1 / 1000000000 ]₊)))
 opaque
  unfolding _·ᵣ_ _+ᵣ_ -ᵣ_ NonExpanding₂.go
  
  ratAprox : ℚ
  ratAprox = getApproxVal (realNum ·ᵣ realNum') [ 1 / 1000 ]₊ 

  _ : ℚ
  _ = {!!}


-- digits : ℕ → ℚ → ℕ × ℕ
-- digits N q =
--  let ((n , m) , _ , u) = ℚ.reduced q
--      n' = ℤ.abs n ℕ.· (10 ℕ.^ N)
--      zz = ℕ.quotient n' / ℕ₊₁→ℕ m
--  in zz , 0 

-- ℯDigits : (iterations : ℕ) → (digits : ℕ) → ℕ × ℕ
-- ℯDigits n d =
--   let
--     frac = SeqℯFrac n ; num = ℤ.abs (fst frac) ; den = ℕ₊₁→ℕ (snd frac)
--     integerPart    = quotient' num / den
--     fractionalPart = quotient' (10 ^ d) ·ℕ (num ℕ.∸ (den ·ℕ integerPart)) / den
--   in
--     integerPart , fractionalPart

module Aprox-𝓮 where
 opaque
  unfolding limₙ→∞[expSeqRatio]=0
            -- _·ᵣ_
            -- _+ᵣ_
            -- -ᵣ_
            -- NonExpanding₂.go
            -- /nᵣ
            -- denseℚinℝ
            -- RatioTest₊.WW.pp
            -- RatioTest₊.WW.s'
            ratio→ℚseqLimit
             -- ℚ.·0< ℚ.+0< invℝ-pos sumR sqᵣ ≤ℚ→≤ᵣ
             -- ·subtype-prf maxᵣ minᵣ 0<max 0<min maxR minR
             
    -- 0<+Closed
    -- 0<·Closed
    -- clampᵣ-rat
    -- clamp-limΣ
    expSeq-rat
    fromLipschitz
    -- sin cos
    -- IsoIsUConvSeries'IsCauchy'SequenceSum ∃rationalApprox ∃rationalApprox≤ ≤ᵣ-refl
    -- <ᵣ-+o <ᵣ-+o-pre <ᵣWeaken≤ᵣ isTrans≤<ᵣ isTrans≤ᵣ +ᵣComm +ᵣAssoc +ᵣ-rat

 
  -- ttt : ℚ₊
  -- ttt = (([ pos (suc (1 .ℕ₊₁.n)) , 2 ] ,
  --                        ℚ.inj {!(pos (0 ℕ.· ℕ₊₁→ℕ 2) ℤ.< pos (suc (1 .ℕ₊₁.n) ℕ.· ℕ₊₁→ℕ 1))!})
  --                       ·₊ 100
  --                       ·₊ ([ 1 / 2 ] , 1/2∈ℚ.0<1/2))


  -- zzz : ℝ
  -- zzz = rat [ pos 1 , (1+ 3628799) ]

  -- zzzz : ℝ
  -- zzzz = {!zzz!}
  -- _ : ℝ
  -- _ = {!(sin 0)!}

--   sinAprox : ℚ
--   sinAprox = {!ℚ.reduce ((getApproxVal (sin 0) 1)) !}


--   _ : ℚ
--   _ = [ pos 9864101 , (1+ 3628799) ]

--   _ : ℚ
--   _ = [ pos 13563139 , (1+ 4989599) ]


--   -- module _ where
--   --  open WithConvexParam [ 1 / 2 ]₊ [ 1 / 2 ]₊ (eq/ _ _ refl)

  _ : ℚ
  _ = [ pos 109601 , (1+ 40319) ]




  eAprox : ℚ
  eAprox = ℚ.reduce (getApproxVal (expℚ₊ [ 12 / 13 ]₊) [ 1 / 100 ]₊) 

  -- _ : ℕ
  -- _ = {!!}
  -- e-dgts : _ 
  -- e-dgts = {!!}

-- -- --   _ : ℕ
-- -- --   _ = 7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274
  
-- -- --   -- zz : ℕ × ℕ
-- -- --   -- zz = 2 , 71828182845904523536

-- -- --   -- _ : ℕ × ℕ
-- -- --   -- _ = {!zz!}



-- -- -- 2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274

  𝑒Aprox : ℕ × ℕ
  𝑒Aprox = {!digitsℝ (expℚ₊ [ 13 / 12 ]₊) 20!}

-- -- -- -- -- --   _ : ℚ
-- -- -- -- -- --   _ = {!𝑒Aprox!}

-- -- -- -- -- -- --   -- 𝑒N : ∃-syntax ℚ (λ m → rat m ∼[ 10 ] 𝑒)
-- -- -- -- -- -- --   -- 𝑒N = {!∃approx 𝑒 10!}


-- -- -- -- -- -- --   -- 𝑒N : ℝ
-- -- -- -- -- -- --   -- 𝑒N = {!𝑒!}


