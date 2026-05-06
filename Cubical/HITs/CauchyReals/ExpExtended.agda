module Cubical.HITs.CauchyReals.ExpExtended where

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
open import Cubical.HITs.CauchyReals.Sequence -- hiding (expℝ) 


open ℚ using (_⁻¹₊)


open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Aproximations

module LipshitzProofIrrelTest (lipPrf : Lipschitz-ℚ→ℝ 10 (λ z → rat z)) where

 testL : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ 10)
 testL = fromLipschitz 10 ((λ z → rat z) , lipPrf )

 test-f : ℝ → ℝ
 test-f = fst testL


 opaque
  unfolding limₙ→∞[expSeqRatio]=0 _·ᵣ_ _+ᵣ_ -ᵣ_ NonExpanding₂.go /nᵣ denseℚinℝ
             RatioTest₊.WW.pp RatioTest₊.WW.s' ratio→ℚseqLimit
              ℚ.·0< ℚ.+0< invℝ-pos sumR sqᵣ ≤ℚ→≤ᵣ
              ·subtype-prf maxᵣ minᵣ 0<max 0<min maxR minR

     0<+Closed 0<·Closed clampᵣ-rat clamp-limΣ expSeq-rat
     fromLipschitz-rat
     -- sin cos

  testA : ℚ
  testA = getApproxVal (test-f 𝑒) [ 1 / 32 ]₊

  -- _ : ℚ
  -- _ = {!digits 10 testA!}
  
module _ where

 expℚclamped : ℚ → ℝ
 expℚclamped q = expℚ₊ (q , {!!})
 -- expℚ₊ (ℚ.min 3 (ℚ.max [ 1 / 2 ] q)
 --   , ℚ.isTrans<≤ _ _ _ (ℚ.pos<pos _)
 --    ((ℚ.≤MonotoneMin [ 1 / 2 ] 3 [ 1 / 2 ] (ℚ.max [ 1 / 2 ] q)
 --      (ℚ.pos≤pos _) (ℚ.≤max [ 1 / 2 ] q))))

 L : ℚ₊
 L = 4

 module _ (expLip : Lipschitz-ℚ→ℝ L expℚclamped)  where

  expℝ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ L)
  expℝ-L = fromLipschitz L (expℚclamped , expLip)

  expℝ = fst expℝ-L


  opaque
   unfolding
     limₙ→∞[expSeqRatio]=0
             _·ᵣ_
             
             RatioTest₊.WW.pp RatioTest₊.WW.s'
             ratio→ℚseqLimit
     _+ᵣ_         
     expSeq-rat
     fromLipschitz

   -- _ : ℝ
   -- _ = {!expℝ (expℝ 𝑒)!}

   -- eAprox' : ℚ
   -- eAprox' = ℚ.reduce (getApproxVal (expℝ (expℝ (𝑒 ·ᵣ (rat [ 1 / 2 ])) ·ᵣ (rat [ 1 / 13 ]))) [ 1 / 10 ]₊)

   -- eAprox : ℚ
   -- eAprox = ℚ.reduce (getApproxVal ((expℝ (𝑒 ·ᵣ (rat [ 1 / 2 ])) ·ᵣ (rat [ 1 / 13 ]))) [ 1 / 10 ]₊)


   eAprox : ℚ
   eAprox = ℚ.reduce (getApproxVal (expℝ 𝑒) [ 1 / 10000 ]₊)


   _ : ℚ
   _ = ?
   
   _ : ℕ × ℕ
   _ = 15 , 154

   -- _ : ℕ × ℕ
   -- _ = {!digits 10 eAprox!}

--    _ : ℚ
--    _ = {!eAprox!}

-- -- [ pos 6839547115541180993 , (1+ 450611114501953124) ]
