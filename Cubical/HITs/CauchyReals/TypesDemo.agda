module Cubical.HITs.CauchyReals.TypesDemo where

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
import Cubical.HITs.CauchyReals.Sequence as S
open import Cubical.HITs.CauchyReals.Sequence using (𝑒)
-- open import Cubical.HITs.CauchyReals.TrigBase

open ℚ using (_⁻¹₊)


open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.Aproximations

open import Cubical.Data.Rationals.Bisection

module NthRoot (pow : ℕ₊₁) (q : ℚ₊) where
 fQ : Σ ℕ₊₁ (λ k → fst q ℚ.< fromNat (ℕ₊₁→ℕ k))
 fQ = ℚ.ceilℚ₊ q
 n' = (ℤ.ℕ₊₁→ℤ (fst fQ))



 open ℚIncrFunBisect [ 1 / 2 ] [ n' / 1 ] (ℚ.pos<pos _)
   (λ x → x ℚ.^ⁿ ℕ₊₁→ℕ pow) (fst q)

 icsNthRoot : S.IsCauchySequence' (λ x → rat (bs x))
 icsNthRoot ε =
   let N , pp = isCauchySequenceSolve ε
   in N , λ m n <m <n → isTrans≡<ᵣ _ _ _
          (cong absᵣ ℚℝ! ∙ absᵣ-rat (bs n ℚ.- bs m) ) (<ℚ→<ᵣ _ _ (pp m n <m <n))

 nthRootℚ₊ : ℝ
 nthRootℚ₊ = S.fromCauchySequence' (rat ∘ bs) icsNthRoot




module _ where

 expℚclamped : ℚ → ℝ
 expℚclamped q = S.expℚ₊ (q , {!!})
 -- expℚ₊ (ℚ.min 3 (ℚ.max [ 1 / 2 ] q)
 --   , ℚ.isTrans<≤ _ _ _ (ℚ.pos<pos _)
 --    ((ℚ.≤MonotoneMin [ 1 / 2 ] 3 [ 1 / 2 ] (ℚ.max [ 1 / 2 ] q)
 --      (ℚ.pos≤pos _) (ℚ.≤max [ 1 / 2 ] q))))

 L : ℚ₊
 L = 4

 module _ (expLip : Lipschitz-ℚ→ℝ L expℚclamped)  where

  expℝ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ L)
  expℝ-L = fromLipschitz L (expℚclamped , expLip)

  


  opaque
   unfolding
     S.limₙ→∞[expSeqRatio]=0
             _·ᵣ_
             
             S.RatioTest₊.WW.pp S.RatioTest₊.WW.s'
             S.ratio→ℚseqLimit
             ·subtype-prf
     _+ᵣ_         
     S.expSeq-rat
     fromLipschitz
     _+ᵣ_ _·ᵣ_ -ᵣ_ NonExpanding₂.go
     sumR


   exp : ℝ → ℝ
   _√_ : ℕ₊₁ → ℚ₊ → ℝ 

   🧙 : (x : ℝ) → (ε : ℚ₊) →  x 🪄 ε
   🔮 : (x : ℝ) → (N : ℕ) →  x d🪄 N

   _ : ℚ
   _ = [
        pos 62686612385019757234899878002317785563136 ,
        (1+ 15190031440851110652620843730232934399999)
        ]

   _ : ℕ × ℕ
   _ = 4 , 126825716887744
   
   _ : ℚ
   _ = [
        pos
        379783877310996879811220087050570613122766106331579386914980138682491875162185339206471205247728437959433972577
        ,
        (1+
         25061193628387784968112059485831847030940915750188528423145915414552197988351999999999999999999999999999999999)
        ]












   exp = fst expℝ-L
   _√_ = NthRoot.nthRootℚ₊

   🧙 = getApproxVal
   🔮 = digitsℝ
