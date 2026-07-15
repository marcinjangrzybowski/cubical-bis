module Cubical.Tactics.CommRingSolver.Specialised.Reals where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Reflection.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Maybe
open import Cubical.Data.NatPlusOne as NatPlusOne
open import Cubical.Data.List
open import Cubical.Data.Int.Fast using (_ℕ-_)
import Cubical.Data.Int.Fast as ℤ
import Cubical.Data.Int.Fast.Order as ℤ

import Cubical.HITs.SetQuotients as SetQuotient

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Sugar

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.Solver.Core
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.GenericCommRing

open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication



open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting


open import Cubical.Algebra.CommRing

open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Data.Rationals as ℚ

import Cubical.Tactics.CommRingSolver.Specialised.Rationals as Sℚ

rat-CommRingHom : IsCommRingHom (ℚCommRing .snd) rat (ℝcommRing .snd)
rat-CommRingHom .IsCommRingHom.pres0 = refl
rat-CommRingHom .IsCommRingHom.pres1 = refl
rat-CommRingHom .IsCommRingHom.pres+ x y = sym (+ᵣ-rat x y)
rat-CommRingHom .IsCommRingHom.pres· = rat·ᵣrat
rat-CommRingHom .IsCommRingHom.pres- = sym ∘ -ᵣ-rat

module Simpleℝ where


 isConstℕ? : Term → Bool
 isConstℕ? (con _ []) = true
 isConstℕ? (lit _) = true
 isConstℕ? (con _ v[ x ]) = isConstℕ? x
 isConstℕ? _ = false

 isConstℤ? : Term → Bool
 isConstℤ? (con _ v[ n ]) = isConstℕ? n
 isConstℤ? _ = false



 isScalarℚ? : List (Arg Term) → Bool
 isScalarℚ? (_ h∷ xs) = isScalarℚ? xs
 isScalarℚ? v[ con (quote _,_) xs ] = isScalarℚ? xs
 isScalarℚ?
  (p v∷ v[ con (quote NatPlusOne.1+_) v[ q ] ]) = isConstℤ? p and isConstℕ? q
 isScalarℚ? _ = false




 ℝ-matcher : RingReflectionMatcher
 ℝ-matcher .RingReflectionMatcher.mkMatchTermTC _ _ =  pure matchTerm

   where

   module _ (be : (Term → TC (Template × Vars))) where
    open BE q[ ℚCommRing ] be

    

    matchTerm : Term → TC (Maybe (Template × Vars))
    matchTerm t@(def (quote -ᵣ_) xs) = just <$> `-_` xs    
    matchTerm t@(def (quote _+ᵣ_) xs) = just <$> `_+_` xs
    matchTerm t@(def (quote _·ᵣ_) xs) = just <$> `_·_` xs
    matchTerm  (con (quote rat) v[ t@(con (quote SetQuotient.[_]) x) ]) =
      
       (if isScalarℚ? x then (returnTC (just ((λ _ → con (quote K) v[ t ]) , [])))
        else (returnTC nothing))
        
    matchTerm t@(con (quote rat) _) = pure nothing
    matchTerm t@(con (quote lim) _) = pure nothing
    matchTerm t@(def _ _) = pure nothing
    matchTerm t@(meta _ _) = pure nothing
    matchTerm t@(var _ _) = pure nothing
    matchTerm t = typeError ("unexpectedTerm in ℝ-matcher:" ∷nl [ t ]ₑ)



 config : CommRingSolverConfig
 config .CommRingSolverConfig.ℓ = _
 config .CommRingSolverConfig.ℓ` = _
 config .CommRingSolverConfig.R = ℚCommRing
 config .CommRingSolverConfig.commAlg = ℝcommRing , rat , rat-CommRingHom
 config .CommRingSolverConfig.mbDiscreteScalars = just ℚ.discreteℚ
 config .CommRingSolverConfig.mbNeg?Scalar = just Sℚ.mbNegℚ
 config .CommRingSolverConfig.mbCommonDenom = nothing
 config .CommRingSolverConfig.mb·`lCancel = nothing
 config .CommRingSolverConfig.mbNotZeroRing =
   just (ℚCommRingIsNotZeroRing ∘ inj-rat _ _)
 config .CommRingSolverConfig.mb≢0r→≢0r` =
   just λ q → _∘ inj-rat q 0
 config .CommRingSolverConfig.ringReflectionMatcher = ℝ-matcher
 config .CommRingSolverConfig.doNotUnfold = []
 config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
 config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)

 open CommRingSolver (debugPrint "commRingSolver" 100) config  hiding (solve!-lemma-macro) public

open Simpleℝ using () renaming (solve! to ℝ!) public
