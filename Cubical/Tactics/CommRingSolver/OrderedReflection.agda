module Cubical.Tactics.CommRingSolver.OrderedReflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
import Cubical.Data.FinData as Fin
open import Cubical.Data.List as L
open import Cubical.Data.Nat.Literals

open import Cubical.Data.Int as Slowℤ using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolver.AlgebraExpression

open import Cubical.Tactics.CommRingSolver.Solver.Core
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Cubical.Reflection.Sugar
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Utilities using (quoteDefsfNames;ω[];_ω∷_;_][_) public
open import Cubical.Tactics.Reflection.Goals

open import Cubical.Data.Int using (ℤ;pos;negsuc)
import Cubical.Data.Int.Fast as Fastℤ
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Algebra.CommRing.Instances.Int.Fast as Fastℤ'
import Cubical.Algebra.OrderedCommRing
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as OrderedRats
import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast as OrderedFastℤ

import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.OrderedSolver.Core
open import Cubical.Tactics.CommRingSolver.OrderedConfig

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
import Cubical.Tactics.CommRingSolver.Specialised.Rationals as Rat
import Cubical.Data.Rationals as Rat
import Cubical.Data.Rationals.Order as Rat
import Cubical.Data.Rationals.Inverse.Base as Rat

import Cubical.Data.Prod as Prod

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals


infix 55 _↘_

opaque
 _↘_ : ∀ {ℓ} {A B : Type ℓ} → A → B → A Prod.× B
 _↘_ = Prod._,_
 
showFailReason : FailReason →  List ErrorPart
showFailReason (tooWeak x) = [ strErr x ]
showFailReason (missingInfo x) =
  "missingInfo:\n\n" ∷ₑ L.join (L.map (λ {
     (noInfoMsg s) →  "no infoMsg: " ∷ₑ s ∷nl []
   ; (noVarInfo k) →   "no info about var: " ∷ₑ " varId:" ∷ₑ mkNiceVar k ∷nl []
    } ) x)
showFailReason (unableToUseAssumption x) =  "unableToUseAssumption: " ∷ₑ x

module _ (log : List ErrorPart → TC Unit) where
 module OrderedCommRingSolver (ocrs : OrderedCommRingSolverConfig) where

  open OrderedCommRingSolverConfig ocrs
  open CommRingSolver log commRingSolverConfig
  open CommRingReflection
  nicelyVars : Vars → List ErrorPart
  nicelyVars = L.join ∘
   L.map (λ (k , tm) →  "\n" ∷ₑ mkNiceVar k ∷ₑ " ∶ " ∷ₑ [ tm ]ₑ) ∘
    zipWithIndex



  IneqData = (Bool × (Term × Term))

  IneqProofData = ((Bool × (Term × Term)) × Term) × Term


  nicelyShowGoal : Vars -> IneqData → TC (List ErrorPart)
  nicelyShowGoal vars (rel , lhs' , rhs') = do
    lhs'' ← prettyExpr (length vars) lhs'
    rhs'' ← prettyExpr (length vars) rhs'

    pure ((" vars: " ∷nl (nicelyVars vars
                    ++nl "\nGOAL:" ∷nl (lhs'' ∷nl (if rel then "<" else "≤") ∷nl [ rhs'' ]ₑ))))



  private
   variableList : Vars → Arg Term
   variableList [] = varg (con (quote emptyVec) [])
   variableList (t ∷ ts)
     = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))

   ≲solverCallWithVars : ℕ → Vars → IneqData → Term → List IneqProofData  → Term → Term
   ≲solverCallWithVars n vars (rel , (lhs , rhs)) OCRSC asmptnsList varsIneqInfo =
     let ineq = def (quote SansReflectionOrdered.Decidable≲.mkInequality)
               (OCRSC v∷ (ℕAsTerm n) v∷ (con (if rel then quote true else quote false) []) v∷ lhs v∷ rhs
                v∷ (variableList vars) ∷ [])
         asmptnsT = toListTerm (L.map
            (λ (((rel , (lhs , rhs)) , prf) , mbElimVar) →
                def (quote SansReflectionOrdered.Decidable≲.mkInequalityProof)
               (OCRSC v∷ (ℕAsTerm n) v∷ (con (if rel then quote true else quote false) []) v∷ lhs v∷ rhs
                v∷ (variableList vars) ∷ prf v∷ mbElimVar v∷ []))
            asmptnsList)
     in def (quote SansReflectionOrdered.Decidable≲.solveInequality)
           (OCRSC v∷ (ℕAsTerm n) v∷ (variableList vars) ∷ ineq v∷ asmptnsT v∷ v[ varsIneqInfo ] )




  record GivenInequality : Type where
   constructor givenInequality
   field
    proofTerm : Term
    strict? : Bool
    lhs rhs : Term


  tryUseAsGivenInequality : Bool → Term → TC (Maybe GivenInequality)
  tryUseAsGivenInequality normaliseFlag tm = 
    map-Maybe (λ (b , lhs , rhs) → givenInequality tm b lhs rhs) <$>
      (inferType tm
        >>= (if normaliseFlag then normalise else pure)
        >>= mkMatchInequalityGoalTC)




  inferIneqsInCtx : TC (List GivenInequality)
  inferIneqsInCtx = do
    ctxLen ← length <$> getContext
    catMaybes <$> mapM (tryUseAsGivenInequality false)
      (L.map (λ k → var k []) (range ctxLen))

  inferIneqsByVars : Vars → TC (List GivenInequality)
  inferIneqsByVars vrs =
    catMaybes <$> mapM (λ tm → tryUseAsGivenInequality true (def (quote snd) v[ tm ]))
      (catMaybes (L.map tryPairFromFst vrs)) 


  macro
   ineqsInCtx : Term → TC Unit
   ineqsInCtx tm = do
     uu ←  (L.join ∘S  L.map (λ (givenInequality tmk rel lhs rhs) →
              (tmk ∷ₑ " : " ∷ₑ lhs ∷ₑ (if rel then "<" else "≤") ∷ₑ rhs  ∷ₑ [ "\n" ]ₑ )))
             <$> inferIneqsInCtx 
     typeError $ "ineqs in ctx: \n" ∷ₑ uu


  collectInfoFromCtx : Term → Vars → TC Term
  collectInfoFromCtx ocrsTerm vars = do
    ineqInfoType ← normalise $ def (quote SansReflectionOrdered.VarsIneqInfo)
           (ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ [ variableList vars ])
    noInfoIneqInfoTm ←
     (checkType (def (quote SansReflectionOrdered.varsIneqNoInfo)
           (ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ [ variableList vars ])) (ineqInfoType))
    infoFromTerms ← pure noInfoIneqInfoTm

    ictx ← _++_ <$> inferIneqsInCtx <*> inferIneqsByVars vars


    (foldlM cifcStep infoFromTerms ictx) -- >>= flip checkType (ineqInfoType))
    where

    cifcStep : Term → GivenInequality → TC Term
    cifcStep t iic = do
      just ((b , prfTm) , k) ← maybeVarIneqInfo iic
         where nothing → (pure t)
      bTm ← quoteTC b >>= normalise
      kTm ← quoteTC k >>= normalise
      pure $ def (quote SansReflectionOrdered.setVarsIneqInfo')
        ((ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ variableList vars ∷
           kTm v∷ bTm v∷ prfTm v∷ v[ t ]))
     where


     maybeVarIneqInfo : GivenInequality → TC (Maybe ((Bool × Term) × _)) 
     maybeVarIneqInfo iic = do
      is0 ← mbPureMatchZero IIC.lhs
      pure $ if is0 
       then ((IIC.strict? , IIC.proofTerm) ,_) <$> indexOfFin IIC.rhs vars
       else nothing
      where module IIC = GivenInequality iic

  quoteIneqType : Term → TC (Abstr IneqData)
  quoteIneqType goal = do
    be ← mkBuildExpr
    just (rel , lhs , rhs) ← mkMatchInequalityGoalTC goal
      where nothing → typeError $  "not an inequality : " ∷ₑ [ goal ]ₑ
    amapM₂ (λ x y →  rel , x , y) (be lhs) (be rhs)

  quoteIneqProof : Term → TC (Abstr IneqProofData)
  quoteIneqProof (def (quote _↘_) xs) = do
    just (prf , vh) ← pure (tryGetTwoVArgs xs)
     where nothing → typeError [ "imposible in quoteIneqProof" ]ₑ
    ty ← inferType prf >>= normalise
    amapM₂ (λ x y →  (x , prf) , y)
     (quoteIneqType ty) (pure (abstrVarId vh))
  quoteIneqProof prf = do
    ty ← inferType prf >>= normalise
    amap ((_, (con (quote nothing) [])) ∘ (_, prf)) <$> (quoteIneqType ty)



  <≤!-macro : Term → List Term → Bool → TC Unit
  <≤!-macro hole asmptionsTms justShow = withReduceDefs (false ,
        (quote SansReflectionOrdered.Decidable≲.x≲y-fromDec) ∷ doNotUnfold) do
    log [ "start" ]ₑ
    goal ← inferType hole >>= normalise
    log $ "goal:" ∷nl [ goal  ]ₑ
    log $ "assumptions:" ∷nl map␤ₑ asmptionsTms
    mapM ((inferType) >=> λ ty → log $ "asmpTy: " ∷ₑ [ ty ]ₑ   ) asmptionsTms
    log [ "reflecting.." ]ₑ
    ((goalIneqData , assmptionsIneqData) , vars) ← assignFst <$>
      ( amapM₂ _,_ (quoteIneqType goal)
         (aForM asmptionsTms quoteIneqProof))
    log [ "reflected!" ]ₑ
    ocrsTerm ← quoteωTC ocrs
    nsg' ← nicelyShowGoal vars goalIneqData
    log ([ "collecting info from ctx.." ]ₑ ++nl nsg')
    ineqInfoTm ← collectInfoFromCtx ocrsTerm vars
    log [ "collected info from ctx!" ]ₑ
    if justShow then ((([_] ∘S strErr)
           <$> (formatErrorParts [ termErr ineqInfoTm ])) >>= typeError ) else (pure tt)
    nothing ← (
      unifyRight hole (≲solverCallWithVars (length vars) vars goalIneqData ocrsTerm
          assmptionsIneqData ineqInfoTm))
       <|> (do
            nrmSol ← normalise (≲solverCallWithVars
                  (length vars) vars goalIneqData ocrsTerm
                       assmptionsIneqData ineqInfoTm)
            (typeError ("failedToUnquoteSum :" ∷nl [ nrmSol ]ₑ)))
      where just failReasonStr → do

               nsg ← nicelyShowGoal vars goalIneqData
               asmptnsNice ← concatMapM ((_<$>_ (" \n\n  " ∷ₑ_))
                ∘ nicelyShowGoal vars ∘ fst ∘ fst) assmptionsIneqData
               typeError (([ "failWithReason: " ] ++ₑ (showFailReason failReasonStr) ) ++nl nsg ++nl
                 asmptnsNice)
    log [ "done" ]ₑ
    pure _
  macro
   <≤! : Term → TC Unit
   <≤! hole = <≤!-macro hole [] false

   prev-<≤! : Term → TC Unit
   prev-<≤! hole = <≤!-macro hole [] true



   <≤![_] : Term → Term → TC Unit
   <≤![_] assumptions hole = <≤!-macro hole (prodToTermList assumptions) false


 module WithOrdering {rℓ rℓ`} (crsc : CommRingSolverConfig) where
  open CommRingSolverConfig crsc
  module _  (ordering : RingOrdering rℓ R)
            (ordering` : RingOrdering rℓ` R`) where
   OR = Iso.inv IsoΣRingOrdering (R , ordering) 
   OR` = Iso.inv IsoΣRingOrdering (R` , ordering`)

   module ORS = OrderedCommRingStr (snd OR)
   module ORS` = OrderedCommRingStr (snd OR`)

   module _
            (scalar`≤ : _)
            (scalar`< : _) (scalar`<-refl : _) (dec< : _) (dec≤ : _) (≡<>??  : _)
            (mbInv : _) (mbPureMatch0 : _) (nm< nm≤ : Name) where

    matchIneqTy : (Name × List (Arg Term)) → Maybe (Bool × (Term × Term))
    matchIneqTy (nm , args) =
      _,_ <$>
        (if (nm == nm<) then just true
       else if (nm == nm≤) then just false
        else nothing)
          <*> tryGetTwoVArgs args
    open OrderedCommRingSolverConfig
    ocrsc : OrderedCommRingSolverConfig
    ocrsc .commRingSolverConfig =
     record crsc { doNotUnfold = nm< ∷ nm≤ ∷ crsc .doNotUnfold }
    ocrsc .oℓ = _
    ocrsc .oℓ` = _
    ocrsc ._<_ = _
    ocrsc .OrderedCommRingSolverConfig._≤_ = _
    ocrsc ._<?_ = dec<
    ocrsc ._≤?_ = dec≤
    ocrsc .≡<>? = ≡<>??
    ocrsc .iocr = ORS.isOrderedCommRing
    ocrsc ._<`_ = _
    ocrsc ._≤`_ = _
    ocrsc .iocr` = ORS`.isOrderedCommRing
    ocrsc .pres< = scalar`< 
    ocrsc .pres≤ = scalar`≤
    ocrsc .reflect< = scalar`<-refl
    ocrsc .mbInverses = mbInv
    ocrsc .mbPureMatchZero = mbPureMatch0
    ocrsc .mkMatchInequalityGoalTC tm =
      pure (tryGetName tm >>= matchIneqTy)
 module OrderedSolverRationals where

   open OrderedCommRingStr (snd ℚOrderedCommRing)
   open OrderedCommRingReasoning ℚOrderedCommRing
   open OrderedCommRingTheory ℚOrderedCommRing

   0ℚraw : Rat.ℚ
   0ℚraw = Rat.[ pos ℕ.zero , (1+ ℕ.zero) ]

   0ℚ-term = q[ 0ℚraw ]

   0ℚtrmTest : Term → Bool
   0ℚtrmTest (con (quote SetQuotient.[_])
      (_ ∷ _ ∷ _ ∷ _ ∷
       v[ con (quote _,_) (_ ∷ _ ∷ _ ∷ _ ∷ con _ v[ lit (nat ℕ.zero) ]
            v∷ v[ con (quote 1+_) v[ lit (nat ℕ.zero) ] ]) ]))  =
          true
   0ℚtrmTest _ = false

   0ℚtrmTestTC : Term → TC Bool
   0ℚtrmTestTC tm = do
     just tm' ← Rat.mbConcreteℚ tm
      where nothing →
              pure false
     pure (0ℚtrmTest tm')

   0ℚtrmTestTC2 : Term → TC Bool
   0ℚtrmTestTC2 tm = 
     ((unify
        0ℚ-term tm) >> 
        pure true) <|> pure false



   ocrsc = WithOrdering.ocrsc Rat.config (_ ,
    snd (OrderedRats.ℚOrderedCommRing) .OrderedCommRingStr.isOrderedCommRing)
     ((_ ,
    snd (OrderedRats.ℚOrderedCommRing) .OrderedCommRingStr.isOrderedCommRing))
    (λ _ _ z → z) (λ _ _ z → z) (λ _ _ z → z)
    Rat.<Dec Rat.≤Dec Rat.≡⊎# (just (curry Rat.Σinverseℚ₊))
      0ℚtrmTestTC (quote Rat._<_) (quote Rat._≤_)

   open OrderedCommRingSolver ocrsc public


 module OrderedSolverInt where

  ≡⊎#ℤ : ∀ x y → (x ≡ y) ⊎ ((x ℤ.< y) ⊎ (y ℤ.< x))
  ≡⊎#ℤ x y with (x ℤ.≟ y)
  ... | ℤ.lt x₁ = inr (inl x₁)
  ... | ℤ.eq x₁ = inl x₁
  ... | ℤ.gt x₁ = inr (inr x₁)

  is0TC? : Term → TC Bool
  is0TC? (con (quote pos) v[ lit (nat ℕ.zero) ]) = pure true
  is0TC? _ = pure false

  ocrscℤ = WithOrdering.ocrsc (FastℤRingSolver.config log)
   (snd (Iso.fun IsoΣRingOrdering OrderedFastℤ.ℤOrderedCommRing)) (snd (Iso.fun IsoΣRingOrdering
    OrderedFastℤ.ℤOrderedCommRing))
   (λ _ _ z → z) (λ _ _ z → z) (λ _ _ z → z)
    ℤ._<?_ ℤ._≤?_ ≡⊎#ℤ nothing
   is0TC?
   (quote ℤ._<_) (quote ℤ._≤_) 

  open OrderedCommRingSolver ocrscℤ public

open OrderedSolverRationals (debugPrint "ℚ commRingSolver" 100) using ()
 renaming (prev-<≤! to prev-<≤ℚ! ; <≤! to <≤ℚ! ; <≤![_] to <≤ℚ![_] ; ineqsInCtx to ineqsInCtxℚ) public

open OrderedSolverRationals (debugPrint "ℚ commRingSolver" 0) using ()
 renaming (prev-<≤! to dbg-prev-<≤ℚ! ; <≤! to dbg-<≤ℚ! ; <≤![_] to dbg-<≤ℚ![_] ; ineqsInCtx to dbg-ineqsInCtxℚ) public


open OrderedSolverInt (debugPrint "ℤ commRingSolver" 100) using ()
 renaming (prev-<≤! to prev-<≤ℤ! ; <≤! to <≤ℤ! ; <≤![_] to <≤ℤ![_] ; ineqsInCtx to ineqsInCtxℤ) public
