module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Total where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Negation
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Subtraction


hasComplexDerivativeAt-add :
  ∀ {f derivativeF g derivativeG z} →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG z →
  HasComplexDerivativeAt
    (addComplexFunctions f g) (derivativeF +ℂ derivativeG) z
hasComplexDerivativeAt-add
  {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt wholeℂ g derivativeG z
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = z}
        derivativeGAt

    sumDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (addComplexFunctions f g) (derivativeF +ℂ derivativeG) z
    sumDerivativeWithin =
      hasComplexDerivativeWithinAt-add
        {P = wholeℂ} {f = f} {derivativeF = derivativeF}
        {g = g} {derivativeG = derivativeG} {z = z}
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = addComplexFunctions f g}
    {derivative = derivativeF +ℂ derivativeG} {z = z}
    sumDerivativeWithin


hasComplexDerivativeAt-neg :
  ∀ {f derivative z} →
  HasComplexDerivativeAt f derivative z →
  HasComplexDerivativeAt
    (negateComplexFunction f) (-ℂ derivative) z
hasComplexDerivativeAt-neg {f} {derivative} {z} derivativeAt =
  let
    derivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivative z
    derivativeWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivative} {z = z}
        derivativeAt

    negDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (negateComplexFunction f) (-ℂ derivative) z
    negDerivativeWithin =
      hasComplexDerivativeWithinAt-neg
        {P = wholeℂ} {f = f} {derivative = derivative} {z = z}
        derivativeWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = negateComplexFunction f}
    {derivative = -ℂ derivative} {z = z}
    negDerivativeWithin


hasComplexDerivativeAt-sub :
  ∀ {f derivativeF g derivativeG z} →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG z →
  HasComplexDerivativeAt
    (subtractComplexFunctions f g)
    (derivativeF +ℂ (-ℂ derivativeG)) z
hasComplexDerivativeAt-sub
  {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt wholeℂ g derivativeG z
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = z}
        derivativeGAt

    subDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (subtractComplexFunctions f g)
        (derivativeF +ℂ (-ℂ derivativeG)) z
    subDerivativeWithin =
      hasComplexDerivativeWithinAt-sub
        {P = wholeℂ} {f = f} {derivativeF = derivativeF}
        {g = g} {derivativeG = derivativeG} {z = z}
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = subtractComplexFunctions f g}
    {derivative = derivativeF +ℂ (-ℂ derivativeG)} {z = z}
    subDerivativeWithin


complexDifferentiableAt-add :
  ∀ {f g z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt g z →
  ComplexDifferentiableAt (addComplexFunctions f g) z
complexDifferentiableAt-add
  {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ fst differentiableG ,
  hasComplexDerivativeAt-add
    {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


complexDifferentiableAt-neg :
  ∀ {f z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt (negateComplexFunction f) z
complexDifferentiableAt-neg {f} {z} differentiable =
  -ℂ fst differentiable ,
  hasComplexDerivativeAt-neg
    {f = f} {derivative = fst differentiable} {z = z}
    (snd differentiable)


complexDifferentiableAt-sub :
  ∀ {f g z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt g z →
  ComplexDifferentiableAt (subtractComplexFunctions f g) z
complexDifferentiableAt-sub
  {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ (-ℂ fst differentiableG) ,
  hasComplexDerivativeAt-sub
    {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


holomorphic-add :
  ∀ {f g} →
  Holomorphic f → Holomorphic g →
  Holomorphic (addComplexFunctions f g)
holomorphic-add {f} {g} holomorphicF holomorphicG z =
  complexDifferentiableAt-add
    {f = f} {g = g} {z = z}
    (holomorphicF z) (holomorphicG z)


holomorphic-neg :
  ∀ {f} → Holomorphic f → Holomorphic (negateComplexFunction f)
holomorphic-neg {f} holomorphic z =
  complexDifferentiableAt-neg
    {f = f} {z = z} (holomorphic z)


holomorphic-sub :
  ∀ {f g} →
  Holomorphic f → Holomorphic g →
  Holomorphic (subtractComplexFunctions f g)
holomorphic-sub {f} {g} holomorphicF holomorphicG z =
  complexDifferentiableAt-sub
    {f = f} {g = g} {z = z}
    (holomorphicF z) (holomorphicG z)
