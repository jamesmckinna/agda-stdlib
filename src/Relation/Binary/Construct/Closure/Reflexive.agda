------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Closure.Reflexive where

open import Data.Unit.Base using (tt)
open import Level using (Level; _⊔_)
open import Function.Base using (_∋_)
open import Relation.Binary.Core using (Rel; _=[_]⇒_; _⇒_)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Construct.Constant.Core using (Const)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a
    R : Rel A ℓ
    x y : A

------------------------------------------------------------------------
-- Definition

data ReflClosure {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  refl : Reflexive (ReflClosure _∼_)
  [_]  : _∼_ ⇒ ReflClosure _∼_

------------------------------------------------------------------------
-- Operations

map : ∀ {R : Rel A ℓ₁} {S : Rel B ℓ₂} {f : A → B} →
      R =[ f ]⇒ S → ReflClosure R =[ f ]⇒ ReflClosure S
map R⇒S [ xRy ] = [ R⇒S xRy ]
map R⇒S refl    = refl

------------------------------------------------------------------------
-- Properties

-- The reflexive closure has no effect on reflexive relations.
drop-refl : Reflexive R → ReflClosure R ⇒ R
drop-refl rfl [ xRy ] = xRy
drop-refl rfl refl    = rfl

reflexive : _≡_ ⇒ ReflClosure R
reflexive refl = refl

[]-injective : ∀ {p q} → (ReflClosure R x y ∋ [ p ]) ≡ [ q ] → p ≡ q
[]-injective refl = refl

------------------------------------------------------------------------
-- Example usage

private
  module Maybe where
    Maybe : Set a → Set a
    Maybe A = ReflClosure (Const A) tt tt

    nothing : Maybe A
    nothing = refl

    just : A → Maybe A
    just = [_]



------------------------------------------------------------------------
-- Deprecations
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- v1.5

Refl = ReflClosure
{-# WARNING_ON_USAGE Refl
"Warning: Refl was deprecated in v1.5.
Please use ReflClosure instead."
#-}
