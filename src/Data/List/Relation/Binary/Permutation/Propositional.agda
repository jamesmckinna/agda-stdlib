------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Equality.Propositional using (_≋_; ≋⇒≡)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; setoid)

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Reasoning.Syntax

import Data.List.Relation.Binary.Permutation.Setoid as Permutation

{-
------------------------------------------------------------------------
-- An inductive definition of permutation

-- Note that one would expect that this would be defined in terms of
-- `Permutation.Setoid`. This is not currently the case as it involves
-- adding in a bunch of trivial `_≡_` proofs to the constructors which
-- a) adds noise and b) prevents easy access to the variables `x`, `y`.
-- This may be changed in future when a better solution is found.

infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : ∀ {xs}        → xs ↭ xs
  prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs
-}
------------------------------------------------------------------------
-- Definition of permutation

private
  module ↭ = Permutation (setoid A)

-- Note that this is now defined in terms of `Permutation.Setoid` (#2317)

open ↭ public
  hiding ( prep; swap; ↭-refl; ↭-reflexive; ↭-pointwise
         ; ↭-isEquivalence; module PermutationReasoning; ↭-setoid
         )

pattern prep {xs} {ys} x xs↭ys = ↭.prep {xs} {ys} {x} {y = _} ≡.refl xs↭ys
pattern swap {xs} {ys} x y xs↭ys = ↭.swap {x = x} {y = y} {xs} {ys} ≡.refl ≡.refl xs↭ys

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-refl : Reflexive _↭_
↭-refl {[]} = []
↭-refl {_ ∷ _} = prep _ ↭-refl

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive ≡.refl = ↭-refl

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise xs≋ys with ≡.refl ← ≋⇒≡ xs≋ys = ↭-refl

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = ↭-refl
  ; sym   = ↭-sym
  ; trans = ↭-trans
  }

↭-setoid : Setoid _ _
↭-setoid = record
  { isEquivalence = ↭-isEquivalence
  }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning.

module PermutationReasoning where

  private module Base = ≈-Reasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public

  -- Some extra combinators that allow us to skip certain elements

  infixr 2 step-swap step-prep

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = ↭-go (↭-prep x xs↭ys) rel

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = ↭-go (↭-swap x y xs↭ys) rel

  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z

