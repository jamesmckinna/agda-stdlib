------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Sets.Membership
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Product.Base as Product using (proj₁)
open import Function.Base using (_∘_)
open import Relation.Nullary.Negation.Core using (¬_)

open StrictTotalOrder strictTotalOrder renaming (Carrier to A)
open import Data.Tree.AVL.Sets strictTotalOrder
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder using (Any)

------------------------------------------------------------------------
-- ∈

infix 4 _∈_ _∉_

_∈_ : A → ⟨Set⟩ → Set _
x ∈ s = Any ((x ≈_) ∘ proj₁) s

_∉_ : A → ⟨Set⟩ → Set _
x ∉ s = ¬ x ∈ s
