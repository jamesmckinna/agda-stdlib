------------------------------------------------------------------------
-- The Agda standard library
--
-- Reverse view
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Reverse where

open import Data.List.Base as L using (List; []; _∷_; _∷ʳ_)
open import Data.List.Properties
  using (unfold-reverse; reverse-involutive)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality.Core
  using (subst; sym)

-- If you want to traverse a list from the end, then you can use the
-- reverse view of it.

infixl 5 _∶_∶ʳ_

data Reverse {a} {A : Set a} : List A → Set a where
  []     : Reverse []
  _∶_∶ʳ_ : ∀ xs (rs : Reverse xs) (x : A) → Reverse (xs ∷ʳ x)

module _ {a} {A : Set a} where

  reverse : (xs : List A) → Reverse (L.reverse xs)
  reverse []       = []
  reverse (x ∷ xs) = cast $ _ ∶ reverse xs ∶ʳ x where
    cast = subst Reverse (sym $ unfold-reverse x xs)

  reverseView : (xs : List A) → Reverse xs
  reverseView xs = cast $ reverse (L.reverse xs) where
    cast = subst Reverse (reverse-involutive xs)
