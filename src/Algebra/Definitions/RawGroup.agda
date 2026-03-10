------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for monoid-like structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (RawGroup)

module Algebra.Definitions.RawGroup {a ℓ} (X : RawGroup a ℓ) where

open import Data.Integer.Base as ℤ using (ℤ; +_; +[1+_]; +0; -[1+_])
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)

private
  variable
    m n : ℕ
    i j : ℤ
    
  module G = RawGroup X

------------------------------------------------------------------------
-- Re-export definitions over a monoid
------------------------------------------------------------------------

open import Algebra.Definitions.RawMonoid G.rawMonoid public
  renaming (_×_ to _×ℕ_; _×′_ to _×ℕ′_)

------------------------------------------------------------------------
-- Multiplication by integer
------------------------------------------------------------------------
-- Standard definition

-- A simple definition, easy to use and prove properties about.

infixr 8 _×_

_×_ : ℤ → G.Carrier → G.Carrier
(+ n)    × x = n ×ℕ x
-[1+ n ] × x = ((suc n) ×ℕ x) G.⁻¹

------------------------------------------------------------------------
-- Type-checking optimised definition, by analogy with _×ℕ′_

infixl 8 _×′_

_×′_ : ℤ → G.Carrier → G.Carrier
(+ n)    ×′ x = n ×ℕ′ x
-[1+ n ] ×′ x = ((suc n) ×ℕ′ x) G.⁻¹

{-# INLINE _×′_ #-}

