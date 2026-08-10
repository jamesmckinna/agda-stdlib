------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --without-K --irrelevant-projections #-}

module Relation.Nullary.Recomputable.Unsafe where

open import Data.Irrelevant using (Irrelevant; irrelevant)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a


------------------------------------------------------------------------
-- Re-export

open import Relation.Nullary.Recomputable public


------------------------------------------------------------------------
-- Constructions

-- Irrelevant types are Recomputable

irrelevant-recompute : Recomputable (Irrelevant A)
irrelevant (irrelevant-recompute a) = irrelevant a

