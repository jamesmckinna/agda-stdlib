------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.Reasoning.Syntax

module Data.List.Relation.Binary.Permutation.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Base using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
import Data.List.Relation.Binary.Pointwise.Properties as Pointwise using (refl)
open import Data.List.Relation.Binary.Equality.Setoid S
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  module Eq = Setoid S
open Eq using (_≈_) renaming (Carrier to A)

private
  variable
    xs ys zs : List A
    x y z v w : A

------------------------------------------------------------------------
-- Definition

open Homogeneous public
  using ([]; swap; trans)

infix 3 _↭_

_↭_ : Rel (List A) (a ⊔ ℓ)
_↭_ = Homogeneous.Permutation _≈_

pattern prep {xs} {ys} {x} {y} x≈y xs↭ys = Homogeneous._∷_ {xs} {ys} {x} {y} x≈y xs↭ys

------------------------------------------------------------------------
-- Constructor aliases and inversions

-- These provide aliases for `swap` and `prep` when the elements being
-- swapped or prepended are propositionally equal

↭-prep : ∀ x {xs ys} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep x xs↭ys = prep Eq.refl xs↭ys

↭-swap : ∀ x y {xs ys} → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
↭-swap x y xs↭ys = swap Eq.refl Eq.refl xs↭ys

-- Inversions

↭-[]-invˡ : [] ↭ xs → xs ≡ []
↭-[]-invˡ = Homogeneous.↭-[]-invˡ

↭-[]-invʳ : xs ↭ [] → xs ≡ []
↭-[]-invʳ = Homogeneous.↭-[]-invʳ

------------------------------------------------------------------------
-- Functions over permutations

steps : ∀ {xs ys} → xs ↭ ys → ℕ
steps []                  = 1
steps (prep _ xs↭ys)      = suc (steps xs↭ys)
steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
steps (trans [] []) = 1
steps (trans [] (trans []↭ys ys↭zs)) = steps ys↭zs
steps (trans (trans xs↭ys ys↭[]) []) = steps xs↭ys
steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-refl : Reflexive _↭_
↭-refl = Homogeneous.refl Eq.refl

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-refl

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise = Homogeneous.↭-pointwise

↭-sym : Symmetric _↭_
↭-sym = Homogeneous.sym Eq.sym

↭-transˡ-≋ : LeftTrans _≋_ _↭_
↭-transˡ-≋ = Homogeneous.↭-transˡ-≋ Eq.trans 

↭-transʳ-≋ : RightTrans _↭_ _≋_
↭-transʳ-≋ = Homogeneous.↭-transʳ-≋ Eq.trans

↭-trans : Transitive _↭_
↭-trans = Homogeneous.↭-trans

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = Homogeneous.isEquivalence Eq.refl Eq.sym

↭-setoid : Setoid _ _
↭-setoid = Homogeneous.setoid {R = _≈_} Eq.refl Eq.sym

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  private module Base = ≈-Reasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public
  open ≋-syntax _IsRelatedTo_ _IsRelatedTo_ (↭-go ∘′ ↭-pointwise) ≋-sym public

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
