------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base as Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Properties as Pointwise
  using (symmetric)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_)

private
  variable
    a r s : Level
    A : Set a
    xs ys zs : List A
    x y z v w : A


------------------------------------------------------------------------
-- Definition and consequences

infixr 5 _∷_

data Permutation {A : Set a} (R : Rel A r) : Rel (List A) (a ⊔ r) where
  []    : Permutation R [] []
  _∷_   : (eq : R x y) → Permutation R xs ys → Permutation R (x ∷ xs) (y ∷ ys)
  swap  : (eq₁ : R x v) (eq₂ : R y w) →
          Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (w ∷ v ∷ ys)
  trans : Permutation R xs ys → Permutation R ys zs → Permutation R xs zs

------------------------------------------------------------------------
-- Consequences

module _ {R : Rel A r} where

-- Smart inversions

  ↭-[]-invˡ : Permutation R [] xs → xs ≡ []
  ↭-[]-invˡ []                  = ≡.refl
  ↭-[]-invˡ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invˡ xs↭ys = ↭-[]-invˡ ys↭zs

  ↭-[]-invʳ : Permutation R xs [] → xs ≡ []
  ↭-[]-invʳ []                  = ≡.refl
  ↭-[]-invʳ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invʳ ys↭zs = ↭-[]-invʳ xs↭ys

-- Smart constructors

  ↭-pointwise : (Pointwise R) ⇒ Permutation R
  ↭-pointwise [] = []
  ↭-pointwise (x∼y ∷ p) = x∼y ∷ ↭-pointwise p

-- A smart version of trans that collapses chains of `[]` (cf. #1113).

  ↭-trans : Transitive (Permutation R)
  ↭-trans []    ys↭zs with ≡.refl ← ↭-[]-invˡ ys↭zs = []
  ↭-trans xs↭ys []    with ≡.refl ← ↭-[]-invʳ xs↭ys = []
  ↭-trans xs↭ys ys↭zs = trans xs↭ys ys↭zs

------------------------------------------------------------------------
-- The Permutation relation is an equivalence

  refl : Reflexive R → Reflexive (Permutation R)
  refl R-refl = ↭-pointwise (Pointwise.refl R-refl)

  sym : Symmetric R → Symmetric (Permutation R)
  sym R-sym []                     = []
  sym R-sym (x∼x′ ∷ xs↭ys)         = R-sym x∼x′ ∷ sym R-sym xs↭ys
  sym R-sym (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (sym R-sym xs↭ys)
  sym R-sym (trans xs↭ys ys↭zs)    = trans (sym R-sym ys↭zs) (sym R-sym xs↭ys)

  isEquivalence : Reflexive R → Symmetric R → IsEquivalence (Permutation R)
  isEquivalence R-refl R-sym = record
    { refl  = refl R-refl
    ; sym   = sym R-sym
    ; trans = ↭-trans
    }

  setoid : Reflexive R → Symmetric R → Setoid _ _
  setoid R-refl R-sym = record
    { isEquivalence = isEquivalence R-refl R-sym
    }

------------------------------------------------------------------------
-- Closure under Pointwise equality

  module _ (R-trans : Transitive R) where

    ↭-transˡ-≋ : LeftTrans (Pointwise R) (Permutation R)
    ↭-transˡ-≋ []               []         = []
    ↭-transˡ-≋ (x≈y ∷ xs≋ys)       (y≈z ∷ ys↭zs)     = R-trans x≈y y≈z ∷ ↭-transˡ-≋ xs≋ys ys↭zs
    ↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs) = swap (R-trans x≈y eq₁) (R-trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
    ↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs) = ↭-trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

    ↭-transʳ-≋ : RightTrans (Permutation R) (Pointwise R)
    ↭-transʳ-≋ [] [] = []
    ↭-transʳ-≋ (x≈y ∷ xs↭ys) (y≈z ∷ ys≋zs) = R-trans x≈y y≈z ∷ ↭-transʳ-≋ xs↭ys ys≋zs
    ↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs) = swap (R-trans eq₁ y≈z) (R-trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
    ↭-transʳ-≋ (trans xs↭ws ws↭ys) ys≋zs = ↭-trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

------------------------------------------------------------------------
-- Map

map : ∀ {R : Rel A r} {S : Rel A s} →
      (R ⇒ S) → (Permutation R ⇒ Permutation S)
map R⇒S []         = []
map R⇒S (e ∷ xs∼ys)       = R⇒S e ∷ map R⇒S xs∼ys
map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)
