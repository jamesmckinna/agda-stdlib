------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties where

open import Data.Product.Base as Product
open import Data.Sum.Base as Sum
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Base using (id)
open import Level
open import Relation.Binary.Core using (Rel; REL; _=[_]⇒_)
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
  using (IsPreorder; IsStrictPartialOrder; IsPartialOrder; IsDecStrictPartialOrder; IsDecPartialOrder; IsStrictTotalOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Reflexive; Asymmetric; Antisymmetric; Trichotomous; Total; Decidable; DecidableEquality; tri<; tri≈; tri>; _Respectsˡ_; _Respectsʳ_; _Respects_; _Respects₂_)
open import Relation.Binary.Construct.Closure.Reflexive as Refl
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Pred)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ p q : Level
    A : Set a
    B : Set b
    _~_ : Rel A ℓ
    P : Pred A p
    x y : A

------------------------------------------------------------------------
-- Relational properties

module _ {_~_ : Rel A ℓ} where

  private

    _~ᵒ_ = ReflClosure _~_

  fromSum : x ≡ y ⊎ x ~ y → x ~ᵒ y
  fromSum (inj₁ refl) = refl
  fromSum (inj₂ y)    = [ y ]

  toSum : x ~ᵒ y → x ≡ y ⊎ x ~ y
  toSum [ x∼y ] = inj₂ x∼y
  toSum refl    = inj₁ refl

  ⊎⇔Refl : (x ≡ y ⊎ x ~ y) ⇔ x ~ᵒ y
  ⊎⇔Refl = mk⇔ fromSum toSum

  sym : Symmetric _~_ → Symmetric _~ᵒ_
  sym ~-sym [ x∼y ] = [ ~-sym x∼y ]
  sym ~-sym refl    = refl

  trans : Transitive _~_ → Transitive _~ᵒ_
  trans ~-trans [ x∼y ] [ y∼z ] = [ ~-trans x∼y y∼z ]
  trans ~-trans [ x∼y ] refl    = [ x∼y ]
  trans ~-trans refl    [ x∼y ] = [ x∼y ]
  trans ~-trans refl    refl    = refl

  antisym : (_≈_ : Rel A p) → Reflexive _≈_ →
            Asymmetric _~_ → Antisymmetric _≈_ _~ᵒ_
  antisym _≈_ ref asym [ x∼y ] [ y∼x ] = contradiction x∼y (asym y∼x)
  antisym _≈_ ref asym [ x∼y ] refl    = ref
  antisym _≈_ ref asym refl    _       = ref

  total : Trichotomous _≡_ _~_ → Total _~ᵒ_
  total compare x y with compare x y
  ... | tri< a _    _ = inj₁ [ a ]
  ... | tri≈ _ refl _ = inj₁ refl
  ... | tri> _ _    c = inj₂ [ c ]

  dec : DecidableEquality A → Decidable _~_ → Decidable _~ᵒ_
  dec ≡-dec ~-dec a b = Dec.map ⊎⇔Refl (≡-dec a b ⊎-dec ~-dec a b)

  decidable : Trichotomous _≡_ _~_ → Decidable _~ᵒ_
  decidable ~-tri a b with ~-tri a b
  ... | tri< a~b  _  _ = yes [ a~b ]
  ... | tri≈ _  refl _ = yes refl
  ... | tri> ¬a ¬b   _ = no λ { refl → ¬b refl ; [ p ] → ¬a p }

  resp : P Respects _~_ → P Respects _~ᵒ_
  resp resp-~ [ x∼y ] = resp-~ x∼y
  resp _      refl    = id

  respˡ : ∀ {R : REL A B p} → R Respectsˡ _~_ → R Respectsˡ _~ᵒ_
  respˡ respˡ-~ [ x∼y ] = respˡ-~ x∼y
  respˡ _       refl    = id

  respʳ : ∀ {R : REL B A p} → R Respectsʳ _~_ → R Respectsʳ _~ᵒ_
  respʳ = respˡ

  resp₂ : ∀ {R : Rel A p} → R Respects₂ _~_ → R Respects₂ _~ᵒ_
  resp₂ = Product.map respˡ respʳ

------------------------------------------------------------------------
-- Structures

  module Structures where

    isPreorder : Transitive _~_ → IsPreorder _≡_ _~ᵒ_
    isPreorder ~-trans = record
      { isEquivalence = ≡.isEquivalence
      ; reflexive     = reflexive
      ; trans         = trans ~-trans
      }

    isPartialOrder : IsStrictPartialOrder _≡_ _~_ → IsPartialOrder _≡_ _~ᵒ_
    isPartialOrder O = record
      { isPreorder = isPreorder O.trans
      ; antisym    = antisym _≡_ refl O.asym
      } where module O = IsStrictPartialOrder O

    isDecPartialOrder : IsDecStrictPartialOrder _≡_ _~_ → IsDecPartialOrder _≡_ _~ᵒ_
    isDecPartialOrder O = record
      { isPartialOrder = isPartialOrder O.isStrictPartialOrder
      ; _≟_            = O._≟_
      ; _≤?_           = dec O._≟_ O._<?_
      } where module O = IsDecStrictPartialOrder O

    isTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsTotalOrder _≡_ _~ᵒ_
    isTotalOrder O = record
      { isPartialOrder = isPartialOrder isStrictPartialOrder
      ; total          = total compare
      } where open IsStrictTotalOrder O

    isDecTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsDecTotalOrder _≡_ _~ᵒ_
    isDecTotalOrder O = record
      { isTotalOrder = isTotalOrder O
      ; _≟_          = _≟_
      ; _≤?_         = dec _≟_ _<?_
      } where open IsStrictTotalOrder O

  open Structures public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

=[]⇒ = Refl.map
{-# WARNING_ON_USAGE =[]⇒
"Warning: Refl was deprecated in v2.1.
Please use ReflClosure.map instead."
#-}
