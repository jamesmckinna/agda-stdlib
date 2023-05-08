------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Setoid where

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Level
open import Function.Base

open import Function.Bundles
  using (Func; Equivalence; LeftInverse; Injection; Surjection; Bijection
        ; _⟶_; _⇔_;_↩_; _↠_; _↣_)
open Func using () renaming (to to _⟨$⟩_)
open import Function.Construct.Symmetry using (⇔-sym)
{-
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; Injective; _↣_; module Injection)

open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; _LeftInverseOf_; _RightInverseOf_; module LeftInverse)
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
-}
open import Relation.Binary as B hiding (_⇔_)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    a₁ a₂ b₁ b₁′ b₂ b₂′ : Level
    A₁ : Set a₁
    A₂ : Set a₂


------------------------------------------------------------------------
-- Properties related to "relatedness"
------------------------------------------------------------------------

private

  subst-cong : ∀ {i a p} {I : Set i} {A : I → Set a}
               (P : ∀ {i} → A i → A i → Set p) {i i′} {x y : A i}
               (i≡i′ : i ≡ i′) →
               P x y → P (P.subst A i≡i′ x) (P.subst A i≡i′ y)
  subst-cong P P.refl p = p

⟶ : {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′)
    (f : A₁ → A₂) → (∀ {x : A₁} → Func (B₁ atₛ x) (B₂ atₛ (f x))) →
    Func (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
⟶ {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} B₂ f g = 
  record
  { to = fg
  ; cong  = fg-cong
  }
  where
  open B.Setoid (setoid (P.setoid A₁) B₁)
    using () renaming (_≈_ to _≈₁_)
  open B.Setoid (setoid (P.setoid A₂) B₂)
    using () renaming (_≈_ to _≈₂_)
  open B using (_=[_]⇒_)

  fg = map f (_⟨$⟩_ g)

  fg-cong : _≈₁_ =[ fg ]⇒ _≈₂_
  fg-cong (P.refl , ∼) = (P.refl , Func.cong g ∼)

module _ {B₁ : IndexedSetoid A₁ b₁ b₁′} {B₂ : IndexedSetoid A₂ b₂ b₂′} where

  module _ (A₁⇔A₂ : A₁ ⇔ A₂) where

    to-Func = Equivalence.to-Func A₁⇔A₂
    open Func to-Func renaming (to to toA; cong to to-congA)
    A₂⇔A₁ : A₂ ⇔ A₁
    A₂⇔A₁ = ⇔-sym A₁⇔A₂
    from-Func = Equivalence.to-Func A₂⇔A₁
    open Func from-Func renaming (to to fromA; cong to from-congA)

    equivalence : 
      (∀ {x} → Func (B₁ atₛ x) (B₂ atₛ (to-Func ⟨$⟩ x))) →
      (∀ {y} → Func (B₂ atₛ y) (B₁ atₛ (from-Func ⟨$⟩ y))) →
      Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
    equivalence B-to B-from = record
      { to = toB 
      ; from = fromB
      ; to-cong = to-congB
      ; from-cong = from-congB
      } where
        open Func (⟶ {B₁ = B₁} B₂ toA B-to) renaming (to to toB; cong to to-congB)
        open Func (⟶ {B₁ = B₂} B₁ fromA B-from) renaming (to to fromB; cong to from-congB)


  module _ (A₁↩A₂ : A₁ ↩ A₂) where
{-

    equivalence-↞ :
      (∀ {x} → Equivalence (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ x)) (B₂ atₛ x)) →
      Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
    equivalence-↞ B₁ {B₂} A₁↞A₂ B₁⇔B₂ =
      equivalence (LeftInverse.equivalence A₁↞A₂) B-to B-from
      where
      B-to : ∀ {x} → _⟶_ (B₁ atₛ x) (B₂ atₛ (LeftInverse.to A₁↞A₂ ⟨$⟩ x))
      B-to = record
        { _⟨$⟩_ = λ x → Equivalence.to B₁⇔B₂ ⟨$⟩
                        P.subst (IndexedSetoid.Carrier B₁)
                         (P.sym $ LeftInverse.left-inverse-of A₁↞A₂ _)
                         x
        ; cong  = Func.cong (Equivalence.to B₁⇔B₂) ∘
                  subst-cong (λ {x} → IndexedSetoid._≈_ B₁ {x} {x})
                         (P.sym (LeftInverse.left-inverse-of A₁↞A₂ _))
        }

    B-from : ∀ {y} → _⟶_ (B₂ atₛ y) (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ y))
    B-from = Equivalence.from B₁⇔B₂
-}

  module _ (A₁↠A₂ : A₁ ↠ A₂) where
{-
  equivalence-↠ : 
    (∀ {x} → Equivalence (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence-↠ B₁⇔B₂ =
    equivalence (Surjection.equivalence A₁↠A₂) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))
    B-to = Equivalence.to B₁⇔B₂

    B-from : ∀ {y} → _⟶_ (B₂ atₛ y) (B₁ atₛ (Surjection.from A₁↠A₂ ⟨$⟩ y))
    B-from = record
      { _⟨$⟩_ = λ x → Equivalence.from B₁⇔B₂ ⟨$⟩
                      P.subst (IndexedSetoid.Carrier B₂)
                         (P.sym $ Surjection.right-inverse-of A₁↠A₂ _)
                         x
      ; cong  = Func.cong (Equivalence.from B₁⇔B₂) ∘
              subst-cong (λ {x} → IndexedSetoid._≈_ B₂ {x} {x})
                         (P.sym (Surjection.right-inverse-of A₁↠A₂ _))
      }
-}

  module _ (A₁↣A₂ : A₁ ↣ A₂) where
{-
  injection : 
    (∀ {x} → Injection (B₁ atₛ x) (B₂ atₛ (Injection.to A₁↣A₂ ⟨$⟩ x))) →
    Injection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  injection B₁↣B₂ = record
    { to        = to
    ; injective = inj
    }
    where
    to = ⟶ B₂ (Injection.to A₁↣A₂ ⟨$⟩_) (Injection.to B₁↣B₂)

    inj : Injective to
    inj (x , y) =
      Injection.injective A₁↣A₂ x ,
      lemma (Injection.injective A₁↣A₂ x) y
      where
      lemma :
        ∀ {x x′}
          {y : IndexedSetoid.Carrier B₁ x} {y′ : IndexedSetoid.Carrier B₁ x′} →
        x ≡ x′ →
        (eq : IndexedSetoid._≈_ B₂ (Injection.to B₁↣B₂ ⟨$⟩ y)
                              (Injection.to B₁↣B₂ ⟨$⟩ y′)) →
        IndexedSetoid._≈_ B₁ y y′
      lemma P.refl = Injection.injective B₁↣B₂
-}
{-

  module _ (A₁↞A₂ : A₁ ↞ A₂) where

  left-inverse : 
    (∀ {x} → LeftInverse (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ x)) (B₂ atₛ x)) →
    LeftInverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  left-inverse B₁ {B₂} A₁↞A₂ B₁↞B₂ = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    eq = equivalence-↞ B₁ A₁↞A₂ (LeftInverse.equivalence B₁↞B₂)

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) =
      LeftInverse.left-inverse-of A₁↞A₂ x ,
      IndexedSetoid.trans B₁
        (LeftInverse.left-inverse-of B₁↞B₂ _)
        (lemma (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x)))
      where
      lemma :
        ∀ {x x′ y} (eq : x ≡ x′) →
        IndexedSetoid._≈_ B₁ (P.subst (IndexedSetoid.Carrier B₁) eq y) y
      lemma P.refl = IndexedSetoid.refl B₁
-}


  module _ (A₁↠A₂ : A₁ ↠ A₂) where
{-
  surjection : 
    (∀ {x} → Surjection (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Surjection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  surjection B₂ A₁↠A₂ B₁↠B₂ = record
    { to         = Equivalence.to eq
    ; surjective = record
      { from             = Equivalence.from eq
      ; right-inverse-of = right
      }
    }
    where
    eq = equivalence-↠ B₂ A₁↠A₂ (Surjection.equivalence B₁↠B₂)

    right : Equivalence.from eq RightInverseOf Equivalence.to eq
    right (x , y) =
      Surjection.right-inverse-of A₁↠A₂ x ,
      IndexedSetoid.trans B₂
        (Surjection.right-inverse-of B₁↠B₂ _)
        (lemma (P.sym $ Surjection.right-inverse-of A₁↠A₂ x))
      where
      lemma : ∀ {x x′ y} (eq : x ≡ x′) →
              IndexedSetoid._≈_ B₂ (P.subst (IndexedSetoid.Carrier B₂) eq y) y
      lemma P.refl = IndexedSetoid.refl B₂
-}

  -- See also Data.Product.Function.Dependent.Setoid.WithK.inverse.
  
