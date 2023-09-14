------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'top' view of Fin
--
-- This is an example of a view of (elements of) a datatype,
-- here i : Fin (suc n), which exhibits every such i as
-- * either, i = fromℕ n
-- * or, i = inject₁ j for a unique j : Fin n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁; inject₁ℕ<)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    n : ℕ
    i : Fin (suc n)
    j : Fin n

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin n

-- NB `Data.Fin.Properties.fromℕ≢inject₁` establishes that the following
-- inductively defined family on `Fin n` has constructors which target
-- *disjoint* instances of the family (moreover at indices `n = suc _`);
-- hence the interpretations of the View constructors will also be disjoint.

data View : (j : Fin n) → Set where
  ‵fromℕ : View (fromℕ n)
  ‵inj₁ : View j → View (inject₁ j)

pattern ‵inject₁ j = ‵inj₁ {j = j} _

-- The view covering function, witnessing soundness of the view

view-zero : ∀ n → View {suc n} zero
view-zero zero    = ‵fromℕ
view-zero (suc n) = ‵inj₁ (view-zero n)

view : (j : Fin n) → View j
view zero = view-zero _
view (suc i) with view i
... | ‵fromℕ     = ‵fromℕ
... | ‵inject₁ j = ‵inj₁ (view (suc j))

-- Interpretation of the view constructors

⟦_⟧ : {j : Fin n} → View j → Fin n
⟦ ‵fromℕ ⟧     = fromℕ _
⟦ ‵inject₁ j ⟧ = inject₁ j

-- Completeness of the view

view-complete : (v : View j) → ⟦ v ⟧ ≡ j
view-complete ‵fromℕ    = refl
view-complete (‵inj₁ _) = refl

-- 'Computational' behaviour of the covering function

view-fromℕ : ∀ n → view (fromℕ n) ≡ ‵fromℕ
view-fromℕ zero                         = refl
view-fromℕ (suc n) rewrite view-fromℕ n = refl

view-inject₁ : (j : Fin n) → view (inject₁ j) ≡ ‵inj₁ (view j)
view-inject₁ zero                           = refl
view-inject₁ (suc j) rewrite view-inject₁ j = refl

-- Uniqueness of the view

view-unique : (v : View j) → view j ≡ v
view-unique ‵fromℕ            = view-fromℕ _
view-unique (‵inj₁ {j = j} v) = begin
  view (inject₁ j) ≡⟨ view-inject₁ j ⟩
  ‵inj₁ (view j)   ≡⟨ cong ‵inj₁ (view-unique v) ⟩
  ‵inj₁ v          ∎ where open ≡-Reasoning

