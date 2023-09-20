------------------------------------------------------------------------
-- The Agda standard library
--
-- Illustration for the `NonEmpty` predicate over `List`
------------------------------------------------------------------------

module README.Data.List.Relation.Unary.NonEmpty where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; null; length)
open import Data.Nat.Base using (ℕ; _>_; z<s)
open import Data.Product.Base using (Σ; _,_)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (contradiction)

private
  variable

    a b : Level
    A   : Set a
    B   : Set b
    x   : A
    xs  : List A


------------------------------------------------------------------------
-- NonEmpty

-- The predicate `NonEmpty` encodes a *refinement* of the `List` type,
-- here exhibited to show comparison with `Data.List.NonEmpty`, with
-- an example to show how to avoid dead code otherwise required by the
-- pattern-matching coverage check... and modelled on `Data.Nat.Base.NonZero`

NonEmpty : List A → Set
NonEmpty = T ∘ not ∘ null

-- Instances

instance
  nonEmpty : NonEmpty (x ∷ xs)
  nonEmpty = _

-- Constructors

≢-nonEmpty : xs ≢ [] → NonEmpty xs
≢-nonEmpty {xs = []}    []≢[] = contradiction refl []≢[]
≢-nonEmpty {xs = _ ∷ _} xs≢[] = _

>-nonEmpty : length xs > 0 → NonEmpty xs
>-nonEmpty {xs = _ ∷ _} _ = _

-- Destructors

≢-nonEmpty⁻¹ : (xs : List A) → .{{NonEmpty xs}} → xs ≢ []
≢-nonEmpty⁻¹ (_ ∷ _) ()

>-nonEmpty⁻¹ : (xs : List A) → .{{NonEmpty xs}} → length xs > 0
>-nonEmpty⁻¹ (_ ∷ _) = z<s

------------------------------------------------------------------------
-- Example deployment: scans

-- Scans

module ScanL (f : A → B → A) where

  scanl : A → List B → List A
  scanl e []       = e ∷ []
  scanl e (x ∷ xs) = e ∷ scanl (f e x) xs

  instance scanlNonEmpty : {e : A} {xs : List B} → NonEmpty (scanl e xs)
  scanlNonEmpty {xs = []}    = _
  scanlNonEmpty {xs = _ ∷ _} = _


module ScanR (f : A → B → B) (e : B) where

-- design pattern: refinement types via Σ-types

  scanrΣ        : List A → Σ (List B) NonEmpty
  scanrΣ []                                       =     e ∷ [] , _
  scanrΣ (x ∷ xs) with ys@(y ∷ _) , _ ← scanrΣ xs = f x y ∷ ys , _

  scanr         : List A → List B
  instance scanrNonEmpty : {xs : List A} → NonEmpty (scanr xs)

  scanr xs with ys , _ ← scanrΣ xs = ys
  scanrNonEmpty {xs = xs} with _ ∷ _ , _ ← scanrΣ xs = _

-- design pattern: refinement types via mutual recursion

-- to simulate the refinement type { xs : List A | NonEmpty xs }
-- define two functions by mutual recursion:
-- `f`         : the bare, 'extracted' underlying function
-- `fNonEmpty` : the witness to the refinement predicate, as an instance

  scanr′ : List A → List B
  instance scanrNonEmpty′ : {xs : List A} → NonEmpty (scanr′ xs)

  scanr′ []       = e ∷ []
  scanr′ (x ∷ xs) 
    with ys ← scanr′ xs | _ ← scanrNonEmpty′ {xs = xs} with y ∷ _ ← ys = f x y ∷ ys

-- is there a 'better' way to express this? eg
--  scanr′ (x ∷ xs) with ys@(y ∷ _) ← scanr′ xs = f x y ∷ ys
--    where instance _ = scanrNonEmpty′ {xs = xs}

  scanrNonEmpty′ {xs = []}     = _
  scanrNonEmpty′ {xs = x ∷ xs}
    with ys ← scanr′ xs | _ ← scanrNonEmpty′ {xs = xs} with y ∷ _ ← ys = _

