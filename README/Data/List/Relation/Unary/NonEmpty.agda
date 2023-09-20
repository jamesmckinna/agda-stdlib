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
    ys  : List B


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

-- BUT here, we seem to need to go via `helper`/`helperNonEmpty`...

-- simpler instance of the pattern: no mutual recursion
 
  helper : A → (ys : List B) → .{{_ : NonEmpty ys}} → List B
  helper x ys@(y ∷ _) = f x y ∷ ys

  -- why does this instance need `nonEmpty` to be supplied explicitly:
  -- why doesn't an irrelevant instance suffice?
  
  instance helperNonEmpty : ∀ {x} {ys} .{{nonEmpty : NonEmpty ys}} →
                            NonEmpty (helper x ys {{nonEmpty}}) 
  helperNonEmpty {ys = y ∷ _} = _

-- now we can instantiate the pattern proper
 
  scanr′ : List A → List B
  instance scanrNonEmpty′ : {xs : List A} → NonEmpty (scanr′ xs)

  scanr′ []       = e ∷ []
  scanr′ (x ∷ xs) = helper x (scanr′ xs) {{scanrNonEmpty′ {xs = xs}}}
  -- but not (why not?):
  -- helper x (scanr′ xs) where instance _ = scanrNonEmpty′ {xs = xs}

  scanrNonEmpty′ {xs = []}     = _
  scanrNonEmpty′ {xs = x ∷ xs} = helperNonEmpty {ys = scanr′ xs} {{scanrNonEmpty′ {xs = xs}}}
