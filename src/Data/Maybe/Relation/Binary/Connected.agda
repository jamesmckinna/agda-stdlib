------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting a relation such that `nothing` is also related to `just`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Relation.Binary.Connected where

open import Level
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; map′)

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    R S T : REL A B ℓ
    x y : A

------------------------------------------------------------------------
-- Definition

data Connected {A : Set a} {B : Set b} (R : REL A B ℓ)
               : REL (Maybe A) (Maybe B) (a ⊔ b ⊔ ℓ) where
  just         : R x y → Connected R (just x) (just y)
  just-nothing : Connected R (just x) nothing
  nothing-just : Connected R nothing (just y)
  nothing      : Connected R nothing nothing

------------------------------------------------------------------------
-- Properties

drop-just : Connected R (just x) (just y) → R x y
drop-just (just p) = p

just-equivalence : R x y ⇔ Connected R (just x) (just y)
just-equivalence = mk⇔ just drop-just

------------------------------------------------------------------------
-- Relational properties

refl : Reflexive R → Reflexive (Connected R)
refl R-refl {just _}  = just R-refl
refl R-refl {nothing} = nothing

reflexive : _≡_ ⇒ R → _≡_ ⇒ Connected R
reflexive reflexive P.refl = refl (reflexive P.refl)

sym : Sym R S → Sym (Connected R) (Connected S)
sym R-sym (just p)     = just (R-sym p)
sym R-sym nothing-just = just-nothing
sym R-sym just-nothing = nothing-just
sym R-sym nothing      = nothing

connected? : Decidable R → Decidable (Connected R)
connected? R? (just x) (just y) = map′ just drop-just (R? x y)
connected? R? (just x) nothing  = yes just-nothing
connected? R? nothing  (just y) = yes nothing-just
connected? R? nothing  nothing  = yes nothing
