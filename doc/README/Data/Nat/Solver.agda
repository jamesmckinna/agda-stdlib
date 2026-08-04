------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of using the simple Algebra.Solver.Ring,
-- with added natural number literals for Ring constants.
------------------------------------------------------------------------

module README.Data.Nat.Solver where

open import Agda.Builtin.FromNat
open import Data.Nat.Base using (ℕ; _+_; _*_)
import Data.Nat.Literals as ℕ
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic.Base as Poly

instance _ = ℕ.number
instance _ = +-*-Solver.number
instance _ = Poly.tt

1+n*1+n≡1+n²+2n : ∀ (n : ℕ) → (1 + n) * (1 + n) ≡ 1 + (2 * n) + (n * n)
1+n*1+n≡1+n²+2n = solve 1 (λ n → (1 :+ n) :* (1 :+ n) := 1 :+ (2 :* n) :+ (n :* n)) refl
  where open +-*-Solver

