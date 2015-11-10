{-# OPTIONS --copatterns #-}

module _ where

open import Data.Nat renaming (_+_ to _N+_)
open import Relation.Binary.PropositionalEquality


-- "power series"
record PS : Set where
  coinductive
  constructor _,_
  field
    head : ℕ
    tail : PS

open PS

-- Bisimulation
record _≃_ (i j : PS) : Set where
  coinductive
  field
    ≃head : head i ≡ head j
    ≃tail : tail i ≃ tail j

open _≃_

_+_ : PS → PS → PS
head (as + bs) = head as N+ head bs
tail (as + bs) = tail as + tail bs

ones : PS
head ones = 1
tail ones = ones

twos : PS
head twos = 2
tail twos = twos

p : (ones + ones) ≃ twos
≃head p = refl
≃tail p = p

import Data.Nat.Properties.Simple as Nat

+-comm+ : ∀ a b → (a + b) ≃ (b + a)
≃head (+-comm+ a b) = Nat.+-comm (head a) (head b)
≃tail (+-comm+ a b) = +-comm+ (tail a) (tail b)


-- record CoList (A : Set) : Set where
--   coinductive
--   constructor _::_
--   field
--     head' : A
--     tail' : CoList A

--   unfold : ∀ {S} → (S → ⊤ ⊎ (A × S)) → S → CoList A
--   head' (unfold f s) = ?
--   tail' (unfold f s) = ?
