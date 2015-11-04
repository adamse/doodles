module Tree where

open import Data.Nat as Nat using (ℕ; zero; suc; _>_; s≤s)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty
open import Data.Maybe renaming (map to mapMaybe)

data T : Set where
  -- 1
  L : T
  -- s₁ + s₂
  B : (s₁ s₂ : T) → T

-- data ℕ+ : Set where
--   one : ℕ+
--   suc : ℕ+ → ℕ+

ℕ+ = ℕ -- zero is one

data Bit : Set where
  one : Bit
  two : Bit

Bits = List⁺ Bit

-- fold : {a : Set} → a → (a → a) → ℕ+ → a
-- fold o s one = o
-- fold o s (suc n) = s (fold o s n)

-- toℕ+ : (n : ℕ) → n > 0 → ℕ+ --
-- toℕ+ zero ()
-- toℕ+ (suc n) (s≤s p) = Nat.fold one suc n

inc : Bits → Bits
inc (one ∷ tail) = two ∷ tail
inc (two ∷ tail) = one ∷ inc' tail
  where
  inc' : List Bit → List Bit
  inc' [] = one ∷ []
  inc' (one ∷ bits) = two ∷ bits
  inc' (two ∷ bits) = one ∷ inc' bits

-- to bits you say
toBits : ℕ+ → Bits
toBits n = reverse (Nat.fold [ one ] inc n)

combineT : T → Maybe T → T
combineT l (just r) = B l r
combineT l nothing = l

completeT : ℕ → Bit → T
completeT zero one = L
completeT zero two = B L L
completeT (suc n) l = B (completeT n l) (completeT n l)

toT : Bits → T
toT (bit ∷ bits) = combineT (completeT (List.length bits) bit) (toT' bits)
  where
  toT' : List Bit → Maybe T
  toT' [] = nothing
  toT' (bit ∷ bits) = just (combineT (completeT (List.length bits) bit) (toT' bits))

mkT : ℕ+ → T
mkT n = toT (toBits n)
