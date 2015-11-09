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

toNat : T → ℕ
toNat L = 1
toNat (B b b₁) = (toNat b) Nat.+ (toNat b₁)

-- zeroless bits
data Bit : Set where
  one : Bit
  two : Bit

-- zeroless binary number
Bits = List⁺ Bit

inc : Bits → Bits
inc (one ∷ tail) = two ∷ tail
inc (two ∷ tail) = one ∷ inc' tail
  where
  inc' : List Bit → List Bit
  inc' [] = one ∷ []
  inc' (one ∷ bits) = two ∷ bits
  inc' (two ∷ bits) = one ∷ inc' bits

toBits : ℕ → Maybe Bits
toBits zero = nothing
toBits (suc n) = just (Nat.fold [ one ] inc n)

combineT : T → Maybe T → T
combineT l (just r) = B l r
combineT l nothing = l

completeT : ℕ → Bit → T
completeT zero one = L
completeT zero two = B L L
completeT (suc n) l = B (completeT n l) (completeT n l)

toT : Bits → T
toT (bits) = go (reverse bits)
  where
  go' : List Bit → Maybe T
  go : Bits → T
  go (bit ∷ bits) = combineT (completeT (List.length bits) bit) (go' bits)
  go' [] = nothing
  go' (bit ∷ bits) = just (combineT (completeT (List.length bits) bit) (go' bits))

mkT : ℕ → Maybe T
mkT n = mapMaybe toT (toBits n)

module test where
  open import Relation.Binary.PropositionalEquality

  t : mkT 1 ≡ just L
  t = refl

  t2 : mkT 2 ≡ just (B L L)
  t2 = refl

  t3 : mkT 3 ≡ just (B (B L L) L)
  t3 = refl

  -- open import Data.Sum

  -- t4 : ∀ n → n ≡ 0 ⊎ mapMaybe toNat (mkT n) ≡ just n
  -- t4 zero = inj₁ refl
  -- t4 (suc n) with mkT (suc n)
  -- ... | h = inj₂ {!!}
