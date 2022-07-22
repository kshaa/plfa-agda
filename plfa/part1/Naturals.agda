module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
-- open import Data.Nat

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}

-- n0 : ℕ
-- n0 = zero

-- n1 : ℕ
-- n1 = suc zero

n2 : ℕ
n2 = suc (suc zero)


_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc (suc (suc (zero)))) + (suc (suc (suc (suc (zero)))))
  ≡⟨⟩
    suc ((suc (suc (zero))) + (suc (suc (suc (suc (zero))))))
  ≡⟨⟩
    suc (suc ((suc (zero)) + (suc (suc (suc (suc (zero)))))))
  ≡⟨⟩
    suc (suc (suc (zero + (suc (suc (suc (suc (zero))))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc (zero)))))))
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)


_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + zero))
  ≡⟨⟩
    4 + (4 + (4))
  ≡⟨⟩
    12
  ∎

-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)

_^_ : ℕ → ℕ → ℕ
m ^ zero      = suc (zero)
m ^ (suc (n)) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (1))))
  ≡⟨⟩
    3 * (3 * (3 * (3)))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎


_ = 5 ∸ 3
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ = 3 ∸ 5
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0 ∸ 0
  ≡⟨⟩
    0
  ∎


{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

eleven : Bin
eleven = ⟨⟩ I O I I

eleven2 : Bin
eleven2 = ⟨⟩ O O I O I I

inc : Bin → Bin
inc ⟨⟩  = ⟨⟩ I
inc (b O) = b I
inc (⟨⟩ I)  = ⟨⟩ I O
inc (b O I) = b I O
inc (b I I) = (inc (b I)) O


_ : inc ⟨⟩ ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ O I O) ≡ ⟨⟩ O I I
_ = refl

_ : inc (⟨⟩ O I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to2 : ℕ → Bin → Bin
to2 (suc n) b = to2 n (inc b)
to2 zero b = b

to : ℕ → Bin
to n = to2 n (⟨⟩ O)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

from2 : Bin → ℕ →  ℕ → ℕ
from2 ⟨⟩ e n = n
from2 (b O) e n = from2 b (e + 1) n
from2 (b I) e n = from2 b (e + 1) (n + (2 ^ e))


from : Bin → ℕ
from b = from2 b 0 0

_ : from ⟨⟩ ≡  0
_ = refl


_ : from (⟨⟩ O) ≡  0
_ = refl

_ : from (⟨⟩ I) ≡  1
_ = refl

_ : from (⟨⟩ I O) ≡  2
_ = refl

_ : from (⟨⟩ I I) ≡  3
_ = refl

_ : from (⟨⟩ I O O) ≡  4
_ = refl

_ : from (⟨⟩ I O I) ≡  5
_ = refl

_ : from (⟨⟩ O I O I) ≡  5
_ = refl
