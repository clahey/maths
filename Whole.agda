module clahey.maths.Whole where

open import Data.Nat using (ℕ; _≤_; s≤s; z≤n; _≥_; suc; zero)
open import Data.Nat.Properties using (⊔-identityʳ)
open import Relation.Binary.PropositionalEquality using (cong; _≡_; refl; sym)

data ℕ⁺ : Set where
  one : ℕ⁺
  suc : ℕ⁺ → ℕ⁺

toℕ : ℕ⁺ → ℕ
toℕ one = 1
toℕ (suc n) = suc (toℕ n)

fromℕ : (n : ℕ) → (n ≥ 1) → ℕ⁺
fromℕ (suc zero) n≥1 = one
fromℕ (suc (suc n)) n≥1 = suc (fromℕ (suc n) (s≤s z≤n))

toℕ≥1 : ∀ (n : ℕ⁺) → toℕ n ≥ 1
toℕ≥1 one = s≤s z≤n
toℕ≥1 (suc n) = s≤s z≤n

fromℕ∘toℕ' : ∀ (n : ℕ⁺) → fromℕ (suc (toℕ n)) (s≤s z≤n) ≡ suc n
fromℕ∘toℕ' one = refl
fromℕ∘toℕ' (suc n) = cong suc (fromℕ∘toℕ' n)

fromℕ∘toℕ : ∀ (n : ℕ⁺) → fromℕ (toℕ n) (toℕ≥1 n) ≡ n
fromℕ∘toℕ one = refl
fromℕ∘toℕ (suc n) = fromℕ∘toℕ' n

toℕ∘fromℕ' : ∀ (n : ℕ) → (n≥1 : n ≥ 1) → toℕ (fromℕ (suc n) (s≤s z≤n)) ≡ suc n
toℕ∘fromℕ' (suc zero) n≥1 = refl
toℕ∘fromℕ' (suc (suc n)) n≥1 = cong suc (toℕ∘fromℕ' (suc n) (s≤s z≤n))

toℕ∘fromℕ : ∀ (n : ℕ) → (n≥1 : n ≥ 1) → toℕ (fromℕ n n≥1) ≡ n
toℕ∘fromℕ (suc zero) n≥1 = refl
toℕ∘fromℕ (suc (suc n)) n≥1 = cong suc (toℕ∘fromℕ (suc n) (s≤s z≤n))

_⊔_ : ℕ⁺ → ℕ⁺ → ℕ⁺
one ⊔ n = n
suc m ⊔ one = suc m
suc m ⊔ suc n = suc (m ⊔ n)

toℕ⊔toℕ : (m n : ℕ⁺) → toℕ (m ⊔ n) ≡ Data.Nat._⊔_ (toℕ m) (toℕ n)
toℕ⊔toℕ one one = refl
toℕ⊔toℕ one (suc n) = refl
toℕ⊔toℕ (suc m) one = cong suc (sym (⊔-identityʳ (toℕ m)))
toℕ⊔toℕ (suc m) (suc n) = cong suc (toℕ⊔toℕ m n)
