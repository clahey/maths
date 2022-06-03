module clahey.maths.Category.Examples.Set where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import clahey.maths.Category using (Category)
open import clahey.maths.Group using (Group; Group-Morphism)
open import clahey.maths.Monoid using (Monoid)
open import clahey.maths.Monoid.Examples using (Nat-monoid-+; Nat-monoid-*)
open import Relation.Binary using (Rel; IsPreorder; IsDecEquivalence; IsEquivalence)
open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Unit using (⊤; tt)
open import Function.Base using (flip)

Set-Category : { l : Level } → Category {lsuc l} {l} {l}
Set-Category {l} = record
                     { Obj = Set l
                     ; _⇒_ = λ A B → A → B
                     ; _≈_ = λ {A} {B} f g → ∀ (a : A) → f a ≡ g a
                     ; isEquivalence = record { refl = λ a → refl ; sym = λ fa≡ga a → sym (fa≡ga a) ; trans = λ fa≡ga ga≡ha a → trans (fa≡ga a) (ga≡ha a) }
                     ; id = Function.Base.id
                     ; _∘_ = λ f g a → f (g a)
                     ; assoc = λ a → refl
                     ; sym-assoc = λ a → refl
                     ; idˡ = λ a → refl
                     ; idʳ = λ a → refl
                     ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} f≈g h≈i a → trans (cong f (h≈i a)) (f≈g (i a))
                     }

-- inj : { l : Level } → {A B : Set l} → (A → B) → Set l
-- inj {A = A} f = (∀ a₁ a₂ : A) → f a₁ ≡ f a₂ → a₁ ≡ a₂

