module clahey.maths.Category where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec)
open import Relation.Binary using (Rel; IsPreorder)

record Monoid {l : Level} : Set (lsuc l) where
  field
    Underlying : Set l
    _∘_ : Underlying → Underlying → Underlying
    ε : Underlying
    assoc : (f g h : Underlying) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    idˡ : {f : Underlying} → ε ∘ f ≡ f
    idʳ : {f : Underlying} → f ∘ ε ≡ f
    
record Category {l l₂ : Level} : Set (lsuc (l ⊔ l₂)) where
  field
    Obj : Set l
    Mor : Obj → Obj → Set l₂
    id : (a : Obj) → Mor a a
    _∘_ : {A B C : Obj} → Mor B C → Mor A B → Mor A C
    assoc : {A B C D : Obj} → {f : Mor C D} → {g : Mor B C} → {h : Mor A B} → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    idˡ : {A B : Obj} → {f : Mor A B} → (id B) ∘ f ≡ f
    idʳ : {A B : Obj} → {f : Mor A B} → f ∘ (id A) ≡ f

  dom : {A B : Obj} → Mor A B → Obj
  dom {A} {_} m = A

  cod : {A B : Obj} → Mor A B → Obj
  cod  {_} {B} m = B

data One-Obj : Set where
  𝟙 : One-Obj
data One-Mor-𝟙-𝟙 : Set where
  id₁ : One-Mor-𝟙-𝟙
One-∘ : {l : Level} → One-Mor-𝟙-𝟙 → One-Mor-𝟙-𝟙 → One-Mor-𝟙-𝟙
One-∘ id₁ id₁ = id₁


One-idʳ :  {A B : One-Obj} {f : One-Mor-𝟙-𝟙} → id₁ ≡ f
One-idʳ {𝟙} {𝟙} {id₁} = refl

One-Mor : One-Obj → One-Obj → Set
One-Mor 𝟙 𝟙 = One-Mor-𝟙-𝟙

One-Category : {l : Level} → Category {lzero} {lzero}
One-Category = record { Obj = One-Obj
--                      ; Mor = One-Mor
                      ; Mor = λ 𝟙 𝟙 → One-Mor-𝟙-𝟙
                      ; id = λ 𝟙 → One-Mor-𝟙-𝟙.id₁
                      ; _∘_ = λ id₁ id₁ → id₁
                      ; assoc = refl
                      ; idˡ = refl
                      ; idʳ = λ {A} {B} {f} → One-idʳ {A} {B} {f}
                      }

Nat-po-assoc : {a b c d : ℕ} {f : c ≤ d} {g : b ≤ c} {h : a ≤ b} → ≤-trans h (≤-trans g f) ≡ ≤-trans (≤-trans h g) f
Nat-po-assoc {zero} {_} {_} {_} {_} {_} {z≤n} = refl
Nat-po-assoc {suc a} {suc b} {suc c} {suc d} {s≤s f} {s≤s g} {s≤s h} = cong s≤s Nat-po-assoc

Nat-po-idˡ : {a b : ℕ} {f : a ≤ b} → ≤-trans f (≤-reflexive refl) ≡ f
Nat-po-idˡ {zero} {_} {z≤n} = refl
Nat-po-idˡ {suc a} {suc b} {s≤s f} = cong s≤s Nat-po-idˡ

Nat-po-idʳ : {a b : ℕ} {f : a ≤ b} → ≤-trans (≤-reflexive refl) f ≡ f
Nat-po-idʳ {zero} {_} {z≤n} = refl
Nat-po-idʳ {suc a} {suc b} {s≤s f} = cong s≤s Nat-po-idʳ

Nat-po-Category : Category
Nat-po-Category = record { Obj = ℕ
                         ; Mor = λ m n → m ≤ n
                         ; id = λ n → ≤-reflexive {n} refl
                         ; _∘_ = λ b≤c a≤b → ≤-trans a≤b b≤c
                         ; assoc = Nat-po-assoc
                         ; idˡ = Nat-po-idˡ
                         ; idʳ = Nat-po-idʳ
                         }

data Monoid-Obj {l : Level} : Set where
  monoid-Singleton : Monoid-Obj

monoid-Category : {l : Level} → Monoid {l} → Category {lzero} {l}
monoid-Category record { Underlying = Underlying
                       ; _∘_ = _∘_
                       ; ε = ε
                       ; assoc = assoc
                       ; idˡ = idˡ
                       ; idʳ = idʳ
                       } = record
                             { Obj = Monoid-Obj {lzero}
                             ; Mor = λ _ _ → Underlying
                             ; id = λ _ → ε
                             ; _∘_ = _∘_
                             ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc f g h
                             ; idˡ = λ {_} {_} {f} → idˡ {f}
                             ; idʳ = λ {_} {_} {f} → idʳ {f}
                             }

Nat-monoid-+ : Monoid {lzero}
Nat-monoid-+ = record
                 { Underlying = ℕ
                 ; _∘_ = λ a b → a + b
                 ; ε = 0
                 ; assoc = +-assoc
                 ; idˡ = λ {a} → +-identityˡ a
                 ; idʳ = λ {a} → +-identityʳ a
                 }

Nat-category-+ : Category {lzero} {lzero}
Nat-category-+ = monoid-Category Nat-monoid-+

Nat-monoid-* : Monoid {lzero}
Nat-monoid-* = record
                 { Underlying = ℕ
                 ; _∘_ = λ a b → a * b
                 ; ε = 1
                 ; assoc = *-assoc
                 ; idˡ = λ {a} → *-identityˡ a
                 ; idʳ = λ {a} → *-identityʳ a
                 }

Nat-category-* : Category {lzero} {lzero}
Nat-category-* = monoid-Category Nat-monoid-*

-- module _  {A : Set} {ℓ : Level} where
--   module _ {_≈_ : Rel A ℓ} {_∼_ : Rel A ℓ} where
--     category : IsPreorder _≈_ _∼_ → Category
--     category isPreorder = record { Obj = A
--                                  ; Mor = λ a b → _~_ a b
--                                  ; id = ?
--                                  ; _∘_ = ?
--                                  ; assoc = ?
--                                  }
-- Error message
-- /home/clahey/clahey/maths/Category.agda:135,50-57
-- Could not parse the application _~_ a b
-- Operators used in the grammar:
--   None
-- when scope checking _~_ a b

-- preorder-Category : {A : Set} → {ℓ : Level} → {_∼_ : Rel A ℓ} → IsPreorder _≡_ _~_ → Category
-- preorder-Category  = ?
-- Error message 
-- /home/clahey/clahey/maths/Category.agda:147,65-83
-- Could not parse the application IsPreorder _≡_ _~_
-- Operators used in the grammar:
-- when scope checking IsPreorder _≡_ _~_
