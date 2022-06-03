module clahey.maths.Category.Examples where

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

preorder-Category : {a l e : Level} → {A : Set a} → {_~_ : Rel A l} → IsPreorder _≡_ _~_ → Category {a} {l} {lzero}
preorder-Category {a} {l} {e} {A} {_~_} record { isEquivalence = isEquivalence
                                               ; reflexive = reflexive
                                               ; trans = trans } = record
                                                           { Obj = A
                                                           ; _⇒_ = λ a b → a ~ b
                                                           ; _≈_ = λ _ _ → ⊤
                                                           ; id = reflexive refl
                                                           ; _∘_ = flip trans
                                                           ; assoc = tt
                                                           ; sym-assoc = tt
                                                           ; idˡ = tt
                                                           ; idʳ = tt
                                                           }

Group-Category : { l : Level } → Category {lsuc l} {l} {l}
Group-Category {l} = record
                       { Obj = Group {l}
                       ; _⇒_ = λ A B → Group-Morphism A B
                       ; _≈_ = λ {A} {B} f g → ∀ (a : Group.Underlying A) → Group-Morphism.apply f a ≡ Group-Morphism.apply g a
                       ; isEquivalence = {!!}
                       ; id = {!!}
                       ; _∘_ = {!!}
                       ; assoc = {!!}
                       ; sym-assoc = {!!}
                       ; idˡ = {!!}
                       ; idʳ = {!!}
                       ; ∘-resp-≈ = {!!}
                       }

data Monoid-Obj {l : Level} : Set where
  monoid-Singleton : Monoid-Obj

monoid-Category : {l e : Level} → Monoid {l} {e} → Category {lzero} {l} {e}
monoid-Category record { Underlying = Underlying
                       ; _≈_ = _≈_
                       ; isEquivalence = isEquivalence
                       ; _∘_ = _∘_
                       ; ε = ε
                       ; assoc = assoc
                       ; sym-assoc = sym-assoc
                       ; idˡ = idˡ
                       ; idʳ = idʳ
                       ; ∘-resp-≈ = ∘-resp-≈
                       } = record
                             { Obj = Monoid-Obj {lzero}
                             ; _⇒_ = λ _ _ → Underlying
                             ; _≈_ = _≈_
                             ; isEquivalence = isEquivalence
                             ; id = λ {_} → ε
                             ; _∘_ = _∘_
                             ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc {f} {g} {h}
                             ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → sym-assoc {f} {g} {h}
                             ; idˡ = λ {_} {_} {f} → idˡ {f}
                             ; idʳ = λ {_} {_} {f} → idʳ {f}
                             ; ∘-resp-≈ = λ {A} {B} {C} → ∘-resp-≈
                             }

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
--                      ; _⇒_ = One-Mor
                      ; _⇒_ = λ 𝟙 𝟙 → One-Mor-𝟙-𝟙
                      ; _≈_ = _≡_
                      ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence
                      ; id = λ {_} → One-Mor-𝟙-𝟙.id₁
                      ; _∘_ = λ id₁ id₁ → id₁
                      ; assoc = refl
                      ; sym-assoc = refl
                      ; idˡ = refl
                      ; idʳ = λ {A} {B} {f} → One-idʳ {A} {B} {f}
                      ; ∘-resp-≈ = λ _ g → g
                      }

Nat-assoc : {a b c d : ℕ} {f : c ≤ d} {g : b ≤ c} {h : a ≤ b} → ≤-trans h (≤-trans g f) ≡ ≤-trans (≤-trans h g) f
Nat-assoc {a = zero} {h = z≤n} = refl
Nat-assoc {suc _} {suc _} {suc _} {suc _} {s≤s _} {s≤s _} {s≤s _} = cong s≤s Nat-assoc

Nat-idˡ : {a b : ℕ} {f : a ≤ b} → ≤-trans f (≤-reflexive refl) ≡ f
Nat-idˡ {a = zero} {f = z≤n} = refl
Nat-idˡ {suc _} {suc _} {s≤s _} = cong s≤s Nat-idˡ

Nat-idʳ : {a b : ℕ} {f : a ≤ b} → ≤-trans (≤-reflexive refl) f ≡ f
Nat-idʳ {a = zero} {f = z≤n} = refl
Nat-idʳ {suc _} {suc _} {s≤s _} = cong s≤s Nat-idʳ

Nat-Category : Category
Nat-Category = record { Obj = ℕ
                         ; _⇒_ = λ m n → m ≤ n
                         ; _≈_ = _≡_
                         ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence
                         ; id = λ {n} → ≤-reflexive {n} refl
                         ; _∘_ = λ b≤c a≤b → ≤-trans a≤b b≤c
                         ; assoc = Nat-assoc
                         ; sym-assoc = sym Nat-assoc
                         ; idˡ = Nat-idˡ
                         ; idʳ = Nat-idʳ
                         ; ∘-resp-≈ = ∘-resp-≈
                         }
  where
    ∘-resp-≈ : {a b c : ℕ} → {f g : b ≤ c} → {h i : a ≤ b} → f ≡ g → h ≡ i → ≤-trans h f ≡ ≤-trans i g
    ∘-resp-≈ {f = f} {g = .f} {h = h} {i = .h} refl refl = refl

Nat-category-+ : Category {lzero} {lzero}
Nat-category-+ = monoid-Category Nat-monoid-+

Nat-category-* : Category {lzero} {lzero}
Nat-category-* = monoid-Category Nat-monoid-*
