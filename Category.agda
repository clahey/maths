module clahey.maths.Category where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Level using (Lift; lift)
open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; _++_; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Rel; IsPreorder; IsDecEquivalence; IsEquivalence)
open import Relation.Binary.Definitions using (Decidable)
open import Data.Bool using (true; false)
open import Function.Base using (flip)


record Monoid {l e : Level} : Set (lsuc (l ⊔ e)) where
  infix  4 _≈_
  infixr 9 _∘_
  field
    Underlying : Set l
    _≈_ : Rel Underlying e
    isEquivalence : IsEquivalence _≈_
    _∘_ : Underlying → Underlying → Underlying
    ε : Underlying
    assoc : {f g h : Underlying} → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    sym-assoc : {f g h : Underlying} → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    idˡ : {f : Underlying} → ε ∘ f ≈ f
    idʳ : {f : Underlying} → f ∘ ε ≈ f
    ∘-resp-≈ : {f g h i : Underlying} → f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i
    
record Category {o l e : Level} : Set (lsuc (o ⊔ l ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set l
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e
    isEquivalence : IsEquivalence {l} {e} _≈_
    id : {a : Obj} → a ⇒ a
    _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C
    assoc : {A B C D : Obj} → {f : C ⇒ D} → {g : B ⇒ C} → {h : A ⇒ B} → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    sym-assoc : {A B C D : Obj} → {f : C ⇒ D} → {g : B ⇒ C} → {h : A ⇒ B} → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    idˡ : {A B : Obj} → {f : A ⇒ B} → id ∘ f ≈ f
    idʳ : {A B : Obj} → {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈ : {A B C : Obj} {f g : B ⇒ C} {h i : A ⇒ B} → f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i

  dom : {A B : Obj} → A ⇒ B → Obj
  dom {A} {_} m = A

  cod : {A B : Obj} → A ⇒ B → Obj
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

Nat-monoid-+ : Monoid {lzero}
Nat-monoid-+ = record
                 { Underlying = ℕ
                 ; _≈_ = _≡_
                 ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                 ; _∘_ = _+_
                 ; ε = 0
                 ; assoc = λ {a} {b} {c} → +-assoc a b c
                 ; sym-assoc = λ {a} {b} {c} → sym (+-assoc a b c)
                 ; idˡ = +-identityˡ _
                 ; idʳ = +-identityʳ _
                 ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    ∘-resp-≈ : {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

Nat-category-+ : Category {lzero} {lzero}
Nat-category-+ = monoid-Category Nat-monoid-+

Nat-monoid-* : Monoid {lzero}
Nat-monoid-* = record
                 { Underlying = ℕ
                 ; _≈_ = _≡_
                 ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                 ; _∘_ = _*_
                 ; ε = 1
                 ; assoc = λ {a} {b} {c} → *-assoc a b c
                 ; sym-assoc = λ {a} {b} {c} → sym (*-assoc a b c)
                 ; idˡ = *-identityˡ _
                 ; idʳ = *-identityʳ _
                 ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    ∘-resp-≈ : {a b c d : ℕ} → a ≡ b → c ≡ d → a * c ≡ b * d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

Nat-category-* : Category {lzero} {lzero}
Nat-category-* = monoid-Category Nat-monoid-*

List-monoid-++ : {l : Level} → (A : Set l) → Monoid {l} {l}
List-monoid-++ A = record
                     { Underlying = List A
                     ; _≈_ = _≡_
                     ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                     ; _∘_ = _++_
                     ; ε = []
                     ; assoc = λ {f} {g} {h} → assoc {f} {g} {h}
                     ; sym-assoc = λ {f} {g} {h} → sym (assoc {f} {g} {h})
                     ; idˡ = refl
                     ; idʳ = idʳ
                     ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    assoc : {f g h : List A} → (f ++ g) ++ h ≡ f ++ g ++ h
    assoc {[]} {g} {h} = refl
    assoc {a ∷ f} {g} {h} = cong (a ∷_) (assoc {f} {g} {h})

    idʳ : {f : List A} → f ++ [] ≡ f
    idʳ {[]} = refl
    idʳ {a ∷ f} = cong (a ∷_) (idʳ {f})

    ∘-resp-≈ : {a b c d : List A} → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

List-Pointwise-monoid-++ : {l e : Level} → (A : Set l) → (_≈_ : Rel A e) → IsEquivalence _≈_ → Monoid {l} {l ⊔ e}
List-Pointwise-monoid-++ A _≈_ isEquivalence = record
                     { Underlying = List A
                     ; _≈_ = Pointwise _≈_
                     ; isEquivalence = Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence
                     ; _∘_ = _++_
                     ; ε = []
                     ; assoc = λ {f} {g} {h} → assoc {f} {g} {h}
                     ; sym-assoc = λ {f} {g} {h} → IsEquivalence.sym (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence) (assoc {f} {g} {h})
                     ; idˡ = IsEquivalence.refl ((Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence))
                     ; idʳ = idʳ
                     ; ∘-resp-≈ = ∘-resp-≈
                     }
  where
    assoc : {f g h : List A} → Pointwise _≈_ ((f ++ g) ++ h) (f ++ g ++ h)
    assoc {[]} {g} {h} = IsEquivalence.refl (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence)
    assoc {a ∷ f} {g} {h} = isEquivalence .IsEquivalence.refl Pointwise.∷ assoc {f} {g} {h}

    idʳ : {f : List A} → Pointwise _≈_ (f ++ []) f
    idʳ {[]} = IsEquivalence.refl (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence)
    idʳ {a ∷ f} =  isEquivalence .IsEquivalence.refl Pointwise.∷ idʳ {f}

    ∘-resp-≈ : {a b c d : List A} → Pointwise _≈_ a b → Pointwise _≈_ c d → Pointwise _≈_ (a ++ c) (b ++ d)
    ∘-resp-≈ {a} {b} {c} {d} a≈b c≈d = Data.List.Relation.Binary.Pointwise.++⁺ a≈b c≈d

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
-- Error message 
-- /home/clahey/clahey/maths/Category.agda:147,65-83
-- Could not parse the application IsPreorder _≡_ _~_
-- Operators used in the grammar:
-- when scope checking IsPreorder _≡_ _~_
