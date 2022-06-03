module clahey.maths.Category where
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
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

fid : {l : Level} → Set l → Set l
fid a = a

    
record Category (o l e : Level) : Set (lsuc (o ⊔ l ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set l
    _≈_ : ∀ {A B : Obj} → Rel (A ⇒ B) e
    isEquivalence : ∀ {A B} → IsEquivalence {l} {e} (_≈_ {A} {B})
    id : {A : Obj} → A ⇒ A
    _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C
    assoc : {A B C D : Obj} → {f : C ⇒ D} → {g : B ⇒ C} → {h : A ⇒ B} → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    sym-assoc : {A B C D : Obj} → {f : C ⇒ D} → {g : B ⇒ C} → {h : A ⇒ B} → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    idˡ : {A B : Obj} → {f : A ⇒ B} → id ∘ f ≈ f
    idʳ : {A B : Obj} → {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈ : {A B C : Obj} {f₁ f₂ : B ⇒ C} {g₁ g₂ : A ⇒ B} → f₁ ≈ f₂ → g₁ ≈ g₂ → f₁ ∘ g₁ ≈ f₂ ∘ g₂

  o-level : Level
  o-level = o

  l-level : Level
  l-level = l

  e-level : Level
  e-level = e

  dom : {A B : Obj} → A ⇒ B → Obj
  dom {A} {_} m = A

  cod : {A B : Obj} → A ⇒ B → Obj
  cod  {_} {B} m = B


private
  variable
    o l e : Level

infix 10  _[_⇒_] _[_≈_] _[_∘_]

_[_⇒_] : (c : Category o l e) → (A B : Category.Obj c) → Set l
_[_⇒_] = Category._⇒_

_[_≈_] : (c : Category o l e) → {A B : Category.Obj c} → Rel (c [ A ⇒ B ]) (Category.e-level c)
_[_≈_] =  Category._≈_

_[_∘_] : (c : Category o l e) → {A B C : Category.Obj c} → c [ B ⇒ C ] → c [ A ⇒ B ] → c [ A ⇒ C ]
_[_∘_] = Category._∘_

sym : {c : Category o l e} → {A B : Category.Obj c} → {f g : c [ A ⇒ B ] } → c [ f ≈ g ] → c [ g ≈ f ]
sym {c = c} f≈g = IsEquivalence.sym (Category.isEquivalence c) f≈g

trans : {c : Category o l e} → {A B : Category.Obj c} → {f g h : c [ A ⇒ B ]} → c [ f ≈ g ] → c [ g ≈ h ] → c [ f ≈ h ]
trans {c = c} = IsEquivalence.trans (Category.isEquivalence c)

refl : {c : Category o l e} → {A B : Category.Obj c} → {f : c [ A ⇒ B ]} → c [ f ≈ f ]
refl {c = c} = IsEquivalence.refl (Category.isEquivalence c)


infix  1 ≈-begin_
infixr 2 _≈⟨_⟩_
infix  3 _≈-∎

≈-begin_ : {c : Category o l e} → {A B : Category.Obj c} → {f g : c [ A ⇒ B ]} → c [ f ≈ g ] → c [ f ≈ g ]
≈-begin_ f≈g = f≈g

_≈⟨_⟩_ : {c : Category o l e} → {A B : Category.Obj c} → {g h : c [ A ⇒ B ]} → (f : c [ A ⇒ B ]) → c [ f ≈ g ] → c [ g ≈ h ] → c [ f ≈ h ]
_≈⟨_⟩_ {c = c} f = trans {c = c}

_≈-∎ : {c : Category o l e} → {A B : Category.Obj c} → (f : c [ A ⇒ B ]) → c [ f ≈ f ]
_≈-∎ {c = c} f = refl {c = c}

congˡ : {c : Category o l e} → {A B C : Category.Obj c} → (f : c [ B ⇒ C ]) → {g₁ g₂ : c [ A ⇒ B ]} → c [ g₁ ≈ g₂ ] → c [ (c [ f ∘ g₁ ]) ≈ (c [ f ∘ g₂ ]) ]
congˡ {c = c} f g≈g = Category.∘-resp-≈ c (refl {c = c}) g≈g

congʳ : {c : Category o l e} → {A B C : Category.Obj c} → {f₁ f₂ : c [ B ⇒ C ]} → (g : c [ A ⇒ B ]) →  c [ f₁ ≈ f₂ ] → c [ (c [ f₁ ∘ g ]) ≈ (c [ f₂ ∘ g ]) ]
congʳ {c = c} g f≈f = Category.∘-resp-≈ c f≈f (refl {c = c})

record Functor {o l e o' l' e' : Level} (c : Category o l e) (c' : Category o' l' e') : Set (lsuc (o ⊔ l ⊔ e ⊔ o' ⊔ l' ⊔ e')) where
  field
    obj : Category.Obj c → Category.Obj c'
    morph : {A B : Category.Obj c} → c [ A ⇒ B ] → c' [ obj A ⇒ obj B ]
    identity : ∀ {A : Category.Obj c} → c' [ morph {A} {A} (Category.id c) ≈ Category.id c' ]
    resp-∘ : ∀ {A B C : Category.Obj c} → {f : c [ B ⇒ C ]} → {g : c [ A ⇒ B ]}
      → c' [ morph {A} {C} (c [ f ∘ g ]) ≈ c' [ morph {B} {C} f ∘ morph {A} {B} g ] ]
