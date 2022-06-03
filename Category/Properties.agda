module clahey.maths.Category.Properties where

open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import clahey.maths.Category using (Category; _[_⇒_]; _[_∘_]; _[_≈_]; ≈-begin_; _≈⟨_⟩_; _≈-∎; congˡ; congʳ; sym; trans; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (IsEquivalence)

epi : {o l e : Level } → {c : Category o l e} → { A B : Category.Obj c } → (g : c [ A ⇒ B ]) → Set (o ⊔ l ⊔ e)
epi {c = c} {B = B} g = ∀ { C : Category.Obj c } → (f₁ f₂ : c [ B ⇒ C ]) → c [ (c [ f₁ ∘ g ]) ≈ (c [ f₂ ∘ g ]) ] → c [ f₁ ≈ f₂ ]

mono : {o l e : Level } → {c : Category o l e} → { B C : Category.Obj c } → (f : c [ B ⇒ C ]) → Set (o ⊔ l ⊔ e)
mono {c = c} {B = B} f = ∀ { A : Category.Obj c } → (g₁ g₂ : c [ A ⇒ B ]) → c [ (c [ f ∘ g₁ ]) ≈ (c [ f ∘ g₂ ]) ] → c [ g₁ ≈ g₂ ]

iso : {o l e : Level } → {c : Category o l e} → { A B : Category.Obj c } → (f : c [ A ⇒ B ]) → (g : c [ B ⇒ A ]) → Set e
iso {c = c} f g = (c [ (c [ f ∘ g ]) ≈ (Category.id c) ]) × (c [ (c [ g ∘ f ]) ≈ Category.id c ])

iso→epi : {o l e : Level } → {c : Category o l e} → { A B : Category.Obj c } → (f : c [ A ⇒ B ]) → (g : c [ B ⇒ A ]) → iso {o} {l} {e} {c} {A} {B} f g → epi {o} {l} {e} {c} {B} {A} g
iso→epi {c = c} f g (_ , g∘f≈id) f₁ f₂ f₁∘g≈f₂∘g =
  -- f₁
  trans {c = c} (sym {c = c} (Category.idʳ c))
  -- c [ f₁ ∘ Category.id c ]
  (trans {c = c} (congˡ {c = c}  f₁ (sym {c = c} g∘f≈id))
  -- c [ f₁ ∘ c [ g ∘ f ] ]
  (trans {c = c} (Category.sym-assoc c)
  -- c [ c [ f₁ ∘ g ] ∘ f ]
  (trans {c = c} (congʳ {c = c} f f₁∘g≈f₂∘g)
  -- c [ c [ f₂ ∘ g ] ∘ f ]
  (trans {c = c} (Category.assoc c)
  -- c [ f₂ ∘ c [ g ∘ f ] ]
  (trans {c = c} (congˡ {c = c} f₂ g∘f≈id)
  -- c [ f₂ ∘ Category.id c ]
                 (Category.idʳ c))))))
  -- f₂

--  ≈-begin
--    f₁
--  ≈⟨ sym {c = c} (Category.idʳ c {f = f₁}) ⟩
--    c [ f₁ ∘ Category.id c ]
--  ≈⟨ congˡ {c = c} f₁ (sym {c = c} g∘f≈id) ⟩
--    c [ f₁ ∘ c [ g ∘ f ] ]
--  ≈⟨ Category.sym-assoc c ⟩
--    c [ c [ f₁ ∘ g ] ∘ f ]
--  ≈⟨ congʳ {c = c}  f f₁∘g≈f₂∘g ⟩
--    c [ c [ f₂ ∘ g ] ∘ f ]
--  ≈⟨ Category.assoc c ⟩
--    c [ f₂ ∘ c [ g ∘ f ] ]
--  ≈⟨ congˡ {c = c}  f₂ g∘f≈id ⟩
--    c [ f₂ ∘ Category.id c ]
--  ≈⟨ Category.idʳ c ⟩
--    f₂
--  ≈-∎


iso→mono : {o l e : Level } → {c : Category o l e} → { A B : Category.Obj c } → (f : c [ A ⇒ B ]) → (g : c [ B ⇒ A ]) → iso {o} {l} {e} {c} {A} {B} f g → mono {o} {l} {e} {c} {A} {B} f
iso→mono {c = c} f g (_ , g∘f≈id) g₁ g₂ f∘g₁≈f∘g₂ =
  -- g₁
  trans {c = c} (sym {c = c} (Category.idˡ c))
  -- c [ Category.id c ∘ g₁ ]
  (trans {c = c} (congʳ {c = c}  g₁ (sym {c = c} g∘f≈id))
  -- c [ c [ g ∘ f ] ∘ g₁ ]
  (trans {c = c} (Category.assoc c)
  -- c [ g ∘ c [ f ∘ g₁ ] ]
  (trans {c = c} (congˡ {c = c} g f∘g₁≈f∘g₂)
  -- c [ g ∘ c [ f ∘ g₂ ] ]
  (trans {c = c} (Category.sym-assoc c)
  -- c [ c [ g ∘ f ] ∘ g₂ ]
  (trans {c = c} (congʳ {c = c} g₂ g∘f≈id)
  -- c [ Category.id c ∘ g₂ ]
                 (Category.idˡ c))))))
  -- f₂

iso-sym : {o l e : Level } → {c : Category o l e} → { A B : Category.Obj c } → (f : c [ A ⇒ B ]) → (g : c [ B ⇒ A ]) → iso {o} {l} {e} {c} {A} {B} f g → iso {o} {l} {e} {c} {B} {A} g f
iso-sym f g (f∘g≈id , g∘f≈id) = (g∘f≈id , f∘g≈id)
