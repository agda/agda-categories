{-# OPTIONS --safe --without-K #-}

module Categories.Category.Monoidal.Instance.Rels where

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Instance.Rels
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Relation.Binary.Pointwise using (⊎-setoid; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Function.Base using (case_of_)
open import Level using (_⊔_; Lift; lift)
open import Relation.Binary.Bundles using (Setoid)

module _ {o ℓ} where

  Rels-Cartesian : Cartesian (Rels o (o ⊔ ℓ))
  Rels-Cartesian = record
    { terminal = record
      { ⊤ = record
        { Carrier = ⊥
        ; _≈_ = λ _ _ → ⊤
        }
      ; ⊤-is-terminal = record
        { ! = λ {A} → record
          { fst = λ { _ () }
          ; snd = record
            { fst = λ { {()} }
            ; snd = λ { {_} {()} }
            }
          }
        ; !-unique = λ {A} f → record
          { fst = λ { {_} {()} }
          ; snd = λ { {_} {()} }
          }
        }
      }
    ; products = record
      { product = λ {A} {B} → record
        { A×B = ⊎-setoid A B
        ; π₁ = record
          { fst = [ Setoid._≈_ A , (λ _ _ → ⊥) ]′
          ; snd = record
            { fst = λ { (inj₁ p) q → Setoid.trans A (Setoid.sym A p) q }
            ; snd = λ { {inj₁ _} p q → Setoid.trans A q p }
            }
          }
        ; π₂ = record
          { fst = [ (λ _ _ → ⊥) , Setoid._≈_ B ]′
          ; snd = record
            { fst = λ { (inj₂ p) q → Setoid.trans B (Setoid.sym B p) q }
            ; snd = λ { {inj₂ _} p q → Setoid.trans B q p }
            }
          }
        ; ⟨_,_⟩ = λ L R → record
          { fst = λ c → [ proj₁ L c , proj₁ R c ]′
          ; snd = record
            { fst = λ
              { {inj₁ _} → proj₁ (proj₂ L)
              ; {inj₂ _} → proj₁ (proj₂ R)
              }
            ; snd = λ
              { (inj₁ p) → proj₂ (proj₂ L) p
              ; (inj₂ p) → proj₂ (proj₂ R) p
              }
            }
          }
        ; project₁ = λ {_} {h} {i} → record
          { fst = λ { (inj₁ _ , xha , a≈y) → proj₂ (proj₂ h) a≈y xha }
          ; snd = λ xhy → inj₁ _ , xhy , Setoid.refl A
          }
        ; project₂ = λ {C} {h} {i} → record
          { fst = λ { (inj₂ a , xia , a≈y) → proj₂ (proj₂ i) a≈y xia }
          ; snd = λ xiy → inj₂ _ , xiy , Setoid.refl B
          }
        ; unique = λ {C} {h} {i} {j} → λ
          { (h;π₁⇒i , i⇒h;π₁) (h;π₂⇒j , j⇒h;π₂) → record
            { fst = λ
              { {x} {inj₁ y} xiy → case i⇒h;π₁ xiy of λ { (inj₁ _ , xhm , m≈y) → proj₂ (proj₂ h) (inj₁ m≈y) xhm }
              ; {x} {inj₂ y} xjy → case j⇒h;π₂ xjy of λ { (inj₂ _ , xhm , m≈y) → proj₂ (proj₂ h) (inj₂ m≈y) xhm }
              }
            ; snd = λ
              { {x} {inj₁ y} xhy → h;π₁⇒i (_ , xhy , Setoid.refl A)
              ; {x} {inj₂ y} xhy → h;π₂⇒j (_ , xhy , Setoid.refl B)
              }
            }
          }
        }
      }
    }

  Rels-Monoidal : Monoidal (Rels o ℓ)
  Rels-Monoidal = monoidalHelper _ record
    { ⊗ = record
      { F₀ = λ { (A , B) → ×-setoid A B }
      ; F₁ = λ
        { (R , S) → record
          { fst = λ { (a , b) (c , d) → proj₁ R a c × proj₁ S b d }
          ; snd = record
            { fst = λ { (b≈c , y≈z) (bRa , ySx) → proj₁ (proj₂ R) b≈c bRa , proj₁ (proj₂ S) y≈z ySx }
            ; snd = λ { (b≈c , y≈z) (aRb , xSy) → proj₂ (proj₂ R) b≈c aRb , proj₂ (proj₂ S) y≈z xSy }
            }
          }
        }
      ; identity = record
        { fst = λ { (lift a≈b , lift x≈y) → lift (a≈b , x≈y) }
        ; snd = λ { (lift (a≈b , x≈y)) → lift a≈b , lift x≈y }
        }
      ; homomorphism = record
        { fst = λ { ((b , aRb , bTc) , (y , xSy , yUz)) → (b , y) , (aRb , xSy) , (bTc , yUz) }
        ; snd = λ { ((b , y) , (aRb , xSy) , (bTc , yUz)) → (b , aRb , bTc) , (y , xSy , yUz) }
        }
      ; F-resp-≈ = λ
        { {A , X} {B , Y} {f , g} {h , i} (f⇔h , g⇔i) → record
          { fst = λ { (afb , xgy) → proj₁ f⇔h afb , proj₁ g⇔i xgy }
          ; snd = λ { (ahb , xiy) → proj₂ f⇔h ahb , proj₂ g⇔i xiy }
          }
        }
      }
    ; unit = record
      { Carrier = ⊤
      ; _≈_ = λ _ _ → ⊤
      }
    ; unitorˡ = λ {X} → record
      { from = record
        { fst = λ { (_ , x) y → Lift o (Setoid._≈_ X x y) }
        ; snd = record
          { fst = λ { (_ , y≈z) (lift y≈x) → lift (Setoid.trans X (Setoid.sym X y≈z) y≈x) }
          ; snd = λ { y≈z (lift x≈y) → lift (Setoid.trans X x≈y y≈z) }
          }
        }
      ; to = record
        { fst = λ { x (_ , y) → Lift o (Setoid._≈_ X x y) }
        ; snd = record
          { fst = λ { y≈z (lift y≈x) → lift (Setoid.trans X (Setoid.sym X y≈z) y≈x) }
            ; snd = λ { (_ , y≈z) (lift x≈y) → lift (Setoid.trans X x≈y y≈z) }
          }
        }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , lift x≈z , lift z≈y) → lift (_ , Setoid.trans X x≈z z≈y) }
          ; snd = λ { (lift (_ , x≈y)) → _ , lift x≈y , lift (Setoid.refl X) }
          }
        ; isoʳ = record
          { fst = λ { (_ , (lift x≈z , lift z≈y)) → lift (Setoid.trans X x≈z z≈y) }
          ; snd = λ { (lift x≈y) → _ , lift x≈y , lift (Setoid.refl X) }
          }
        }
      }
    ; unitorʳ = λ {X} → record
      { from = record
        { fst = λ { (x , _) y → Lift o (Setoid._≈_ X x y) }
        ; snd = record
          { fst = λ { (y≈z , _) (lift y≈x) → lift (Setoid.trans X (Setoid.sym X y≈z) y≈x) }
          ; snd = λ { y≈z (lift x≈y) → lift (Setoid.trans X x≈y y≈z) }
          }
        }
      ; to = record
        { fst = λ { x (y , _) → Lift o (Setoid._≈_ X x y) }
        ; snd = record
          { fst = λ { y≈z (lift y≈x) → lift (Setoid.trans X (Setoid.sym X y≈z) y≈x) }
          ; snd = λ { (y≈z , _) (lift x≈y) → lift (Setoid.trans X x≈y y≈z) }
          }
        }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , lift x≈z , lift z≈y) → lift (Setoid.trans X x≈z z≈y , _) }
          ; snd = λ { (lift (x≈y , _)) → _ , lift x≈y , lift (Setoid.refl X) }
          }
        ; isoʳ = record
          { fst = λ { (_ , lift x≈z , lift z≈y) → lift (Setoid.trans X x≈z z≈y) }
          ; snd = λ { (lift x≈y) → _ , lift x≈y , lift (Setoid.refl X) }
          }
        }
      }
    ; associator = λ {X} {Y} {Z} → record
      { from = record
        { fst = λ { ((x , y) , z) (x′ , (y′ , z′)) → Lift o (Setoid._≈_ X x x′ × Setoid._≈_ Y y y′ × Setoid._≈_ Z z z′) }
        ; snd = record
          { fst = λ { ((x≈x′ , y≈y′) , z≈z′) (lift (x≈x″ , y≈y″ , z≈z″)) → lift (Setoid.trans X (Setoid.sym X x≈x′) x≈x″ , Setoid.trans Y (Setoid.sym Y y≈y′) y≈y″ , Setoid.trans Z (Setoid.sym Z z≈z′) z≈z″) }
          ; snd = λ { (x′≈x″ , (y′≈y″ , z′≈z″)) (lift (x≈x′ , y≈y′ , z≈z′)) → lift (Setoid.trans X x≈x′ x′≈x″ , Setoid.trans Y y≈y′ y′≈y″ , Setoid.trans Z z≈z′ z′≈z″) }
          }
        }
      ; to = record
        { fst = λ { (x , (y , z)) ((x′ , y′) , z′) → Lift o (Setoid._≈_ X x x′ × Setoid._≈_ Y y y′ × Setoid._≈_ Z z z′) }
        ; snd = record
          { fst = λ { (x′≈x″ , (y′≈y″ , z′≈z″)) (lift (x′≈x , y′≈y , z′≈z)) → lift (Setoid.trans X (Setoid.sym X x′≈x″) x′≈x , Setoid.trans Y (Setoid.sym Y y′≈y″) y′≈y , Setoid.trans Z (Setoid.sym Z z′≈z″) z′≈z) }
          ; snd = λ {xyz} {xyz′} {xyz″} → λ { ((x′≈x″ , y′≈y″) , z′≈z″) (lift (x≈x′ , y≈y′ , z≈z′)) → lift (Setoid.trans X x≈x′ x′≈x″ , Setoid.trans Y y≈y′ y′≈y″ , Setoid.trans Z z≈z′ z′≈z″) }
          }
        }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , (lift (p , q , r) , lift (p′ , q′ , r′))) → lift ((Setoid.trans X p p′ , Setoid.trans Y q q′) , Setoid.trans Z r r′) }
          ; snd = λ { (lift ((p , q) , r)) → _ , lift (p , q , r) , lift (Setoid.refl X , Setoid.refl Y , Setoid.refl Z) }
          }
        ; isoʳ = record
          { fst = λ { (_ , (lift (p , q , r) , lift (p′ , q′ , r′))) → lift (Setoid.trans X p p′ , (Setoid.trans Y q q′ , Setoid.trans Z r r′)) }
          ; snd = λ { (lift (p , (q , r))) → _ , lift (p , q , r) , lift (Setoid.refl X , Setoid.refl Y , Setoid.refl Z ) }
          }
        }
      }
    ; unitorˡ-commute = λ {X} {Y} {R} → record
      { fst = λ { (_ , (_ , xRy′) , lift y′≈y) → _ , lift (Setoid.refl X) , proj₂ (proj₂ R) y′≈y xRy′ }
      ; snd = λ { (_ , lift x≈x′ , x′Ry) → _ , (_ , proj₁ (proj₂ R) (Setoid.sym X x≈x′) x′Ry) , lift (Setoid.refl Y) } 
      }
    ; unitorʳ-commute = λ {X} {Y} {R} → record
      { fst = λ { (_ , (xRy′ , _) , lift y′≈y) →  _ , lift (Setoid.refl X) , proj₂ (proj₂ R) y′≈y xRy′ }
      ; snd = λ { (_ , lift x≈x′ , x′Ry) →  _ , (proj₁ (proj₂ R) (Setoid.sym X x≈x′) x′Ry , _) , lift (Setoid.refl Y) }
      }
    ; assoc-commute = λ {U} {V} {R} {W} {X} {S} {Y} {Z} {T} → record
      { fst = λ { (_ , (((uRv′ , wSx′) , yTz′) , lift (v′≈v , x′≈x , z′≈z))) → _ , lift (Setoid.refl U , Setoid.refl W , Setoid.refl Y) , (proj₂ (proj₂ R) v′≈v uRv′ , (proj₂ (proj₂ S) x′≈x wSx′ , proj₂ (proj₂ T) z′≈z yTz′)) }
      ; snd = λ { (_ , lift (u≈u′ , w≈w′ , y≈y′) , (u′Rv , (w′Sx , y′Tz))) → _ , ((proj₁ (proj₂ R) (Setoid.sym U u≈u′) u′Rv , proj₁ (proj₂ S) (Setoid.sym W w≈w′) w′Sx) , proj₁ (proj₂ T) (Setoid.sym Y y≈y′) y′Tz) , lift (Setoid.refl V , Setoid.refl X , Setoid.refl Z) }
      }
    ; triangle = λ {X} {Y} → record
      { fst = λ { (_ , lift (x≈x″ , _ , y≈y″) , lift x″≈x′ , lift y″≈y′) → lift (Setoid.trans X x≈x″ x″≈x′) , lift (Setoid.trans Y y≈y″ y″≈y′) }
      ; snd = λ { {(x , _) , y} {x′ , y′} (lift x≈x′ , lift y≈y′) → _ ,  lift (x≈x′ , _ , y≈y′) , lift (Setoid.refl X) , lift (Setoid.refl Y) }
      }
    ; pentagon = λ {W} {X} {Y} {Z} → record
      { fst = λ
        { (_ , (_ , ((lift (w≈w‴ , (x≈x‴ , y≈y‴)) , lift z≈z‴) , lift (w‴≈w″ , ((x‴≈x″ , y‴≈y″) , z‴≈z″)))) , lift w″≈w′ , lift (x″≈x′ , y″≈y′ , z″≈z′))
        → _ , lift ((w≈w‴ , x≈x‴) , (y≈y‴ , z≈z‴)) , lift (Setoid.trans W w‴≈w″ w″≈w′ , (Setoid.trans X x‴≈x″ x″≈x′ , (Setoid.trans Y y‴≈y″ y″≈y′ , Setoid.trans Z z‴≈z″ z″≈z′)))
        }
      ; snd = λ
        { (_ , (lift ((w≈w″ , x≈x″) , (y≈y″ , z≈z″)) , lift (w″≈w′ , (x″≈x′ , (y″≈y′ , z″≈z′)))))
        → _ , (_ , ((lift (w≈w″ , x≈x″ , y≈y″) , lift z≈z″) , lift (w″≈w′ , (x″≈x′ , y″≈y′) , z″≈z′))) , lift (Setoid.refl W) , lift (Setoid.refl X , Setoid.refl Y , Setoid.refl Z)
        }
      }
    }

  Rels-Symmetric : Symmetric Rels-Monoidal
  Rels-Symmetric = symmetricHelper _ record
    { braiding = niHelper record
      { η = λ
        { (X , Y) → record
          { fst = λ { (x₁ , y₁) (y₂ , x₂) → Lift o (Setoid._≈_ X x₁ x₂ × Setoid._≈_ Y y₁ y₂) }
          ; snd = record
            { fst = λ { (x₂≈x₃ , y₂≈y₃) (lift (x₂≈x₁ , y₂≈y₁)) → lift (Setoid.trans X (Setoid.sym X x₂≈x₃) x₂≈x₁ , Setoid.trans Y (Setoid.sym Y y₂≈y₃) y₂≈y₁) }
            ; snd = λ { (y₂≈y₃ , x₂≈x₃) (lift (x₁≈x₂ , y₁≈y₂)) → lift (Setoid.trans X x₁≈x₂ x₂≈x₃ , Setoid.trans Y y₁≈y₂ y₂≈y₃) }
            }
          }
        }
      ; η⁻¹ = λ
        { (X , Y) → record
          { fst = λ { (y₁ , x₁) (x₂ , y₂) → Lift o (Setoid._≈_ X x₁ x₂ × Setoid._≈_ Y y₁ y₂) }
          ; snd = record
            { fst = λ { (y₂≈y₃ , x₂≈x₃) (lift (x₂≈x₁ , y₂≈y₁)) → lift (Setoid.trans X (Setoid.sym X x₂≈x₃) x₂≈x₁ , Setoid.trans Y (Setoid.sym Y y₂≈y₃) y₂≈y₁) }
            ; snd = λ { {y₁ , x₁} {x₂ , y₂} {x₃ , y₃} (x₂≈x₃ , y₂≈y₃) (lift (x₁≈x₂ , y₁≈y₂)) → lift (Setoid.trans X x₁≈x₂ x₂≈x₃ , Setoid.trans Y y₁≈y₂ y₂≈y₃) }
            }
          }
        }
      ; commute = λ
        { {W , X} {Y , Z} ((R , R-resp-≈) , (S , S-resp-≈)) → record
          { fst = λ { ((y₂ , z₂) , (wRy₂ , xSz₂) , lift (y₂≈y₁ , z₂≈z₁)) → _ , lift (Setoid.refl W , Setoid.refl X) , (proj₂ S-resp-≈ z₂≈z₁ xSz₂ , proj₂ R-resp-≈ y₂≈y₁ wRy₂) }
          ; snd = λ { ((x₂ , w₂) , lift (w₁≈w₂ , x₁≈x₂) , (x₂Sz , w₂Ry)) → _ , (proj₁ R-resp-≈ (Setoid.sym W w₁≈w₂) w₂Ry , proj₁ S-resp-≈ (Setoid.sym X x₁≈x₂) x₂Sz) , lift (Setoid.refl Y , Setoid.refl Z) }
          }
        }
      ; iso = λ
        { (X , Y) → record
          { isoˡ = record
            { fst = λ { (_ , lift (x₁≈x₃ , y₁≈y₃) , lift (x₃≈x₂ , y₃≈y₂)) → lift (Setoid.trans X x₁≈x₃ x₃≈x₂ , Setoid.trans Y y₁≈y₃ y₃≈y₂) }
            ; snd = λ { (lift (x₁≈x₂ , y₁≈y₂)) → _ , lift (x₁≈x₂ , y₁≈y₂) , lift (Setoid.refl X , Setoid.refl Y) }
            }
          ; isoʳ = record
            { fst = λ { (_ , lift (x₁≈x₃ , y₁≈y₃) , lift (x₃≈x₂ , y₃≈y₂)) → lift (Setoid.trans Y y₁≈y₃ y₃≈y₂ , Setoid.trans X x₁≈x₃ x₃≈x₂) }
            ; snd = λ { (lift (y₁≈y₂ , x₁≈x₂)) → _ , lift (x₁≈x₂ , y₁≈y₂) , lift (Setoid.refl X , Setoid.refl Y) }
            }
          }
        }
      }
    ; commutative = λ {X} {Y} → record
      { fst = λ { (_ , (lift (y₁≈y₃ , x₁≈x₃) , lift (x₃≈x₂ , y₃≈y₂))) → lift (Setoid.trans Y y₁≈y₃ y₃≈y₂ , Setoid.trans X x₁≈x₃ x₃≈x₂) }
      ; snd = λ { (lift (y₁≈y₂ , x₁≈x₂)) → _ , lift (y₁≈y₂ , x₁≈x₂) , lift (Setoid.refl X , Setoid.refl Y) }
      }
    ; hexagon = λ {X} {Y} {Z} → record
      { fst = λ { (_ , (_ , (lift (x₁≈x₄ , y₁≈y₄) , lift z₁≈z₄) , lift (y₄≈y₃ , (x₄≈x₃ , z₄≈z₃))) , (lift y₃≈y₂ , lift (x₃≈x₂ , z₃≈z₂))) → _ , (_ , lift (x₁≈x₄ , (y₁≈y₄ , z₁≈z₄)) , lift (x₄≈x₃ , (y₄≈y₃ , z₄≈z₃))) , lift (y₃≈y₂ , (z₃≈z₂ , x₃≈x₂)) }
      ; snd = λ { (_ , (_ , lift (x₁≈x₄ , (y₁≈y₄ , z₁≈z₄)) , lift (x₄≈x₃ , (y₄≈y₃ , z₄≈z₃))) , lift (y₃≈y₂ , (z₃≈z₂ , x₃≈x₂))) → _ , ((_ , ((lift (x₁≈x₄ , y₁≈y₄) , lift z₁≈z₄)) , lift (y₄≈y₃ , (x₄≈x₃ , z₄≈z₃)))) , (lift y₃≈y₂ , lift (x₃≈x₂ , z₃≈z₂)) }
      }
    }
