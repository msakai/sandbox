-- 6.4 記法の展開を楽にする
module LeanBook.NatOrder.NotationSimp where

open import Function
open import Relation.Nullary.Negation

open import LeanBook.NatOrder.StrictOrder public

-- 6.4.1 simp による方法

<-def : {m n : MyNat} → m < n ⇔ m + 1 ≤ n
<-def = mk⇔ id id

-- 6.4.2 simp ラッパーを作成する

module _ where private
  example : (m n : MyNat) → m < n → m + 1 ≤ n
  example m n h = h

-- 6.4.3 notation_simp? を定義する

-- 6.4.4 練習問題 （回答は204 ページ）

module _ where private
  example : (a b : MyNat) → a < b → a ≯ b
  example a b a<b a>b = a≱b a≥b
    where
      a≱b : a ≱ b
      a≱b = <⇒≱ a<b
      a≥b : a ≥ b
      a≥b = <⇒≤ a>b
