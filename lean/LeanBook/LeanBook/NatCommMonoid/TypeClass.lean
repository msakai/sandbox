-- 4.1 型クラスで見やすく綺麗に
import LeanBook.FirstProof.NaturalNumber

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0
#check 1
#check OfNat

instance : Add MyNat where
  add := MyNat.add

#check 1 + 1
#check MyNat.zero + MyNat.one

#eval 0 + 0
#eval 1 + 2

def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | MyNat.zero => 0
  | MyNat.succ m => MyNat.toNat m + 1

#check repr
#check Repr

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval 0 + 0
#eval 1 + 1

example (n : MyNat) : n + 0 = n := by
  rfl
