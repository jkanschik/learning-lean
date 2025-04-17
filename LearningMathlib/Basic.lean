import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

theorem easy : 2 + 2 = 4 :=
  rfl
#check easy





def m : Nat := 7


theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp



/- asdsadsd -/

#check and_commutative
#check m

#eval m + 2

#check Nat → Nat
#check Nat.succ 2
#eval (0, 1)
#check (0, 1).allI
#check Nat × Nat


#check fun (x: Nat) => x + 5
#eval (fun (x:Nat) => x+5) 3
