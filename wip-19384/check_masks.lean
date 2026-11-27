import PEqualNP.Defs.Represents
import PEqualNP.Defs.CircuitLowerBounds

open PEqualNP

-- band7w2: notA(u,v) = [(v-u) % 7 in {0,1}], A = complement
-- mask bit (7*u+v) should equal the function value
def bandNotA : Fin 7 -> Fin 7 -> Bool := fun u v => (v.val + 7 - u.val) % 7 = 0 || (v.val + 7 - u.val) % 7 = 1

-- check mask 289184493536003 encodes bandNotA: bit (7u+v) = bandNotA u v
def maskCheck (m : Nat) (f : Fin 7 -> Fin 7 -> Bool) : Bool :=
  (List.finRange 7).all fun u => (List.finRange 7).all fun v =>
    ((m >>> (7 * u.val + v.val)) &&& 1) == (if f u v then 1 else 0)

#eval maskCheck 289184493536003 bandNotA
#eval maskCheck 273765459885308 (fun u v => !bandNotA u v)
