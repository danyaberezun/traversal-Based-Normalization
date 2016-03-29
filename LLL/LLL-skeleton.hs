import Data.List

--
-- TRAVERSAL GENERATOR for mul example (Church numerals)
--
data Token =
  A | B | C | D | E | F | G | H | I | J | K | L | M | N 
  | O | P | Q | R | S | T | U | V | W | X | Y | Z 
  | AA | AB | AC | AD | AE | AF | AG | AH
  | END 
  | CGAUXBUG | TRAV | TRAV1  deriving (Eq, Show)

type Item = (Token, Int)

main = print (reverse (a [(A,0)]))


-- MAIN BODY OF “MULT”

a tr = b ( (B, 0) : tr )
b tr = c ( (C, length tr) : tr )
c tr = d ( (D, fq C tr) : tr )
d tr = cgoto tr 1

e tr = f ( (F, fq C tr) : tr )
f tr = cgoto tr 2

g tr = h ( (H, fq C tr) : tr )
h tr = cgoto tr 3

i tr = j ( (J, fq G tr) : tr )
j tr = cgoto tr 1

k tr = l ( (L, fq E tr) : tr )
l tr = cgoto tr 1

m tr = n ( (M, fq C tr) : tr )
n tr = cgoto tr 4


-- THE CONSTANT 3 (Church numeral)

o tr = p ( (P, fq O tr) : tr )
p tr = cgoto tr 1

q tr = r ( (R, fq O tr) : tr )
r tr = cgoto tr 1

s tr = t ( (T, fq O tr) : tr )
t tr = cgoto tr 1

u tr = v ( (V, fq O tr) : tr )
v tr = cgoto tr 2


-- THE CONSTANT 2 (Church numeral)

w tr = x ( (X, fq W tr) : tr )
x tr = cgoto tr 1

y tr = z ( (Z, fq W tr) : tr )
z tr = cgoto tr 1

aa tr = ab ( (AB, fq W tr) : tr )
ab tr = cgoto tr 2


-- NEXT-TO-LAST BODY OF “MULT”

ac tr = ad ( (AD, 1) : tr ) 
ad tr = ae ( (AE, length tr) : tr )

ae tr = af ( (AF, fq AC tr) : tr )
af tr = cgoto tr 1

ag tr = ah ( (AH, 1) : tr )
ah tr = (END, 99) : tr


-- LAST BODY OF “MULT”

pfx i tr = reverse (take i (reverse tr))


-- COMPUTED GOTO

cgoto :: [Item] -> Int -> [Item]

cgoto tr i = 
   let (tk, bp) : _ = tr in
    let pred = pfx (bp - 1) tr in
     let (cause, _) : _ = pred 
     in cgaux tk cause i pred tr

cgaux tk B  1 tr1 tr = o ((O,  length tr1) : tr)
cgaux tk B  2 tr1 tr = w ((W,  length tr1) : tr)
cgaux tk B  3 tr1 tr = ac ((AC, length tr1) : tr)
cgaux tk B  4 tr1 tr = ag ((AG, length tr1) : tr)

cgaux tk D  1 tr1 tr = e((E,  length tr1) : tr)
cgaux tk D  2 tr1 tr = m((M,  length tr1) : tr)

cgaux tk F  1 tr1 tr = g((G,  length tr1) : tr)
cgaux tk F  2 tr1 tr = k((K,  length tr1) : tr)

cgaux tk H  1 tr1 tr = i((I,  length tr1) : tr)


-- THE CONSTANT 3 (Church numeral)
cgaux tk P  1 tr1 tr = q((Q,  length tr1) : tr)
cgaux tk R  1 tr1 tr = s((S,  length tr1) : tr)
cgaux tk T  1 tr1 tr = u((U,  length tr1) : tr)

-- THE CONSTANT 2 (Church numeral)
cgaux tk X 1 tr1 tr = y((Y,  length tr1) : tr)
cgaux tk Z 1 tr1 tr = aa((AA, length tr1) : tr)

cgaux tk AC 1 tr1 tr = ad((AD, length tr1) : tr)
cgaux tk AE 1 tr1 tr = af((AF, length tr1) : tr)

cgaux tk AG 1 tr1 tr = ah((AH, length tr1) : tr)

cgaux tk tk1 i tr1 tr = 
   (CGAUXBUG, 1) : (tk, -1) : (tk1, -2) : (I, i) : (TRAV1, -999) : 
    (tr1 ++ [(TRAV, -999)] ++ tr ++ [(CGAUXBUG, 1)])


-- FQ auxiliary function

fq have tr = let (tk, bp) : tr0 = tr in
          if have == tk 
          then (length tr)
          else fq have (pfx (bp - 1) tr) 