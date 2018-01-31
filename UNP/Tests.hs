module Tests where

import DataTypes

-- ============= 
-- TEST EXAMPLES, all type  example :: Exp
-- ============= 

-- ==================================================================
-- baby examples: free and bound variables, applicationss and Lambdas
-- ==================================================================

example1  =  (V "y1")
example2  =  App 1 (V "y1") (V "y2")
example3  =  App 1 (V "y1") (App 2 (V "y2") (V "y3"))
example4  =  App 1 (App 2 (V "y1") (V "y2")) (App 3 (V "y3") (V "y4")) 
 
example5  = Lam "x" (V "x")
example6  = Lam "x" (App 1 (V "x") (V "y2"))
example7  = Lam "x" (App 1 (V "y1") (V "x"))
example8  = App 1 (V "y1") (Lam "x" (V "y2")) 
example9  = App 1 (V "y1") (Lam "x" (V "x")) 
example10 = App 1 (Lam "x" (V "y1")) (V "y2")
example11 = App 1 (Lam "x" (V "x")) (V "y2")
example12 = Lam "x" (App 1 (V "y1") (App 2 (V "y2") (V "y3")))
example13 = Lam "x" (App 1 (V "x") (App 2 (V "y2") (V "y3")))
example14 = Lam "x" (App 1 (V "y1") (App 2 (V "x") (V "y3")))
example15 = Lam "x" (App 1 (V "y1") (App 2 (V "y2") (V "x")))
example16 = Lam "x" (App 1 (V "y1") (App 2 (V "x") (V "y3")))
example17 = App 1 (Lam "x" (App 2 (V "y1") (V "y2"))) (V "y3")
example18 = App 1 (App 2 (V "y1") (V "y2")) (Lam "z" (V "z"))
example19 = App 1 (App 2 (V "y1") (Lam "w" (V "w"))) (V "y3")

testR = (App 1 (Lam "x" (Lam "y" (App 2 (V "x") (V "y")))) (V "y"))

-- Abstraction used both "stand-alone and in an application context
-- ================================================================
example20 = App 1 (Lam "u" (App 2 (V "u") (App 3 (V "y1") (V "u")))) 
                  (Lam "v" (App 4 (V "v") (V "y2")))

example21 = App 9 (App 10 (V "g1") (Lam "b" (V "b"))) (V "g3")

example22 = App 9 (App 10 (V "g1") (Lam "b" (V "b11"))) (V "g3")

example23 = App 1 (Lam "x" (App 2 (V "x") (V "y"))) (Lam "x" (V "x"))

example24 = App 1 (Lam "x" (App 2 (V "y") (V "x"))) (Lam "x" (V "x"))

example25 = App 1 (Lam "x" (App 2 (V "x") (V "x"))) (Lam "x" (V "x"))

example26 = App 1 (Lam "y2" (App 2 (V "y2") (App 3 (V "y1") (V "y2")))) 
                  (Lam "v" (App 4 (V "v") (V "y2")))


example27 = App 1 (Lam "y2-1" (App 2 (V "y2-1") (App 3 (V "y1") (V "y2-1")))) 
                  (Lam "v" (App 4 (V "v") (V "y2")))

example28 = App 1 (Lam "u" (App 2 (V "u") (App 3 (V "y1") (V "u")))) 
 
example30 = Lam "x" (App 1 (V "x") (V "x"))

example31 = Lam "x" (App 1 (Lam "y" (V "y")) 
                           (V "z"))

example32 = Lam "x" (App 1 (Lam "y" (V "y")) 
                           (Lam "z" (V "z")))

example33 = App 1 (Lam "x" (App 2 (V "x") (V "x"))) (V "y")

example340 = (App 1 (Lam "x" (App 2 (V "x") (V "x"))) (V "y"))

example34 = App 1 (Lam "z" (App 2 
                                 (App 3 
                                       (Lam "x" (App 2 
                                                      (V "x") 
                                                      (V "x"))) 
                                       (V "y")) 
                                 (V "z")) )
                  (V "w")

example35 = App 1 (App 2 (Lam "x" (App 3 (V "x") (V "x"))) (V "y1")) (V "y2")


example36 = App 1 (App 2 (Lam "x" (Lam "z" (App 3 (V "x") (App 4 (V "z") (V "x"))))) (V "y1")) (V "y2")

example37 =  Lam "x1" (Lam "x2" (Lam "s" (Lam "z" 
              (App 7  (App 8  (V "x1") (V "s")) 
              (App 77 (App 88 (V "x2") (V "s")) 
                      (V "z"))))))


example38 =  Lam "x" (Lam "x" (Lam "s" (Lam "z" 
              (App 7  (App 8  (V "x") (V "s")) 
              (App 7 (App 8 (V "x") (V "s")) 
                      (V "z"))))))

-- example where renaming is necessary
-- ===================================

example39 =  App 1 (Lam "x" (Lam "y" (App 2 (V "x") (V "y")))) (V "y")

example42 = App 1 (Lam "u" (App 2 (V "u") (V "u"))) (App 3 (Lam "v" (App 4 (V "v") (V "v"))) (V "x"))

example43 =  App 1 (App 2 (V "u") (App 3 (Lam "v" (V "v")) (V "w"))) (V "x")

example44 = (Lam "q" (Lam "t" (Lam "u" (App 1 (App 2 
                 (App 3 (Lam "p" (V "p")) (Lam "v" (App 4 (V "q") (V "v"))))
                 (App 5 (Lam "s" (V "s")) (V "t")))
               (V "u")))))


example45 =  App 1 (Lam "u" 
                (App 2 (V "u") (Lam "v" (App 3 (V "u") 
                     (Lam "w" (App 4 (V "v") (V "w")))))))
              (Lam "z" (V "z"))


-- variants on Ong 2015 examples
-- ==============================



ong2 = App 10 (App 6 a1' a6') (App 11 (V "g2") (Lam "n" (V "n")))
a1' = Lam "phi" (Lam "z" a2')
a2' = App 4 a3' (App 5 (V "z") (V "a2"))
a3' = App 1 (V "phi") a4'
a4' = Lam "x" (App 3 a5' (V "a1"))
a5' = App 2 (V "phi") (Lam "q" (V "x"))
a6' = Lam "f" (Lam "y" a7')
a7' = App 7 (V "f") (App 9 (App 8 (V "g1") (Lam "b" (V "b"))) (V "y"))

ong3 = App 1 (App 2 a1D a6D) (App 11 (V "g2") (Lam "q" (V "q")))
a1D = Lam "phi" (Lam "z" a2D)
a2D = App 3 a3D (App 7 (V "z") (V "a2"))
a3D = App 4 (V "phi") a4D
a4D = Lam "x" (App 5 a5D (V "a1"))
a5D = App 6 (V "phi") (Lam "x1" (V "x"))
a6D = Lam "f" (Lam "y" a7D)
a7D = App 8 (V "f") (App 9 (App 10 (V "g1") (Lam "b" (V "b11"))) (V "y"))

-- Multiplying Church numerals
-- ===========================

mul22 = App 1 (App 2 b1 (App 5 b2 (V "S"))) (V "Z")
b1 = Lam "s1" (Lam "z1" (App 3 (V "s1") (App 4 (V "s1") (V "z1"))))
b2 = Lam "s2" (Lam "z2" (App 6 (V "s2") (App 7 (V "s2") (V "z2"))))

mul32 = App 1 (App 2 c1 (App 5 c2 (V "S"))) (V "Z")
c1 = Lam "s1" (Lam "z1" (App 3 (V "s1") (App 4 (V "s1") (App 5 (V "s1") (V "z1")))))
c2 = Lam "s2" (Lam "z2" (App 6 (V "s2") (App 7 (V "s2") (V "z2"))))

-- Ackermann's function 
-- ====================

ack = Lam "m" (App 2 d1 successor)
d1 = App 3 (V "m") (Lam "g" (Lam "n" d2))
d2 = App 4 (App 5 (V "n") (V "g")) (App 6 (V "g") one)
successor  = 
 Lam "x" (Lam "s" (Lam "z" (App 50 (V "s") (App 51 (App 52 (V "x") (V "s")) (V "z")))))

ackhelp m n = App 88 (App 77 (App 0 (App 1 ack m) n) (V "S")) (V "Z")
ack00 = ackhelp zero zero
ack01 = ackhelp zero one
ack02 = ackhelp zero two
ack10 = ackhelp one zero
ack11 = ackhelp one one
ack12 = ackhelp one two
ack13 = ackhelp one three
ack20 = ackhelp two zero
ack21 = ackhelp two one  --  BUG! ack21 swaps S and Z
ack30 = ackhelp three zero
ack31 = ackhelp three one


-- =====================
--  STANDARD TEST SUITE
-- =====================

-- a few CHURCH NUMERALS

zero  = Lam "s0" (Lam "z0" (V "z0"))
one   = Lam "s1" (Lam "z1" (App 10 (V "s1") (V "z1")))
two  =  Lam "s2" (Lam "z2" (App 20 (V "s2") (App 21 (V "s2") (V "z2"))))
three = Lam "s3" (Lam "z3" (App 30 (V "s3") (App 31 (V "s3") (App 32 (V "s3") (V "z3")))))

renaming =  App 1 (Lam "x" (Lam "y" (App 2 (V "x") (V "y")))) (V "y")
ong1 = App 1 (App 2 a1 a6) (V "g2")

a1 = Lam "phi" (Lam "z" a2)
a2 = App 3 a3 (App 7 (V "z") (V "a2"))
a3 = App 4 (V "phi") a4
a4 = Lam "x" (App 5 a5 (V "a1"))
a5 = App 6 (V "phi") (Lam "x'" (V "x"))
a6 = Lam "f" (Lam "y" a7)
 
-- ====================
a7 = App 8 (V "f") (App 9 (V "g1") (V "y"))-- Ackermann's function 
-- ====================

-- ====================================================
-- Example with variable arity (renaming is essential!)
-- ====================================================

varity = Lam "t1" (App 1 (App 2 (App 3 (V "t1") va1) (Lam "a" (V "a"))) zero)

va1 = Lam "n" (Lam "a1" (Lam "x1" (App 4 (V "n") va2)))

va2 = Lam "sva2" (Lam "zva2" (App 5 (App 6 (V "a1") (V "sva2")) (App 7 (App 8 (V "x1") (V "sva2")) (V "zva2"))))

varity0 = App 999 varity zero
varity1 = App 999 varity one
varity2 = App 999 varity two
varity3 = App 999 varity three

--varity2 = (\t1 . ((t1 (\ n . (\ a1 . (\ x1 . (n (\ sva2 . (\ zva2 . ((a1 sva2) ((x1 sva2) (zva2))))))))) (\a. a)) (\s.\z.z))) (\s.\z.s(s z))
--result = \x1.\x11.\sva2.\zva2.x1 sva2 (x11 sva2 zva2)
