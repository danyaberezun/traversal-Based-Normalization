module Examples (examples_picture, examples_normalize_only,
				 examples_picture_names, examples_normalize_only_names) where

examples_picture = [p_zero, p_one_three, p_two_three_four, p_three_three_four_five, p_one, p_two]
examples_picture_names = ["p zero", "p one three", "p two three four", "p three three four five", "p one", "p two"]

examples_normalize_only = [ack_three]
examples_normalize_only_names = ["ack three"]

p_zero = "(\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . z2)"
p_one  = "(\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . s2 @ z2)"
p_two  = "(\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . s2 @ (s2 @ z2))"
p_one_three  = "((\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . s2 @ z2)) @ (\\ s3 . \\ z3 . s3 @ (s3 @ (s3 @ z3)))"
p_two_three_four = "(((\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . s2 @ (s2 @ z2))) @ (\\ s3 . \\ z3 . s3 @ (s3 @ (s3 @ z3)))) @ (\\ s4 . \\ z4 . s4 @ (s4 @ (s4 @ (s4 @ z4))))"
p_three_three_four_five = "((((\\ t . (((t @ (\\ n . \\ a . \\ x . n @ (\\ s . \\ z . (a @ s) @ ((x @ s) @ z)))) @ (\\ a1 . a1)) @ (\\ s1 . \\ z1 . z1))) @ (\\ s2 . \\ z2 . s2 @ (s2 @ (s2 @ z2)))) @ (\\ s3 . \\ z3 . s3 @ (s3 @ (s3 @ z3)))) @ (\\ s4 . \\ z4 . s4 @ (s4 @ (s4 @ (s4 @ z4))))) @ (\\ s5 . \\ z5. s5 @ (s5 @ (s5 @ (s5 @ (s5 @ z5)))))"
ex_mult_free_m_n = "\\ s . \\ z . (m @ (n @ s)) @ z"

ack_three = "(\\ m . (m @ (\\ g. \\ n . (n @ g) @ (g @ (\\ s1 . \\ z1. s1 @ z1)))) @ (\\ n2 . \\ s2 . \\ z2 . (n2 @ s2) @ (s2 @ z2))) @ (\\ s . \\ z . s @ (s @ (s @ z)))"

--examples = [ex_1, ex_2, ex_3, ex_4, ex_4', ex_5, ex_succ2, ex_9, ex_11,
--	ex_f0, ex_f1, ex_f2, ex_LO1, ex_LO2, ex_LO3, ex_LO4, ex_1, ex_6, ex_7]
--examples_names = ["ex\\_1", "ex\\_2", "ex\\_3", "ex\\_4", "ex\\_4'", "ex\\_5", "succ two",
--	"ex\\_9", "ex\\_11", "ex\\_f0", "ex\\_f1", "ex\\_f2", "ex\\_LO1", "ex\\_LO2", "ex\\_LO3",
--	"ex\\_LO4", "ex\\_1", "NPR", "mut three two"]

--ex = "(\\a . (\\w . w @ (w @ a)) @ s) @ (s @ z)"
--ex_1 = "(g @ (\\ n . n))"
--ex_2 = "((\\ h . h) @ (\\ f . f)) @ a"
--ex_3 = "((\\ h . h @ a) @ (\\ f . f))"
--ex_4 = "\\ f . \\ y . (y @ f) @ y"
--ex_4' = "\\ f . \\ y . (y @ (\\ z . z)) @ y"
--ex_5 = "\\ y . \\ f . (y @ f) @ y"
--ex_6 = "((\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))) @ (\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y))) @ (g @ (\\ n . n))"
--ex_7 = "((\\ m . \\ n . \\ s . \\ z . (m @ (n @ s)) @ z) @ (\\ a . \\ q . a @ (a @ (a @ q)))) @ (\\ d . \\ e . d @ (d @ e))"
--ex_succ2 = "(\\ n . \\ s . \\ z . (n @ s) @ (s @ z)) @ (\\ p . \\ o . p @ (p @ o))"
--ex_succ = "(\\ n . \\ s . \\ z . s @ ((n @ s) @ z)) @ ( \\ s1 . \\ z1 . (m @ s1) @ z1)"
--ex_mult = "\\ m . \\ n . \\ s . \\ z . (m @ (n @ s)) @ z"

--fib = "\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1)))"
--fib2 = "(\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1))))  @ (\\ s1 . \\ z1 . s1 @ (s1 @ z1))"
--fib4 = "(\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1))))  @ (\\ s1 . \\ z1 . s1 @ (s1 @ (s1 @ (s1 @ z1))))"

---- unfypable in STLC
--ex_9 = "(\\ x . x @ x) @ (\\ z . z)"
--ex_11 = "(\\ x . \\ y . x @ (x @ y)) @ (\\ p . q)"

--ex_f0 = "(\\ n . (n @ (\\ s . \\ z . s @ (s @ ((n @ s) @ z)))) @ (\\ s1 . \\ z1 . z1)) @ (\\ s2 . \\ z2 . z2)"
--ex_f1 = "(\\ n . (n @ (\\ s . \\ z . s @ (s @ ((n @ s) @ z)))) @ (\\ s1 . \\ z1 . z1)) @ (\\ s2 . \\ z2 . s2 @ z2)"
--ex_f2 = "(\\ n . (n @ (\\ s . \\ z . s @ (s @ ((n @ s) @ z)))) @ (\\ s1 . \\ z1 . z1)) @ (\\ s2 . \\ z2 . s2 @ (s2 @ z2))"

--ex_LO1 = "(\\ f . \\ x . f @ (x @ ((f @ x) @ x))) @ (\\ a . \\ b . a)"
--ex_LO2 = "(\\ x . (x @ x) @ x) @ (\\ a . \\ b . a)"
--ex_LO3 = "(\\ x . x @ (\\ y . y)) @ (\\ a . \\ b . b)"
--ex_LO4 = "(\\ x . x @ (\\ y . y)) @ (\\ a . \\ b . a)"
--ex_LO5 = "(\\ f . \\ x . f @ (x @ ((f @ x) @ x))) @ (\\ a . \\ b . a @ b)"
