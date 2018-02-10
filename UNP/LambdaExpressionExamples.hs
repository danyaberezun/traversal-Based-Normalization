module LambdaExpressionExamples (examples, expectedResults) where

examples         = babyExs  ++ churchExs  ++ varityExs
expectedResults  = babyRess ++ churchRess ++ varityRess

-- ========================================================================
-- ========================================================================
--   How to add a test:
--      1. write a test, say 'newTest'
--      2. write an expected result, say 'newTestResult'
--      3. add 'newTest' to the begin of examples list
--         and 'newTestResult' to the begin of expectedResults list
--      4. run main from Main.hs to see the result
--         If failes then look into Testing.hs
-- ========================================================================
-- ========================================================================

-- =================
--   Baby examples
-- =================

babyExs  = [babyEx1,babyEx2,babyEx3,babyEx4,babyEx5,babyEx6,babyEx7,babyEx8,
            babyEx9,babyEx10,babyEx11,babyEx12,babyEx13,babyEx14,babyEx15,
            babyEx16,babyEx17,babyEx18,babyEx19]
babyRess = [babyRes1,babyRes2,babyRes3,babyRes4,babyRes5,babyRes6,babyRes7,babyRes8,
            babyRes9,babyRes10,babyRes11,babyRes12,babyRes13,babyRes14,babyRes15,
            babyRes16,babyRes17,babyRes18,babyRes19]

babyEx1   = "y1"
babyRes1  = "y1"
babyEx2   = "y1 y2"
babyRes2  = "y1 y2"
babyEx3   = "y1 (y2 y3)"
babyRes3  = "y1 (y2 y3)"
babyEx4   = "(y1 y2) (y3 y4)"
babyRes4  = "(y1 y2) (y3 y4)"
babyEx5   = "\\ x . x"
babyRes5  = "\\ x . x"
babyEx6   = "\\ x . x y2"
babyRes6  = "\\ x . x y2"
babyEx7   = "\\ x . y1 x"
babyRes7  = "\\ x . y1 x"
babyEx8   = "y1 (\\ x . y2)"
babyRes8  = "y1 (\\ x . y2)"
babyEx9   = "y1 (\\ x . x)"
babyRes9  = "y1 (\\ x . x)"
babyEx10  = "(\\ x . y1) y2"
babyRes10 = "y1"
babyEx11  = "(\\ x . x ) y2"
babyRes11 = "y2"
babyEx12  = "\\ x. y1 (y2 y3)"
babyRes12 = "\\ x. y1 (y2 y3)"
babyEx13  = "\\ x. x  (y2 y3)"
babyRes13 = "\\ x. x  (y2 y3)"
babyEx14  = "\\ x. y1 (x  y3)"
babyRes14 = "\\ x. y1 (x  y3)"
babyEx15  = "\\ x. y1 (y2 x )"
babyRes15 = "\\ x. y1 (y2 x )"
babyEx16  = "\\ x. y1 (x1 y3)"
babyRes16 = "\\ x. y1 (x1 y3)"
babyEx17  = "(\\ x . y1 y2) y3"
babyRes17 = "y1 y2"
babyEx18  = "(y1 y2) (\\ z . z)"
babyRes18 = "(y1 y2) (\\ z . z)"
babyEx19  = "(y1 (\\ w . w)) y3"
babyRes19 = "(y1 (\\ w . w)) y3"

-- ===========================
-- Multiplying Church numerals
-- ===========================

churchExs  = [mul22Ex ]
churchRess = [mul22Res]

mul = "\\ m . \\ n . \\ s . \\ z . m (n s) z"
two = "\\ s . \\ z . s (s z)"

mul22Ex  = "(" ++ mul ++ ") (" ++ two ++ ") (" ++ two ++ ")"
mul22Res = "\\ s . \\ z . s (s (s (s z)))"

-- ========================================================
--   Example with variable arity (renaming is essential!)
-- ========================================================

varityExs  = [varity2Ex ]
varityRess = [varity2Res]

varity = "\\ t . (t (\\ n .  \\ a . \\ x .  n (\\ s . \\ z . (a s) (x s z)))) (\\ a .  a) (\\ s . \\ z . z)"

varity2Ex  = "(" ++ varity ++ ") (" ++  two ++ ")"
varity2Res = "\\ x . \\x1 . \\ s . \\z . x s (x1 s z)"
