module Disp where

import Examples
import Main
import DataTypes
import ToPdf

mul22 = "((\\ s1 . \\ z1 . s1 @ (s1 @ z1)) @ ((\\ s2 . \\ z2 . s2 @ (s2 @ z2)) @ S)) @ Z"

dispNormal = 
  let t@(Tr tr) = head . runExamples $ [mul22]
  in do
    (putStrLn . showT) t
    putStrLn $ display . reverse $ tr

showT (Tr tr) = show' tr' 1 where
  tr' = reverse tr
  show' [] _ = ""
  show' (x:xs) i =
    show i ++ ". " ++ show1 x ++ "\n" ++ show' xs (i + 1)
    where
      show1 (t, (b, (hp, un))) =
        let
          st = show t
        in st ++ " " ++ show b ++ " " ++ show hp ++ " " ++ show un
