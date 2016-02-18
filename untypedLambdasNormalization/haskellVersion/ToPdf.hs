module ToPdf (showPdf) where
import Data.List

import DataTypes

showPdf :: [Traversal] -> [[Char]] -> [Char]
showPdf trs ns =
    (fst $ mapAccumL (\acc (x, n) -> case x of
      Tr xs -> (acc ++ "\\newpage\nexample $" ++ termToTex n ++ "$\n" ++ showPdf_traversal xs, (x,n))) document_begin (zip trs ns)) ++ document_end
  where
    termToTex [] = []
    termToTex (y:ys) = if y == '\\' then "\\lambda " ++ termToTex ys else y : (termToTex ys)
    document_begin   = "\\documentclass[a4paper, 10pt]{article}\n\\usepackage{tikz}\n\\usepackage{lscape}\n\\usetikzlibrary{arrows}\n\\newcommand{\\tikzmark}[3][]{\\tikz[remember picture,baseline] \\node [inner xsep=0pt,anchor=base,#1](#2) {#3};}\n\\begin{document}\n\\begin{landscape}\n"
    document_end = "\\end{landscape}\\end{document}\n"
    showPdf_traversal :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))] -> [Char]
    showPdf_traversal tr' = show_tikz where
      tr = (reverse tr')
      show_tikz :: [Char]
      show_tikz = tikz_head ++ show' tr 1 tikz_begin ++ "\n"
      show' [] _ tikz = tikz ++ tikz_end
      show' ((t, (b, (np', bp'))):xs) i tikz =
        let
          np = up2int np'
          bp = bp2int bp'
        in show' xs (i + 1) $ tikz ++
          (if np /= 0
            then let
                color = case np' of
                  CAP _ -> "red"
                  LUP _ -> "brown"
              in "\t \\color{" ++ color ++ "}{\\draw[->] (" ++ show i ++ ".north) to[bend right] (" ++ show np ++ ".north);}\n"
            else "")
          ++ (if bp /= 0 then "\t \\color{green}{\\draw[->] (" ++ show i ++ ".south) to[bend left] (" ++ show bp ++ ".south);}\n"
            else "")
      tikz_begin :: [Char]
      tikz_begin = "\\begin{tikzpicture}[remember picture,overlay]\n"
      tikz_end :: [Char]
      tikz_end = "\\end{tikzpicture}\n"
      tikz_head :: [Char]
      tikz_head = "\\[" ++ (generate_tikz_items 1 tr) ++ "\\]\n"
      generate_tikz_items i [] = ""
      generate_tikz_items i ((t, _):tr) =
        "\\ \\ \\tikzmark{" ++ show i ++ "}{$" ++ show_item t ++ "$}" ++ generate_tikz_items ((+) i 1) tr
      show_item (ULAbs _ x _) = "\\lambda " ++ x
      show_item (ULApp _ _ _) = "@"
      show_item (ULVar _ z  ) = z
