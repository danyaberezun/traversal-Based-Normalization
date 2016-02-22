module ToPdf (showPdf) where
import Data.List
import Data.Char

import DataTypes

showPdf :: [Traversal] -> [[Char]] -> [[Char]] -> [Char]
showPdf trs ns exameples_names =
    (fst $ fst $ mapAccumL (\(acc, na:names) (x, n) -> case x of
      Tr xs -> ((acc ++ "\\newpage\n\\section*{Example " ++ na ++ "}\n Input term: \\ $"
      	++ termToTex n 1 ++ "$\n" ++ showPdf_traversal xs
      	++ "\\\\[1in] Normal form: $" ++ (display . reverse $ xs) ++ "$\n"
      	, names), (x, n))) (document_begin, exameples_names) (zip trs ns)) ++ document_end
  where
    termToTex [] _ = []
    termToTex (y:ys) i = if y == '\\' then "\\lambda " ++ termToTex ys i
    	else if y == '@' then "@_{" ++ show i ++ "}" ++ termToTex ys ((+) i 1)
    	else y : termToTex ys i
    document_begin   = "\\documentclass[10pt]{article}\n\\usepackage{pgfplots}\n\\usepackage[paperheight=50in,paperwidth=20in]{geometry}\n\\usepackage{lscape}\n\\usetikzlibrary{arrows}\n\\newcommand{\\tikzmark}[3][]{\\tikz[remember picture,baseline] \\node [inner xsep=0pt,anchor=base,#1](#2) {#3};}\n\\begin{document}\n\\begin{landscape}\n"
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
      tikz_begin = "\\begin{tikzpicture}[remember picture,overlay,scale=6,domain=0:1]\n"
      tikz_end :: [Char]
      tikz_end = "\\end{tikzpicture}"
      tikz_head :: [Char]
      tikz_head = "\\[" ++ (generate_tikz_items 1 tr) ++ "\\]\n"
      generate_tikz_items i [] = ""
      generate_tikz_items i ((t, _):tr) =
        "\\ \\ \\tikzmark{" ++ show i ++ "}{$" ++ show_item t ++ "$}" ++ generate_tikz_items ((+) i 1) tr
      show_item (ULAbs _ x _) = "\\lambda " ++ x
      show_item (ULApp i _ _) = "@_{" ++ i ++ "}"
      show_item (ULVar _ z  ) = z

display :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))] -> [Char]
display = fst . toLambda . throwOut
  where
    throwOut :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))]
      -> [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))]
    throwOut [] = []
    throwOut (x@(x_e, (False, _)):trs) = throwOut trs
    throwOut (x@(x_e, (True , _)):trs) = x : throwOut trs
    toLambda :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))]
      -> ([Char], [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))])
    toLambda [] = ("", [])
    toLambda (x@(ULVar _ z, (_, _)):trs) =
        (z, trs)
    toLambda (x@(x_e, (_, _)):trs) = let
        (str', trs') = toLambda trs
      in case x_e of
        ULAbs name z _ -> ("\\lambda " ++ z ++ " . " ++ str', trs')
        ULApp name _ _ -> let
            (str'', trs'') = toLambda trs'
            str'''  = if member '@' str' then "(" ++ str' ++ ")" else str'
            str'''' = if member '@' str'' then "(" ++ str'' ++ ")" else str''
          in (str''' ++ " @ " ++ str'''', trs'')

member x xs = (/=) (filter ((==) x) xs) []