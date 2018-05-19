module Lindenmayer where
import Painter

-- Implementierung von Lindenmayer-Systemen: Elemente der Menge Lindenmayer
-- der Form (d,a,s,rs) beinhalten die Angabe d zur Distanz, um die sich die
-- Schildkršte vorwŠrts bewegt, den Winkel a, um den sie sich fŸr die 
-- Symbole '+' und '-' dreht (in Grad), den Startstring s und die 
-- Ersetzungsregeln rs. Letztere haben die gleiche Form wie die Regeln von 
-- kontextfreien Grammatiken und werden hier als 2-Tupel gespeichert.
--
-- Die Funktion Lindenmayer hat als Parameter neben dem Lindenmayer-System
-- den Modus, mit dem gezeichnet wird, und die Zahl n der Iterationen von 
-- Ersetzungen, die durchgefŸhrt werden sollen.
--
-- iterate ist die Hilfsfunktion, die die Iterationen durchfŸhrt,
-- applyRules fŸhrt die Ersetzungen durch und moveL Ÿbersetzt schlie§lich 
-- den String Ÿber den Zeichen {A,B,F,J,+,-,[,]} in Turtle-Aktionen.
--
-- 'A','B' und 'F' werden in der Regel fŸr VorwŠrtsbewegung benutzt '+','-' 
-- fŸr Drehung, '[' fŸr das Schreiben auf den Keller der Schildkršte, ']' 
-- fŸr das Lesen vom Keller. Hier steht au§erdem 'J' fŸr das 
-- VorwŠrtsspringen.

type Lindenmayer = (Float, Float, String, [(Char,String)])

lindenmayer :: Int -> Int -> Lindenmayer -> Curve
lindenmayer mode n (d, a, s, rs) = 
    turtle green mode $ Turn 270 : map t (iterate f s!!n) 
    where t :: Char -> Action
          t '+' = Turn $ -a
          t '-' = Turn a
          t '[' = Open green 1 False
          t ']' = Close
          t 'F' = Move d
          t 'A' = Move d
          t 'B' = Move d
          t 'J' = Jump d
   	  t _   = Skip
          f = concatMap $ applyRules rs

applyRules :: [(Char,String)] -> Char -> String
applyRules ((l,r):rs) c = if c == l then r else applyRules rs c
applyRules _ c 		= [c]

-- Beispiele 

sierp draw = draw 8 (2,60,"A",[('A',"B-A-B"),('B',"A+B+A")])
fern' draw = draw 6 (3,25,"X",[('X',"F-[[X]+X]+F[+FX]-X"),('F',"FF")])
curve draw = draw 30 (22,25,"X",[('X',"F-X"),('X',"F+X")])
tree' draw = draw 5 (3,10,"FFX",[('X',"[+++[FX]+FFX][FFFX][--FX]"),('F',"FF"),
		                 ('X',"[---[FX]-FFX][FFFX][++FX]")])

draw1 depth = drawC1 . hueCol 1 . lindenmayer 14111 depth
draw2 depth = drawC1 . lindenmayer 12111 depth
