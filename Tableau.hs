module Tableau where

-- 21.4.2016

import Control.Monad
import Data.Maybe
import Painter(Parser,Tree(F,V),root,subtrees,parse,token,tstring,tchar,many,
	       char,sat,nat,parse,newlines,fold2,drawTermsP)

{- GRAMMAR
Modal      ::= OrExpr | OrExpr "==>" OrExpr
OrExpr     ::= AndExpr ("or" AndExpr)*
AndExpr    ::= NotExpr ("and" NotExpr)*
PrefixExpr ::= ("!" | "<>" | "[]") PrefixExpr | BasicExpr
BasicExpr  ::= "(" OrExpr ")" | VarExpr | ConstantExpr
VarExpr    ::= "x"Nat | "y"Nat | "z"Nat
ConstExpr  ::= "false" | "true"
-}

isV (V _) = True
isV _     = False

updList s i a = take i s++a:drop (i+1) s

-- nodes/leaves t pos is a list of all nodes/leaves of t.

nodes,leaves :: Tree a -> [[Int]]

nodes (F _ ts)  = []:[i:pos | (t,i) <- zip ts [0..], pos <- nodes t]
nodes _         = [[]]

leaves (F _ ts) = [i:pos | (t,i) <- zip ts [0..], pos <- leaves t]
leaves _        = [[]]

-- getSub t p is the subtree of t at position p by u. 
-- putSub t u replaces it by u.

getSub :: Tree a -> [Int] -> Tree a
getSub t [] = t
getSub (F _ ts) (i:is) | i < length ts = getSub (ts!!i) is
getSub _ _  = error "getSub"

putSub :: Tree a -> [Int] -> Tree a -> Tree a
putSub _ [] u          = u
putSub (V a) [0] u     = F a [u]
putSub (F a ts) (n:p) u 
   | n < lg            = F a $ updList ts n $ putSub (ts!!n) p u
   | n == lg && null p = F a $ ts++[u] where lg = length ts
putSub _ _ _           = error "putSub"

-- path(t)(p) is the list of labels on the path from the root of t to p.

path :: Tree a -> [Int] -> [a]
path t p = map (root . getSub t . flip take p) [0..length p]

-- PARSER FOR MODAL FORMULAS

modalParser :: Parser (Tree String)
modalParser  = do t <- orParser
		  msum [do tstring "==>"; u <- orParser; return $ F "==>" [t,u],
		        return t]
                     
orParser     = do t <- andParser
 		  ts <- many $ do tstring "or"; andParser
 		  return $ if null ts then t else F "or" $ t:ts
                     
andParser    = do t <- prefixParser
 	          ts <- many $ do tstring "and"; prefixParser
 	          return $ if null ts then t else F "and" $ t:ts
                     
prefixParser = msum [basicParser, 
                     do op <- msum $ map tstring $ words "! <> []"
                        a <- prefixParser
                        return $ F op [a]]
                      
basicParser  = msum [token varParser, 
		     constParser "false", 
		     constParser "true", 
		     do tchar '('; a <- token $ modalParser; tchar ')'
 		        return a]

varParser    = do x <- msum $ map char "xyz"
	          n <- many $ sat (`elem` "0123456789")
                  return $ V $ x:n
                 
constParser c = do tstring c; return $ F c []

-- TABLEAU CALCULUS

type Tableau = Tree TabNode
data TabNode = TN {state :: Int, phi :: Tree String, visited :: Bool} 
	       deriving Eq

isBox (F "[]" _)        = True
isBox (F "!" [F"<>" _]) = True
isBox _                 = False

isLiteral (V _)         = True
isLiteral (F "!" [V _]) = True
isLiteral _             = False

contra :: TabNode
contra = TN 0 (F "false" []) False

iniTab :: Tree String -> Tableau
iniTab phi = V $ TN 1 phi False

reduceTab :: String -> String -> IO ()
reduceTab file formula = do writeFile redfile $ newlines $ map f 
					      $ iteration (iniTab phi) 2 []
                            drawTermsP redfile
                         where f (t,next,p) = show (t,p)  
			       Just phi = parse modalParser formula
			       redfile = file ++ "Reduction"  
			       
iteration :: Tableau -> Int -> [Int] -> [(Tableau,Int,[Int])]
iteration t n p = case redStepP t n of Just (u,k,q) | (t,n) /= (u,k) 
		       	                 -> prev:(t,n,q):iteration u k q
		                       _ -> [prev]
		  where prev = (t,n,p)

-- In addition to redStep (see Painter.hs), redStepP stores the root positions 
-- of the redices and reducts of all reduction steps.

redStepP :: Tableau -> Int -> Maybe (Tableau,Int,[Int])
redStepP t n = f t n [] where
               f u n p = msum [do (t,n) <- tabRules u n t p
		 		  Just (t,n,p),
		 	       do F a ts <- Just u
		 	          (ts,n,p) <- g ts n p 0
		 	          Just (F a ts,n,p)]
	       g ts n p i = do t:ts <- Just ts
		               case f t n $ p++[i] of 
				    Just (t,n,p) -> Just (t:ts,n,p)
		 		    _ -> do (ts,n,p) <- g ts n p $ i+1
					    Just (t:ts,n,p)

not_ t = F "!" [t]

zeros = iterate (0:) [0]

tabRules :: Tableau -> Int -> Tableau -> [Int] -> Maybe (Tableau,Int)
tabRules tab succ t p =
 do guard $ not visited
    msum [do F "or" phis <- Just phi
	     add succ [(p++[n], tnF phi) | p <- ps,(n,phi) <- zip [0..] phis],
          do F "and" phis <- Just phi
             add succ [(p++q, tnF phi)   | p <- ps, (q,phi) <- zip zeros phis],
          do F "==>" [phi,psi] <- Just phi
	     add succ $ [(p++[0], tnF $ not_ phi) | p <- ps] ++
	     	        [(p++[1], tnF psi)        | p <- ps],
          do F "<>" [phi] <- Just phi
             add (succ+1) $ [(p++[0], tnF $ F (show succ) []) | p <- ps] ++
	     		    [(p++[0,0], TN succ phi False)    | p <- ps] ++
            	            [(p++q, TN succ phi False)        | p <- ps, 
				       (q,phi) <- zip (drop 2 zeros) $ boxes p],
              
          do F "[]" [phi] <- Just phi
	     add succ [(p++q, TN succ phi False) | p <- ps, 
					       (q,succ) <- zip zeros $ succs p],
          do F "!" [F "!" [phi]] <- Just phi
	     Just (tab' $ tnF phi, succ),
          do F "!" [F "<>" [phi]] <- Just phi
	     Just (tab' $ tnF $ F "[]" [F "!" [phi]], succ),
          do F "!" [F "[]" [phi]] <- Just phi
	     Just (tab' $ tnF $ F "<>" [F "!" [phi]], succ),
          do F "!" [F "or" phis] <- Just phi
             add succ [(p++q, tnF $ not_ phi) | p <- ps,
	     				        (q,phi) <- zip zeros phis],
          do F "!" [F "and" phis] <- Just phi
	     add succ [(p++[n], tnF $ not_ phi) | p <- ps, 
	                                          (n,phi) <- zip [0..] phis],
          do F "!" [F "==>" [phi,psi]] <- Just phi
	     add succ $ [(p++[0], tnF phi)          | p <- ps] ++
	     	        [(p++[0,0], tnF $ not_ psi) | p <- ps],
          do z@(V x) <- Just phi
	     let ps = [p | p <- nodes tab, 
	     		   root (getSub tab p) == tnF (F "!" [z])]
             guard $ not $ null ps; Just (mkFalse ps, succ),
          do F "!" [z@(V x)] <- Just phi
             let ps = [p | p <- nodes tab, root (getSub tab p) == tnF z]
             guard $ not $ null ps; Just (mkFalse ps, succ)]
	     
    where TN state phi visited = root tab
    
          tnF phi = TN state phi False
   
          tab' root = if isV tab then V root else F root $ subtrees tab

          ps = [p | p <- leaves tab, root (getSub tab p) /= contra]
	 
	  mkFalse = foldl f tab where f t p = putSub t p $ V contra
	 
          add succ nodes = Just (fold2 putSub newTab ps $ map V labs, succ)
	                   where newTab = tab' newRoot
			         (ps,labs) = unzip nodes
	  
          newRoot = TN state (if isBox phi then phi else F "true" []) True
			          
          -- boxes(q) and succs(q) are the sets of all state formulas 
	  -- (state,[]phi,True) resp. transitions (state,state') on the path
	  -- from the root of t to p++q.

          boxes :: [Int] -> [Tree String]
          boxes q = [phi | TN state' (F "[]" [phi]) True <- path t $ p++q, 
	 		   state == state']

	  succs :: [Int] -> [Int]
          succs q = [fromJust succ | TN state' (F str []) _ <- path t $ p++q, 
	 		             state == state', 
			             let succ = parse nat str, isJust succ]

-- UNPARSER FOR TABLEAU NODES

instance Show TabNode where 
         show (TN _ (F "false" []) _) = quote "false"
         show (TN _ (F "true" []) _)  = quote "true"
         show (TN state (F succ [] ) _) 
            | isJust $ parse nat succ = quote $ "s"++show state++"->"++"s"++succ
         show (TN state phi b)        = quote $ "s"++show state++"|satisfies|"++
                                        showFormula phi++if b then "|visited" 
							      else ""

quote s = '\"' : s ++ "\""

showFormula,enclose :: Tree String -> String

showFormula (V x)         = x
showFormula (F op [t])    = op ++ enclose t
showFormula (F op (t:ts)) = enclose t ++ concatMap (f op . enclose) ts
			    where f op str = ' ':op++' ':str
showFormula _	          = error "showFormula"

enclose t = if isV t || root t `elem` words "! <> []"
	    then showFormula t else '(':showFormula t++")"

-- EXAMPLES

test1 = reduceTab "test1" 					     -- hor = 11
		  "(x and y or z) and x1 or y1 or z1 or !x2"         -- ver = 44
test2 = reduceTab "test2" 
		  "!x and (y or x) and (y ==> x) or x and (!x and y or !y)" 
                  -- LogikSchwentick 6/4
test3 = reduceTab "test3" "<><>x and [](x ==> []!x)"
                  -- LogikSchwentick 6/14
test4 = reduceTab "test4" "<>x and []!y and <>(x ==> y)"
                  -- LogikSchwentick 6/15
test5 = reduceTab "test5" "[](x ==> y) and <>x and []!y"
                  -- LogikSchwentick 6/17
test6 = reduceTab "test6" "!([](x ==> y) and <>x and []!y)"

