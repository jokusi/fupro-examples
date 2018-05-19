{-# LANGUAGE TypeFamilies, FlexibleInstances, LambdaCase #-}
-- TypeSynonymInstances, ScopedTypeVariables, MultiParamTypeClasses
             
-- 25.3.2018

module Compiler where
		      
import Control.Exception
import Control.Applicative (Applicative(pure,(<*>)))
import Control.Monad
import Data.Maybe
import Painter (Tree(F),mkTreeC,update,insert,union,unionMap,readFileAndDo)

rel :: String -> Int -> Int -> Bool
rel = \case "<"  -> (<)
	    ">"  -> (>)
	    "<=" -> (<=)
	    ">=" -> (>=)
	    "==" -> (==)
	    "!=" -> (/=)


-- Reg-ALGEBRAS 

data Reg reg = Reg {par,seq_ :: reg -> reg -> reg, 
		    iter :: reg -> reg,
		    base :: String -> reg, 
		    var :: String -> reg}

-- Initial Reg-algebra
			  
data RegT = Par RegT RegT | Seq RegT RegT | Iter RegT | Base String | Var String 
	    deriving (Eq,Show)
	   
regT :: Reg RegT
regT = Reg {par = Par, seq_ = Seq, iter = Iter, base = Base, var = Var}

-- foldReg alg t folds t in alg.

foldReg :: Reg reg -> RegT -> reg
foldReg alg = \case Par t u -> par alg (f t) $ f u
		    Seq t u -> seq_ alg (f t) $ f u
		    Iter t  -> iter alg $ f t
		    Base b  -> base alg b
		    Var x   -> var alg x
	      where f = foldReg alg		
		
-- The Reg-algebra regNorm interprets a regular expression by its additive
-- normal form, which can be obtained by applying semiring equations. 

regNorm :: Reg RegT
regNorm = Reg {par  = \t u -> let ts = summands $ Par t u
			      in if null ts then mt else foldr1 Par ts,
               seq_ = \t u -> let ts = factors $ Seq t u
               		      in if null ts then one
	       		                    else if mt `elem` ts 
	       		         	         then mt else foldr1 Seq ts,
               iter = \t -> if t `elem` [one,mt] then one else Iter t,
               base = Base,
               var  = Var}
          where mt = Base "mt"; one = Base "eps"
	        

summands,factors :: RegT -> [RegT]
summands (Par t u)   = summands t `union` summands u
summands (Base "mt") = []
summands t           = [t]
factors (Seq t u)    = factors t ++ factors u
factors (Base "eps") = []
factors t            = [t]

-- Folding a Reg-term in the Reg-algebra regWord leads to a string with as less
-- brackets as possible, in accordance with the usual priorities of regular 
-- operators: prio(par) = 0, prio(seq) = 1, prio(iter) = 3. ****
	      
regWord :: Reg (Int -> String)
regWord = Reg {par  = \f g n -> enclose (n > 0) $ f 0 ++ '+':g 0,
               seq_ = \f g n -> enclose (n > 1) $ f 1 ++ '.':g 1,
               iter = \f n -> enclose (n > 2) $ f 2 ++ "*",
               base = \b -> const b,
               var  = \x -> const x}
	  where enclose b w = if b then '(':w++")" else w

showReg :: RegT -> String
showReg = flip (foldReg regWord) 0

-- The Reg-algebra regNDA computes the nondeterministic acceptor of a regular
-- language.

type NDA = Int -> String -> [Int]

regNDA :: Reg ((NDA,Int,Int,Int) -> (NDA,Int))
regNDA = Reg {par  = \f g (d,s,s',next) -> let (d',next') = f (d,s,s',next) 
                                           in g (d',s,s',next'),
              seq_ = \f g (d,s,s',next) -> let (d',next') = f (d,s,next,next+1) 
              				   in g (d',next,s',next'),
              iter = \f (d,s,s',next) -> let next1 = next+1
			       	             next2 = next1+1
				             (d1,next3) = f (d,next,next1,next2)
				             d2 = addTo d1 s "eps" next
				             d3 = addTo d2 next1 "eps" next
				             d4 = addTo d3 next1 "eps" s'   
				         in (addTo d4 s "eps" s',next3),
	      base = \case "mt"  -> \(d,_,_,next) -> (d,next)
	      		   b     -> \(d,s,s',next) -> (addTo d s b s',next),
	      var  = \x (d,s,s',next) -> (addTo d s x s',next)}

addTo :: (Eq a,Eq b,Eq c) => (a -> b -> [c]) -> a -> b -> c -> a -> b -> [c]
addTo f a b c = update f a $ update (f a) b $ insert c $ f a b

type Rules = [(String,String)]

eqs :: Rules -> String -> RegT
eqs rules s = runAndApp (compReg rules regT) (const $ Base "mt") id 
			$ fromJust $ lookup s rules

-- The Reg(String)-algebra regA/B rules interprets a regular expression 
-- (with variables of a non-left-recursive CFG given by rules) in accC and 
-- behFun, respectively (see below).

regA :: Rules -> Reg AccC
regA rules = Reg {par = par, seq_ = seq, iter = iter,
                  base = \case "eps" -> one; "mt" -> mt 
                  	       "Int" -> mkCon int; "Bool" -> mkCon bool
                               c -> DA {deltaC = \x -> if x == c 
                               			       then one else mt,
                               	        betaC = False},
                  var = foldReg (regA rules) . eqs rules}
             where par (DA f b) (DA g c) = 
                       DA {deltaC = \x -> par (f x) (g x), betaC = b || c}
                   seq (DA f b) t@(DA g c) =
                       if b then DA {deltaC = \x -> par (seq (f x) t) $ g x,
                  	             betaC = c}
                  	    else DA {deltaC = \x -> seq (f x) t,
                  	             betaC = False}
                   iter t@(DA f _) = DA {deltaC = \x -> seq (f x) $ iter t,
                                         betaC = True}
                   one = DA {deltaC = const mt, betaC = True}
                   mt  = DA {deltaC = const mt, betaC = False}
                   mkCon p  = DA {deltaC = runAndApp p (const mt) $ const one,
                    	          betaC = False}

regB :: Rules -> Reg ([String] -> Bool)
regB rules = Reg {par  = liftM2 (||),
                  seq_ = \f g w -> f [] && g w || f w && g [] ||
		                   or [f w1 && g w2 | [w1,w2] <- mkParts w],
		  iter = \f w -> null w || or [all f ws | ws <- mkParts w],
                  base = \case "eps"  -> null
                  	       "mt"   -> const False
	                       "Int"  -> \case [x] -> mkFun int x;  _ -> False
	                       "Bool" -> \case [x] -> mkFun bool x; _ -> False
	                       c -> \case [x] -> x == c; _ -> False,
	          var = foldReg (regB rules) . eqs rules}
	     where mkParts [x]    = [[[x]]]
	           mkParts (x:w)  = concatMap glue $ mkParts w where
	                            glue p@(w:p') = [[x]:p,(x:w):p']
	           mkParts _      = []
	           mkFun p = runAndApp p (const False) $ const True
       
		
-- Acc-ALGEBRAS

data Acc state = Acc {delta :: state -> String -> state, beta :: state -> Bool}

-- Final Acc-algebras

data AccC = DA {deltaC :: String -> AccC, betaC :: Bool}

accC :: Acc AccC
accC = Acc {delta = deltaC, beta = betaC}

behFun :: Acc ([String] -> Bool)
behFun = Acc {delta = \f x -> f . (x:), beta = ($ [])}
		
-- unfoldB and unfoldC alg a unfold a in behFun resp. accC.
 
unfoldB :: Acc state -> state -> [String] -> Bool
unfoldB alg state = beta alg . foldl (delta alg) state
 
unfoldC :: Acc state -> state -> AccC
unfoldC alg state = DA {deltaC = unfoldC alg . delta alg state,
			betaC = beta alg state}

-- The Acc-algebra accNDA f is the power automaton obtained from the 
-- nondeterministic acceptor f.

accNDA :: NDA -> (Acc [Int],[Int])
accNDA nda = (Acc {delta = (epsHull .) . deltaP, beta = (elem 1)},epsHull [0])
           where deltaP :: [Int] -> String -> [Int]
                 deltaP qs x = unionMap (flip nda $ scan x) qs 
                 epsHull :: [Int] -> [Int]
                 epsHull qs = if all (`elem` qs) qs' then qs 
           		      else epsHull $ qs `union` qs'
                              where qs' = deltaP qs "eps"
                 scan :: String -> String
                 scan x = case runC int ((1,1),x) :: Either String Int of 
                   	  Right _ -> "Int"
                   	  _ -> case runC bool ((1,1),x) :: Either String Bool of
        		         	 Right _ -> "Bool"
        		         	 _ -> x
	
-- The Acc(String)-algebra accT rules is the Brzozowski automaton for
-- regular expressions and the CFG given by rules.

accT :: Rules -> Acc RegT 
accT rules = Acc {delta = delta, beta = beta} where
             delta = \case Par t u -> \x -> Par (delta t x) $ delta u x
			   Seq t u -> \x -> let v = Seq (delta t x) u
					    in if beta t then Par v $ delta u x
					     	         else v
		           Iter t  -> \x -> Seq (delta t x) $ Iter t
		           Base "eps"  -> const mt
		           Base "mt"   -> const mt
		           Base "Int"  -> mkReg int
		           Base "Bool" -> mkReg bool
		           Base c      -> \x -> if x == c then one else mt
		           Var s       -> delta $ eqs rules s
	     beta = \case Par t u -> beta t || beta u
		          Seq t u -> beta t && beta u
		          Iter t  -> True
		          Base b  -> b == "eps"
		          Var s   -> beta $ eqs rules s
	     mkReg p = runAndApp p (const mt) $ const one	
	     one = Base "eps"
	     mt  = Base "mt"

accNorm :: Rules -> Acc RegT 
accNorm rules = Acc {delta = \s -> foldReg regNorm . delta alg s,
		     beta = beta alg}
                where alg = accT rules

				 		       
-- COMPILER

done :: Monad m => m ()
done = return ()

-- transition monad and basic compilers
	       
newtype StateT state m a = StateT {runST :: state -> m (a,state)}

instance Monad m => Functor (StateT state m) where fmap = liftM
 	 
instance Monad m => Applicative (StateT state m) where pure  = return
         					       (<*>) = liftM2 id

instance Monad m => Monad (StateT state m) where
	 return a = StateT $ \st -> return (a,st)
         StateT h >>= f = StateT $ (>>= \(a,st) -> runST (f a) st) . h

class Monad m => Compiler m where
      type Input m :: *
      errmsg :: Input m -> m a
      empty  :: Input m -> m Bool
      ht     :: Input m -> m (Char,Input m)
      plus   :: m a -> m a -> m a

type Trans m = StateT (Input m) m

instance Compiler [ ] where 
	 type Input [ ] = String
	 errmsg _ = []
	 empty = return . null
	 ht (c:str) = [(c,str)]
	 plus = (++)
	 
instance Compiler (Either String) where
         type Input (Either String) = (Pos,String)
	 errmsg (pos,_) = Left $ "error at position "++show pos
         empty = return . null . snd
         ht ((i,j),c:str) = Right (c,(pos,str)) where
                            pos = if c == '\n' then (i+1,1) else (i,j+1)
         Left _ `plus` m = m
         m `plus` _      = m

runC :: Compiler m => Trans m a -> Input m -> m a
runC comp input = do (a,input) <- runST comp input
 		     b <- empty input
                     if b then return a else errmsg input

runAndApp :: Trans (Either String) a -> (String -> b) -> (a -> b) -> String -> b
runAndApp comp applyL applyR input = case runC comp ((1,1),input) of 
        		                  Left str -> applyL str
        		                  Right a -> applyR a
			     
cplus :: Compiler m => Trans m a -> Trans m a -> Trans m a
StateT g `cplus` StateT h = StateT $ liftM2 plus g h

csum :: Compiler m => [Trans m a] -> Trans m a
csum = foldr1 cplus 

some, many :: Compiler m => Trans m a -> Trans m [a]
some comp = do a <- comp; as <- many comp; return $ a:as
many comp = csum [some comp, return []]

cguard :: Compiler m => Bool -> Trans m ()
cguard b = if b then done else StateT errmsg

sat :: Compiler m => (Char -> Bool) -> Trans m Char
sat f = StateT $ \input -> do b <- empty input
                              let err = errmsg input
			      p@(c,_) <- if b then err else ht input
                              if f c then return p else err
		 
char :: Compiler m => Char -> Trans m Char
char chr = sat (== chr)

nchar :: Compiler m => String -> Trans m Char
nchar chrs = sat (`notElem` chrs)
    	     
digit,letter,delim :: Compiler m => Trans m Char
digit  = csum $ map char ['0'..'9']
letter = csum $ map char $ ['a'..'z']++['A'..'Z']
delim  = csum $ map char " \n\t"

string :: Compiler m => String -> Trans m String
string = mapM char

bool :: Compiler m => Trans m Bool
bool  = csum [do string "True"; return True,
              do string "False"; return False]

nat,int :: Compiler m => Trans m Int
nat = do ds <- some digit; return $ read ds
int = csum [nat, do char '-'; n <- nat; return $ -n]

identifier :: Compiler m => Trans m String 
identifier = do ident <- liftM2 (:) letter $ many 
					   $ nchar "(){}<>=!&|+-*/^.,:; \n\t"
		cguard $ ident `notElem` words "eps Mt Int Bool"
		return ident
		 
relation :: Compiler m => Trans m String
relation  = csum $ map string $ words "<= >= < > == !="

token :: Compiler m => Trans m a -> Trans m a
token comp = do many delim; a <- comp; many delim; return a 

tchar :: Compiler m => Char -> Trans m Char
tchar = token . char

tstring :: Compiler m => String -> Trans m String
tstring = token . string

tbool :: Compiler m => Trans m Bool
tbool = token bool

tint :: Compiler m => Trans m Int
tint = token int

tidentifier,trelation :: Compiler m => Trans m String
tidentifier = token identifier
trelation   = token relation

-- Reg(String)-compiler

compReg :: Compiler m => Rules -> Reg reg -> Trans m reg 
compReg rules alg = do r <- summand
	               csum [do tchar '+'; r' <- compReg rules alg
	                        return $ par alg r r',
			     return r] where
	            summand = do r <- iterC; csum [do tchar '.'; r' <- summand
		                                      return $ seq_ alg r r',
			                           return r]
	            iterC = do r <- factor
		               csum [do stars <- some $ tchar '*'
				        return $ iterate (iter alg) r
				    	         !!length stars,
	                            return r]
	            factor = csum [do tstring "eps"; return $ base alg "eps",
	      		           do tstring "mt"; return $ base alg "mt",
			           do tstring "Int"; return $ base alg "Int",
			           do tstring "Bool"; return $ base alg "Bool",
			           do x <- tidentifier
			              return $ if x `elem` map fst rules
			                       then var alg x else base alg x,
			           do tchar '('; r <- compReg rules alg
			              tchar ')'; return r]
	       
-- loop beh applies the behavior function beh to interactively entered lists of 
-- strings.

loop :: ([String] -> Bool) -> IO ()
loop beh = do putStrLn $ "Enter a list of strings separated " ++
                         "by blanks or a call of the function exa!"
	      str <- getLine 
	      let ws = words str
	          ws' = case ws of ["exa",arg] -> words $ exa $ read arg
	          		   _ -> ws
              when (not $ null ws') $ do putStrLn $ if beh ws' then "accepted" 
              						       else "rejected"
              			         loop beh

-- reg2alg file n exp reads the rules of a context-free grammar G from file and
-- compiles regular expression (exp), possibly including non-terminals of G into 
-- the value (state) of exp in a Reg(String)-algebra (regT, regB, regA, regNDA, 
-- regNorm or regWord).

-- If n < 6, then the algebra has the same carrier as a corresponding Acc(x)-
-- algebra alg, i.e., a deterministic acceptor of the language of exp (accT,
-- accNorm, behFun, accC or accNDA, respectively), and reg2alg n exp proceeds
-- with calling unfoldBLoop alg state.

reg2alg :: String -> String -> Int -> IO ()
reg2alg file input n = 
               do w <- readFile file `catch` handler
                  let ws = words w
                      rules = if null ws then [] else zip (init ws) $ tail ws
                      run :: Reg a -> (a -> IO ()) -> IO ()
                      run alg a = runAndApp (compReg rules alg) putStrLn a input
                  case n of 1 -> run (regB rules) loop
         	            2 -> run (regA rules) $ loop . unfoldB accC
         	            3 -> run regT $ loop . unfoldB (accT rules)
         	            4 -> run regT $ loop . unfoldB (accNorm rules)
         	            5 -> run regNDA $ loop . uncurry unfoldB . accNDA
         	           			   . fst . ($ emptyNDA)
         	            6 -> run regT $ mkTreeC "regterm" . show
         	            7 -> run regNorm $ mkTreeC "regnorm" . show
         	            _ -> run regWord $ \f -> putStrLn $ f 0 
               where handler :: IOError -> IO String
		     handler _ = return ""
		     emptyNDA = (const $ const [],0,1,2)
          	 
-- Examples

reg1 = "((aa.Int+b)*+cc.Bool.d*)*"
reg2 = "(Bool+Int+c+ab)*"
reg3 = "((a+b.a)*.c)*"

-- reg2alg "" reg1 n  	accepts  "aa 666 b cc True d".
-- reg2alg "" reg2 n  	accepts  "c ab -4 ab True c".
-- reg2alg "" reg3 n  	accepts  "c b a c a a c".

-- contents of sab: S  a.B+b.A+eps   A  a.S+b.A.A   B  b.S+a.B.B"
--       	    T  a.T.U+a.U     U  b+Int

exa 0 = "a b b b a a"
exa 1 = "a b a b b a b a a b"
exa 2 = "a b a b b a a a b a b b a b a b b a a b b a b a a b b a"
exa 3 = "a b a b b a b b a b"
exa 4 = "a a b a b b a b a a b d"
exa 5 = unwords $ replicate 55 "a"++replicate 55 "b"
exa 6 = unwords $ replicate 55 "a"++replicate 54 "77"++["87"]
exa 7 = unwords $ replicate 55 "a"++replicate 56 "b"

-- reg2alg "sab" "S" n      	accepts exa 0,exa 1,exa 2.
-- reg2alg "sab" "S" n 	rejects exa 3.
-- reg2alg "sab" "a.S.d" n 	accepts exa 4.
-- reg2alg "sab" "T" n 	accepts exa 5,exa 6.
-- reg2alg "sab" "T" n 	rejects exa 7.


-- A simple parser for regular expressions and CFGs               

data Reg_ = Eps | Empty | Reg_ :+ Reg_ | Reg_ :* Reg_ | Star Reg_ | Plus Reg_ | 
	    Bool | Int | Z String | S String deriving Eq

infixr 6 :+
infixr 7 :*

reg :: Compiler m => (String -> Reg_) -> Reg_ -> Trans m ()
reg eqG = f where f Eps      = done
                  f Empty    = StateT errmsg
		  f (t :+ u) = f t `cplus` f u
		  f (t :* u) = f t >> f u
		  f (Star t) = f (Plus t) `cplus` done
		  f (Plus t) = f t >> f (Star t)
		  f (Z s)    = string s >> done
		  f (S s)    = f (eqG s) >> done
		  f Bool     = bool >> done
		  f Int      = int >> done

emptyG,eqSAB :: String -> Reg_

emptyG = const Eps

eqSAB "S" = Z"a":*S"B":+Z"b":*S"A":+Eps   	-- S -> a*B|b*A|Eps
eqSAB "A" = Z"a":*S"S":+Z"b":*S"A":*S"A"	-- A -> a*S|b*A*A
eqSAB "B" = Z"b":*S"S":+Z"a":*S"B":*S"B"	-- B -> b*S|a*B*B
eqSAB "T" = Z"a":*S"T":*Z"b":+Eps		-- T -> a*T*b|Eps
eqSAB "I" = Z"a":*S"I":*Int:*Z" ":+Eps		-- I -> a*I*Int*blank|Eps

reg0 = Plus $ Bool:+Int:+Z"c":+Z"ab"

pa :: Int -> [((),String)]
pa 0 = runST (reg emptyG $ Z"ab":*Empty) "ab"           		-- :-(
pa 1 = runST (reg emptyG $ Plus $ Z"c":+Z"ab") "cabacc" 		-- :-(
pa 2 = runST (reg emptyG reg0) "cab-4abTruec"           		-- :-)
pa 3 = runST (reg emptyG reg0) "cab55abcc"              		-- :-)
pa 4 = runST (reg eqSAB $ S"S") "ababbabaab"            		-- :-)
pa 5 = runST (reg eqSAB $ S"S") "ababbabbab"            		-- :-(
pa 6 = runST (reg eqSAB $ S"S") "abaaababbbba"          		-- :-)
pa 7 = runST (reg eqSAB $ S"S") "ababbaaababbababbaabbabaabba" 		-- :-)
pa 8 = runST (reg eqSAB $ S"T") $ replicate 55 'a'++replicate 55 'b' 	-- :-)
pa 9 = runST (reg eqSAB $ S"T") $ replicate 55 'a'++replicate 56 'b'    -- :-(
pa _ = runST (reg eqSAB $ S"I") $ replicate 55 'a'++
				  concat (replicate 54 "77 ")++"8 " 	-- :-)

				 		        
-- From binary to decimal rationals

data Bin nat rat = Bin {o,i:: nat, appN0 :: nat -> nat, appN1 :: nat -> nat,
		        nat_ :: nat -> rat, appR0 :: rat -> rat, 
		        appR1 :: rat -> rat}

floatAlg :: Bin Float (Float,Float)
floatAlg = Bin {o = 0, i = 1, appN0 = \n -> 2*n, appN1 = \n -> 2*n+1,
	        nat_ = \n -> (n,1), 
	        appR0 = \(r,inc) -> (r,inc/2),
	        appR1 = \(r,inc) -> (r+inc/2,inc/2)}

binNat :: Compiler m => Bin nat rat -> Trans m nat
binNat alg = csum [do tchar '0'; loop $ o alg,
  	           do tchar '1'; loop $ i alg]
             where loop bin = csum [do tchar '0'; loop $ appN0 alg bin,
		   	            do tchar '1'; loop $ appN1 alg bin,
		   	            return bin]
				 
binRat :: Compiler m => Bin nat rat -> Trans m rat
binRat alg = csum [do bin <- binNat alg
                      csum [do tchar '.'; loop $ nat_ alg bin,
			    return $ nat_ alg bin]]
	     where loop bin = csum [do tchar '0'; loop $ appR0 alg bin,
		   	            do tchar '1'; loop $ appR1 alg bin,
		   	            return bin]

bin1 = runAndApp (binRat floatAlg) id show "101.011"
						    -- > (5.375,0.125)
bin2 = runAndApp (binRat floatAlg) id show "101.021"
						    -- > error at position (1,6)

data NatT = O | I | AppN0 NatT | AppN1 NatT 
data RatT = N NatT | AppR0 RatT | AppR1 RatT 

compNat :: NatT -> Float
compNat O 	  = 0
compNat I 	  = 1
compNat (AppN0 n) = 2*compNat n
compNat (AppN1 n) = 2*compNat n+1

compRat :: RatT -> (Float,Float)
compRat (N n)     = (compNat n,1)
compRat (AppR0 r) = (val,inc/2)       where (val,inc) = compRat r
compRat (AppR1 r) = (val+inc/2,inc/2) where (val,inc) = compRat r
		        
foldBinN :: Bin nat rat -> NatT -> nat
foldBinN alg O = o alg
foldBinN alg I = i alg
foldBinN alg (AppN0 n) = appN0 alg $ foldBinN alg n
foldBinN alg (AppN1 n) = appN1 alg $ foldBinN alg n
		        
foldBinR :: Bin nat rat -> RatT -> rat
foldBinR alg (N n)     = nat_ alg $ foldBinN alg n
foldBinR alg (AppR0 r) = appR0 alg $ foldBinR alg r
foldBinR alg (AppR1 r) = appR1 alg $ foldBinR alg r


-- SAB compiler

-- r1 = S -> aB 	 r2 = S -> bA		r3 = S -> eps	
-- r4 = A -> aS		 r5 = A -> bAA          
-- r6 = B -> bS		 r7 = B -> aBB	        

data SAB s a b = SAB {f_1 :: b -> s, f_2 :: a -> s, f_3 :: s,
		      f_4 :: s -> a, f_5 :: a -> a -> a,
		      f_6 :: s -> b, f_7 :: b -> b -> b}

transS :: Compiler m => SAB s a b -> Trans m s
transS alg = csum [do char 'a'; c <- transB alg; return $ f_1 alg c,
                   do char 'b'; c <- transA alg; return $ f_2 alg c,
		   return $ f_3 alg]
		  
transA :: Compiler m => SAB s a b -> Trans m a
transA alg = csum [do char 'a'; c <- transS alg; return $ f_4 alg c,
 		   do char 'b'; c <- transA alg; d <- transA alg
		      return $ f_5 alg c d]
		  
transB :: Compiler m => SAB s a b -> Trans m b
transB alg = csum [do char 'b'; c <- transS alg; return $ f_6 alg c,
		   do char 'a'; c <- transB alg; d <- transB alg
		      return $ f_7 alg c d]

type Pos = (Int,Int)
			    
sabCount :: SAB Pos Pos Pos
sabCount = SAB {f_1 = suc1, f_2 = suc2, f_3 = (0,0), 
		f_4 = suc1, f_5 = \(i,j) (k,l) -> (i+k,j+l+1),
		f_6 = suc2, f_7 = \(i,j) (k,l) -> (i+k+1,j+l)}
	   where suc1 (i,j) = (i+1,j); suc2 (i,j) = (i,j+1)

sab1 = runAndApp (transS sabCount) id show "aabaabbabb" 	
						    -- > (5,5)
sab2 = runAndApp (transS sabCount) id show "aababbabb" 	
						    -- > error at position (1,9)
sab3 = runAndApp (transB sabCount) id show "aababbabb" 	
						    -- > (4,5)
				   
data S = F1 B | F2 A | F3  deriving Show
data A = F4 S | F5 A A     deriving Show
data B = F6 S | F7 B B     deriving Show
				   
sabTerm :: SAB S A B
sabTerm = SAB F1 F2 F3 F4 F5 F6 F7


-- XMLstore

data XMLstore store orders person emails email items stock suppliers id =
     XMLstore {store     :: stock -> store, 
               storeO    :: orders -> stock -> store, 
               orders    :: person -> items -> orders -> orders,
               embedO    :: person -> items -> orders,
               person    :: String -> person, 
               personE   :: String -> emails -> person, 
               emails    :: email -> emails -> emails,
               none      :: emails,
               email     :: String -> email,
               items     :: id -> String -> items -> items,
               embedI    :: id -> String -> items,
               stock     :: id -> Int -> suppliers -> stock -> stock,
               embedS    :: id -> Int -> suppliers -> stock,
               supplier  :: person -> suppliers,
               parts     :: stock -> suppliers,
               id_       :: String -> id}

data Store     = Store Stock | StoreO (Orders,Stock) deriving Show
data Orders    = Orders (Person,Items,Orders) | EmbedP (Person,Items)
		 deriving Show
data Person    = Person String | PersonE (String,Emails) deriving Show
data Emails    = Emails (Email,Emails) | None deriving Show
data Email     = Email String deriving Show 
data Items     = Items (Id,String,Items) | EmbedI (Id,String) deriving Show
data Stock     = Stock (Id,Int,Suppliers,Stock) | EmbedS (Id,Int,Suppliers) 
		 deriving Show
data Suppliers = Supplier Person | Parts Stock deriving Show
data Id        = Id String deriving Show

xmlTerm :: XMLstore Store Orders Person Emails Email Items Stock Suppliers Id 
xmlTerm = XMLstore Store (curry StoreO) (curry3 Orders) (curry EmbedP) Person 
                   (curry PersonE) (curry Emails) None Email (curry3 Items)
                   (curry EmbedI) (curry4 Stock) (curry3 EmbedS) Supplier Parts 
                   Id
		 
curry3 f a b c   = f (a,b,c) 
curry4 f a b c d = f (a,b,c,d) 

type Store'     = (Orders',Stock')
type Orders'    = [(Person',Items')]
type Person'    = (String,Emails') 
type Emails'    = [Email']
type Email'     = String
type Items'     = [(Id',String)]
type Stock'     = [(Id',Int,Suppliers')]
data Suppliers' = Pers Person' | Stoc Stock' deriving Show
type Id'        = String

xmlList :: XMLstore Store' Orders' Person' Emails' Email' Items' Stock' 
                    Suppliers' Id'
xmlList  = XMLstore {store = \st -> ([],st),
                     storeO = \ords st -> (ords,st),
		     orders = \p i os -> (p,i):os,
		     embedO = \p i -> [(p,i)],
		     person = \str -> (str,[]),
		     personE = \str ems -> (str,ems),
		     emails = \em ems -> em:ems,
		     none = [],
		     email = id,
		     items = \id str is -> (id,str):is,
		     embedI = \id str -> [(id,str)],
		     stock = \id qty supps st -> (id,qty,supps):st,
		     embedS = \id qty supps -> [(id,qty,supps)],
		     supplier = Pers,
		     parts = Stoc,
		     id_ = id}

compStore :: Compiler m => XMLstore s1 s2 s3 s4 s5 s6 s7 s8 s9 -> Trans m s1
compStore alg = do tstring "<store>"
	           csum [do stck <- stock'; return $ store alg stck,
		         do ords <- ordersC; stck <- stock'
			    return $ storeO alg ords stck] where
	           stock'    = do tstring "<stock>"; stck <- stockC
	      		          tstring "</stock>"; tstring "</store>"
	      		          return stck
                   ordersC   = do (p,is) <- order
                                  csum [do os <- ordersC
                                           return $ orders alg p is os,
                                        return $ embedO alg p is]
                   order     = do tstring "<order>"; tstring "<customer>"
		                  p <- personC; tstring "</customer>"
			          is <- itemsC; tstring "</order>"
			          return (p,is)
	           personC   = do tstring "<name>"; name <- text
	                          tstring "</name>"
         	                  csum [do ems <- emailsC
         	            	           return $ personE alg name ems,
				        return $ person alg name]
	           emailsC   = csum [do em <- emailC; ems <- emailsC
	                                return $ emails alg em ems,
			             return $ none alg]
	           emailC    = do tstring "<email>"; em <- text
	                          tstring "</email>"; return $ email alg em
	           itemsC    = do (id,price) <- item
	      		          csum [do is <- itemsC
	      		    	           return $ items alg id price is,
	      		      	        return $ embedI alg id price]
	           item      = do tstring "<item>"; id <- idC; tstring "<price>"
		                  price <- text; tstring "</price>"
			          tstring "</item>"; return (id,price)
	           stockC    = do (id,qty,supps) <- iqs
	      		          csum [do is <- stockC
	      		      	           return $ stock alg id qty supps is,
	      		      	        return $ embedS alg id qty supps]
	           iqs       = do tstring "<item>"; id <- idC
	                          tstring "<quantity>"; qty <- tint
	                          tstring "</quantity>"; supps <- suppliers
	                          tstring "</item>"; return (id,qty,supps)
	           suppliers = csum [do tstring "<supplier>"; p <- personC
		                        tstring "</supplier>"
		                        return $ supplier alg p,
			             do stck <- stockC; return $ parts alg stck]
	           idC       = do tstring "<id>"; t <- text; tstring "</id>"
		                  return $ id_ alg t
	       
text :: Compiler m => Trans m String
text = do strs <- some $ token $ some $ nchar "< \n\t"
          return $ unwords strs
			      
-- xml2alg file compiles the XML text stored in file to an element of xmlTerm
-- or xmlList and draws the result in Pix/xmllist.svg.
			    
xml2alg :: String -> Int -> IO ()
xml2alg file = readFileAndDo file .
		               \case 1 -> runAndApp (compStore xmlTerm) putStrLn
		 			            $ mkTreeC "xmlterm" . show
		 	             _ -> runAndApp (compStore xmlList) putStrLn
		 			            $ mkTreeC "xmllist" . show

