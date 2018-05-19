{-# LANGUAGE TypeSynonymInstances, ScopedTypeVariables, MultiParamTypeClasses, 
             FlexibleInstances, FunctionalDependencies, LambdaCase #-}
             
-- JavaLight and its compilers into syntax trees, a state model and an assembly 
-- language

-- 16.3.2018

module Java where

import Control.Monad (when,liftM2)
import Painter (readFileAndDo,mkTreeC,Tree(F),update,fold2)
import Compiler (Compiler,Trans,runAndApp,cplus,csum,tchar,tstring,tbool,tint,
		 tidentifier,trelation,rel)
		 
curry3 f a b c = f (a,b,c)

data JavaExp sum prod factor = 
     JavaExp {sum_       :: prod -> sum,
     	      plus,minus :: sum -> prod -> sum,
     	      prod       :: factor -> prod,
     	      times,div_ :: prod -> factor -> prod,
     	      embedI	 :: Int -> factor,
     	      var        :: String -> factor,
     	      encloseS   :: sum -> factor}

-- subsignature of derec(JavaExp)

data SumProd sum sumsect prod prodsect factor = 
     SumProd {sum'         :: prod -> sumsect -> sum,
              plus',minus' :: prod -> sumsect -> sumsect,
              nilS         :: sumsect,
              prod'        :: factor -> prodsect -> prod,
              times',div'  :: factor -> prodsect -> prodsect,
              nilP         :: prodsect}

data JavaCom commands command sum disjunct conjunct literal = 
     JavaCom {seq_       :: command -> commands -> commands,
     	      embed      :: command -> commands,
     	      block      :: commands -> command,
     	      assign     :: String -> sum -> command,
     	      cond       :: disjunct -> command -> command -> command,
     	      cond1,loop :: disjunct -> command -> command,
     	      disjunct   :: conjunct -> disjunct -> disjunct,
     	      embedC     :: conjunct -> disjunct,
     	      conjunct   :: literal -> conjunct -> conjunct,
     	      embedL     :: literal -> conjunct,
     	      not_       :: literal -> literal,
     	      atom	 :: String -> sum -> sum -> literal,
     	      embedB     :: Bool -> literal,
     	      encloseD   :: disjunct -> literal}
     	        
-- extension of JavaExp- to SumProd-algebras

derec :: JavaExp sum prod factor 
	 -> SumProd sum (sum -> sum) prod (prod -> prod) factor	 
derec alg = SumProd {sum'   = \a h   -> h $ sum_ alg a,
		     plus'  = \a h b -> h $ plus alg b a,
		     minus' = \a h b -> h $ minus alg b a,
		     nilS   = id,
		     prod'  = \a h   -> h $ prod alg a,
		     times' = \a h b -> h $ times alg b a,
		     div'   = \a h b -> h $ div_ alg b a,
		     nilP   = id}
		       
-- terms

data Commands  = Seq (Command,Commands) | Embed Command deriving Show
data Command   = Block Commands | Assign (String,Sum) | 
		 Cond (Disjunct,Command,Command) | Cond1 (Disjunct,Command) | 
		 Loop (Disjunct,Command) deriving Show
data Sum       = SUM Prod | PLUS (Sum,Prod) | MINUS (Sum,Prod) |
	         Sum (Prod,Sumsect) deriving Show
data Sumsect   = Plus (Prod,Sumsect) | Minus (Prod,Sumsect) | NilS deriving Show
data Prod      = PROD Factor | TIMES (Prod,Factor) | DIV (Prod,Factor) |
		 Prod (Factor,Prodsect) deriving Show
data Prodsect  = Times (Factor,Prodsect) | Div_ (Factor,Prodsect) | NilP 
		 deriving Show
data Factor    = EmbedI Int | Var String | EncloseS Sum deriving Show 
data Disjunct  = Disjunct (Conjunct,Disjunct) | EmbedC Conjunct deriving Show
data Conjunct  = Conjunct (Literal,Conjunct) | EmbedL Literal deriving Show
data Literal   = Not Literal | Atom (String,Sum,Sum) | EmbedB Bool | 
		 EncloseD Disjunct deriving Show

-- term algebras

termExp,termExp' :: JavaExp Sum Prod Factor

termExp = JavaExp {sum_ = SUM, plus = curry PLUS, minus = curry MINUS, 
	           prod = PROD, times = curry TIMES, div_ = curry DIV,
	           embedI = EmbedI, var = Var, encloseS = EncloseS}
	           
termExp' = termExp {sum_ = sum_, plus = plus, minus = minus, 
                    prod = prod, times = times, div_ = div_}
	   where sum_ t = Sum (t,NilS)
	         plus (Sum (t,t')) u  = Sum (t,Plus (u,t'))
	         minus (Sum (t,t')) u = Sum (t,Minus (u,t'))
	         prod t = Prod (t,NilP)
	         times (Prod (t,t')) u = Prod (t, Times(u,t'))
	         div_ (Prod (t,t')) u  = Prod (t, Div_(u,t'))

termCom :: JavaCom Commands Command Sum Disjunct Conjunct Literal
termCom = JavaCom {seq_ = curry Seq, embed = Embed, block = Block, 
	           assign = curry Assign, cond = curry3 Cond, 
	           cond1 = curry Cond1, loop = curry Loop, 
	           disjunct = curry Disjunct, embedC = EmbedC, 
	           conjunct = curry Conjunct, embedL = EmbedL, 
	           not_ = Not, atom = curry3 Atom, embedB = EmbedB, 
	           encloseD = EncloseD}

-- word algebras

wordExp :: JavaExp String String String
wordExp = JavaExp {sum_       = id, 
		   plus       = \e e' -> e++'+':e',
                   minus      = \e e' -> e++'-':e,
                   prod       = id, 
                   times      = \e e' -> e++'*':e',
                   div_       = \e e' -> e++'/':e',
                   embedI     = show,
                   var        = id, 
                   encloseS   = \e -> '(':e++")"}

wordCom :: JavaCom String String String String String String
wordCom = JavaCom {seq_       = (++),
    		   embed      = id,
    		   block      = \cs -> " {"++cs++"}",
    		   assign     = \x e -> x++" = "++e++"; ",
    		   cond       = \e c c' -> "if "++e++c++" else"++c',
    		   cond1      = \e c -> "if "   ++e++c,
    		   loop       = \e c -> "while "++e++c,
    		   disjunct   = \e e' -> e++" || "++e',
    		   embedC     = id,
    		   conjunct   = \e e' -> e++" && "++e',
    		   embedL     = id,
    		   not_       = \be -> '!':be,
    		   atom       = \rel e e' -> e++rel++e',
    		   embedB     = show,
    		   encloseD   = \e -> '(':e++")"}
		      		      	   
-- derivation tree algebras

type TS = Tree String

deriExp :: JavaExp TS TS TS
deriExp = JavaExp {sum_       = \e -> F "Sum" [e],
                   plus       = \e e' -> F "Sum" [e,e'],
                   minus      = \e e' -> F "Sum" [e,e'],
                   prod       = \e -> F "Prod" [e],
                   times      = \e e' -> F "Prod" [e,e'],
                   div_       = \e e' -> F "Prod" [e,e'],
                   embedI     = \i -> factor [leaf $ show i],
                   var        = \x -> factor [leaf x],
                   encloseS   = \e -> factor [leaf "(",e,leaf ")"]}
          where factor = F "Factor"; leaf = flip F []

deriCom :: JavaCom TS TS TS TS TS TS
deriCom = JavaCom {seq_       = \c c' -> F "Commands" [c,c'],
                   embed      = \c -> F "Commands" [c],
                   block      = \c -> command [c],
                   assign     = \x e -> command [leaf x,leaf "=",e,leaf ";"],
                   cond       = \e c c' -> command [leaf "if",e,c,
		    				    leaf "else",c'],
                   cond1      = \e c -> command [leaf "if",e,c],
                   loop       = \e c -> command [leaf "while",e,c],
                   disjunct   = \e e'-> F "Disjunct" [e,leaf "||",e'],
                   embedC     = \e -> F "Disjunct" [e],
                   conjunct   = \e e'-> F "Conjunct" [e,leaf "&&",e'],
                   embedL     = \e -> F "Conjunct" [e],
                   not_       = \be -> literal [leaf "!",be],
                   atom       = \rel e e' -> literal [e,leaf rel,e'],
                   embedB     = \b -> literal [leaf $ show b],
                   encloseD   = \e -> literal [leaf "(",e,leaf ")"]}
          where command = F "Command"; literal = F "Literal"; leaf = flip F []
	         
-- hierarchical-list algebras

type BIS = Bool -> Int -> String

listExp :: JavaExp BIS BIS BIS
listExp = JavaExp {sum_     = indent1 "sum",
		   plus     = indent2 "plus",
		   minus    = indent2 "minus",
		   prod     = indent1 "prod",
		   times    = indent2 "times",
		   div_     = indent2 "div",
		   embedI   = indent1 "embedI" . indent0 . show,
		   var      = indent1 "var" . indent0,
		   encloseS = indent1 "encloseS"}

listCom :: JavaCom BIS BIS BIS BIS BIS BIS
listCom = JavaCom {seq_     = indent2 "seq", 
		   embed    = indent1 "embed", 
		   block    = indent1 "block", 
		   assign   = indent2 "assign" . indent0,
		   cond     = indent3 "cond", 
		   cond1    = indent2 "cond1",
		   loop     = indent2 "loop",
		   disjunct = indent2 "disjunct",      
		   embedC   = indent1 "embedC",
		   conjunct = indent2 "conjunct", 
		   embedL   = indent1 "embedL",
		   not_     = indent1 "not", 
		   atom     = indent3 "atom" . indent0,
		   embedB   = indent1 "embedB" . indent0 . show,
		   encloseD = indent1 "encloseD"}
                      
indent0 x       = blanks x []
indent1 x f     = blanks x [f]
indent2 x f g   = blanks x [f,g]
indent3 x f g h = blanks x [f,g,h]
blanks :: String -> [BIS] -> BIS
blanks x fs b n = if b then str else '\n':replicate n ' '++str
 		  where str = case fs of f:fs -> x++' ':g True f++
					                concatMap (g False) fs
					 _ -> x
 			g b f = f b $ n+length x+1
	   
-- state model

stateExp :: JavaExp (Store -> Int) (Store -> Int) (Store -> Int) 
stateExp = JavaExp {sum_       = id,
                    plus       = liftM2 (+),
                    minus      = liftM2 (-),
                    prod       = id,
                    times      = liftM2 (*),
                    div_       = liftM2 div,
                    embedI     = const, 
                    var        = flip ($), 
                    encloseS   = id}

stateCom :: JavaCom (Store -> Store) (Store -> Store) (Store -> Int) 
		    (Store -> Bool) (Store -> Bool) (Store -> Bool)
stateCom = JavaCom {seq_       = flip (.),
		    embed      = id,
		    block      = id,
		    assign     = \x e st -> update st x $ e st,
		    cond       = cond,
		    cond1      = \p f -> cond p f id,
		    loop       = loop,
		    disjunct   = liftM2 (||),
		    embedC     = id,
		    conjunct   = liftM2 (&&),
		    embedL     = id,
		    not_       = (not .), 
		    atom       = liftM2 . rel,
		    embedB     = const,
		    encloseD   = id}
	   where cond p f g st = if p st then f st else g st
	         loop p f st   = if p st then loop p f $ f st else st 
                    
-- stack machine

type Store    = String -> Int		  
type Jstate = ([Int],Store,Int)
		
-- assembly language

data StackCom = Push Int | Pop | Load String | Save String | Add | Sub | Mul | 
		Div | Or_ | And_ | Inv | Cmp String | Jump Int | JumpF Int
		deriving (Eq,Show)

executeCom :: StackCom -> Jstate -> Jstate
executeCom com (stack,store,n) = 
          case com of Push a    -> (a:stack,store,n+1)
	              Pop       -> (tail stack,store,n+1)
		      Load x    -> (store x:stack,store,n+1)
		      Save x    -> (stack,update store x $ head stack,n+1)
		      Add       -> (a+b:s,store,n+1)	     where a:b:s = stack
		      Sub       -> (b-a:s,store,n+1)	     where a:b:s = stack
		      Mul       -> (a*b:s,store,n+1)         where a:b:s = stack
	              Div       -> (b`div`a:s,store,n+1)     where a:b:s = stack
	              Or_       -> (max a b:s,store,n+1)     where a:b:s = stack
		      And_      -> (a*b:s,store,n+1)	     where a:b:s = stack
		      Inv       -> ((a+1)`mod`2:s,store,n+1) where a:s = stack
	              Cmp str   -> (c:s,store,n+1) 
		                   where a:b:s = stack
		                         c = if rel str b a then 1 else 0
                      Jump k    -> (stack,store,k)
                      JumpF k   -> (stack,store,if head stack == 0 then k 
                      					           else n+1)

execute :: [StackCom] -> Jstate -> Jstate
execute cs state@(_,_,n) = if n >= length cs then state  
                           else execute cs $ executeCom (cs!!n) state
		       
-- stack algebra

type LCom = Int -> [StackCom]

stackExp :: JavaExp LCom LCom LCom
stackExp = JavaExp {sum_       = id, 
		    plus       = apply2 Add,
		    minus      = apply2 Sub,
		    prod       = id, 
		    times      = apply2 Mul,
		    div_       = apply2 Div,
		    embedI     = \i -> const [Push i],
		    var        = \x -> const [Load x], 
		    encloseS   = id}
		    
apply1 :: StackCom -> LCom -> LCom
apply1 op e lab = e lab++[op]

apply2 :: StackCom -> LCom -> LCom -> LCom
apply2 op e e' lab = code++e' (lab+length code)++[op] where code = e lab

stackCom :: JavaCom LCom LCom LCom LCom LCom LCom
stackCom = JavaCom {seq_    = \c c' lab -> let code = c lab
					   in code++c' (lab+length code),  
		    embed   = id, 
		    block   = id, 
		    assign  = \x e lab -> e lab++[Save x,Pop],
		    cond    = \e c c' lab 
		                  -> let code = e lab
		  	                 lab1 = lab+length code+1
		  	                 code1 = c lab1
		  	                 lab2 = lab1+length code1+1
		  	                 code2 = c' lab2
		  	                 exit = lab2+length code2
		  	             in code++JumpF lab2:code1++Jump exit:code2,
                    cond1   = \e c lab -> let code = e lab
                                              lab' = lab+length code+1
		  	                      code' = c lab'
		  	                      exit = lab'+length code'
		  	                  in code++JumpF exit:code',                    
                    loop    = \e c lab -> let code = e lab
		  	                      lab' = lab+length code+1
		  	                      code' = c lab'
		  	                      exit = lab'+length code'+1
		  	                  in code++JumpF exit:code'++[Jump lab],
		    disjunct = apply2 Or_,  
		    embedC   = id,
		    conjunct = apply2 And_, 
		    embedL   = id,
		    not_     = apply1 Inv,
		    atom     = apply2 . Cmp,
		    embedB   = \b -> const [Push $ if b then 1 else 0],
		    encloseD   = id}

-- JavaLight-compiler into the assembly language

compSum :: Compiler m => JavaExp sum prod factor -> Trans m sum
compSum alg = do e <- prod; f <- sumsect; return $ sum' alg' e f where
              alg' = derec alg
              sumsect = csum [do op <- csum $ map tchar "+-"
	                         e <- prod; f <- sumsect
	                         return $ if op == '+' then plus' alg' e f
	                                               else minus' alg' e f,
	                      return $ nilS alg']
              prod = do e <- factor; f <- prodsect; return $ prod' alg' e f
	      prodsect = csum [do op <- csum $ map tchar "*/"
	                          e <- factor; f <- prodsect
	                          return $ if op == '*' then times' alg' e f
	                                                else div' alg' e f,
	                       return $ nilP alg']
              factor = csum [do i <- tint; return $ embedI alg i,
		             do x <- tidentifier; return $ var alg x,
			     do tchar '('; e <- compSum alg; tchar ')'
			        return $ encloseS alg e]

compComms :: Compiler m => JavaCom commands command sum disjunct conjunct 
				   literal
		           -> JavaExp sum prod factor -> Trans m commands
compComms alg alg' = do c <- command
           	        csum [do cs <- compComms alg alg'
           	                 return $ seq_ alg c cs,
           		      return $ embed alg c] where
                     command = csum [do tstring "if"; e <- disjunctC
                                        c <- command
			                csum [do tstring "else"; c' <- command
			     	                 return $ cond alg e c c', 
			                      return $ cond1 alg e c], 
		                     do tstring "while"; e <- disjunctC
		                        c <- command; return $ loop alg e c,
			             do tchar '{'; cs <- compComms alg alg'
			                tchar '}'; return $ block alg cs,
			             do x <- tidentifier; tchar '='
			                e <- compSum alg'; tchar ';'
			                return $ assign alg x e]
                     disjunctC = do e <- conjunctC
           		            csum [do tstring "||"; e' <- disjunctC
           		                     return $ disjunct alg e e',
           		  	          return $ embedC alg e]
                     conjunctC = do e <- literal
	                            csum [do tstring "&&"; e' <- conjunctC
	                                     return $ conjunct alg e e',
	                  	          return $ embedL alg e]
                     literal = csum [do b <- tbool; return $ embedB alg b,
			             do tchar '!'; e <- literal
			                return $ not_ alg e, 
	              	             do e <- compSum alg'; rel <- trelation
	              	                e' <- compSum alg'
	              	                return $ atom alg rel e e',
			             do tchar '('; e <- disjunctC; tchar ')'
			                return $ encloseD alg e]
           
java2alg :: String -> Int -> IO ()
java2alg file = readFileAndDo file .
 \case 
     1  -> runAndApp (compSum termExp) putStrLn $ mkTree "javaterm"
     2  -> runAndApp (compSum termExp') putStrLn $ mkTree "javaterm'" 
     3  -> runAndApp (compSum wordExp) putStrLn $ writeFile "javaword"
     4  -> runAndApp (compSum deriExp) putStrLn $ mkTree "javaderi"
     5  -> runAndApp (compSum listExp) putStrLn act where
                 act (a::BIS) = writeFile "javalist" $ a True 0
     6  -> runAndApp (compSum stateExp) putStrLn loop where
      	         loop (a::Store -> Int) = do (vars,store) <- mkStore
                                             showValue vars (a store) $ loop a      
     7  -> runAndApp (compSum stackExp) putStrLn act where 
      	         act (a::LCom) = do let code = a 0
			            writeFile "javatarget" $ showCode code
				    loopStack True code
     8  -> runAndApp (compComms termCom termExp) putStrLn $ mkTree "javaterm"
     9  -> runAndApp (compComms termCom termExp') putStrLn $ mkTree "javaterm'"
     10 -> runAndApp (compComms wordCom wordExp) putStrLn $ writeFile "javaderi"
     11 -> runAndApp (compComms deriCom deriExp) putStrLn $ mkTree "javaderi"
     12 -> runAndApp (compComms listCom listExp) putStrLn act where
		 act (a::BIS) = writeFile "javalist" $ a True 0
     13 -> runAndApp (compComms stateCom stateExp) putStrLn loop where
	         loop (a::Store -> Store) = do (vars,store) <- mkStore
                                               showStore vars (a store) $ loop a
     _  -> runAndApp (compComms stackCom stackExp) putStrLn act where
	         act (a::LCom) = do let code = a 0
				    writeFile "javatarget" $ showCode code
				    loopStack False code
  where mkTree file = mkTreeC file . show
				              
showCode :: [StackCom] -> String
showCode = concat . zipWith f [0..]
	   where f n c = '\n':replicate (5-length lab) ' '++lab++": "++show c
	                 where lab = show n

mkStore :: IO ([String],Store)
mkStore = do putStrLn "Enter variables!"; varstring <- getLine
             putStrLn "Enter values!"; valstring <- getLine
             let vars = words varstring
                 vals = map read $ words valstring
	         vals' = vals++replicate (length vars-length vals) 0
	     return (vars, fold2 update (const 0) vars vals')
		    
showValue :: Show val => [String] -> val -> IO () -> IO ()
showValue vars val continue = when (not $ null vars) $ do putStrLn $ show val
						          continue
		    
showStore :: Show val => [String] -> (String -> val) -> IO () -> IO ()
showStore vars store continue = when (not $ null vars) $ do mapM_ g vars
							    continue
  		                where g x = putStrLn $ x++" = "++show (store x)
   
loopStack :: Bool -> [StackCom] -> IO ()
loopStack b code = do (vars,store) <- mkStore
		      let (val:_,store',_) = execute code ([],store,0)
                      if b then showValue vars val $ loopStack b code
                           else showStore vars store' $ loopStack b code
		                   
{- Beispiele

55/3-77+14/2				     	x = -52

1*2*3-4*5*6+1*2*3-250/25/5           	 	x = -110	

x=3+5*y+6; y=3*5*z;
 
x=11*x*3+5*x*2+16*x+33;

if x>0 x=33; else x=44;

fact=1; while x>1 {fact=fact*x; x=x-1;}		fact = x! 	
    
fact=1; while x>1 {fact=fact**x; x=x-1;} 	error at position (1,9)

if x>1 {fact = fact*x; x = x+1;} else =4; 	error at position (1,34)

if x>1 {fact = fact*x; x = x+1;} else {fact = fact*(x+3)-5/6*y; x = x-1;}

while x>0 && y<5+8/6 || !!z!=7 {fact = fact*x; x = x-1;}

while x>2 || y==7 {fact = fact*x; x = x-1; y = y+1;}

while x<n x=2*x;

while True x=5; y=;                      	error at position (1,17)

-}

