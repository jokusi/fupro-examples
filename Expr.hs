{-# LANGUAGE LambdaCase, TypeFamilies #-}

module Expr where

-- 27.3.2018

import Data.Maybe
import Control.Exception
import Control.Applicative (Applicative(pure,(<*>)),Alternative(empty,(<|>)))
import Control.Monad
import Painter (readFileContinue,readFileAndDo,fold2,mkInt,Rules,reduce,update,
                MaybeT(MaybeT,runMT),MonadTrans(type M,lift,liftT),Tree(V,F),
                root,mkTree,insert,updList)
import Coalg (TreeSig(TreeSig,var_,fun),foldTree,State(State),runS,
              StateT(StateT),runST)

instance Monad m => MonadPlus (MaybeT m) where
         mzero = MaybeT $ return Nothing
         m `mplus` m' = MaybeT $ do ma <- runMT m
                                    if isJust ma then return ma else runMT m' 

instance Monad m => Alternative (MaybeT m) where empty = mzero
                                                 (<|>) = mplus

single :: a -> [a]
single a = [a]

newtype ListT m a = ListT {runLT :: m [a]}

instance Monad m => Monad (ListT m) where
         return = ListT . return . single
         m >>= f = ListT $ do mas <- runLT m
                              mass <- mapM (runLT . f) mas
                              return $ concat mass
                                                
instance Monad m => MonadPlus (ListT m) where
         mzero = ListT $ return []
         m `mplus` m' = ListT $ do [mas,mas'] <- mapM runLT [m,m']
                                   return $ mas++mas'

instance Monad m => Functor (ListT m) where fmap = liftM 
         
instance Monad m => Applicative (ListT m) where pure  = return
                                                (<*>) = liftM2 id

instance Monad m => Alternative (ListT m) where empty = mzero
                                                (<|>) = mplus
                 
instance MonadTrans ListT where 
                    type M ListT = [ ] 
                    lift  = ListT . liftM single -- :: m a -> ListT m a
                    liftT = ListT . return       -- :: [a] -> ListT m a
                                                
instance MonadTrans (StateT state) where
                    type M (StateT state) = State state
                    lift m = StateT $ \st -> do a <- m; return (a,st)
                                                   -- :: m a -> StateT state m a
                    liftT (State f) = StateT $ return . f  
                                         -- :: State state a -> StateT state m a
                                                 
-- EXPRESSIONS

data Exp x = Con Int | Var x | Sum [Exp x] | Prod [Exp x] | Exp x :- Exp x | 
             Exp x :/ Exp x | Int :* Exp x | Exp x :^ Int deriving (Eq,Show)

zero,one :: Exp x
zero = Con 0
one  = Con 1

mul :: Exp x -> Exp x -> Exp x
mul e e' = Prod [e,e']
            
instance Functor Exp where 
         fmap f = \case Con i   -> Con i
                        Var x   -> Var $ f x
                        Sum es  -> Sum $ map (fmap f) es
                        Prod es -> Prod $ map (fmap f) es
                        e :- e' -> fmap f e :- fmap f e'
                        e :/ e' -> fmap f e :/ fmap f e'
                        i :* e  -> i :* fmap f e
                        e :^ i  -> fmap f e :^ i
            
instance Monad Exp where                                        -- Exp monad
         return = Var
         e >>= f = case e of Con i   -> Con i
                             Var x   -> f x
                             Sum es  -> Sum $ map (>>= f) es
                             Prod es -> Prod $ map (>>= f) es
                             e :- e' -> (e >>= f) :- (e' >>= f)
                             e :/ e' -> (e >>= f) :/ (e' >>= f)
                             i :* e  -> i :* (e >>= f)
                             e :^ i  -> (e >>= f) :^ i

instance Applicative Exp where pure  = return
                               (<*>) = liftM2 id
            
data BExp x = True_ | False_ | BVar x | Or [BExp x] | And [BExp x] |
              Not (BExp x) | Exp x :< Exp x | Exp x := Exp x | Exp x :<= Exp x
              deriving (Eq,Show)

-- def/use example

data DefUse x = Def x (Exp x) | Use x
         
trace :: Eq x => [DefUse x] -> Store x -> ([(x,Int)],Store x)
trace (Def x e:s) store = trace s $ updStore x e store
trace (Use x:s) store   = ((x,store x):s',store')
                          where (s',store') = trace s store
trace _ store           = ([],store)

updStore :: Eq x => x -> Exp x -> Store x -> Store x
updStore x e store = update store x $ eval store e

setS :: Eq x => x -> Exp x -> State (Store x) ()
setS x e = State $ \store -> ((),updStore x e store) 

getS :: x -> State (Store x) Int
getS x = State $ \store -> (store x,store) 
               
traceS :: Eq x => [DefUse x] -> State (Store x) [(x,Int)]  
traceS (Def x e:s) = do setS x e; traceS s
traceS (Use x:s)   = do i <- getS x; s' <- traceS s; return $ (x,i):s'
traceS _           = return []
               
traceIO :: (Eq x,Show x) => [DefUse x] -> StateT (Store x) IO ()  
traceIO (Def x e:s) = do liftT $ setS x e; traceIO s
traceIO (Use x:s)   = do i <- liftT $ getS x
                         lift $ putStrLn $ show (x,i)
                         traceIO s
traceIO _           = return ()
     
data V = X | Y | Z deriving (Eq,Show)

dflist :: [DefUse V]
dflist = [Def X $ Con 1,Use X,Def Y $ Con 2,Use Y,Def X $ Sum [Var X,Var Y],
          Use X,Use Y]
                  
tra,traS :: [(V,Int)]
tra  = fst $ trace dflist $ const 0             -- > [(X,1),(Y,2),(X,3),(Y,2)]    
traS = fst $ runS (traceS dflist) $ const 0     -- > [(X,1),(Y,2),(X,3),(Y,2)] 

traIO :: IO ((),Store V)
traIO = runST (traceIO dflist) $ const 0        -- > (X,1)
                                                --   (Y,2)
                                                --   (X,3)
                                                --   (Y,2)
-- evaluation of arithmetic expressions

eval :: Store x -> Exp x -> Int     
eval st = \case Con i   -> i
                Var x   -> st x
                Sum es  -> sum $ map f es
                Prod es -> product $ map f es
                e :- e' -> f e - f e'
                e :/ e' -> f e `div` f e'
                i :* e  -> i * f e
                e :^ i  -> f e ^ i    
          where f = eval st       
 
evalM :: Store x -> Exp x -> Maybe Int    
evalM st = \case Con i   -> Just i
                 Var x   -> Just $ st x
                 Sum es  -> fmap sum $ mapM f es
                 Prod es -> fmap product $ mapM f es
                 e :- e' -> liftM2 (-) (f e) $ f e'
                 e :/ e' -> do k <- m; guard $ k /= 0; liftM2 div (f e) m
                            where m = f e'
                 i :* e  -> fmap (i*) $ f e
                 e :^ i  -> fmap (^i) $ f e
            where f = evalM st    

evalR :: Exp x -> Store x -> Int        -- eval with do notation for
evalR = \case Con i   -> return i       -- for reader functor (->) (Store x)
              Var x   -> ($x)
              Sum es  -> fmap sum $ mapM evalR es
              Prod es -> fmap product $ mapM evalR es
              e :- e' -> liftM2 (-) (evalR e) $ evalR e'
              e :/ e' -> liftM2 div (evalR e) $ evalR e'
              i :* e  -> liftM2 (-) (const i) $ evalR e
              e :^ i  -> liftM2 (^) (evalR e) $ const i
                                     
writeVal :: Store String -> Exp String -> (String,Int)  -- with do notation for 
writeVal st e = case e of                               -- writer functor 
                     Con i   -> ("",i)                  -- (,) String
                     Var x   -> out $ st x
                     Sum es  -> fmap sum (mapM f es) >>= out
                     Prod es -> fmap product (mapM f es) >>= out
                     e :- e' -> liftM2 (-) (f e) (f e') >>= out
                     e :/ e' -> liftM2 div (f e) (f e') >>= out
                     i :* e  -> fmap (i*) (f e) >>= out
                     e :^ i  -> fmap (^i) (f e) >>= out
             where out i = ("The value of "++showExp e++" is "++show i++".\n",i)
                   f = writeVal st

-- arithmetic signatures

data Arith x val = Arith {con       :: Int -> val,
                          var       :: x -> val,
                          sum_,prod :: [val] -> val,
                          sub,div_  :: val -> val -> val,
                          scal      :: Int -> val -> val,
                          expo      :: val -> Int -> val}

data ArithP x val = ArithP {conP       :: Int -> val,           
                            varP       :: x -> val,
                            sumP,prodP :: [Exp x] -> [val] -> val,
                            subP,divP  :: Exp x -> val -> Exp x -> val -> val,
                            scalP      :: Int -> Exp x -> val -> val,
                            expoP      :: Exp x -> val -> Int -> val}
-- term algebra

arithT :: Arith x (Exp x)
arithT = Arith Con Var Sum Prod (:-) (:/) (:*) (:^) 

-- translator from ArithP to Arith

mkArith :: ArithP x val -> Arith x (Exp x,val)
mkArith alg = Arith {con  = \i -> (Con i,conP alg i),
                     var  = \x -> (Var x,varP alg x),   
                     sum_ = list Sum sumP,
                     prod = list Prod prodP,
                     sub  = bin (:-) subP,
                     div_ = bin (:/) divP,
                     scal = \i (e,a) -> (i:*e,scalP alg i e a),
                     expo = \(e,a) i -> (e:^i,expoP alg e a i)}
              where list c op eas = (c es,op alg es as) 
                                    where (es,as) = unzip eas
                    bin c op (e,a) (e',b) = (c e e',op alg e a e' b)

-- fold from the Arith-term algebra into an Arith-algebra

foldArith :: Arith x val -> Exp x -> val
foldArith alg = \case Con i   -> con alg i
                      Var x   -> var alg x
                      Sum es  -> sum_ alg $ map f es
                      Prod es -> prod alg $ map f es
                      e :- e' -> sub alg (f e) $ f e'
                      e :/ e' -> div_ alg (f e) $ f e'
                      i :* e  -> scal alg i $ f e
                      e :^ i  -> expo alg (f e) i
                where f = foldArith alg

-- paramorphic fold from the Arith-term algebra into an ArithP-algebra

paraArith :: ArithP x val -> Exp x -> val
paraArith alg = \case Con i   -> conP alg i
                      Var x   -> varP alg x
                      Sum es  -> sumP alg es $ map f es
                      Prod es -> prodP alg es $ map f es
                      e :- e' -> subP alg e (f e) e' $ f e'
                      e :/ e' -> divP alg e (f e) e' $ f e'
                      i :* e  -> scalP alg i e $ f e
                      e :^ i  -> expoP alg e (f e) i
                where f = paraArith alg

-- Arith-algebras
        
type Store x = x -> Int

evalAlg :: Arith x (Store x -> Int)         -- foldArith evalAlg = flip eval
evalAlg = Arith {con  = const,
                 var  = flip ($),
                 sum_ = \bs st   -> sum $ map ($st) bs,
                 prod = \bs st   -> product $ map ($st) bs,
                 sub  = \b b' st -> b st-b' st,
                 div_ = \b b' st -> b st`div`b' st,
                 scal = \i b st  -> i*b st,
                 expo = \b i st  -> b st^i}     
                 
exp0 = Sum [Var"x":^4, 5:*(Var"x":^3), 11:*(Var"x":^2), Con 222]

fold0 = foldArith evalAlg exp0 $ \"x" -> 4

evalMAlg :: Arith x (Store x -> Maybe Int)  -- foldArith evalMAlg = flip evalM  
evalMAlg = Arith {con  = const . Just,
                  var  = \x       -> Just . ($x),
                  sum_ = \bs st   -> fmap sum $ mapM ($st) bs,
                  prod = \bs st   -> fmap product $ mapM ($st) bs,
                  sub  = \b b' st -> liftM2 (-) (b st) $ b' st,
                  div_ = \b b' st -> do let m = b' st
                                        k <- m; guard $ k /= 0
                                        liftM2 div (b st) m,
                  scal = \i b st  -> fmap (i*) $ b st,
                  expo = \b i st  -> fmap (^i) $ b st}

evalRAlg :: Arith x (Store x -> Int)        -- foldArith evalRAlg = evalR
evalRAlg = Arith {con  = const,
                  var  = flip ($), 
                  sum_ = fmap sum . sequence,
                  prod = fmap product . sequence,
                  sub  = liftM2 (-),
                  div_ = liftM2 div,
                  scal = \i   -> liftM2 (*) $ const i,
                  expo = \b i -> liftM2 (^) b $ const i}                   

evalIO :: (Eq x,Read x,Show x) => String -> Exp x -> MaybeT IO Int          
evalIO store = \case Con i   -> return i
                     Var x   -> do store <- lift $ readFileContinue [] store 
                                                 $ return . read
                                   let val = lookup x store
                                   lift $ putStrLn $ show x ++
                                          case val of Just i -> " = " ++ show i
                                                      _ -> " is undefined"
                                   liftT val
                     Sum es  -> fmap sum $ mapM f es
                     Prod es -> fmap product $ mapM f es
                     e :- e' -> liftM2 (-) (f e) $ f e'
                     e :/ e' -> do let m = f e'
                                   k <- m 
                                   if k /= 0 then liftM2 div (f e) m
                                   else do lift $ putStrLn "divide by zero?"
                                           mzero
                     i :* e  -> fmap (i*) $ f e
                     e :^ i  -> fmap (^i) $ f e
               where f = evalIO store

-- translation of arithmetic expressions into assembler programs
         
data StackCom x = Push Int | Load x | Add Int | Mul Int | Sub | Div | Up
                  deriving Show

type Estate x = ([Int],Store x)

executeCom :: StackCom x -> Estate x -> Estate x
executeCom (Push a) (stack,store) = (a:stack,store)
executeCom (Load x) (stack,store) = (store x:stack,store) 
executeCom (Add n) st             = executeOp sum n st
executeCom (Mul n) st             = executeOp product n st
executeCom Sub st                 = executeOp (foldl1 (-)) 2 st
executeCom Div st                 = executeOp (foldl1 div) 2 st
executeCom Up st                  = executeOp (foldl1 (^)) 2 st
                                                
executeOp :: ([Int] -> Int) -> Int -> Estate x -> Estate x
executeOp f n (stack,store) = (f (reverse as):bs,store)
                              where (as,bs) = splitAt n stack

execute :: [StackCom x] -> Estate x -> Estate x
execute = flip $ foldl $ flip executeCom

codeAlg :: Arith x [StackCom x]
codeAlg = Arith {con = \i     -> [Push i],
                 var = \x     -> [Load x],
                 sum_ = \cs   -> concat cs++[Add $ length cs],
                 prod = \cs   -> concat cs++[Mul $ length cs],
                 sub = \c c'  -> c++c'++[Sub],
                 div_ = \c c' -> c++c'++[Div],
                 scal = \i c  -> Push i:c++[Mul 2],
                 expo = \c i  -> c++[Push i,Up]}

code :: Exp x -> [StackCom x]                   -- code = foldArith codeAlg
code = \case Con i   -> [Push i]
             Var x   -> [Load x]
             Sum es  -> concatMap code es++[Add $ length es]
             Prod es -> concatMap code es++[Mul $ length es]
             e :- e' -> code e++code e'++[Sub]
             e :/ e' -> code e++code e'++[Div]
             i :* e  -> Push i:code e++[Mul 2]
             e :^ i  -> code e++[Push i,Up]
                        
treeAlg :: Arith String (Tree String)                   
treeAlg = Arith {con  = \i    -> int i,
                 var  = \x    -> V x,
                 sum_ = \ts   -> F "Sum" ts,
                 prod = \ts   -> F "Prod" ts,
                 sub  = \t t' -> F "-" [t,t'],
                 div_ = \t t' -> F "/" [t,t'],
                 scal = \i t  -> F "*" [int i,t],
                 expo = \t i  -> F "^" [t,int i]}       
          where int i = F (show i) []

stringTree :: Exp String -> Tree String        -- stringTree = foldArith treeAlg
stringTree = \case Con i   -> int i
                   Var x   -> V x
                   Sum es  -> F "Sum" $ map stringTree es
                   Prod es -> F "Prod" $ map stringTree es
                   e :- e' -> F "-" [stringTree e,stringTree e']
                   e :/ e' -> F "/" [stringTree e,stringTree e']
                   i :* e  -> F "*" [int i,stringTree e]
                   e :^ i  -> F "^" [stringTree e, int i]
             where int i = F (show i) []

storeAlg :: Store String -> TreeSig String Int
storeAlg st = TreeSig st $ \case "Sum" -> sum 
                                 "Prod" -> product
                                 "-" -> \[i,k] -> i-k
                                 "/" -> \[i,k] -> i`div`k
                                 "*" -> \[i,k] -> i*k
                                 "^" -> \[i,k] -> i^k
                                 i -> const $ read i
             
evalTree :: Exp String -> Store String -> Int    -- evalTree = foldArith evalAlg
evalTree = flip (foldTree . storeAlg) . stringTree 

-- symbolic differentiation

diffE :: Eq x => x -> Exp x -> Exp x
diffE x = \case Con _   -> zero
                Var y   -> if x == y then one else zero
                Sum es  -> Sum $ map d es
                Prod es -> Sum $ zipWith g [0..] es
                           where g i = Prod . updList es i . d
                e :- e' -> d e :- d e'
                e :/ e' -> (mul (d e) e' :- mul e (d e')) :/ (e':^2)
                i :* e  -> i :* d e
                e :^ i  -> i :* (mul (d e) $ e:^(i-1))
          where d = diffE x

diffAlg :: Eq x => ArithP x (x -> Exp x)       -- paraArith diffAlg = flip diffE
diffAlg = ArithP {conP  = \_ _        -> zero,
                  varP  = \x y        -> if x == y then one else zero,
                  sumP  = \_ fs x     -> Sum $ map ($x) fs,
                  prodP = \es fs x    -> let f i e = Prod $ updList es i 
                                                          $ (fs!!i) x
                                         in Sum $ zipWith f [0..] es,
                  subP  = \_ f _ g x  -> f x :- g x,
                  divP  = \e f e' g x -> (mul (f x) e':-mul e (g x)) :/ (e':^2),
                  scalP = \i _ f x    -> i :* f x,
                  expoP = \e f i x    -> i :* (mul (f x) $ e:^(i-1))}

-- output of arithmetic expressions

showExp :: Exp String -> String
showExp e = showsPrec 0 e "" where 
            showsPrec :: Int -> Exp String -> String -> String
            showsPrec _ (Con i)   = shows i
            showsPrec _ (Var x)   = (x++)
            showsPrec p (Sum es)  = enclose (p>0) $ showMore 0 '+' es
            showsPrec p (Prod es) = enclose (p>1) $ showMore 1 '*' es
            showsPrec p (e :- e') = enclose (p>0) $ showsPrec 0 e . ('-':) . 
                                                    showsPrec 1 e' 
            showsPrec p (e :/ e') = enclose (p>1) $ showsPrec 1 e . ('/':) . 
                                                    showsPrec 2 e' 
            showsPrec p (i :* e)  = enclose (p>1) $ shows i . ('*':) .
                                                    showsPrec 1 e 
            showsPrec p (e :^ i)  = enclose (p>2) $ showsPrec 2 e . ('^':) . 
                                                    shows i
                
            enclose :: Bool -> (String -> String) -> String -> String
            enclose b f = if b then ('(':) . f . (')':) else f
                        
            showMore :: Int -> Char -> [Exp String] -> String -> String
            showMore p op (e:es) = foldl f (showsPrec p e) es where
                                   f state e = state . (op:) . showsPrec p e                       

-- reduction of arithmetic expressions

type Rstate x = (Int,[Exp x],Exp x -> Int)

updState :: Eq x => Rstate x -> Exp x -> Int -> Rstate x
updState (c,bases,f) e i = (c,insert e bases,update f e $ f e+i)

applyL :: ([a] -> a) -> [a] -> a
applyL _ [a] = a
applyL f as  = f as

reduceE :: Eq x => Exp x -> Exp x
reduceE = \case e :- e'       -> reduceE e :- reduceE e'
                i :* Con j    -> Con $ i*j
                0 :* e        -> zero
                1 :* e        -> reduceE e
                i :* (j :* e) -> reduceE $ (i*j) :* e
                i :* e        -> i :* reduceE e
                e :/ e'       -> reduceE e :/ reduceE e'
                Con i :^ j    -> Con $ i^j
                e :^ 0        -> one
                e :^ 1        -> reduceE e
                (e :^ i) :^ j -> reduceE $ e :^ (i*j)
                e :^ i        -> reduceE e :^ i
                Sum es        -> case f es of (c,[]) -> Con c
                                              (0,es) -> applyL Sum es
                                              (c,es) -> applyL Sum $ Con c:es
                Prod es       -> case g es of (c,[]) -> Con c
                                              (1,es) -> applyL Prod es
                                              (c,es) -> c :* applyL Prod es
                e -> e
      where f es = (c,map summand bases) where
                   (c,bases,scal) = foldl trans (0,[],const 0) $ map reduceE es
                   summand e = if i == 1 then e else i :* e where i = scal e
                   trans state@(c,bases,scal) = \case Con 0 -> state
                                                      Con i -> (c+i,bases,scal)
                                                      i:*e -> updState state e i
                                                      e -> updState state e 1
            g es = (c,map factor bases) where
                   (c,bases,expo) = foldl trans (1,[],const 0) $ map reduceE es
                   factor e = if i == 1 then e else e :^ i where i = expo e
                   trans state@(c,bases,expo) = \case Con 1 -> state
                                                      Con i -> (c*i,bases,expo)
                                                      e:^i -> updState state e i
                                                      e -> updState state e 1
                           
-- GENERIC EXPRESSION COMPILER

-- basic compilers

some, many :: MonadPlus m => m a -> m [a]
some p = do a <- p; as <- many p; return $ a:as
many p = msum [some p, return []]

type Compiler = StateT String Maybe

parse :: Compiler a -> String -> Maybe a
parse p str = do (a,_) <- runST p str; Just a

sat :: (Char -> Bool) -> Compiler Char
sat f = StateT $ \str -> do c:str <- return str
                            if f c then return (c,str) else mzero

char :: Char -> Compiler Char
char chr = sat (== chr)

nchar :: String -> Compiler Char
nchar chrs = sat (`notElem` chrs)

digit,letter,delim :: Compiler Char
digit  = msum $ map char ['0'..'9']
letter = msum $ map char $ ['a'..'z']++['A'..'Z']
delim  = msum $ map char " \n\t"

string :: String -> Compiler String
string = mapM char

bool :: Compiler Bool
bool = msum [string "True"  >> return True,
             string "False" >> return False]

nat,int :: Compiler Int
nat = fmap read $ some digit
int = msum [nat, do char '-'; n <- nat; return $ -n]

identifier :: Compiler String
identifier = liftM2 (:) letter $ many $ nchar "(){};=!>+-*/^ \n\t"

token :: Compiler a -> Compiler a
token comp = do many delim; a <- comp; many delim; return a

tchar       = token . char
tstring     = token . string
tbool       = token bool
tint        = token int
tidentifier = token identifier

-- expression compiler

compE :: Arith String val -> Compiler val
compE alg = summand >>= moreSummands where

          summand       = mplus scalar factor >>= moreFactors
         
          factor        = msum [fmap (con alg) tint >>= power,
                                fmap (var alg) tidentifier >>= power,
                                do tchar '('; a <- compE alg; tchar ')'
                                   power a]
          moreSummands a = msum [tchar '-' >> fmap (sub alg a) summand
                                           >>= moreSummands,
                                 some (tchar '+' >> summand)
                                           >>= moreSummands . sum_ alg . (a:),
                                 return a]
          moreFactors a  = msum [do tchar '/' >> fmap (div_ alg a) factor
                                              >>= moreFactors,
                                 some (tchar '*' >> mplus scalar factor)
                                              >>= moreFactors . prod alg . (a:),
                                 return a]
          scalar  = do i <- tint
                       let lift = fmap $ scal alg i
                       msum [tchar '*' >>
                              msum [lift scalar,
                                    fmap (var alg) tidentifier >>= lift . power,
                                    do tchar '('; a <- compE alg; tchar ')'
                                       return $ scal alg i a],
                            power $ con alg i]
          power a = msum [tchar '^' >> fmap (expo alg a) tint,
                          return a]

-- full compiler  

exp2alg :: String -> Int -> IO ()
exp2alg file n = readFileAndDo file h where
   h str = case n of 0  -> act parser out
                     1  -> act (fmap (diffE "x") parser) out
                     2  -> act (fmap (flip (paraArith diffAlg) "x") parser) out
                     3  -> act (fmap (paraArith diffAlg) parser) $ out . ($"x")
                     4  -> act (compE diffAlg') $ out . ($"x") . snd
                     5  -> act (fmap (foldArith diffAlg') parser) $ 
                               out . ($"x") . snd
                     6  -> act (compE evalAlg) loopR
                     7  -> act (fmap (flip eval) parser) loopR
                     8  -> act (fmap evalTree parser) loopR
                     9  -> act (fmap evalR parser) loopR
                     10 -> act (compE evalRAlg) loopR
                     11 -> act (compE codeAlg) loopC
                     12 -> act (fmap code parser) loopC
                     _  -> act (fmap (flip writeVal) parser) $ loopT result
           where parser = compE arithT
                 diffAlg' = mkArith diffAlg
                 out = mkTree result . showExp . reduceE
                 result = file ++ "Result"
                 act :: Compiler a -> (a -> IO ()) -> IO ()
                 act comp continue = case runST comp str of 
                                     Just (a,"") -> continue a
                                     Just (a,str) 
                                       -> do putStrLn $ "unparsed suffix: "++str
                                             continue a
                                     _ -> putStrLn "syntax error"

loopR :: (Store String -> Int) -> IO ()
loopR val = do (store,b) <- input
               when b $ do putStrLn $ "result = "++show (val store); loopR val
           
loopT :: String -> (Store String -> (String,Int)) -> IO ()
loopT file val = do (store,b) <- input
                    when b $ do writeFile file $ fst $ val store; loopT file val
                           
loopC :: [StackCom String] -> IO ()
loopC code = do writeFile "code" $ fold2 f "" [0..] code; loop where
             f str n c = str ++ '\n':replicate (5-length lab) ' ' ++ 
                         lab ++ ": "++ show c where lab = show n
             loop = do (store,b) <- input
                       let (result:_,_) = execute code ([],store)
                       when b $ do putStrLn $ "result = "++show result; loop 
                           
input :: IO (Store String,Bool)
input = do putStrLn "Enter variables!"; str <- getLine
           let vars = words str
           putStrLn "Enter values!"; str <- getLine
           let vals = map read $ words str
               vals' = vals++replicate (length vars-length vals) 0
           return (fold2 update (const 0) vars vals', not $ null vars)

-- Examples

x = Var "x"
y = Var "y"
z = Var "z"

t1  = Sum [5:*Con 11,6:*Con 12,Prod[x,y,z]]              -- 5*11+6*12+x*y*z
t2  = Sum [Prod [x,y,z], Con 127]                        -- x*y*z+127
t3  = Sum [11 :* (x :^ 3),5 :* (x :^ 2),16 :* x,Con 33]  -- 11*x^3+5*x^2+16*x+33
t4  = Sum [11 :* (x :^ 3),5 :* (x :^ 2),16 :* x,Con 33,22 :* (x :^ 2)] 
t5  = Sum [5 :* (x :^ 2),22 :* (x :^ 2)] 
t6  = Prod [x :^5,Prod [x :^5,x :^6]]
t7  = Sum [11:*(x:^3),5:*(x:^2),16:*x,Con 33,x:-(y:-z),
           Prod[x:^5,Sum[x:^5,x:^6]]]
t8  = Sum [11:*(x:^3),5:*(x:^2),16:*x,Con 33,Sum[x,y,z]:-z,
           Prod[x:^5,Sum[x:^5,x:^6]]]
t9  = Prod [x,Con 5,5:*Prod[x:-y,y,z]]
t10 = Sum [Var"x":^4,5:*(Var"x":^3),11:*(Var"x":^2),Con 222]
t11 = t10 >>= \"x" -> 2:*Con 2 
t12 = Con 5:/(Con 4:-Var"x")

store1 = \case "x" -> 4; "y" -> 55

val1 = eval store1 t10                  -- > 974
val2 = eval (const 0) t11               -- > 974
val3 = evalM store1 t10                 -- > Just 974
val4 = evalM store1 t12                 -- > Nothing
val5 = evalR t10 store1                 -- > 974
val6 = foldArith evalAlg t10 store1     -- > 974
val7 = foldArith evalMAlg t10 store1    -- > Just 974

-- Inhalt von "store1": [("x",4),("y",55)]
-- Inhalt von "store2": [("z",4),("y",55)]

val8  = runMT $ evalIO "store1" t10     -- > "x" = 4
                                        --   "x" = 4
                                        --   "x" = 4
                                        --   Just 974
val9  = runMT $ evalIO "store1" t12     -- > "x" = 4
                                        --   divide by zero
                                        --   Nothing
val10 = runMT $ evalIO "store2" t10     -- > "x" is undefined
                                        --   Nothing
val11 = runMT $ evalIO "store2" t12     -- > "x" is undefined
                                        --   Nothing
val12 = runMT $ evalIO "store3" t10     -- > store3 does not exist
                                        --   "x" is undefined
                                        --   Nothing

exp1  = "5*11+6*12+x*y*z"
exp2  = "11*x^3+5*x^2+16*x+33"
exp3  = "x^3*x^5"
exp4  = "5*(6*(11*(x+y+z)*14+(c+g+b)*22)+44*(gg+hh))"
exp5  = "x-x-x"
exp6  = "11*x^3*x^4+33+3*x+5*x^2+16*x+(6*x^2+55)*5*x^2"
exp7  = "x^4+5*x^3-11*2*3*4*x^2+222"
exp8  = "5*6*7+x-5*2*3"
exp9  = "9*x^2+xx/x-x*5*z+yy+5*6*x+yy/5*6/5"
exp10 = "diff(x)(Sum(Var(x)^4,5*(Var(x)^3),11*(Var(x)^2),Con(222)))"
exp11 = "eval(Sum(Var(x):^4,5:*(Var(x):^3),11:*(Var(x):^2),Con 222))"

{- exp2alg "exp1" 0               --> t1        
   exp2alg "exp1" 1               --> t3                
   exp2alg "exp2" 2               --> 33*x^2+10*x+16
   exp2alg "exp7" 2               --> 4*x^3+15*x^2-528*x
   exp2alg "exp2" 6..10 /\ x = 5  --> 1613
   exp2alg "exp7" 6..10 /\ x = 4  --> -3426
   exp2alg "exp8" 13 /\ x = 66    --> The value of 6*7 is 42.
                                      The value of 5*6*7 is 210.
                                      The value of x is 66.
                                      The value of 5*6*7+x is 276.
                                      The value of 2*3 is 6.
                                      The value of 5*2*3 is 30.
                                      The value of 5*6*7+x-5*2*3 is 246. -}
                 
mkCon :: Int -> Tree String
mkCon i = F "Con" [mkInt i]

-- stepwise differentiation

diffStep :: Rules String
diffStep (F "$" [F "diff" [V x],e]) = 
         case e of F "Con" [t] | isJust i 
                                 -> Just $ mkCon 0 where i = parse int $ root t
                   F "Var" [V y] -> Just $ mkCon $ if x == y then 1 else 0
                   F "Sum" es    -> Just $ F "Sum" $ map diff es
                   F "Prod" es   -> Just $ F "Sum" $ zipWith f [0..] es
                                    where f i = F "Prod" . updList es i . diff
                   F "-" [e,e']  -> Just $ F "-" [diff e,diff e']
                   F "*" [t,e] | isJust $ parse int $ root t
                                 -> Just $ F "*" [t,diff e]
                                    where i = parse int $ root t
                   F "^" [e,t] | isJust i 
                                 -> Just $ F "*" [t,F "Prod" [diff e,e']]
                                    where i = parse int $ root t
                                          e' = F "^" [e,mkInt $ fromJust i-1]
                   _ -> Nothing
         where diff e = F "$" [F "diff" [V x],e]
diffStep _ = Nothing  

-- stepwise reduction

redStep :: Rules String
redStep = \case F "Sum" es | any (== zero) es
                  -> Just $ F "Sum" $ filter (/= zero) es where zero = mkCon 0
                F "Sum" [e] -> Just e
                F "Prod" es | any (== one) es 
                  -> Just $ F "Sum" $ filter (/= one) es where one = mkCon 1
                F "Prod" [e] -> Just e
                F "*" [t,e] | isJust i && fromJust i == 1 -> Just e 
                              where i = parse int $ root t
                F "*" [t,F "*" [u,e]] | isJust i && isJust j 
                  -> Just $ F "*" [mkInt $ fromJust i*fromJust j,e]
                     where [i,j] = map (parse int . root) [t,u]
                F "^" [e,t] | isJust i && fromJust i == 1 -> Just e 
                              where i = parse int $ root t
                F "^" [F "^" [e,t],u] | isJust i && isJust j
                  -> Just $ F "^" [e,mkInt $ fromJust i*fromJust j] 
                     where [i,j] = map (parse int . root) [t,u]
                _ -> Nothing

-- stepwise evaluation

evalStep :: Store String -> Rules String
evalStep st (F "eval" [e]) = 
            case e of F "Con" [t] | isJust $ parse int $ root t 
                                    -> Just t
                      F "Var" [V x] -> Just $ mkInt $ st x
                      F "Sum" es    -> Just $ F "+" $ map eval es
                      F "Prod" es   -> Just $ F "*" $ map eval es
                      F "-" [e,e']  -> Just $ F "-" [eval e,eval e']
                      F "/" [e,e']  -> Just $ F "/" [eval e,eval e']
                      F "*" [t,e] | isJust $ parse int $ root t
                                    -> Just $ F "*" [t,eval e]
                      F "^" [e,t] | isJust $ parse int $ root t 
                                    -> Just $ F "^" [eval e,t]
                      _             -> Nothing
            where eval e = F "eval" [e]
evalStep _ _ = Nothing

reduce1 = reduce "exp10" [diffStep] 
reduce2 = reduce "exp10" [diffStep,redStep] 
reduce3 = reduce "exp11" [evalStep store1] 

