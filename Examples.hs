{-# LANGUAGE EmptyDataDecls, ExistentialQuantification, FlexibleInstances, 
             GADTs, LambdaCase, RankNTypes, TypeFamilies, TypeSynonymInstances, 
             DataKinds, IncoherentInstances, ScopedTypeVariables, LambdaCase,
             FlexibleContexts, TupleSections, RecursiveDo #-}
    
-- 13.10.2017

module Examples where

import Data.Array(Ix,Array,array,(!),bounds,index,range,listArray)
import Data.Maybe
import Data.List(zip5,permutations)
import Data.Monoid (Monoid(mempty,mappend))
import Data.IORef
import Control.Monad
import System.Process
import System.IO.Unsafe
import qualified Data.List as DL
import Data.Set (fromList,toList,findMin)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DMS

-- import System.IO

import Painter (Tree(F,V),root,subtrees,mkTree,float,float2,RGB,red,hue,update,
                insert,remove,diff,union,unionMap,subset,fold2,fixpt,
                (***),(&&&),MonadTrans(lift))
import Coalg (Bintree(Empty,Fork),Id(Id),StateT(StateT),runST,getSubtree)
import Expr (Compiler,some,many,ListT(runLT))

-- infixl 9 &

(&) :: a -> (a -> b) -> b
(&) = flip ($)

xx = False && undefined                 -- >  False
yy = take 9 $ [1..9]++undefined         -- >  [1..9]
zz = msum [Just 5,undefined]            -- >  Just 5

pow1 = ((+5)^^^6) 8

fact = \case 0 -> 1; n -> n*fact(n-1)

fact' = \case 0 -> 1; n | n > 0 -> n*fact'(n-1)
                     -- | True -> undefined

maybeRepeat :: Int -> Maybe [Int] 
maybeRepeat i = do rec s <- Just (i:s)
                   Just s
                   
s0 = take 22 s where Just s = maybeRepeat 5

nonempty :: MonadPlus m => [a] -> m ()
nonempty = guard . not . null

foo :: Int -> Int
foo k = k+(read $ unsafePerformIO $ readFile "testt")

foo1 = \case Just a -> \case Nothing -> Nothing; Just b -> Just a
             _ -> \case Just a -> Nothing; _ -> Nothing

baltree :: [a] -> Bintree a
baltree [] = Empty
baltree s  = Fork a (baltree s1) (baltree s2)
             where (s1,a:s2) = splitAt (length s`div`2) s        

data Point = Point {x,y :: Float} deriving Eq

data DRect = DRect {center :: Point, width,height :: Float, color :: RGB}

instance Show Point where 
         show (Point x y) = '(':show x ++ ',':show y ++ ")"

distance :: Point -> Point -> Float
distance (Point x1 y1) (Point x2 y2) = sqrt $ (x2-x1)^2+(y2-y1)^2
              
lengthPath :: [Point] -> Float                       
lengthPath path = sum $ zipWith distance path $ tail path

p = Point {x=5.7, y=3.66}

Point aa bb = p

rect = DRect {center=p, width=11, height=5, color=red}

access = rect&center&x

-- O'Haskell templates as Haskell data types with references

data Cell' = Cell' {getPoint :: IO Point,
                    setPoint :: Point -> IO (),
                    getNext :: IO (Maybe Cell'), 
                    setNext :: Maybe Cell' -> IO (),
                    getDist :: IO Float}

newCell :: Point -> Maybe Cell' -> IO Cell'
newCell point next = do pointRef <- newIORef point
                        nextRef  <- newIORef next
                        let getPoint = readIORef pointRef
                            setPoint = writeIORef pointRef
                            getNext = readIORef nextRef
                            setNext = writeIORef nextRef
                            getDist = do pt <- getPoint                  -- (1)
                                         next <- getNext
                                         case next of 
                                              Nothing -> return 0
                                              Just (Cell' getPt _ _ _ _)
                                                -> do pt' <- getPt
                                                      return $ distance pt pt'
                                                 --   pt <- path&getPoint 
                                                 -- > type conflict with (1)                              
                        return $ Cell' getPoint setPoint getNext setNext getDist
                     
lengthCyclic' :: Cell' -> IO (Float,Bool)
lengthCyclic' cell = do point <- cell&getPoint
                        next <- cell&getNext
                        dist <- cell&getDist
                        let loop :: Maybe Cell' -> IO (Float,Bool)
                            loop Nothing     = return (dist,False)
                            loop (Just cell) = do pt <- cell&getPoint
                                                  next <- cell&getNext
                                                  dist <- cell&getDist
                                                  if point == pt 
                                                  then return (dist,True)
                                                  else do (dist',b) <- loop next
                                                          return (dist+dist',b)
                        loop next

data Cell = Cell {point :: Point, next :: Maybe (IORef Cell)}
                     
lengthCyclic :: IORef Cell -> IO (Float,Bool)
lengthCyclic ref = do 
         Cell pt0 next <- readIORef ref
         let loop :: Float -> Point -> Maybe (IORef Cell) -> IO (Float,Bool)
             loop dist _ Nothing     = return (dist,False)
             loop dist pt (Just ref) = do Cell pt' nx <- readIORef ref
                                          let dist' = dist+distance pt pt'
                                          if pt0 == pt' then return (dist',True)
                                                        else loop dist' pt' nx
         loop 0 pt0 next 
                     
lengthCyclicL :: [Point] -> (Float,Bool)
lengthCyclicL (pt0:s) = loop 0 pt0 s where
                        loop :: Float -> Point -> [Point] -> (Float,Bool)
                        loop dist _ []       = (dist,False)
                        loop dist pt (pt':s) = if pt0 == pt' then (dist',True)
                                               else loop dist' pt' s
                                               where dist' = dist+distance pt pt'

outPathInfo :: [Point] -> IORef Cell -> IO ()
outPathInfo path ref = do 
                putStrLn $ "\npath = " ++ show (take 4 path) ++
                           "\nlengthCyclicL = " ++ show (lengthCyclicL path)
                lgb <- lengthCyclic ref
                putStrLn $ "lengthCyclic = " ++ show lgb
 
testPath :: IO ()
testPath = do let path@[pt1,pt2,pt3] = [Point 77 6,Point 99 13,Point 111 43]
              rec ref1 <- newIORef $ Cell pt1 $ Just ref2
                  ref2 <- newIORef $ Cell pt2 $ Just ref3
                  ref3 <- newIORef $ Cell pt3 Nothing
              outPathInfo path ref1             -- (55.39778,False)
              
              cell2 <- readIORef ref2
              let pt = cell2&point
                  pt2 = pt {x = pt&x-55}
                  path' = [pt1,pt2,pt3]
              writeIORef ref2 $ cell2 {point = pt2}
              outPathInfo path' ref1            -- (107.14406,False)
              
              cell3 <- readIORef ref3
              writeIORef ref3 $ cell3 {next = Just ref1}
              let poly = path'++poly
              outPathInfo poly ref1             -- (157.39343,True)
              
              {- old version:
              rec cell1 <- newCell pt1 $ Just cell2 
                  cell2 <- newCell pt2 $ Just cell3
                  cell3 <- newCell pt3 Nothing
              (lg,b) <- lengthCyclic cell1
              putStrLn $ "length = " ++ show lg ++ "\ncyclic = " ++ show b
              --                        55.39778                    False
              pt <- cell2&getPoint
              (cell2&setPoint) $ pt {x = pt&x-55}
              (lg,b) <- lengthCyclic cell1
              putStrLn $ "length = " ++ show lg ++ "\ncyclic = " ++ show b
              --                        107.14406                   False
              (cell3&setNext) $ Just cell1
              (lg,b) <- lengthCyclic cell1
              putStrLn $ "length = " ++ show lg ++ "\ncyclic = " ++ show b
                                        157.39343                   True
              O'Haskell version: 
              fldit-www.cs.uni-dortmund.de/~peter/Haskellprogs/Pointer.hs -}

-- LISTS

indices s = [0..length s-1]

-- search f s searches for the first element of s satisfying f and returns its
-- position within s.

search f = g 0 where g i (x:s) = if f x then Just i else g (i+1) s
                     g _ _     = Nothing
                     
type Boolfun a  = a -> a -> Bool

sort :: Boolfun a -> [a] -> [a]
sort rel (x:s) = sort rel [y | y <- s, rel y x] ++ x:
                 sort rel [y | y <- s, not $ rel x y]
sort _ s = s

-- searchAll f s searches all elements of s satisfying f and returns their
-- positions within s.

searchAll :: (a -> Bool) -> [a] -> [Int]
searchAll f s = snd $ foldr g (length s-1,[]) s
                where g x (i,is) = (i-1,if f x then i:is else is)
                             
updList :: [a] -> Int -> a -> [a]
updList s i a = take i s++a:drop (i+1) s

updRel :: (Eq a,Eq b,Eq c) => (a -> b -> [c]) -> a -> b -> c -> a -> b -> [c]
updRel f a b c = update f a $ update (f a) b $ c:f a b

foo2 = listArray (0,7)[1..7]!5

horner :: [Float] -> Float -> Float
horner bs x = foldl1 f bs where f a b = a*x+b
nats n = cons n $ nats $ n+1

revAcc :: [a] -> [a]                            -- reversed list
revAcc = loop [] where loop s (a:s') = loop (a:s) s'
                       loop s _      = s

-- removeSub s s' removes all occurrences of the sublist s' from the list s.

removeSub s s' = f False s s' [] []
           where f _ (x:s) (y:s1) s2 s3 | x == y = f True s s1 (s2++[x]) s3
                                        | True   = f False s s' [] (s3++s2++[x])
                 f _ s@(_:_) [] _ s3             = f False s s' [] s3
                 f _ _ _ s2 s3                   = s3++s2 

f^^^n = (!!n) . iterate f 

cons :: a -> (Int -> a) -> Int -> a
cons a f = \case 0 -> a; n -> f $ n-1

blink = cons 0 $ cons 1 blink

-- list zipper

type ListIndex a  = ([a],Int)                   
type ListZipper a = ([a],[a])           -- (reversed context, referenced suffix)

indexToZipper :: ListIndex a -> ListZipper a
indexToZipper = loop [] where loop :: [a] -> ([a],Int) -> ([a],[a])
                              loop c (s,0)   = (c,s)
                              loop c (a:s,n) = loop (a:c) (s,n-1)

zipperToIndex :: ListZipper a -> ListIndex a
zipperToIndex (c,s) = loop c (s,0) 
                      where loop :: [a] -> ([a],Int) -> ([a],Int)
                            loop (a:c) (s,n) = loop c (a:s,n+1)
                            loop _ sn        = sn
                          
-- s /= [] /\ 0 <= n < length s ==> zipperToIndex $ indexToZipper (s,n) = (s,n)
-- s /= []                      ==> indexToZipper $ zipperToIndex (c,s) = (c,s)

back,forth :: ListZipper a -> ListZipper a
back (a:c,s)  = (c,a:s)
forth (c,a:s) = (a:c,s)
                          
-- NONEMPTY BINARY TREES

data BintreeL a = Leaf a | Bin a (BintreeL a) (BintreeL a)

-- reads "5(7(3, 8),6 ) " :: [(BintreeL Int,String)]    
                             -- > [(5,"(7(3, 8),6 ) "),(5(7(3,8),6)," ")]
-- read "5(7(3, 8),6 ) "  :: BintreeL Int          
                             -- > 5(7(3,8),6)
-- reads "5(7(3,8),6)hh"  :: [(BintreeL Int,String)]    
                             -- > [(5,"(7(3,8),6)hh"),(5(7(3,8),6),"hh")]
-- read "5(7(3,8),6)hh"   :: BintreeL Int          
                             -- > Exception: ...: no parse                           

-- binary-tree zipper (see http://www.haskell.org/haskellwiki/Zipper)

type TreeNode a = (BintreeL a,[Int])

data Context a = Top | L a (Context a) (BintreeL a) 
                     | R a (BintreeL a) (Context a) 
                        
type TreeZipper a = (Context a,BintreeL a)              -- (reversed context, 
                                                        --  referenced subtree)

treeToZipper :: TreeNode a -> TreeZipper a
treeToZipper (t,node) = loop Top t node
               where loop :: Context a -> BintreeL a -> [Int] -> TreeZipper a
                     loop c (Bin a t u) (0:node) = loop (L a c u) t node
                     loop c (Bin a t u) (1:node) = loop (R a t c) u node
                     loop c t _                  = (c,t)
                    
zipperToTree :: TreeZipper a -> TreeNode a
zipperToTree (c,t) = loop c t [] 
             where loop :: Context a -> BintreeL a -> [Int] -> TreeNode a
                   loop (L a c t) u node = loop c (Bin a u t) (0:node)
                   loop (R a t c) u node = loop c (Bin a t u) (1:node)
                   loop _ t node         = (t,node)

up,sibling,left,right :: TreeZipper a -> TreeZipper a
up (L a c u,t)      = (c,Bin a t u)
up (R a t c,u)      = (c,Bin a t u)
sibling (L a c u,t) = (R a t c,u)
sibling (R a t c,u) = (L a c u,t)
left  (c,Bin a t u) = (L a c u,t)
right (c,Bin a t u) = (R a t c,u)
                          
getSub :: TreeNode a -> BintreeL a
getSub (Bin a t u,0:node) = getSub (t,node)
getSub (Bin a t u,1:node) = getSub (u,node)
getSub (t,[])             = t

-- getSub tnode defined ==> zipperToTree $ treeToZipper tnode = tnode
-- treeToZipper . zipperToTree = id
                          
getSub' :: String -> String -> TreeZipper Int
getSub' tree node = treeToZipper (read tree,map readChar node)
                    where readChar c = if c == '0' then 0 else 1

tn1 = getSub' "1(2(3(4,5),6(7,8)),9(10(11,12),13(14,15)))" "010"
tn2 = fst $ zipperToTree tn1    -- > 1(2(3(4,5),6(7,8)),9(10(11,12),13(14,15)))
tn3 = snd tn1                   -- > 7
tn4 = snd $ sibling tn1         -- > 8
tn5 = snd $ up tn1              -- > 6(7,8)
tn6 = snd $ right $ up $ tn1    -- > 8
                          
putSub :: TreeNode a -> BintreeL a -> BintreeL a
putSub (Bin a t u,0:node) v = Bin a (putSub (t,node) v) u
putSub (Bin a t u,1:node) v = Bin a t (putSub (u,node) v)
putSub (_,[]) v             = v

instance Show a => Show (BintreeL a) where
                   showsPrec _ (Leaf a)           = shows a
                   showsPrec _ (Bin a left right) = shows a . ('(':) . 
                                                    shows left . (',':) .
                                                    shows right . (')':)

instance Read a => Read (BintreeL a) where
                   readsPrec _ s = [(Leaf a,s) | (a,s) <- reads s] ++
                                   [(Bin a left right,s) | (a,s) <- reads s,   
                                                           ("(",s) <- lex s,
                                                           (left,s) <- reads s,
                                                           (",",s) <- lex s,
                                                           (right,s) <- reads s,
                                                           (")",s) <- lex s]
                
bintree :: Compiler a -> Compiler (BintreeL a)
bintree comp = do a <- comp
                  msum [do tchar '('; left <- bintree comp
                           tchar ','; right <- bintree comp
                           tchar ')'; return $ Bin a left right,
                        return $ Leaf a]
                     
compileB = runST $ bintree int

data Test = (:+++) Int Bool Int

(+++) x y z = x+y+z
                            
fs1 = [(+1),(*2),(+11),(*111)]
f1 = map ($5) fs1
f2 = zipWith ($) fs1 [1,11,22,33] 
f3 = foldr ($) 5 fs1         
f4 = foldl (flip ($)) 5 $ reverse fs1 

twice f = f . f

-- self f = f $ f Occurs check: cannot construct the infinite type: a = a -> b

mapS :: [a -> b] -> [[a] -> [b]]
mapS = map map

tt = (mapS [(+1),(*3)]!!1)[5,6,7]

-- strict foldl

foldls :: (b -> a -> b) -> b -> [a] -> b 
foldls f b (x:xs) = flip (foldls f) xs $! f b x
                    -- let y = f b x in seq y (foldls f y xs ) 
foldls f b _      = b

fol = foldls (+) 0 [1..10^7]

zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f (a:s@(_:_)) (b:s'@(_:_)) = f a b:zipWith' f s s'
zipWith' f (a:s@(_:_)) [b]          = f a b:zipWith' f s [b]
zipWith' f [a] (b:s@(_:_))          = f a b:zipWith' f [a] s
zipWith' f [a] [b]                  = [f a b]
zipWith' f _ _                      = []

baum1 = mkTree "32(25(17,30 27),50(42,63 89))"
baum2 = mkTree "32 [25 [17,30 [27]],50 [42,63 [89]]]"
      

checksum :: Integer -> Integer
checksum = sum . map (read . \x -> [x]) . show

liste = [g b | a <- s, let b = f a, p b] where s = [1..10]
                                               f = (*2)
                                               p = (< 10)
                                               g = (`div` 2)

ljapunow period = log $ take 400 (foldl f [0] (take 500 (cycle period)))/400
                  where f s@(x:_) a = g' a x:s
                        g a x = a*x*(1-x)
                        g' a x = a-2*a*x
                        
-- DEPENDENT TYPES

data Rose f a = Rose a (f (Rose f a))
                  
data Dynamic = forall a.(Read a,Show a) => Dyn a

instance Show Dynamic where show (Dyn a) = show a

dyn = [Dyn 5,Dyn "ggg",Dyn (True,"hello")]

data Labtree a = Lab a [(Dynamic,Labtree a)] deriving Show

lt1 = Lab 5 [(Dyn 2,Lab 6 [(Dyn "x",Lab 7 [])])]

class TT a where type T a :: *
                 f :: [a] -> T a
                   
instance TT Int where type T Int = Bool
                      f s = sum s < 10
                   
instance TT Bool where type T Bool = Int
                       f = length 

data Z
data S n

data List a n where Nil  :: List a Z
                    (:-) :: a -> List a n -> List a (S n)
                    
type List3 = List Int (S (S (S Z)))

list3 = 6 :- (7 :- (8 :- Nil)) :: List3
            
-- BINARY MAP

class Functor2 f where map2 :: (a -> b) -> (c -> d) -> f a c -> f b d
  
data Tree2 a b = Leaf2 a | Fork2 (Tree2 a b) b (Tree2 a b) 
                 deriving (Read,Show)

instance Functor2 Tree2 
   where map2 f _ (Leaf2 x)       = Leaf2 (f x)
         map2 f g (Fork2 t1 x t2) = Fork2 (map2 f g t1) (g x) (map2 f g t2) 

t3 = Fork2 (Leaf2 5) True (Fork2 (Leaf2 7) False (Leaf2 9)) 
t4 = map2 (+10) not t3

-- ARRAYS

data Foo = Fst (Int,Int,Int) deriving (Eq,Show,Ord,Ix)

a = index ((0,5,3),(1,6,4)) (0,6,3)

fa = index (Fst (0,5,3),Fst (1,6,4)) (Fst (0,6,3))

r = range  ((0,5,3),(1,6,4))

mkArray :: Ix a => (a,a) -> (a -> b) -> Array a b 
mkArray bds f = array bds [(x,f x) | x <- range bds] 

fib :: Array Int Integer
fib = mkArray (0,1000000) f where f 0 = 1
                                  f 1 = 1 
                                  f n = fib!(n-1) + fib!(n-2) 
                              
fi 0 = 1
fi 1 = 1 
fi n = fi (n-1) + fi (n-2) 

insertChar :: a -> [a] -> [Int] -> [a]
insertChar x = foldl f where f xs i = take i xs++x:drop i xs 
                                       
-- TREES
  
showTree :: Show a => Tree a -> ShowS
showTree (V a)        = shows a
showTree (F a [])     = shows a 
showTree (F a (t:ts)) = shows a . ('(':) . showTree t . foldl h id ts . (')':)
                        where h g t = g . (',':) . showTree t

size :: Tree a -> Int
size (F _ ts) = sum (map size ts)+1
size _        = 1

t0 = F 1 [F 2 [F 2 [V 3,V(-1)],V(-2)],F 4 [V(-3),V 5]]

type Node = [Int]

-- path(t)(node) is the list of labels on the path from the root of t to node.

path :: Tree a -> Node -> [a]
path t node = map (root . getSubtree t . flip take node) [0..length node]

-- putSubtree(t)(node)(u) replaces getSubtree(t)(node) by u. 

putSubtree :: Tree a -> Node -> Tree a -> Tree a
putSubtree t [] u = u
putSubtree (F a ts) (i:node) u | i < length ts = F a $ updList ts i 
                                                     $ putSubtree (ts!!i) node u
putSubtree _ _ _ = error "putSubtree"

t00 = putSubtree t0 [0,0,1] $ getSubtree t0 [1]

putSubtreeHO :: Tree a -> Node -> Tree a -> Tree a
putSubtreeHO _ [] u      = u
putSubtreeHO (V a) [0] u = F a [u]
putSubtreeHO (F a ts) (i:node) u 
       | i < lg               = F a $ updList ts i $ putSubtreeHO (ts!!i) node u
       | i == lg && null node = F a $ ts++[u] 
                                where lg = length ts
putSubtreeHO _ _ _ = error "putSubtreeHO"

(>>>) :: Tree a -> (a -> Tree a) -> Tree a
F a ts >>> sub = F a $ map (>>> sub) ts  
V a >>> sub    = sub a

t1 :: Tree String
t1 = F "+" [F "*" [F "5" [],V "x"],V "y",F "11" []]

sub :: String -> Tree String
sub = \case "x" -> F "/" [F "-" [c "6"],c "9",V "z"]
            "y" -> F "-" [c "7",F "*" [c "8",c "0"]]
            x -> V x
      where c = flip F []
  
t1s = t1 >>> sub 
      {- --> F "+" [F "*" [F "5" [],F "/" [F "-" [F "6" []],F "9" [],V "z"]],
                    F "-" [F "7" [],F "*" [F "8" [],F "0" []]],
                    F "11" []] -}

unify :: Eq a => Tree a -> Tree a -> Maybe (a -> Tree a)
unify (V a) (V b)       = Just $ if a == b then V else update V a $ V b
unify (V a) t           = do guard $ f t; Just $ update V a t
                          where f (V b)    = a /= b
                                f (F _ ts) = all f ts
unify t (V a)           = unify (V a) t
unify (F f ts) (F g us) = do guard $ f == g && length ts == length us
                             unifyall ts us

unifyall :: Eq a => [Tree a] -> [Tree a] -> Maybe (a -> Tree a)
unifyall [] []         = Just V
unifyall (t:ts) (u:us) = do sub <- unify t u
                            let msub = map (>>> sub)
                            sub' <- unifyall (msub ts) $ msub us
                            Just $ (>>> sub') . sub

sub1 = unify (F "+" [F "-" [V "x", V "y"],V "z"]) 
             (F "+" [V "a",F "*" [V "b", V "c"]])
             
ts1 = case sub1 of Just sub -> [sub "z", sub "a"]; _ -> []
                -- > [F "*" [V "b",V "c"], F "-" [V "x",V "y"]]
                
-- DEPTH- and BREADTHFIRST SEARCH

class TreeC t where rootC :: t a -> a
                    subtreesC :: t a -> [t a]
                    
instance TreeC Tree where rootC = root
                          subtreesC = subtrees
                    
instance TreeC Bintree where rootC (Fork a _ _) = a
                             subtreesC (Fork _ left right) = [left,right]
                    
instance TreeC BintreeL where rootC (Leaf a) = a
                              rootC (Bin a _ _) = a
                              subtreesC (Leaf _) = []
                              subtreesC (Bin _ left right) = [left,right]

creturn :: MonadPlus m => (a -> Bool) -> a -> m a
creturn f a = do guard $ f a; return a

depthfirst,breadthfirst :: (TreeC t,MonadPlus m) => (a -> Bool) -> t a -> m a
depthfirst f t = msum $ creturn f (rootC t) : map (depthfirst f) (subtreesC t)
breadthfirst f t = visit [t] where
                   visit [] = mzero
                   visit ts = msum $ map (creturn f . rootC) ts ++
                                     [visit $ ts >>= subtreesC]

t2 :: Tree Int
t2 = F 1 [F 2 [F 2 [V 3 ,V (-1)],V (-2)],F 4 [V (-3),V 5]]

s1 = depthfirst (< 0) t2 :: Maybe Int    -- >  Just (-1)
s2 = depthfirst (< 0) t2 :: [Int]        -- >  [-1,-2,-3]
s3 = breadthfirst (< 0) t2 :: Maybe Int  -- >  Just (-2)
s4 = breadthfirst (< 0) t2 :: [Int]      -- >  [-2,-3,-1]

bt :: BintreeL Int
bt = read "5(4(3,8(9,3)),6(1,2))"

s5 = depthfirst (> 5) bt :: Maybe Int   -- > Just 8        
s6 = depthfirst (> 5) bt :: [Int]       -- > [8,9,6]        
s7 = breadthfirst (> 5) bt :: Maybe Int -- > Just 6  
s8 = breadthfirst (> 5) bt :: [Int]     -- > [6,8,9]  
                            
-- A GADT of expressions
  
data Expr a where
     IntE   :: Int  -> Expr Int
     Bool   :: Bool -> Expr Bool
     (:+)   :: Expr Int -> Expr Int -> Expr Int
     (:*)   :: Expr Int -> Expr Int -> Expr Int
     (:<=)  :: Expr Int -> Expr Int -> Expr Bool        
     (:/\)  :: Expr Bool -> Expr Bool -> Expr Bool      
     If     :: Expr Bool -> Expr a -> Expr a -> Expr a
     PairE  :: Expr a -> Expr b -> Expr (a,b)
     ListE  :: [Expr a] -> Expr [a]
     TreeE  :: Tree (Expr a) -> Expr (Tree a)
       
eval :: Expr a -> a
eval (IntE n)      = n
eval (Bool b)      = b
eval (e1 :+ e2)    = eval e1 + eval e2
eval (e1 :* e2)    = eval e1 * eval e2
eval (e1 :<= e2)   = eval e1 < eval e2
eval (e1 :/\ e2)   = eval e1 && eval e2
eval (If b e1 e2)  = if eval b then eval e1 else eval e2
eval (PairE e1 e2) = (eval e1, eval e2)
eval (ListE es)    = map eval es
eval (TreeE t)     = fmap eval t

e1 = TreeE $ F (IntE 5 :+ IntE 6) [F (IntE 7 :+ IntE 8) []]

tr1 = F 5 [F 6 [F 6 [],F 7 []],
           F 7 [F 6 [],F 7 [],F 8 []],
           F 8 [F 6 [],F 7 [F 6 [],F 7 [],F 8 []],F 8 []]]
                      
tr2 = fmap show tr1
                
incTree :: Tree Int -> Tree Int
incTree = fmap (+1)

-- SPINES (see Hinze et al., SYB Reloaded)

data Type a where Int     :: Type Int
                  String  :: Type String
                  Pair    :: Type a -> Type b -> Type (a,b)
                  List    :: Type a -> Type [a]
                  Tree    :: Type a -> Type (Tree a)
                  Forest  :: Type a -> Type [Tree a]
                  Bintree :: Type a -> Type (Bintree a)

data Typed a = (:%) {obj :: a, typ :: Type a}

data Spine a = Constr a | forall b.Spine (b -> a) :$ Typed b

toSpine :: Typed a -> Spine a
toSpine (n :% Int)        = Constr n
toSpine (s :% String)     = Constr s
toSpine (p :% Pair a b)   = Constr (,) :$ (x :% a) :$ (y :% b) where (x,y) = p
toSpine (s :% List a)     = case s of [] -> Constr s
                                      x:s -> Constr (:) :$ (x :% a) 
                                                        :$ (s :% List a)
toSpine (t :% Tree a)     = Constr F :$ (x :% a) :$ (s :% Forest a)
                            where F x s = t
toSpine (ts :% Forest a)  = case ts of [] -> Constr ts
                                       t:ts -> Constr (:) :$ (t :% Tree a) 
                                                          :$ (ts :% Forest a)
toSpine (bt :% Bintree a) = case bt of 
                            Empty -> Constr bt
                            Fork x l r -> Constr Fork :$ (x :% a)
                                                      :$ (l :% Bintree a)
                                                      :$ (r :% Bintree a)
                                                      
-- QUERIES

type Query r = forall a.Typed a -> r         -- SYB: Data a => a -> r

foldQ :: (r -> r -> r) -> Query r -> r -> Spine a -> r
foldQ op q r (f :$ x) = op (foldQ op q r f) $ q x
foldQ _ _ r _         = r

everything :: (r -> r -> r) -> Query r -> Query r
everything op q x = foldQ op (everything op q) (q x) $ toSpine x

allQ :: Query Int
allQ (n :% Int)    = n
allQ (s :% String) = length s
allQ _             = 0

leafQ :: Query Int
leafQ (t :% Tree Int)    = case t of F n [] -> n;        _ -> 0
leafQ (t :% Tree String) = case t of F s [] -> length s; _ -> 0
leafQ _                  = 0

inner :: Query Int
inner (t :% Tree Int)    = case t of F n (_:_) -> n;        _ -> 0
inner (t :% Tree String) = case t of F s (_:_) -> length s; _ -> 0
inner _                  = 0

listQ :: Query [Int]
listQ (n :% Int)    = [n]
listQ (s :% String) = [length s]
listQ _             = []

n1 = everything (+)  allQ  $ tr1 :% Tree Int    -- > 102
n2 = everything (+)  leafQ $ tr1 :% Tree Int    -- > 69
n3 = everything (+)  inner $ tr1 :% Tree Int    -- > 33
n4 = everything (+)  allQ  $ [tr1,tr1] :% List (Tree Int) -- > 204
n5 = everything (++) listQ $ ([tr1,tr1],tr2) :% 
                             Pair (List $ Tree Int) (Tree String)
     -- > [5,6,6,7,7,6,7,8,8,6,7,6,7,8,8,
     --    5,6,6,7,7,6,7,8,8,6,7,6,7,8,8,
     --    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
                             
-- TRAVERSALS

type Traversal = forall a.Typed a -> a       -- SYB: Data a => a -> a

mapT :: Traversal -> Spine a -> Spine a
mapT t (f :$ x) = mapT t f :$ (t x :% typ x) 
mapT _ sp       = sp

fromSpine :: Spine a -> a 
fromSpine (Constr c) = c
fromSpine (f :$ x)   = fromSpine f $ obj x

everywhereBU,everywhereTD :: Traversal -> Traversal
everywhereBU t x = t $ fromSpine (mapT (everywhereBU t) $ toSpine x) :% typ x
everywhereTD t x = fromSpine $ mapT (everywhereTD t) $ toSpine $ t x :% typ x

doubleE :: Traversal
doubleE (t :% Tree Int) = case t of F n (t:_) | n == 7 -> F 1 [t]
                                    _ -> t
doubleE (n :% Int)    = n+n
doubleE (s :% String) = s++s
doubleE (x :% _)      = x

tr3 = everywhereBU doubleE $ tr1 :% Tree Int
tr4 = everywhereTD doubleE $ tr1 :% Tree Int

-- DIVTREE

data BST a b = BST {rbst :: a, fork :: Either b (BST a b,BST a b)} 
               deriving Show

divTree :: Int -> Int -> BST Bool Int
divTree n x = BST {rbst = divides n x, 
                   fork = if divides n $ 2*x then Left n
                          else Right (divTree (n-1) x,divTree (n+1) x)}

divides n x = n /= 0 && x`mod`n == 0

-- interior p poly returns True iff p is located within poly.
                        
interior :: (Float,Float) -> [(Float,Float)] -> Bool
interior p@(x,y) ps = pr3 $ foldl f (0,length ps-2,False) $ init ps
               where f (i,j,b) (x,y) = if yi < y && y <= yj || yj < y && y <= yi
                                       then if xi+(y-yi)/(yj-yi)*(xj-xi) < x 
                                            then (i+1,i,not b) else (i+1,i,b)
                                       else (i+1,j,b)
                                       where (xi,yi) = ps!!i; (xj,yj) = ps!!j
                     pr3 (_,_,b) = b

cloop :: IO ()
cloop = do putStrLn "Enter an integer x!"
           str <- getLine
           let x = read str
           if x < 5 then putStrLn "x < 5"
                    else do putStrLn $ "x = "++show x; cloop

type Pos = (Int,Int)
 
-- getReps as pairs returns all maximal subsets bs of as such that 
-- (i,j) in pairs implies that {as!!i,as!!j} is not a subset of bs.

getReps :: [a] -> [Pos] -> [[a]]
getReps as pairs = [[as!!i | i <- is] | is <- iss]
                   where iss = maxima length $ union [] 
                                             $ foldl g [indices as] pairs
                         g iss (i,j) = do is <- iss; [remove i is,remove j is]

aaa = getReps [1..3] [(0,1),(1,2)]
bbb = getReps [1..3] [(0,1),(0,2),(1,2)]

sorted (x:s@(y:_)) = x <= y && sorted s
sorted _           = True
          
mergesort,mergesort2 :: Ord a => [a] -> [a]

mergesort (x:y:s) = merge (mergesort $ x:s1) (mergesort $ y:s2)
                    where (s1,s2) = split s
mergesort s       = s    

mergesort2 s | n < 2 = s
             | True  = merge (mergesort2 s1) (mergesort2 s2)
                       where n = length s
                             (s1,s2) = splitAt (n `div` 2) s
   
split :: [a] -> ([a],[a])
split (x:y:s) = (x:s1,y:s2) where (s1,s2) = split s
split s       = (s,[])

split2 :: (a -> Bool) -> (a -> Bool) -> [a] -> Maybe ([a],[a])
split2 f g (x:s) = do (s1,s2) <- split2 f g s
                      if f x then Just (x:s1,s2) 
                             else do guard $ g x; Just (s1,x:s2) 
split2 _ _ _     = Just ([],[])
          
merge :: Ord a => [a] -> [a] -> [a]
merge s1@(x:s2) s3@(y:s4) = if x <= y then x:merge s2 s3 else y:merge s1 s4
merge [] s                = s
merge s _                 = s

minis :: Boolfun a -> [a] -> [a]
minis rel = foldr f [] where f x (y:s) | rel x y = f x s
                                       | rel y x = f y s
                                       | True    = y:f x s
                             f x _               = [x]
maxis = minis . flip

-- maxima f s returns the subset of all x in s such that f(x) agrees with the 
-- maximum of f(s).

maxima, minima :: Ord b => (a -> b) -> [a] -> [a]
maxima f s = [x | x <- s, f x == maximum (map f s)]
minima f s = [x | x <- s, f x == minimum (map f s)]

-- insertion sort with counter

sortC (x:s) = insert x s1 m
              where (s1,m) = sortC s
                    insert x s@(y:xs) m = if x <= y then (x:s,m) else (y:ys,n+1)
                                          where (ys,n) = insert x xs m
                    insert x _ m        = ([x],m)
sortC s     = (s,0)

-- PARSER
                
type Parser = StateT String

digit,delim :: MonadPlus m => Parser m Char
digit  = msum $ map char ['0'..'9']
delim  = msum $ map char " \n\t"
                                        
char :: MonadPlus m => Char -> Parser m Char
char chr = StateT $ \str -> do c:str <- return str
                               if c == chr then return (c,str) else mzero

string :: MonadPlus m => String -> Parser m String
string = mapM char

token :: MonadPlus m => Parser m a -> Parser m a
token p = do space; a <- p; space; return a
          where space = many delim
          
tchar :: MonadPlus m => Char -> Parser m Char
tchar = token . char

bool :: MonadPlus m => Parser m Bool
bool = msum [do token $ string "True"; return True,
             do token $ string "False"; return False]

nat,int :: MonadPlus m => Parser m Int
nat = do ds <- some digit; return $ read ds
int = nat `mplus` do char '-'; n <- nat; return $ -n

bintreeL :: Read a => Parser [ ] (BintreeL a)
bintreeL = do a <- StateT reads
              msum [do "(" <- StateT lex; left <- bintreeL
                       "," <- StateT lex; right <- bintreeL
                       ")" <- StateT lex; return $ Bin a left right,
                    do return $ Leaf a]

-- instance Read a => Read (BintreeL a) where readsPrec _ = runST bintreeL
                          
-- BINOMIALS

binom n k = product [k+1..n]`div`product [1..n-k]

pascal0 0 = [1]
pascal0 n = zipWith (+) (s++[0]) (0:s) where s = pascal0 $ n-1

pascal1 0 = [1]
pascal1 n = 1:[s!!(k-1)+s!!k | k <- [1..n-1]]++[1] where s = pascal1 $ n-1

pascal2 0 = [1]
pascal2 n = let s = pascal2 $ n-1
            in 1:[s!!(k-1)+s!!k | k <- [1..n-1]]++[1] 

pascal3 0 = [1]
pascal3 n = 1:[pascal3 (n-1)!!(k-1)+pascal3 (n-1)!!k | k <- [1..n-1]]++[1] 

-- DIAGONALS

cantor n s = foldl f s $ indices s
             where f s' i = updList s' (x*n+y) $ s!!i where (x,y) = p i
                   p 0 = (0,0)
                   p i = if even x
                         then if even y
                              then if x > 0 
                                   then if y' < n then (x-1,y') else (x',y)
                                   else if y' < n then (0,y') else (1,y) 
                              else if x' < n then (x',y-1) else (x,y') 
                         else if even y
                              then if y > 0 
                                   then if x' < n then (x',y-1) else (x,y') 
                                   else if x' < n then (x',0) else (x,1)
                              else if y' < n then (x-1,y') else (x',y) 
                         where (x,y) = p $ i-1; x' = x+1; y' = y+1

mapfilter2 :: (a -> b -> Bool) -> (a -> b -> c) -> [a] -> [b] -> [c]
mapfilter2 p f as bs = [f a b | a <- as, b <- bs, p a b]

filterL :: ([a] -> Bool) -> [[a]] -> [[a]]
filterL p ss = [s | s <- sequence ss, p s]

sublist :: [a] -> Int -> Int -> [a]
sublist (x:s) 0 0                  = [x]
sublist (x:s) 0 j | j > 0          = x:sublist s 0 (j-1)
sublist (x:s) i j | i > 0 && j > 0 = sublist s (i-1) (j-1)
sublist _ _ _                      = []

sublists :: [a] -> [[a]]
sublists []    = [[]]
sublists (a:s) = ss ++ map (a:) ss where ss = sublists s

-- subsets n returns all nonempty proper subsets of [0..n-1].
                                            
subsets n = concatMap (subsetsN n) [1..n-1]

-- subsetsN n k returns all subsets of [0..n-1] with exactly k elements.

subsetsN _ 0 = [[]]
subsetsN n k = [insertSet x xs | xs <- subsetsN n (k-1), 
                                 x <- [0..n-1] `diff` xs] 

-- subsetsB n k returns all subsets of [0..n-1] with at most k elements.

subsetsB n k = concatMap (subsetsN n) [0..k]

prod2 as bs = [(a,b) | a <- as, b <- bs]

prod :: [[a]] -> [[a]]                  -- prod = sequence
prod (s:ss) = [a:s | a <- s, s <- prod ss] 
prod _      = [[]]

-- prodF f ss returns the subset r of prod ss such that [a1,...,an] is in r 
-- iff f ai aj for all 1 <= i =/= j <= n.

prodF :: Boolfun a -> [[a]] -> [[a]] 
prodF rel (s:ss) = [a:s | a <- s, s <- prodF rel ss, all (rel a) s]
prodF _ _        = [[]]

prodexa = prodF disjoint [subsetsB 2 2,subsetsB 2 2]

disjoint s = all (`notElem` s)  

{- [[[],[]],[[],[0]],[[],[1]],[[],[0,1]],[[0],[]],[[0],[1]],[[1],[]],[[1],[0]],
    [[0,1],[]]] -}

-- BINARY RELATIONS

class Semiring r where add,mul :: r -> r -> r; zero,one :: r

instance Semiring Bool where add = (||); mul = (&&); zero = False; one = True
instance Semiring Int  where add = (+);  mul = (*);  zero = 0; one = 1

type BinRel a = [(a,a)]

instance Eq a => Semiring (BinRel a) where 
                 add = union
                 mul rel rel' = [(a,c) | (a,b) <- rel, (b',c) <- rel', b == b']
                 zero = []
                 one = []

plusBR :: Eq a => BinRel a -> BinRel a
plusBR rel = fixpt subset (add rel . mul rel) []
                 
type BRfun a = a -> [a]

instance Eq a => Semiring (BRfun a) where 
                 add sucs sucs' = liftM2 union sucs sucs'
                 mul sucs sucs' = unionMap sucs' . sucs
                 zero = const []
                 one  = single
                
type BRfunL a = (a,[a]) -> [(a,[a])]

instance Eq a => Semiring (BRfunL a) where 
                 add rel rel' = liftM2 unionL rel rel'
                 mul rel rel' = unionMapL rel' . rel
                 zero = const []
                 one  = single
                 
type TRfun a label = a -> [(label,a)]
 
-- GRAPHS

data Graph a        = G  [a] (BRfun a)
data GraphL a label = GL [a] (TRfun a label)

graph2Rel :: Graph a -> BinRel a 
graph2Rel (G nodes sucs) = [(a,b) | a <- nodes, b <- sucs a]

rel2Graph :: Eq a => BinRel a -> Graph a
rel2Graph rel = G nodes sucs where 
                (nodes,sucs) = foldl f ([], const []) rel
                f (as,g) (a,b) = (insert a as, update g a $ insert b $ g a)
                 
insertL :: Eq a => (a,[a]) -> [(a,[a])] -> [(a,[a])]
insertL x@(a,as) (y@(b,bs):s) = if a == b then (a,as `union` bs):s 
                                          else y:insertL x s
insertL x _ = [x]

unionL :: Eq a => [(a,[a])] -> [(a,[a])] -> [(a,[a])]
unionL = foldl $ flip insertL

unionMapL :: Eq a => BRfunL a -> [(a,[a])] -> [(a,[a])]
unionMapL rel = foldl unionL [] . map rel

closureF,closureT,warshall,diagonal,closureG :: Eq a => Graph a -> Graph a

closureF (G nodes sucs) = G nodes sucs' where
                          sucs' = fixpt le (mul sucs . add one) zero
                          le sucs sucs' = all (liftM2 subset sucs sucs') nodes

closureT (G nodes sucs) = G nodes sucs'             -- only for acyclic graphs
                          where sucs' = mul sucs $ add one sucs'

warshall (G nodes sucs) = G nodes sucs' where       
                          sucs' = foldl trans sucs nodes
                          trans sucs a = fold2 update sucs nodes $ map f nodes 
                             where f b = if a `elem` cs then cs `union` sucs a
                                                        else cs 
                                         where cs = sucs b 

diagonal (G nodes sucs) = G nodes $ fold2 update sucs nodes $ map add nodes
                          where add a = insert a $ sucs a

closureG (G nodes sucs) = G nodes $ map fst . rel' . \a -> (a,[])
                          where rel' = mul rel $ add one rel'
                                rel (a,as) = [(b,insert a as) | b <- sucs a, 
                                                                b `notElem` as]

instance Show a => Show (Graph a) where
         show (G nodes sucs) = concatMap f $ filter (not . null . sucs) nodes
                         where f a = '\n':show a++" -> "++show (sucs a)

instance (Show a,Show label) => Show (GraphL a label) where
         show (GL nodes sucs) = concatMap f $ filter (not . null . sucs) nodes
                          where f a = '\n':show a++" -> "++show (sucs a)

reachables,reachables' :: Eq a => Graph a -> a -> [a]
reachables (G nodes sucs) a  = fixpt subset step [a]
                               where step as = union as $ unionMap sucs as
reachables' (G nodes sucs) a = fst $ fixpt le step ([a],[]) where
         le (as,visited) (bs,visited') = subset as bs && subset visited visited'
         step (as,visited) = (union as $ unionMap sucs $ diff as visited, 
                              union visited as)    

-- MATRICES

type Matrix = Array Pos

dim :: Matrix r -> Int
dim = fst . snd . bounds

mkMat :: Int -> (Pos -> r) -> Matrix r
mkMat d = mkArray ((1,1),(d,d))

zeroM,oneM :: Semiring r => Int -> Matrix r
zeroM d = mkMat d $ const zero
oneM d  = mkMat d $ \(i,j) -> if i == j then one else zero
               
instance Semiring r => Semiring (Matrix r) where
                       add m m' = mkMat (dim m) $ liftM2 add (m!) (m'!)
                       mul m m' = mkMat d $ \p -> foldl1 add $ map (f p) [1..d] 
                                  where d = dim m
                                        f (i,j) k = mul (m!(i,k)) $ m'!(k,j)
                       zero = zeroM 1; one = oneM 1
               
power :: (Eq r,Semiring r) => Matrix r -> Int -> Matrix r
power m k = iterate (mul m) (oneM $ dim m)!!k

plus :: (Eq r,Semiring r) => (r -> r -> Bool) -> Matrix r -> Matrix r
plus le m = fixpt le' (add m . mul m) $ zeroM $ dim m
            where le' m m' = all (liftM2 le (m!) (m'!)) [(i,j) | i <- s, j <- s]
                             where s = [1..dim m]

instance Show (Matrix Bool) where 
         show m = concatMap f s where
                  s = [1..dim m]
                  f i = '\n':show i++" -> "++show [j | j <- s, m!(i,j)]
                  
instance Show r => Show (Matrix r) where 
         show m = concatMap f $ range ((1,1),(d,d)) where
                  d = dim m
                  f (i,j) = '\n':show i++" -- "++show (m!(i,j))++" --> "++show j

extendM :: (Eq r,Semiring r) => Matrix r -> Matrix r -> (Matrix r,Matrix r)
extendM m m' = case (dim m,dim m') of (1,n) | m!(1,1) == zero  -> (zeroM n,m')
                                            | m!(1,1) == one   -> (oneM n,m')
                                      (n,1) | m'!(1,1) == zero -> (m,zeroM n)
                                            | m'!(1,1) == one  -> (m,oneM n)
                                      _ -> (m,m')

-- GRAPHS AS MATRICES

data GraphM a r = M [a] (Matrix r)

position1 :: Eq a => [a] -> a -> Int
position1 s a = case search (== a) s of Just i -> i+1; _ -> 0

graph2mat :: Eq a => Graph a -> Matrix Bool
graph2mat (G nodes sucs) = mkMat (length nodes) f where
                           f (i,j) = nodes!!(j-1) `elem` sucs (nodes!!(i-1)) 
                         
graphL2mat :: (Eq a,Semiring r) => GraphL a r -> Matrix r
graphL2mat (GL nodes sucs) = mkMat (length nodes) f where
                      f (i,j) = case lookup (nodes!!(j-1)) $ map (snd *** fst) 
                                                           $ sucs (nodes!!(i-1))
                                of Just label -> label; _ -> zero                        

mat2graph :: Eq a => GraphM a Bool -> Graph a
mat2graph (M nodes m) = G nodes $ f . position1 nodes where
                        f i = [nodes!!(j-1) | j <- [1..length nodes], m!(i,j)]
                  
mat2graphL :: (Eq a,Eq r,Semiring r) => GraphM a r -> GraphL a r
mat2graphL (M nodes m) = GL nodes $ f . position1 nodes where
                         f i = [(label,nodes!!(j-1)) | j <- [1..length nodes],
                                                       let label = m!(i,j), 
                                                       label /= zero]

closureM :: Eq a => Graph a -> Graph a
closureM graph@(G nodes _) = mat2graph $ M nodes $ plus (<=) $ graph2mat graph
     
type Paths a = ([[a]],Int)

instance Eq a => Semiring (Paths a) where 
         add (ps,m) (qs,n) = (rs,length rs) where rs = union ps qs
         mul (ps,m) (qs,n) = (rs,length rs)
                             where rs = filter f [p++q | p <- ps, q <- qs]
                                   f p = length p == length (union [] p)
         zero = ([],0); one = ([],0)

-- allpaths g labels every edge a->b of g with a list and the number of all 
-- paths from a to b that contain every node of g at most once.

allpaths :: Eq a => Graph a -> GraphL a Int         
allpaths (G nodes sucs) = g $ mat2graphL $ M nodes $ plus le $ graphL2mat 
                                                   $ GL nodes $ map f . sucs
                          where le (_,m) (_,n) = m <= n          
                                f a = (([[a]],1),a)
                                g (GL nodes sucs) = GL nodes $ map h . sucs
                                h ((_,n),a) = (n,a)
     
type Path a = ([a],Int)

instance Semiring (Path a) where 
         add (p,m) (q,n) = if m <= n then (p,m) else (q,n)
         mul (p,m) (q,n) = (p++q,
                            if maxBound `elem` [m,n] then maxBound else m+n)
         zero = ([],maxBound); one = ([],0)

-- minpaths g labels every edge a->b of g with the shortest path from a to b and 
-- its weight (= sum of the labels of the edges that form the path).

minpaths :: Eq a => GraphL a Int -> GraphL a (Path a)
minpaths (GL nodes sucs) = mat2graphL $ M nodes $ plus le $ graphL2mat 
                                                $ GL nodes $ map f . sucs
                           where le (_,m) (_,n) = m >= n
                                 f (n,a) = (([a],n),a) 
                               
-- GRAPH EXAMPLES

graph1,graph2,graph3,graph4 :: Graph Int
graph1 = G [1..6] $ \case 1 -> [2,3]; 3 -> [1,4,6]; 4 -> [1]
                          5 -> [3,5]; 6 -> [2,4,5]; _ -> []
graph2 = G [1..6] $ \a -> if a `elem` [1..5] then [a+1] else []
graph3 = G [1..6] $ \a -> [a+1..6]
graph4 = G [1,11,12,111,112,121,122,1121,1122] $ 
           \a -> if a `elem` [1,11,12,112] then [a*10+1,a*10+2] else []
                          
clos1R = rel2Graph $ plusBR $ graph2Rel graph1
clos1W = warshall graph1
clos1F = closureF graph1
clos1M = closureM graph1
{- 
1 -> [1,2,3,4,5,6]
3 -> [1,2,3,4,5,6]
4 -> [1,2,3,4,5,6]
5 -> [1,2,3,4,5,6]
6 -> [1,2,3,4,5,6] 
-}
clos1G = closureG graph1
{- 
1 -> [2,3,4,5,6]
3 -> [1,2,4,5,6]
4 -> [1,2,3,5,6]
5 -> [1,2,3,4,5,6]
6 -> [1,2,3,4,5] 
-}
clos2R = rel2Graph $ plusBR $ graph2Rel graph2
clos2G = closureG graph2
clos2T = closureT graph2
clos2W = warshall graph2 
clos2F = closureF graph2
clos2M = closureM graph2
{-
1 -> [2,3,4,5,6]
2 -> [3,4,5,6]
3 -> [4,5,6]
4 -> [5,6]
5 -> [6]
-}
clos3R = rel2Graph $ plusBR $ graph2Rel graph3
clos3G = closureG graph3
clos3T = closureT graph3
clos3W = warshall graph3
clos3F = closureF graph3
clos3M = closureM graph3
{-
1 -> [2,3,4,5,6]
2 -> [3,4,5,6]
3 -> [4,5,6]
4 -> [5,6]
5 -> [6]
-}
clos4R = rel2Graph $ plusBR $ graph2Rel graph4
clos4G = closureG graph4
clos4T = closureT graph4
clos4W = warshall graph4
clos4F = closureF graph4
clos4M = closureM graph4
{- 
1 -> [11,12,111,112,1121,1122,121,122]
11 -> [111,112,1121,1122]
12 -> [121,122]
112 -> [1121,1122]
-}   
reach1  = reachables graph1 1
reach2  = reachables graph2 1
reach3  = reachables graph3 1
reach1' = reachables' graph1 1
reach2' = reachables' graph2 1
reach3' = reachables' graph3 1

path1 = allpaths graph1
{-
1 -> [(3,1),(5,2),(1,3),(2,4),(1,5),(1,6)]
3 -> [(5,1),(8,2),(4,3),(5,4),(3,5),(3,6)]
4 -> [(1,1),(2,2),(1,3),(2,4),(1,5),(1,6)]
5 -> [(6,1),(8,2),(2,3),(4,4),(2,5),(2,6)]
6 -> [(4,1),(7,2),(2,3),(3,4),(2,5),(2,6)]
-}
path2 = allpaths graph2
{-
1 -> [(1,2),(1,3),(1,4),(1,5),(1,6)]
2 -> [(1,3),(1,4),(1,5),(1,6)]
3 -> [(1,4),(1,5),(1,6)]
4 -> [(1,5),(1,6)]
5 -> [(1,6)]
-}
path3 = allpaths graph3
{-
1 -> [(1,11),(1,12),(1,111),(1,112),(1,121),(1,122),(1,1121),(1,1122)]
11 -> [(1,111),(1,112),(1,1121),(1,1122)]
12 -> [(1,121),(1,122)]
112 -> [(1,1121),(1,1122)]
-}
path4 = allpaths graph4
{- 
1 -> [(1,2),(2,3),(4,4),(8,5),(16,6)]
2 -> [(1,3),(2,4),(4,5),(8,6)]
3 -> [(1,4),(2,5),(4,6)]
4 -> [(1,5),(2,6)]
5 -> [(1,6)]
-}
graph5 :: GraphL Int Int
graph5 = GL [1..5] $ \case 1 -> [(100,5),(40,2)]
                           2 -> [(50,5),(10,3)]
                           3 -> [(20,4)]
                           4 -> [(10,5)]
                           _ -> []

path5 = minpaths graph5
{- 
1 -> [((40,[2]),2),((50,[2,3]),3),((70,[2,3,4]),4),((80,[2,3,4,5]),5)]
2 -> [((10,[3]),3),((30,[3,4]),4),((40,[3,4,5]),5)]
3 -> [((20,[4]),4),((30,[4,5]),5)]
4 -> [((10,[5]),5)]
-}
          
-- KRUSKAL ALGORITHM

type LGraph = [(Int,Int,Int)]

single x = [x]

spanTree :: LGraph -> Maybe LGraph

spanTree graph = loop (sort r graph) (map single allNodes) []
                 where r (_,x,_) (_,y,_) = x <= y

loop :: LGraph -> [[Int]] -> LGraph -> Maybe LGraph

loop _ [_] tree                          = Just tree
loop [] (_:_:_) _                        = Nothing
loop (edge@(m,_,n):graph) partition tree = 
                 if nodes1 == nodes2 then loop graph partition tree
                 else loop graph partition' $ edge:tree
                 where nodes n = head $ filter (n `elem`) partition
                       nodes1 = nodes m
                       nodes2 = nodes n
                       partition' = (nodes1++nodes2):
                                    filter (`notElem` [nodes1,nodes2]) partition

allNodes = [1..6]

graph6 :: LGraph
graph6 = [(1,11,2),(2,11,3),(3,11,1),(3,11,4),(3,11,5),(4,11,5),(4,11,6)]

-- spanTree graph5 = Just [(2,11,3), (3,11,1), (3,11,5), (4,11,5), (4,11,6)]

-- KNUTH-MORRIS-PRATT ALGORITHM

-- siehe: Uwe Schöning, Algorithmen - kurz gefasst, $ 8.3, oder
--        http://www.informatik.uni-leipzig.de/lehre/Heyer0001/AD2-Vorl9

-- kmp pat text schreibt * unter das erste Zeichen jedes Vorkommens von pat in
-- text.

kmp :: String -> String -> IO ()
kmp pat text = writeFile "KMP" $ text++'\n':map f textInds where
               textInds = indices text
               f i = if i `elem` positions then '*' else ' '
               positions = snd $ foldl g (0,[]) textInds
               lg = length pat
               g (q,ps) i = if q' == lg then (tab!lg,i+1-lg:ps) else (q',ps) 
                            where q' = loop q
                                  loop q = if q > 0 && not b then loop $ tab!q 
                                           else if b then q+1 else q
                                           where b = text!!i == pat!!q
               tab = array (1,lg) [(q,maximum $ s q) | q <- [1..lg]] where
               s q = [k | k <- [0..q-1], take k pat == drop (q-k) (take q pat)]

kmp1 = kmp "kakao" "kakaakakakaoka"
kmp2 = kmp "kakao" "kakaakakakabka"
kmp3 = kmp "kakao" "kakaakakakaokakakaakakakaoka"
kmp4 = kmp "kaka" "kakakakakakakakaka"
kmp5 = kmp "ananas" "ananananassananas"

-- LIST INVERSION
               
-- i in invertRel s n ks!!k iff k in s!!i. Assumption: k in [0..n].
-- invertRel [[1,2,3],[1,2,3],[1,2,3]] 3 ---> [[],[0,1,2],[0,1,2],[0,1,2]]

invertRel :: [[Int]] -> Int -> [[Int]]
invertRel iss n = map f [0..n] where f k = searchAll (k `elem`) iss
               
-- i in (invertRel2 s m n!!k)!!lab iff k in (s!!i)!!lab. 
-- Assumptions: lab in [0..m], k in [0..n]. For all i, length (s!!i) = m+1
-- invertRel2 [[[1,2],[3]],[[1],[2,3]],[[],[1,2,3]]] 1 3 
--                           ---> [[[],[]],[[0,1],[2]],[[0],[1,2]],[[],[0,1,2]]]

invertRel2 :: [[[Int]]] -> Int -> Int -> [[[Int]]]
invertRel2 isss m n = map f [0..n]
                      where f k = map g [0..m]
                                  where g lab = searchAll h isss
                                                where h iss = k `elem` iss!!lab

-- VALIDITY OF PROPOSITIONAL FORMULAS

data Prop = X Int | Not Prop | Prop :& Prop | Prop :| Prop | Prop :=> Prop |
            Prop := Prop

mkFun :: Prop -> [Bool] -> Bool
mkFun (X i) s     = s!!i
mkFun (Not p) s   = not $ mkFun p s
mkFun (p :& q) s  = mkFun p s && mkFun q s
mkFun (p :| q) s  = mkFun p s || mkFun q s
mkFun (p :=> q) s = not (mkFun p s) || mkFun q s
mkFun (p := q) s  = mkFun p s == mkFun q s

vars :: Prop -> [Int]
vars (X i)     = [i]
vars (Not p)   = vars p
vars (p :& q)  = vars p `union` vars q
vars (p :| q)  = vars p `union` vars q
vars (p :=> q) = vars p `union` vars q
vars (p := q)  = vars p `union` vars q

valid :: Prop -> Bool
valid p = and $ map (mkFun p) $ args $ maximum (vars p)+1

args :: Int -> [[Bool]]             -- creates all Boolean lists with n elements
args 0 = [[]]
args n = [b:bs | b <- [True,False], bs <- args $ n-1]

funToSet :: [a] -> [Bool] -> [a]
funToSet s f = map (s!!) $ filter (f!!) $ indices s

powerset,powersetR :: Eq a => [a] -> [[a]]
powerset s = map (funToSet s) $ args $ length s
powersetR (a:s) = if a `elem` s then ps else ps ++ map (a:) ps
                  where ps = powersetR s
powersetR _     = [[]]

showTrans :: (Show a,Show b) => a -> b -> String
showTrans a b = "\n& " ++ show a ++ " -> " ++ show b

showTransR :: Show a => a -> [a] -> String
showTransR a []  = ""
showTransR a [b] = showTrans a b
showTransR a s   = "\n& " ++ show a ++ " -> branch" ++ show s

concatTrans :: Show a => [(a,[a])] -> String
concatTrans = concatMap $ uncurry showTransR 

showTransR' :: Show a => a -> DS.Set a -> String                -- not used
showTransR' a s  = case DS.size s of 
                        0 -> ""
                        1 -> showTrans a $ findMin s
                        _ -> "\n& " ++ show a ++ " -> branch" ++ show s

showTransN :: Eq a => [a] -> a -> a -> String                   -- not used
showTransN s  a b = showTrans (f a) $ f b where f = position s

showTransRN :: Eq a => [a] -> (a,[a]) -> String
showTransRN s (a,s') = showTransR (f a ) $ map f s' where f = position s

position :: Eq a => [a] -> a -> Int
position s a = case search (== a) s of Just i -> i; _ -> 1000

-- SET TYPES

newtype Set a = Set {list :: [a]} 

instance Eq a => Eq (Set a) where 
                 s == s' = s <= s' && s' <= s

instance Eq a => Ord (Set a) where
                 s <= s' = list s `subset` list s'
                   
instance Ord a => Monoid (Set a) where 
                  mempty = Set []
                  mappend (Set s) (Set s') = Set $ foldl (flip insertSet) s s'

insertSet :: Ord a => a -> [a] -> [a]
insertSet x s@(y:s') = if x == y then s 
                                 else if x < y then x:s else y:insertSet x s'
insertSet x _        = [x]

instance Show a => Show (Set a) where
                   show = ('{':) . (++"}") . init . tail . show . list
                
set1 = Set [1,2,3] <= Set [3,4,2,5,1,99]
set2 = Set [1,2,3] >= Set [3,4,2,5,1,99]

mkSet :: Eq a => [a] -> Set a
mkSet = Set . union []          

{- Since constraints are not allowed in Monad instances, Set cannot be a Monad 
   instance:

instance Monad Set
         where (>>=) :: Eq b => Set a -> (a -> Set b) -> Set b
               Set s >>= f = Set $ unionMap (list . f) s
               return a = Set [a]
               fail _ = mzero

instance MonadPlus Set 
         where mzero = Set []
               mplus (Set s) (Set s') = Set $ union s s' -}

-- RELATION TYPES

newtype Rel a = Rel {rlist :: [(a,[a])]} 

instance Eq a => Eq (Rel a) where 
                 r == r' = r <= r' && r' <= r

instance Eq a => Ord (Rel a) where
                 r <= r' = Set dom_r <= Set (dom r') && vals r <= vals r'
                           where dom = map fst . rlist
                                 dom_r = dom r
                                 fun r a = fromJust $ lookup a r
                                 vals r = Set $ map (fun $ rlist r) dom_r
                   
instance Ord a => Monoid (Rel a) where 
                  mempty = Rel []
                  mappend (Rel r) (Rel r') = Rel $ foldl insertRel r r' 
                 
insertRel :: Ord a => [(a,[a])] -> (a,[a]) -> [(a,[a])]
insertRel (p@(x,s):r) p'@(y,s') = if x == y then (x,s`union`s'):r
                                            else if y < x then p:p':r
                                                          else p:insertRel r p'
insertRel _ p = [p]

{-
instance Ord a => Monoid (DS.Set a) where mempty = DS.empty
                                          mappend = DS.union

type RelD a = DMS.Map a [a]

instance Ord a => Monoid (RelD a) where mempty = DMS.empty
                                        mappend = DMS.union
-} 

assoc :: (Eq a,Eq b) => [(a,[b])] -> [(a,[b])]
assoc ((_,[]):rel) = assoc rel
assoc ((a,bs):rel) = insertAssoc a bs (assoc rel)
assoc _            = []
                      
insertAssoc :: (Eq a,Eq b) => a -> [b] -> [(a,[b])] -> [(a,[b])]
insertAssoc a bs (p@(x,cs):s) | a == x = if null cs then insertAssoc a bs s
                                         else insertAssoc a (bs`union`cs) s
                              | True   = p:insertAssoc a bs s
insertAssoc a bs _                     = [(a,bs)]

assoc2 :: (Eq a,Eq b,Eq c) => [(a,b,[c])] -> [(a,[(b,[c])])]
assoc2 ((_,_,[]):rel) = assoc2 rel
assoc2 ((a,b,cs):rel) = insertAssoc2 a [(b,cs)] (assoc2 rel)
assoc2 _              = []

insertAssoc2 :: (Eq a,Eq b,Eq c) 
                => a -> [(b,[c])] -> [(a,[(b,[c])])] -> [(a,[(b,[c])])]
insertAssoc2 a bcs (t@(x,ccs):s) 
                  | a == x = if null ccs then insertAssoc2 a bcs s
                                         else insertAssoc2 a (foldr f ccs bcs) s
                  | True   = t:insertAssoc2 a bcs s
                             where f (b,cs) = insertAssoc b cs
insertAssoc2 a bcs _       = [(a,bcs)]

-- PARTITIONS

{- logic program

partsL [a] [[a]]
partsL (a:s) ([a]:part)    <== partsL s part
partsL (a:s) ((a:s'):rest) <== partsL s (s':rest) -}
                                        
-- partsL/M s returns all list partitions of s.
                                        
partsL,partsLM :: [a] -> [[[a]]]

partsL [a]     = [[[a]]]
partsL (a:s)   = concatMap glue $ partsL s
                 where glue part@(s':rest) = [[a]:part,(a:s'):rest]     
                 
partsLM [a]    = [[[a]]]
partsLM (a:s)  = do part@(s':rest) <- partsLM s
                    [[a]:part,(a:s'):rest]      

partsC :: Int -> Int -> [[[Int]]]
partsC n lg = [p | p <- partsLM [1..n], all ((>= lg) . length) p]

-- partsC 10 3

-- parts/2 s returns all set partitions of s.

parts,partsM :: [a] -> [[[a]]]

parts [a]   = [[[a]]]
parts (a:s) = concatMap (glue []) $ parts s
              where glue part (s:rest) = ((a:s):part++rest):glue (s:part) rest
                    glue part _        = [[a]:part]

partsM [a]   = [[[a]]]
partsM (a:s) = concatMap (glue []) $ parts s
               where glue part (s:rest) = ((a:s):part++rest):glue (s:part) rest
                     glue part _        = [[a]:part]

partsS :: Eq a => [a] -> [Set (Set a)]
partsS [a] = [Set [Set [a]]]
partsS s   = unionMap f $ indices s
             where f i = concatMap (glue a) $ partsS $ remove a s where a = s!!i
                   glue a (Set part@(Set s:rest)) = map (Set $)[Set [a]:part,
                                                                Set (a:s):rest]

partsno 0 = 1
partsno n = sum $ map f [0..n-1] where f i = binom (n-1) i*partsno i

pp = length (partsS [0..9]) == partsno 10

partsnos = map partsno [1..10] -- [1,2,5,15,52,203,877,4140,21147,115975]

-- INTERVALS
                                        
-- intervals/M m n returns all partitions of the interval (m,n)

{- logic program

intervals m n [(m,n)]        <== m+1 = n
intervals m n ((m,m+1):ints) <== intervals s (m+1) n ints
intervals m n ((m,k):rest)   <== intervals s (m+1) n ((_,k):rest) -}
                                        
intervals,intervalsM :: Int -> Int -> [[(Int,Int)]]
intervals m n | m' == n  = [[(m,n)]] 
              | True     = concatMap glue $ intervals m' n
                         where m' = m+1
                               glue ints@((_,k):rest) = [(m,m'):ints,(m,k):rest]
intervalsM m n | m' == n = [[(m,n)]] 
               | True    = do ints@((_,k):rest) <- intervalsM m' n
                              [(m,m'):ints,(m,k):rest]
                           where m' = m+1
intervalsC n lg = [p | p <- intervalsM 0 n, all f p] where f (m,n) = n-m >= lg

-- intervalsC 20 5

-- PERMUTATIONS

isPerm :: Eq a => [a] -> [a] -> Bool
isPerm s s' = f s == f s' where f s0 = map (card s0) $ s++s'

card :: Eq a => [a] -> a -> Int
card s a = length $ filter (== a) s

insertBag :: Eq a => [[a]] -> [a] -> [[a]]
insertBag s@(x:s') x' = if isPerm x x' then s else x:insertBag s' x'
insertBag _ x = [x]

unionBag = foldl insertBag

insert3,remove3 :: Ord a => [([a],[a],[a])] -> ([a],[a],[a]) -> [([a],[a],[a])]
insert3 s@(t@(x,y,z):s') t'@(x',y',z') = 
                                    if DL.sort (x++y++z) == DL.sort (x'++y'++z')
                                    then s else t:insert3 s' t'
insert3 _ t = [t]
remove3 s (x,y,z) = filter f s where
                    f (x',y',z') = DL.sort (x++y++z) /= DL.sort (x'++y'++z')
                    
union3,diff3 :: Ord a => [([a],[a],[a])] -> [([a],[a],[a])] -> [([a],[a],[a])]
union3 = foldl insert3
diff3  = foldl remove3

insertBagR :: Eq a => [([a],[[a]])] ->  ([a],[[a]])-> [([a],[[a]])] 
insertBagR (p@(x,s):r) p'@(x',s') = if isPerm x x' 
                                    then (x,foldl insertBag s s'):r 
                                    else p:insertBagR r p'
insertBagR _ p = [p]
                 
insertBagR3 :: Eq a => [(([a],[a],[a]),[([a],[a],[a])])] 
                    ->  (([a],[a],[a]),[([a],[a],[a])])
                    -> [(([a],[a],[a]),[([a],[a],[a])])] 
insertBagR3 (p@((x,y,z),s):r) p'@((x',y',z'),s') = 
              if and $ zipWith isPerm [x,y,z] [x',y',z']
              then ((x,y,z),zip3 s7 s8 s9):r else p:insertBagR3 r p'
              where (s1,s2,s3) = unzip3 s
                    (s4,s5,s6) = unzip3 s'
                    [s7,s8,s9] = zipWith (foldl insertBag) [s1,s2,s3] [s4,s5,s6]
insertBagR3 _ p = [p]

nextPerm :: Ord a => [a] -> [a]
nextPerm s@(x:xs) = if sorted s then reverse s else next [x] xs where
          next s@(x:_) (y:ys) = if x <= y then next (y:s) ys else swap s where
                   swap [x]      = y:x:ys
                   swap (x:z:xs) = if z > y then x:swap (z:xs) else y:z:xs++x:ys
          nextPerm _ = []
          
{- logic programs

permsLR [] []
permsLR s (s!!i:z) <== i <- indices s /\ permsLR (take i s++drop (i+1) s) z

permsL s z <== loop s [] z
loop [] s s
loop s s' z <== i <- indices s /\ loop (take i s++drop (i+1) s) (s!!i:s') z 

permsR [] []
permsR s (x:z) <== x <- s /\ permsR (remove x s) z

perms s z <== loop s [] z
loop [] s s
loop s s' z <== x <- s /\ loop (remove x s) (x:s') z 

permsC c s z <== loop s [] z where
loop [] s s
loop s s' z <== x <- s /\ c (x:s') /\ loop (remove x s) (x:s') z 
-}

permsLR,permsLRM,permsL,permsLM :: [a] -> [[a]] 
                                        -- computes all permutations of a list
permsLR []  = [[]]
permsLR s   = concatMap f $ indices s where
              f i = map (s!!i:) $ permsLR $ take i s++drop (i+1) s
permsLRM [] = [[]]
permsLRM s  = do i <- indices s
                 s' <- permsLRM $ take i s++drop (i+1) s
                 [s!!i:s']
permsL s  = loop s [] where 
            loop [] s = [s]                 
            loop s s' = concatMap f $ indices s where
                        f i = loop (take i s++drop (i+1) s) $ s!!i:s'
permsLM s = loop s [] where 
            loop [] s = [s]                 
            loop s s' = do i <- indices s
                           loop (take i s++drop (i+1) s) $ s!!i:s'

permsR,permsRM,perms,permsM :: Eq a => [a] -> [[a]]  
                                        -- computes all permutations of a list
permsR []  = [[]]                       -- with pairwise different elements                             
permsR s   = concatMap f s where f x = map (x:) $ permsR $ remove x s
permsRM [] = [[]]
permsRM s  = do x <- s
                s' <- permsRM $ remove x s
                [x:s']
perms s  = loop s [] where              
           loop [] s = [s]                  
           loop s s' = concatMap f s where f x = loop (remove x s) $ x:s'
permsM s = loop s [] where              
           loop [] s = [s]                  
           loop s s' = do x <- s
                          loop (remove x s) $ x:s'

permsC,permsCM,permsLCM :: Eq a => ([a] -> Bool) -> [a] -> [[a]]
permsC c s  = loop s [] where           -- computes all permutations of a list
              loop [] s = [s]           -- with pairwise different elements
                                        -- satisfying c  
              loop s s' = concatMap f s where 
                          f x | c new = loop (remove x s) new
                              | True  = [] where new = x:s'
permsCM c s = loop s [] where           
              loop [] s = [s]           
              loop s s' = do x <- s       
                             let new = x:s'
                             guard $ c new
                             loop (remove x s) new
permsLCM c s = loop s [] where 
               loop [] s = [s]              
               loop s s' = do i <- indices s
                              let new = s!!i:s'
                              guard $ c new
                              loop (take i s++drop (i+1) s) new

type Branch  state m = state -> [state] -> m ()
type Branch' state m = state -> DS.Set state -> m ()

-- QUEENS

-- 4 queens yield 2 solutions and 15 further states
-- 5 queens yield 10 solutions and 44 further states
-- 6 queens yield 4 solutions and 149 further states
-- 7 queens yield 40 solutions and 512 further states
-- 8 queens yield 92 solutions and 1965 further states
-- 9 queens yield 352 solutions and 8042 further states
-- 10 queens yield 724 solutions and 34815 further states
-- 11 queens yield 2680 solutions and 164246 further states

safe :: Int -> [Int] -> Bool
safe i (k:col:val) = col-i /= k && k /= col+i && safe (i+1) (k:val)
safe _ _           = True
                                          
queensR,queensI :: Int -> [[Int]]             
queensR n = qrec [1..n] where
            qrec :: [Int] -> [[Int]]
            qrec [] = [[]]
            qrec s  = do k <- s
                         val <- qrec $ remove k s
                         let val' = k:val
                         guard $ safe 1 val'
                         [val']
queensI n = permsLCM (safe 1) [1..n] 
                 
type Qstate = ([Int],[Int])             -- free resp. occupied column indices
type Qtrans = (Qstate,[Qstate])         -- state transitions

qfirst :: Int -> Qstate 
qfirst n = ([1..n],[])

qsuccessors :: Qstate -> [Qstate]
qsuccessors st@(s,val) = do k <- s
                            let val' = k:val
                            guard $ safe 1 val'
                            [(remove k s,val')]

qloop :: Monad m => Branch Qstate m -> Qstate -> ListT m [Int]  
qloop _ ([],val) = return val
qloop branch st  = do lift $ branch st sts
                      msum $ map (qloop branch) sts
                   where sts = qsuccessors st

qheader file n = writeFile file $ "specs: queens\naxioms:\nprocs == [1.." ++ 
                                  show n ++ "]"
                   
queens,queensIO,queensS :: Int -> IO (Int,[[Int]])

queens n   = return (length solutions,solutions)
             where Id solutions = runLT $ qloop branch $ qfirst n
                   branch :: Branch Qstate Id
                   branch _ _ = Id ()

queensIO n = do qheader "queensIO" n
                solutions <- runLT $ qloop branch $ qfirst n
                return (length solutions,solutions)
             where branch :: Branch Qstate IO
                   branch st sts = appendFile "queensIO" $ showTransR st sts
                   
queensS n  = do qheader "queensS" n
                appendFile "queensS" transitions
                return (length solutions,solutions)
             where (transitions,solutions) = runLT $ qloop branch $ qfirst n
                   branch :: Branch Qstate ((,) String)
                   branch st sts = (showTransR st sts,())
                        
queensW :: Int -> IO (Int,Int,[[Int]])

queensW n  = do qheader "queensW" n
                appendFile "queensW" $ concatTrans transitions
                return (length solutions,length transitions,solutions) 
             where (transitions,solutions) = runLT $ qloop branch $ qfirst n
                   branch :: Branch Qstate ((,) [Qtrans])
                   branch st sts = ([(st,sts)],())

-- MUTUAL EXCLUSION

-- 2 processes yield 9 states
-- 3 processes yield 31 states
-- 4 processes yield 129 states
-- 5 processes yield 651 states
-- 6 processes yield 3913 states
-- 7 processes yield 27399 states

type Mstate   = ([Int],[Int],[Int]) 
type Mtrans   = (Mstate,[Mstate])

mfirst :: Int -> Mstate           
mfirst n = ([1..n],[],[])         

msuccessors :: Mstate -> [Mstate]
msuccessors (is,ws,cs) = concat [do i <- is
                                    [(remove i is,i:ws,cs)],
                                 do nonempty ws
                                    guard $ null cs
                                    [(is,init ws,[last ws])],
                                 do nonempty cs
                                    [(insertSet (head cs) is,ws,[])]]
                      
mloop :: Monad m => Branch Mstate m -> [Mstate] -> [Mstate] -> m [Mstate]
mloop branch old (st:new) = do branch st sts
                               mloop branch old' new' 
                            where sts = msuccessors st
                                  old' = st:old
                                  new' = union new $ diff sts old'
mloop _ old _ = return old

mheader file n = writeFile file $ "axioms:\nstates == " ++ show [mfirst n]

mutexIO,mutexS,mutexW,mutexR,mutexD,mutexN :: Int -> IO Int

mutexIO n = do mheader "mutexIO" n
               states <- mloop branch [] [mfirst n]
               return $ length states
            where branch :: Branch Mstate IO
                  branch st sts = appendFile "mutexIO" $ showTransR st sts

{- ghci execution times: mutexIO 5: 0.16 secs
                         mutexIO 6: 2.89 secs
                         mutexIO 7: 292.68 secs -}

-- mutexS computes the set of state transitions as an element of the monoid
-- [String] and the set of states as output of the writer monad 
-- ([String],[Mstate]).

mutexS n  = do mheader "mutexS" n
               appendFile "mutexS" transitions
               return $ length states
            where (transitions,states) = mloop branch [] [mfirst n]
                  branch :: Branch Mstate ((,) String)
                  branch st sts = (showTransR st sts,())
                                                
-- mutexW computes the set of state transitions as element of the monoid
-- [Mtrans] and the set of states as output of the writer monad 
-- ([Mtrans],[Mstate]).

mutexW n  = do mheader "mutexW" n 
               appendFile "mutexW" $ concatTrans transitions
               return $ length states
            where (transitions,states) = mloop branch [] [mfirst n]
                  branch :: Branch Mstate ((,) [Mtrans])
                  branch st sts = ([(st,sts)],())
                                                
-- mutexR computes the sets of transitions as an element of the monoid 
-- Rel Mstate and the set of states as output of the writer monad 
-- (Rel Mstate,[Mstate]).                                       -- slow 

mutexR n  = do mheader "mutexR" n 
               appendFile "mutexR" $ concatTrans transitions
               return $ length states
            where (Rel transitions,states) = mloop branch [] [mfirst n]
                  branch :: Branch Mstate ((,) (Rel Mstate))
                  branch st sts = (Rel [(st,sts)],())

type RelD a = DMS.Map a [a]

-- mutexD computes the sets of transitions as an element of the monoid 
-- RelD Mstate and the set of states as output of the writer monad 
-- (RelD Mstate,[Mstate]).                                      -- fast

mutexD n  = do mheader "mutexD" n 
               appendFile "mutexD" $ concatTrans transitionsL
               return $ length states
            where (transitions,states) = mloop branch [] [mfirst n]
                  transitionsL = DMS.toList transitions
                  branch :: Branch Mstate ((,) (DMS.Map Mstate [Mstate]))
                  branch st sts = (DMS.singleton st sts,())
                                                
-- mutexN works as mutexD. In addition, states in transitions are replaced
-- by their respective positions in the list of all states returned by mloop.

mutexN n  = do mheader "mutexN" n 
               appendFile "mutexN" $ concatMap (showTransRN states) transitionsL
               return $ length states
            where (transitions,states) = mloop branch [] [mfirst n]
                  transitionsL = DMS.toList transitions
                  branch :: Branch Mstate ((,) (DMS.Map Mstate [Mstate]))
                  branch st sts = (DMS.singleton st sts,())

-- mloopN works as mloop, but hands over states to branch in terms of their
-- respective positions in the list old'++new' of all states:

mloopN :: Monad m => Branch Int m -> [Mstate] -> [Mstate] -> m [Mstate]
mloopN branch old (st:new) = do branch i is 
                                mloopN branch old' new'
                             where old' = old ++ [st]
                                   new' = new `union` diff sts old'
                                   sts = msuccessors st
                                   i:is = map (position $ old'++new') $ st:sts
mloopN _ old _             = return old
                                                
-- mutexN2 works as mutexD. In addition, in every iteration of mloopN, 
-- states in transitions are represented by their respective positions in the 
-- list of all states built up stepwise by mloopN.

mutexN2 :: Int -> IO Int

mutexN2 n = do mheader "mutexN2" n 
               appendFile "mutexN2" $ concatTrans transitionsL
               return $ length states
            where (transitions,states) = mloopN branch [] [mfirst n]
                  transitionsL = DMS.toList transitions
                  branch :: Branch Int ((,) (DMS.Map Int [Int]))
                  branch st sts = (DMS.singleton st sts,())

-- DISSECTIONS

-- dissections (partitions of a rectangle into rectangles)

hori,vert,square :: Rectangle -> Bool
hori (x,y,x',y')   = x'-x >= y'-y
vert (x,y,x',y')   = x'-x <= y'-y
square (x,y,x',y') = x'-x == y'-y

prop :: Int -> Rectangle -> Bool
prop p (x,y,x',y') = b == p*h || h == p*b where b = x'-x; h = y'-y

area,width',height' :: [Int] -> Rectangle -> Bool
area s (x,y,x',y')    = (x'-x)*(y'-y) `elem` s
width' s (x,y,x',y')  = x'-x `elem` s
height' s (x,y,x',y') = y'-y `elem` s

dsize,bricksh,bricksv :: Int -> Rects -> Bool
dsize n dissect   = length dissect == n
bricksh h dissect = null $ do rect@(x,_,_,y) <- dissect
                              guard $ x > 0 && y < h
                              let f (x',y',_,_) = x == x' && y == y'
                              guard $ any f $ DL.delete rect dissect
bricksv b dissect = null $ do rect@(_,y,x,_) <- dissect
                              guard $ y > 0 && x < b
                              let f (x',y',_,_) = x == x' && y == y'
                              guard $ any f $ DL.delete rect dissect
                                      
showDis :: Int -> RGB -> Rects -> String
showDis mode color rects = "turt[" ++ init (concat $ zipWith f rects [1..n]) 
                                   ++ "]" 
        where n = length rects
              m = 3*n
              f (x,y,x',y') i = if mode `elem` [0,1,4,5] 
                                then string n i rect
                                else string m (3*i) tria1 ++
                                     string m (3*i+1) tria2 ++
                                     string m (3*i+2) tria3 ++
                                     string m (3*i+3) tria4
                          where [x1,y1,x2,y2] = map (*30) [x,y,x',y']
                                rect@[ul,ur,lr,ll] = 
                                    map float2 [(x1,y1),(x2,y1),(x2,y2),(x1,y2)]
                                mid = (float (x1+x2)/2,float (y1+y2)/2)
                                tria1 = [ul,ur,mid]
                                tria2 = [ur,lr,mid]
                                tria3 = [lr,ll,mid]
                                tria4 = [ul,ll,mid]
              string n i path = '\n':"shine(11)$" ++ show (hue 1 color n i) ++ 
                                fillmode ++ init (tail $ show path) ++ "],"
              fillmode = if even mode then "$pathF[" else "$pathSF["
                   
showDiss :: Int -> [Rects] -> String
showDiss _ []      = "[]"
showDiss mode sols = '[':init (init $ concat $ zipWith f sols [1..n]) ++ "]\n"
                     where f rects i = showDis mode color rects ++ ",\n"
                                       where color = if mode < 4 then red 
                                                     else hue 2 red n i
                           n = length sols

type Rectangle = (Int,Int,Int,Int)
type Rects     = [Rectangle]
type Dstate    = (Rects,Rects,Rects)
type Dstates   = [Dstate]
type Dtrans    = (Dstate,Dstates)
type Dparams   = (Rectangle -> Bool,Int,Rects -> Bool,Bool,Int,Int) 

dsuccessors :: (Rectangle -> Bool) -> Int -> Dstate -> Dstates
dsuccessors c bound ((0,0,x2,y2):top,left,inner) =
              concat [-- split vertically:
                      do guard $ lg < bound && x2 > 1
                         x1 <- [1..x2-1]
                         [((0,0,x1,y2):(x1,0,x2,y2):top,left,inner)],
                      -- split horizontally:
                      do guard $ lg < bound && y2 > 1
                         y1 <- [1..y2-1]
                         [((0,0,x2,y1):top,(0,y1,x2,y2):left,inner)],
                      -- join horizontally:
                      do nonempty top
                         let (x1,0,x3,y3):top1 = top
                             new = (x1,y2,x3,y3)
                         guard $ x1 == x2 && y3 > y2 && c new
                         [((0,0,x3,y2):top1,left,new:inner)],
                      -- join vertically:
                      do nonempty left
                         let (0,y1,x3,y3):left1 = left   
                             new = (x2,y1,x3,y3)
                         guard $ y1 == y2 && x3 > x2 && c new
                         [((0,0,x2,y3):top,left1,new:inner)]]
              where lg = length top+length left+length inner+1

dsuccessorsDL :: (Rectangle -> Bool) -> Int -> Dstate -> Dstates    -- not used
dsuccessorsDL c bound ((0,0,x2,y2):top,left,inner) =
              concat [-- split vertically:
                      do guard $ lg < bound && x2 > 1
                         x1 <- [1..x2-1]
                         [(DL.insert (0,0,x1,y2) $ DL.insert (x1,0,x2,y2) top,
                           left,inner)],
                      -- split horizontally:
                      do guard $ lg < bound && y2 > 1
                         y1 <- [1..y2-1]
                         [(DL.insert (0,0,x2,y1) top,
                           DL.insert (0,y1,x2,y2) left,inner)],
                      -- join horizontally:
                      do nonempty top
                         let (x1,0,x3,y3):top1 = top
                             new = (x1,y2,x3,y3)
                         guard $ x1 == x2 && y3 > y2 && c new
                         [(DL.insert (0,0,x3,y2) top1,left,
                           DL.insert new inner)],
                      -- join vertically:
                      do nonempty left
                         let (0,y1,x3,y3):left1 = left   
                             new = (x2,y1,x3,y3)
                         guard $ y1 == y2 && x3 > x2 && c new
                         [(DL.insert (0,0,x2,y3) top,left1,
                           DL.insert new inner)]]
              where lg = (sum $ map length [top,left,inner])+1

dauto0 :: Dparams -> [Rects]
dauto0 (c,bound,c',tree,l,h) = if tree then dloop first else dloopG [] [first]
              where first :: Dstate
                    first = ([(0,0,l,h)],[],[])
                    out st = do guard $ all c topleft && c' dissect
                                return dissect
                             where (top,left,inner) = st
                                   topleft = top++left
                                   dissect = DL.sort $ topleft++inner
                    dloop st = msum $ out st:map dloop sts
                               where sts = dsuccessors c bound st
                    dloopG old (st:new) = msum [out st,dloopG old' new']
                                          where sts = dsuccessors c bound st
                                                old' = st:old
                                                new' = union new $ diff sts old'
                    dloopG _ _          = mzero

dauto :: Monad m => Dparams -> Branch Dstate m -> ListT m Rects
dauto (c,bound,c',tree,l,h) branch = if tree then dloop first 
                                             else dloopG [] [first]
              where first :: Dstate
                    first = ([(0,0,l,h)],[],[])
                    out st = do guard $ all c topleft && c' dissect
                                return dissect
                             where (top,left,inner) = st
                                   topleft = top++left
                                   dissect = DL.sort $ topleft++inner
                    dloop st = msum [out st,
                                     do lift $ branch st sts
                                        msum $ map dloop sts]
                               where sts = dsuccessors c bound st
                    dloopG old (st:new) = msum [out st,
                                                do lift $ branch st sts
                                                   dloopG old' new']
                                          where sts = dsuccessors c bound st
                                                old' = st:old
                                                new' = union new $ diff sts old'
                    dloopG _ _          = mzero

dheader :: String -> Int -> Int -> IO ()
dheader file l h = writeFile file $ "axioms:\nstates == " ++ 
                                    show [([(0,0,l,h)],[]::Rects,[]::Rects)]

dissects0,dissects,dissectsS,dissectsIO,dissectsW :: Dparams -> IO Int

dissects0 ps = do writeFile "disSols" $ showDiss 0 sols   -- 0..7 (see showDiss)
                  return $ length sols
               where solutions = dauto0 ps
                     sols = union [] solutions

dissects ps = do writeFile "disSols" $ showDiss 6 sols
                 return $ length sols
              where Id solutions = runLT $ dauto ps branch
                    sols = union [] solutions
                    branch :: Branch Dstate Id
                    branch _ _ = Id ()

dissectsS ps = do writeFile "disSols" $ showDiss 1 $ toList $ DS.map toList sols
                  return $ DS.size sols
               where Id solutions = runLT $ dauto ps branch
                     sols = fromList $ map fromList solutions
                     branch :: Branch Dstate Id
                     branch _ _ = Id ()

dissectsIO ps@(_,_,_,_,l,h) = do dheader "dissectsIO" l h
                                 solutions <- runLT $ dauto ps branch
                                 let sols = union [] solutions
                                 writeFile "disSols" $ showDiss 1 sols
                                 return $ length sols
             where branch :: Branch Dstate IO
                   branch st sts = appendFile "dissectsIO" $ showTransR st sts
                   
dissectsW ps@(_,_,_,_,l,h) = do dheader "dissectsW" l h
                                appendFile "dissectsW" $ concatTrans transitions
                                writeFile "disSols" $ showDiss 1 sols
                                return $ length sols
                where (transitions,solutions) = runLT $ dauto ps branch
                      sols = unionBag [] solutions
                      branch :: Branch Dstate ((,) [Dtrans])
                      branch st sts = ([(st,sts)],())
                      -- tras1 = foldl insertBagR [] $ map f transitions -- slow
                      -- f (x,s) = (g x,map g s)
                      -- g (x,y,z) = x++y++z
                      -- tras2 = foldl insertBagR3 [] transitions        -- slow

distest1 = dissects (const True,6,const True,True,2,3)          -- 34 solutions
                                                                -- 0.02 secs
distest2 = dissects (const True,9,const True,True,3,3)          -- 322 solutions
                                                                -- 0.02 secs
distest3 = dissects (area [1,2],9,const True,True,3,3)          -- 131 solutions
                                                                -- 0.13 secs
distest4 = dissects (area [1,2] &&& hori,9,const True,True,3,3) -- 27 solutions
                                                                -- 0.03 secs
distest5 = dissects (const True,12,const True,True,4,3)        -- 3164 solutions
                                                               -- 11.71 secs
distest6 = dissects (const True,16,const True,True,4,4)         -- ? solutions
                                                                -- ? secs
distest7 = dissects (area [2],8,const True,True,4,4)            -- 36 solutions
                                                                -- 0.16 secs
distest8 = dissects (area [1,2] &&& hori,12,bricksh 4,True,5,4) -- 2 solutions
                                                                -- 18.95 secs
distest9 = dissects (area [1,2] &&& vert,12,bricksv 4,True,4,5) -- 2 solutions
                                                                -- 18.83 secs
distest10 = dissects (prop 2,6,dsize 6,True,3,6)                -- 14 solutions
                                                                -- 0.05 secs
distest11 = dissects (prop 2,6,dsize 6,True,4,6)                -- 67 solutions
                                                                -- 0.14 secs
distest12 = dissects (area [4],6,dsize 6,True,6,4)              -- 35 solutions
                                                                -- 0.08 secs
distest13 = dissects (area [4],6,dsize 6,False,6,4)             -- 35 solutions
                                                                -- 0.55 secs
distest14 = dissects (area [1,2] &&& hori,14,bricksh 4,True,6,4) -- 2 solutions
                                                                -- 331.48 secs
distest15 = dissects (prop 2,6,dsize 6,True,5,5)                -- 0 solutions
                                                                -- 0.14 secs
distest16 = dissects (prop 2,6,dsize 6,True,5,6)                -- 20 solutions
                                                                -- 0.20 secs
distest17 = dissects (prop 2,6,dsize 6,False,5,6)               -- 20 solutions
                                                                -- 6.46 secs
distest18 = dissects (prop 2,6,dsize 6,True,6,6)                -- 48 solutions
                                                                -- 0.37 secs
distest19 = dissects (prop 2,6,dsize 6,False,6,6)               -- 48 solutions
                                                                -- 19.52 secs
                                                                
-- PYTHAGOREAN TRIPLES

pyTriples = [(a,b,c) | c <- [2..], b <- [2..c-1], a <- [2..b-1], a*a+b*b == c*c]

pyt = take 222 pyTriples
                  
-- CRYPTOGRAMS

-- character codes satisfying send+more=money resp. eins+neun=zehn

getIndex :: Eq a => [a] -> a -> Int
getIndex s a = fromJust $ lookup a $ zip s [0..]

codes1,codes1M :: [[(Char,Int)]]                          
codes1 = [zip code [0..] | code <- perms "sendmory01", check code]

check code = -- m == 1 && s > 0 && 
             1000*(s+m)+100*(e+o)+10*(n+r)+d+e == 10000*m+1000*o+100*n+10*e+y
             where [s,e,n,d,m,o,r,y] = map (getIndex code) "sendmory"
             
codes1M = do code <- perms "sendmory01"
             guard $ check code
             [zip code [0..]]
              
-- take 2 codes1 --> [[('o',0),('m',1),('y',2),('1',3),('0',4),('e',5),('n',6),
--                     ('d',7),('r',8),('s',9)],
--                    [('o',0),('m',1),('y',2),('0',3),('1',4),('e',5),('n',6),
--                     ('d',7),('r',8),('s',9)]]

codes2 :: [[(Char,Int)]]                          
codes2 = do code <- perms "einsuzh012"
            guard $ check code
            [zip code [0..]]
         where check code = 1000*(e+n)+100*(i+e)+10*(n+u)+s+n == 
                            1000*z+100*e+10*h+n
                           where [e,i,n,s,u,z,h] = map (getIndex code) "einsuzh"
                           
-- head codes2 --> [('s',0),('e',1),('2',2),('h',3),('1',4),('n',5),('0',6),
--                  ('z',7),('u',8),('i',9)]

-- old attempt of solving send+more=money

addO = [o:st | o <- vals, st <- addR, o `notElem` st, relO(st)(o)]
addR = [r:st | r <- vals, st <- addN, r `notElem` st, relR(st)(r)]
addN = [n:st | n <- vals, st <- addY, n `notElem` st]
addY = [y:st | y <- vals, st <- addE, y `notElem` st, relY(st)(y)]
addE = [[e,d] | e <- vals, d <- vals, d /= e]

vals = 0:[2..8]

relY[e,d](y)       = (d+e)`mod`10 == y
relR[n,y,e,d](r)   = ((n+r)*10+d+e)`mod`100 == e*10+y
relO[r,n,y,e,d](o) = eqHolds[o,r,n,y,e,d]

eqHolds [o,r,n,y,e,d] = (e+o)*100+(n+r)*10+d+e == o*1000+n*100+e*10+y

-- addO = [[0,8,6,2,5,7]] = [[o,r,n,y,e,d]] 
-- m = 1 and s = 9 follow from s+m > 9.

-- ZEBRA PROBLEM 

{- https://en.wikipedia.org/wiki/Zebra_Puzzle
-- https://de.wikipedia.org/wiki/Zebrarätsel
-- https://de.wikibooks.org/wiki/Algorithmensammlung:_Spezielle_Probleme:_Das_
-- Zebrarätsel
-- https://www.logisch-gedacht.de/logikraetsel/einsteinraetsel/loesung

 1. The Englishman lives in the red house.                                      
 2. The Spaniard owns the dog.
 3. Coffee is drunk in the green house.
 4. The Ukrainian drinks tea.
 5. The green house is immediately to the right of the white house.
 6. The Old Gold smoker owns snails.
 7. Kools are smoked in the yellow house.
 8. Milk is drunk in the middle house.
 9. The Norwegian lives in the first house.
10. The man who smokes Chesterfields lives in the house next to the man with the 
    fox.
11. Kools are smoked in the house next to the house where the horse is kept.
12. The Lucky Strike smoker drinks orange juice.
13. The Japanese smokes Dunhill.
14. The Norwegian lives next to the blue house.

The following solution algorithm is based on 
https://rosettacode.org/wiki/Zebra_puzzle#LP-like_version
-}

firstHouse,middleHouse :: Eq a => a -> [a] -> Bool
firstHouse  x xs = head xs == x
middleHouse x xs = xs!!2 == x

sameHouse,rightHouse,nextHouse :: Eq a => a -> [a] -> a -> [a] -> Bool
sameHouse  x xs y ys = (x,y) `elem` zip xs ys
rightHouse x xs y ys = sameHouse x (tail xs) y ys 
nextHouse  x xs y ys = rightHouse x xs y ys || rightHouse y ys x xs

cond1  color nation = sameHouse   "Red      " color  "British  " nation 
cond2  nation pet   = sameHouse   "Spaniard " nation "Dog      " pet 
cond3  color drink  = sameHouse   "Green    " color  "Coffee   " drink          
cond4  nation drink = sameHouse   "Ukrainian" nation "Tea      " drink                  
cond5  color        = rightHouse  "Green    " color  "White    " color          
cond6  smoke pet    = sameHouse   "Gold     " smoke  "Snails   " pet            
cond7  color smoke  = sameHouse   "Yellow   " color  "Kools    " smoke          
cond8  drink        = middleHouse "Milk     " drink             
cond9  nation       = firstHouse  "Norwegian" nation            
cond10 smoke pet    = nextHouse   "Chester  " smoke  "Fox      " pet    
cond11 smoke pet    = nextHouse   "Kools    " smoke  "Horse    " pet    
cond12 drink smoke  = sameHouse   "Juice    " drink  "Lucky    " smoke  
cond13 nation smoke = sameHouse   "Japanese " nation "Dunhill  " smoke  
cond14 color nation = nextHouse   "Blue     " color  "Norwegian" nation 

colors  = ["Red      ","Green    ","White    ","Yellow   ","Blue     "]
nations = ["British  ","Spaniard ","Ukrainian","Japanese ","Norwegian"]
drinks  = ["Coffee   ","Tea      ","Milk     ","Juice    ","Water    "]
smokes  = ["Gold     ","Chester  ","Kools    ","Lucky    ","Dunhill  "]
pets    = ["Dog      ","Snails   ","Fox      ","Horse    ","Zebra    "]
             
{- logic program

solution color nation drink smoke pet
          <== perm colors color /\ cond5 color /\ perm nations nation & ... -}

solutions = [[color,nation,drink,smoke,pet] |
             color <- perms colors, 
             cond5 color, 
             nation <- perms nations, 
             cond1 color nation && cond9 nation && cond14 color nation,
             drink <- perms drinks, 
             cond3 color drink && cond8 drink && cond4 nation drink,
             smoke <- perms smokes, 
             cond7 color smoke && cond12 drink smoke && cond13 nation smoke,
             pet <- perms pets, 
             cond2 nation pet && cond6 smoke pet && cond10 smoke pet && 
             cond11 smoke pet]
             
solutionsM = do color <- perms colors
                guard $ cond5 color
                nation <- perms nations
                guard $ cond1 color nation && cond9 nation && 
                        cond14 color nation
                drink <- perms drinks
                guard $ cond3 color drink && cond8 drink && cond4 nation drink
                smoke <- perms smokes
                guard $ cond7 color smoke && cond12 drink smoke && 
                        cond13 nation smoke
                pet <- perms pets
                guard $ cond2 nation pet && cond6 smoke pet && 
                        cond10 smoke pet && cond11 smoke pet 
                return [color,nation,drink,smoke,pet]

showMat houses =
        putStrLn $ "house  | 1         2         3         4         5    \n" ++
                   "color  | "++ unwords (houses!!0) ++ "\n" ++
                   "nation | "++ unwords (houses!!1) ++ "\n" ++
                   "drink  | "++ unwords (houses!!2) ++ "\n" ++
                   "smoke  | "++ unwords (houses!!3) ++ "\n" ++
                   "pet    | "++ unwords (houses!!4) 
                         
printMats = mapM_ showMat solutions

{-
house  | 1         2         3         4         5    
color  | Yellow    Blue      Red       White     Green      
nation | Norwegian Ukrainian British   Spaniard  Japanese 
drink  | Water     Tea       Milk      Juice     Coffee   
smoke  | Kools     Chester   Gold      Lucky     Dunhill     
pet    | Fox       Horse     Snails    Dog       Zebra
-}

showRel houses = filter (`notElem` "\" ") $ show $ concatMap f [0..4] where
                 f i = map (g i) [1..5] where
                       g i j = (rows!!i,j,houses!!i!!(j-1))
                       rows = words "color nation drink smoke pet"

{- map showRel solutions -->
   ["[(color,1,Yellow),(color,2,Blue),(color,3,Red),(color,4,White),
      (color,5,Green),(nation,1,Norwegian),(nation,2,Ukrainian),
      (nation,3,British),(nation,4,Spaniard),(nation,5,Japanese),
      (drink,1,Water),(drink,2,Tea),(drink,3,Milk),(drink,4,Juice),
      (drink,5,Coffee),(smoke,1,Kools),(smoke,2,Chester),(smoke,3,Gold),
      (smoke,4,Lucky),(smoke,5,Dunhill),(pet,1,Fox),(pet,2,Horse),
      (pet,3,Snails),(pet,4,Dog),(pet,5,Zebra)]"] -}
      
printSols = writeFile "zebrasol" $ filter (/= '\"') $ show 
                                 $ map showRel solutions 

-- discarded attempts

zebraProd :: [[[Int]]]
zebraProd = [[colors,nations,drinks,smokes,pets] | colors <- ps, nations <- ps, 
                                        drinks <- ps, smokes <- ps, pets <- ps]
            where ps = permutations [1..5]

zebraSolsP :: [[Int]]
zebraSolsP = head $ filter zebraCond zebraProd

fivePerms :: Eq a => [[a]] -> [[[a]]]
fivePerms s = g s empty where 
              g s s' = if s == empty then [s']                
                       else do ks <- sequence s 
                               g (zipWith remove ks s) $ zipWith (:) ks s'
              empty = [[],[],[],[],[]]

zebraSolsF :: [[Int]]
zebraSolsF = head $ filter zebraCond $ fivePerms $ replicate 5 [1..5]
             
zebraCond :: [[Int]] -> Bool
zebraCond [colors,nations,drinks,smokes,pets] = all c [1..14]
    where c 1  = nations!!0 == 5 
          c 2  = colors!!1 == 5                  --  2 <==> 1/\3/\15
          c 3  = drinks!!2 == 3
          c 4  = any c [2,3,4]   where c i = colors!!i == 1 && nations!!i == 1
          c 5  = any c [1..4]    where c i = nations!!i == 2 && pets!!i == 1
          c 6  = any c [0,3,4]   where c i = colors!!i == 2 && drinks!!i == 1
          c 7  = any c [1,3,4]   where c i = nations!!i == 3 && drinks!!i == 2
          c 8  = any c [0..4]    where c i = smokes!!i == 1 && pets!!i == 2
          c 9  = any c [0,2,3,4] where c i = colors!!i == 4 && smokes!!i == 3
          c 10 = any c [0,1,3,4] where c i = drinks!!i == 4 && smokes!!i == 4
          c 11 = any c [1..4]    where c i = nations!!i == 4 && smokes!!i == 5
          c 12 = c 2 || c 3     where c i = colors!!i == 3 && colors!!(i+1) == 2
          c 13 = any (c 1) [0..3] || any (c (-1)) [1..4]
                                where c k i = smokes!!i == 2 && pets!!(i+k) == 3
          c 14 = any (c 1) [0..3] || any (c (-1)) [1..4]
                                where c k i = smokes!!i == 3 && pets!!(i+k) == 4
          c 15 = any (c 1) [0..3] || any (c (-1)) [1..4]
                                where c k i = colors!!i == 5 && 
                                              nations!!(i+k) == 5
                                              
zebraSolsI = head $ foldl (flip filter) (fivePerms $ replicate 5 [1..5])
                  $ map c $ [1..4]++[7..14] -- ++[5,6]          
    where c 1  [_,nations,_,_,_]      = nations!!0 == 5
          c 2  [colors,_,d_,_,_]      = colors!!1 == 5    --  2 <==> 1/\3/\15
          c 3  [_,_,drinks,_,_]       = drinks!!2 == 3
          c 4  [colors,nations,_,_,_] = any c [2,3,4] 
               where c i = colors!!i == 1 && nations!!i == 1
          c 5  [_,nations,_,_,pets]   = any c [1..4]
               where c i = nations!!i == 2 && pets!!i == 1
          c 6  [colors,_,drinks,_,_]  = any c [0,3,4]
               where c i = colors!!i == 2 && drinks!!i == 1
          c 7  [_,nations,drinks,_,_] = any c [1,3,4]
               where c i = nations!!i == 3 && drinks!!i == 2
          c 8  [_,_,_,smokes,pets]    = any c [0..4]
               where c i = smokes!!i == 1 && pets!!i == 2
          c 9  [colors,_,_,smokes,_]  = any c [0,2,3,4]
               where c i = colors!!i == 4 && smokes!!i == 3
          c 10 [_,_,drinks,smokes,_]  = any c [0,1,3,4]
               where c i = drinks!!i == 4 && smokes!!i == 4
          c 11 [_,nations,_,smokes,_] = any c [1..4]
               where c i = nations!!i == 4 && smokes!!i == 5
          c 12 [colors,_,_,_,_]       = c 2 || c 3 
               where c i = colors!!i == 3 && colors!!(i+1) == 2
          c 13 [_,_,_,smokes,pets]    = any (c 1) [0..3] || any (c (-1)) [1..4]
               where c k i = smokes!!i == 2 && pets!!(i+k) == 3
          c 14 [_,_,_,smokes,pets]    = any (c 1) [0..3] || any (c (-1)) [1..4]
               where c k i = smokes!!i == 3 && pets!!(i+k) == 4
          c 15 [colors,nations,_,_,_] = any (c 1) [0..3] || any (c (-1)) [1..4]
               where c k i = colors!!i == 5 && nations!!(i+k) == 5
               
data FF = One | Two | Three | Four | Five deriving (Eq,Show,Enum)       

zebraSolsD :: [[FF]]
zebraSolsD = head $ filter zebraCondD $ fivePerms $ replicate 5 [One ..Five]
             
zebraCondD :: [[FF]] -> Bool
zebraCondD [colors,nations,drinks,smokes,pets] = c1_1 && c1_2 && c1_3 &&
           any c2 [2,3,4] && any c3 [1..4] && any c4 [0,3,4] && 
           any c5 [1,3,4] && any c6 [0..4] && any c7 [0,2,3,4] && 
           any c8 [0,1,3,4] && any c9 [1..4] && any c10 [2,3] && 
           (any (c11 1) [0..3] || any (c11 (-1)) [1..4]) &&
           (any (c12 1) [0..3] || any (c12 (-1)) [1..4]) 
     where c1_1 = nations!!0 == Five 
           c1_2 = colors!!1 == Five             -- follows from c13
           c1_3 = drinks!!2 == Three
           c2 i = colors!!i == One && nations!!i == One
           c3 i = nations!!i == Two && pets!!i == One
           c4 i = colors!!i == Two && drinks!!i == One
           c5 i = nations!!i == Three && drinks!!i == Two
           c6 i = smokes!!i == One && pets!!i == Two
           c7 i = colors!!i == Four && smokes!!i == Three
           c8 i = drinks!!i == Four && smokes!!i == Four
           c9 i = nations!!i == Four && smokes!!i == Five
           c10 i = colors!!i == Three && colors!!(i+1) == Two
           c11 k i = smokes!!i == Two && pets!!(i+k) == Three
           c12 k i = smokes!!i == Three && pets!!(i+k) == Four
           c13 k i = colors!!i == Five && nations!!(i+k) == Five

-- SUDOKUS

-- sudoku a values checks whether the 9*9 array a with given values is a sudoku.

sudoku :: Array (Int,Int) Int -> [((Int,Int),Int)] -> Bool
sudoku a values = all sat values &&
                  all isPerm (map (map (a!)) $ rows++columns++squares) where
                  sat (p,v) = a!p == v
                  rows    = map row [1..9] where row i = [(i,j) | j <- [1..9]]
                  columns = map col [1..9] where col j = [(i,j) | i <- [1..9]]
                  squares = map square [(i,j) | i <- [2,5,8], j <- [2,5,8]]
                            where square (i,j) = [(i+k,j+m) | k <- [-1,0,1], 
                                                              m <- [-1,0,1]]
                  isPerm s = and $ map (== 1) $ map (card s) [1..9]

-- CYCLES

-- cycles s computes a sequence of two-cycles that leads from [indices s] to
-- permutation s.

cycles :: Ord a => [a] -> ([a],[(a,a)])
cycles (x:s) = insert x s' cs
             where (s',cs) = cycles s
                   insert x s@(y:xs) cs = if x <= y then (x:s,cs) else (y:ys,ds)
                              where (ys,ds) = insert x xs ((min x y,max x y):cs)
                   insert x _ cs        = ([x],cs)
cycles s = (s,[])

-- cycles perm1 = [(2,1),(2,0),(4,3),(4,1),(4,0),(7,6),(7,5),(6,5)]

s1@(_:_) -+- s2@(y:s) = if last s1 == y then init s1 -+- s else s1++s2
s1 -+- s2             = s1++s2

-- cycleDiff s1 s2 computes a sequence of two-cycles that leads from permutation
-- s1 to permutation s2. 

cycleDiff :: Ord a => [a] -> [a] -> [(a,a)]
cycleDiff s1 s2 = snd (cycles s2) -+- reverse (snd (cycles s1))

-- acyclic xs ts checks whether the relation that consists of all pairs (y,z) of 
-- r (see below) such that y is r-reachable from some x in xs is acyclic (see 
-- the pathsort program in Paulson, ML for the Working Programmer, p. 106).

acyclic xs ts = case f xs [] [] of Just _ -> True; _ -> False
         where f (x:xs) path zs = do guard $ x `notElem` path
                                     if x `elem` zs then f xs path zs
                                        else do zs <- f [z | (y,z) <- r, x == y]
                                                        (x:path) (x:zs) 
                                                f xs path zs
               f _ _ zs         = Just zs
               r = [(xs!!i,x) | i <- indices ts, x <- vars $ ts!!i]

-- cycles' r x returns all elements that are r-reachable from x and belong to a 
-- cycle. 

cycles' r x = f [] [] x where                                        
              f path zs x | x `elem` path = path
                          | x `elem` zs   = []
                          | True          = unionMap (f (x:path) (x:zs)) 
                                                     [z | (y,z) <- r, x == y]
                  
-- REDUCTIONS 

type Rules a = Tree a -> Maybe (Tree a)

reduction :: Eq a => Rules a -> Rules a -> Tree a -> [Tree a]
reduction rules1 rules2 t = init red ++ iteration (redStep rules2) (last red)
                            where red = iteration (redStep rules1) t

iteration :: Eq a => (a -> Maybe a) -> a -> [a]
iteration f a = case f a of Just a' | a /= a' -> a:iteration f a'
                            _ -> [a]

redStep :: Rules a -> Tree a -> Maybe (Tree a)
redStep rules = f where f t = msum [rules t,
                                    do F a ts <- Just t
                                       ts <- g ts; Just $ F a ts]
                        g ts = do t:ts <- Just ts
                                  case f t of Just t -> Just $ t:ts
                                              _ -> do ts <- g ts; Just $ t:ts
                                                        
-- GRAPHS

type Graph2 = ([(Pos,Pos)],Int,Int,Pos -> Int)

fun2Graph :: [[Int]] -> Graph2
fun2Graph s = (edges,2,maximum ((length s-1):map maximum s)+1,label) 
              where edges = concat $ zipWith f [0..] s
                            where f i s = map g s where g k = ((1,i+1),(2,k+1))
                    label (_,i) = i-1

graph7,graph8 :: Graph2
graph7 = ([((1,1),(4,6)),((5,5),(3,2)),((4,4),(2,1))],5,6,\(x,y)->x*6-6+y)
graph8 = fun2Graph [[0],[1,2],[0,3,4],[0,2],[3],[2,4]]

s = [([],[]),([],[0]),([],[1]),([],[2]),([],[3]),([],[0,2]),([],[1,3]),
    ([0,1,2,3],[]),([3,2,1,0],[]),([2,3,1,0],[]),([3,1,2,0],[]),([1,3,2,0],[]),
    ([2,1,3,0],[]),([1,2,3,0],[]),([3,2,0,1],[]),([2,3,0,1],[]),([3,0,2,1],[]),
    ([0,3,2,1],[]),([2,0,3,1],[]),([0,2,3,1],[]),([3,1,0,2],[]),([1,3,0,2],[]),
    ([3,0,1,2],[]),([0,3,1,2],[]),([1,0,3,2],[]),([0,1,3,2],[]),([2,1,0,3],[]),
    ([1,2,0,3],[]),([2,0,1,3],[]),([0,2,1,3],[]),([1,0,2,3],[]),
    ([0],[]),([0],[1]),([0],[2]),([0],[3]),([0],[1,3]),
    ([1],[]),([1],[0]),([1],[2]),([1],[3]),([1],[0,2]),
    ([2],[]),([2],[0]),([2],[1]),([2],[3]),([2],[1,3]),
    ([3],[]),([3],[0]),([3],[1]),([3],[2]),([3],[0,2]),
    ([0,1],[]),([0,1],[2]),([0,1],[3]),
    ([1,0],[]),([1,0],[2]),([1,0],[3]),
    ([0,2],[]),([0,2],[1]),([0,2],[3]),([0,2],[1,3]),
    ([2,0],[]),([2,0],[1]),([2,0],[3]),([2,0],[1,3]),
    ([0,3],[]),([0,3],[1]),([0,3],[2]),
    ([3,0],[]),([3,0],[1]),([3,0],[2]),
    ([1,2],[]),([1,2],[0]),([1,2],[3]),
    ([2,1],[]),([2,1],[0]),([2,1],[3]),
    ([1,3],[]),([1,3],[0]),([1,3],[2]),([1,3],[0,2]),
    ([3,1],[]),([3,1],[0]),([3,1],[2]),([3,1],[0,2]),
    ([2,3],[]),([2,3],[0]),([2,3],[1]),
    ([3,2],[]),([3,2],[0]),([3,2],[1]),
    ([0,1,2],[]),([0,1,2],[3]),([2,1,0],[]),([2,1,0],[3]),
    ([1,2,0],[]),([1,2,0],[3]),([2,0,1],[]),([2,0,1],[3]),
    ([0,2,1],[]),([0,2,1],[3]),([1,0,2],[]),([1,0,2],[3]),
    ([0,1,3],[]),([0,1,3],[2]),([3,1,0],[]),([3,1,0],[2]),
    ([1,3,0],[]),([1,3,0],[2]),([3,0,1],[]),([3,0,1],[2]),
    ([0,3,1],[]),([0,3,1],[2]),([1,0,3],[]),([1,0,3],[2]),
    ([0,2,3],[]),([0,2,3],[1]),([3,2,0],[]),([3,2,0],[1]),
    ([2,3,0],[]),([2,3,0],[1]),([3,0,2],[]),([3,0,2],[1]),
    ([0,3,2],[]),([0,3,2],[1]),([2,0,3],[]),([2,0,3],[1]),
    ([1,2,3],[]),([1,2,3],[0]),([3,2,1],[]),([3,2,1],[0]),
    ([2,3,1],[]),([2,3,1],[0]),([3,1,2],[]),([3,1,2],[0]),
    ([1,3,2],[]),([1,3,2],[0]),([2,1,3],[]),([2,1,3],[0])]

-- DRAW COMMANDS

{- knight paths: mutually-recursive version

pathR :: Int -> String -> Int -> Point -> IO ()
pathR mode file n p = case rec (n*n) [p] of 
                           Just ps -> do writeFile file $ show [ps]
                                         drawTrack True file mode
                           _ -> putStrLn "Nothing"
                  where rec :: Int -> Path -> Maybe Path
                        rec 1 ps       = Just $ reverse ps
                        rec k ps@(p:_) = try (k-1) [q:ps | q <- nextPoss n ps p]
                        try :: Int -> [Path] -> Maybe Path
                        try k pss = do ps:pss <- Just pss
                                       rec k ps `mplus` try k pss

realPos (x,y) = (y*50,x*50)

draw :: Window -> Color -> Graphic -> IO ()
draw w color = drawInWindow w . withColor color

drawLn :: Window -> (Pos,Pos) -> IO ()
drawLn w (p,q) = draw w (if p <= q then Red else Magenta) 
                        (line (realPos p) (realPos q))

drawPt :: Window -> (Pos,Int) -> IO ()
drawPt w (p,n) = do draw w Green (ellipse (x+12,y+12) (x-12,y-12))
                    draw w Blue (text (x-7,y-6) (show n))
                 where (x,y) = realPos p

colorBack :: Window -> Color -> IO () 
colorBack w color = do (x,y) <- getWindowSize w
                       draw w White (polygon [(0,0),(0,y),(x,y),(x,0)])

drawGraph :: Graph -> IO ()
drawGraph (edges,m,n,label) = runGraphics $
                              do w <- openWindow "graph" size
                                 colorBack w White
                                 mapM (drawLn w) edges
                                 mapM (drawPt w) (zip nodes (map label nodes)) 
                                 getRBP w
                                 closeWindow w
                              where size = (n*50+50,m*50+50)
                                    nodes = [(x,y) | x <- [1..m], y <- [1..n]]

drawLNodes :: Bool -> RGB -> Path -> [String] -> String
drawLNodes moreCols col ps = concat . f ps
                where f = if moreCols then zipWith2 (drawLNode . g) [indices lg]
                                      else zipWith $ drawLNode $ mkLight col
                      g = mkLight . hue lg col; lg = length ps
-}

