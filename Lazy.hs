{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses,
             RecursiveDo #-}

-- 24.10.2017

module Lazy where

import Control.Monad (msum)

foo1 :: [a1] -> Int
foo1 (x:s) = 1
foo1 _     = undefined
foo2 ~(x:s) = 1

foo3 (x,y)  = 1
foo4 ~(x,y) = 1

foo5 x = 1 where (y,z) = x
foo6 x = let (y,z) = x in 1

foo7 (x:s) = if x > 10 then s else undefined

pair = (8,9)
(x,y) = pair

-- INFINITE OBJECTS

nats n = n:map (+1) (nats n)

fibs = 0:zipWith (+) fibs (1:fibs)
							
-- take 12 fibs   ===>   [0,1,1,2,3,5,8,13,21,34,55,89]

concfibs = 0:concat fibs where fibs = [1]:tailfibs
	                       tailfibs = [0]:zipWith (++) tailfibs fibs
			       
concfibs2 n = fibs n where fibs 0 = [1]
	                   fibs 1 = [0]
			   fibs n = fibs (n-1)++fibs (n-2)
	    {- (fibs,concfibs) = (fibs,concfibs2 infinity)
	       is the unique solution of the equations
	       f (0:s) = 0:1:f s
	       f (1:s) = 1:f s
	       f fib   = fib   (<==> exists gib : fib = 0:gib /\ gib = 1:f(gib))
	       in (fib,f)
	       see: H. Zantema, Well-definedness of streams,...
	            and http://www.win.tue.nl/~hzantema/strfib.html -}

primes :: [Integer]
primes = sieve $ nats 2 

sieve (p:s) = p:sieve [n | n <- s, n `mod` p /= 0]
sieve _     = []

-- take 11 prims   ===>   [2,3,5,7,11,13,17,19,23,29,31]

mirps :: Int -> [Integer]
mirps upb = filter ((`elem` prims) . f) prims 
	    where prims = sieve $ take upb $ nats 2
	          f = read . reverse . show

-- take 999 mirps   
-- ===> [2,3,5,7,11,13,17,31,37,71,73,79,97,101,107,113,131,149,151,157,167,179,
--       181,191,199,311,313,337,347,353,359,373,383,389,701,709,727,733,739,
--	 743,751,757,761,769,787,797,907,919,929,937,941,953,967,971,983,991]

hamming = 1:foldl1 merge (map (\x -> map (*x) hamming) [2,3,5])
          
merge s1@(x:s2) s3@(y:s4) = if x < y then x:merge s2 s3 
			    else if x > y then y:merge s1 s4 else merge s1 s4
merge [] s 		  = s
merge s _  		  = s

-- take 30 hamming   ===>  [1,2,3,4,5,6,8,9,10,12,15,16,18,20,24,25,27,30,32,36,
--                          40,45,48,50,54,60,64,72,75,80]

hamming' = 1:map (*2) hamming`join`map (*3) hamming`join`map (*5) hamming

join s (x:s') = if x `elem` s then join s s' else x:join s s'
join s _      = s

joinMap :: Eq b => (a -> [b]) -> [a] -> [b]
joinMap = (foldl join [] .) . map

-- MERGESORT

mergesort (x:y:s) = merge (mergesort $ x:s1) (mergesort $ y:s2) 
   		    where (s1,s2) = split s
mergesort s      = s
   
split (x:y:s) = (x:s1,y:s2) where (s1,s2) = split s
split s       = (s,[])

mergesortF (x:y:s) = (\(s1,s2) -> merge (mergesortF $ x:s1) (mergesortF $ y:s2))
		     $ splitF s
mergesortF s       = s

splitF (x:y:s) = (\(s1,s2) -> (x:s1,y:s2)) $ splitF s
splitF s       = (s,[])

-- BINARY TREES

data Btree a = L a | Btree a :# Btree a

tree1 = (L 3:#(L 22:#L 4)):#(L 2:#L 11)
tree2 = (L 3:#(L 22:#L 4)):#((L 5:#L 16):#L 11)

instance Show a => Show (Btree a) 
		   where show (L a)    = show a
		   	 show (t1:#t2) = '(':show t1++'#':show t2++")"

depfront :: Ord a => Btree a -> ([a],Int)  -- depfront t x = (front t x,depth t)
depfront (L x)    = ([x],0)
depfront (t1:#t2) = (if x > y then xs else if y > x then ys else xs++ys,
		     max x y+1)
                    where (xs,x) = depfront t1; (ys,y) = depfront t2

-- depfront tree2 ---> ([22,4,5,16],3)
			 			  
replace :: (a -> a -> a) -> Btree a -> Btree a
replace f t = u where (x,u) = foldRepl f t x
-- replace f t = let (x,u) = foldRepl f t x in u

foldRepl :: (a -> a -> a) -> Btree a -> a -> (a,Btree a)
          		          -- foldRepl f t x = (foldT f t,t[x/leaves(t)])
foldRepl _ (L x) y    = (x,L y)
foldRepl f (t1:#t2) x = (f y z,u1:#u2) where (y,u1) = foldRepl f t1 x
			                     (z,u2) = foldRepl f t2 x

-- replace min tree1 ---> ((2#(2#2))#(2#2))
-- replace (+) tree1 ---> ((42#(42#42))#(42#42))
			 			  
replaceM,replaceMS :: (a -> a -> a) -> Btree a -> Maybe (Btree a)
replaceM f t  = do rec (x,u) <- foldReplM f t x
		   Just u
replaceMS f t = do rec (x,u) <- foldReplMS f t x
		   Just u

foldReplM,foldReplMS :: (a -> a -> a) -> Btree a -> a -> Maybe (a,Btree a)
foldReplM _ (L x) y    = Just (x,L y)
foldReplM f (t1:#t2) x = do (y,u1) <- foldReplM f t1 x
			    (z,u2) <- foldReplM f t2 x
			    Just (f y z,u1:#u2) 			                     
foldReplMS f t x = msum [do L y <- Just t
			    Just (y,L x),
			 do t1:#t2 <- Just t
			    (y,u1) <- foldReplMS f t1 x
			    (z,u2) <- foldReplMS f t2 x
			    Just (f y z,u1:#u2)]

-- replaceM min tree1 ---> Just ((2#(2#2))#(2#2))
-- replaceM (+) tree1 ---> Just ((42#(42#42))#(42#42))

-- PALINDROMES

pal,palF,palI :: Eq a => [a] -> Bool       
pal s = b where (r,b) = revEq s r
-- pal s = let (r,b) = revEq s r in b   

revEq :: Eq a => [a] -> [a] -> ([a],Bool)   -- revEq s1 s2 = (reverse s1,s1==s2)
revEq (x:s1) s       = (r++[x],x==y && b) where y:s2 = s; (r,b) = revEq s1 s2
-- revEq (x:s1) ~(y:s2) = (r++[x],x==y && b) where (r,b) = revEq s1 s2
-- revEq (x:s1) (y:s2)  = (r++[x],x==y && b) where (r,b) = revEq s1 s2 
--                        loops if called by pal.
revEq _ _            = ([],True)

-- pal [1,2,3,2,1] ---> True

pal1 = pal $ take 12 (nats 22) ++ reverse (take 12 $ nats 22)
pal2 = pal $ take 12 (nats 22) ++ 111:reverse (take 12 $ nats 22)
pal3 = pal $ take 12 (nats 22) ++ 111:114:reverse (take 12 $ nats 22)

palF s = f r where (r,f) = revEqF s

revEqF :: Eq a => [a] -> ([a],[a] -> Bool)
revEqF (x:s1) = (r++[x],\(y:s2) -> x==y && f s2) where (r,f) = revEqF s1
revEqF _      = ([],const True)

palI s = b where (r,b) = revEqI s r []

revEqI :: Eq a => [a] -> [a] -> [a] -> ([a],Bool)
				  -- revEqI s1 s2 acc = (reverse s1++acc,s1==s2)
revEqI (x:s1) ~(y:s2) acc = (r,x==y && b) where (r,b) = revEqI s1 s2 (x:acc)
revEqI _ _ acc            = (acc,True)

-- TREE SORTING

-- sortT ((L 3:#(L 22:#L 4)):#((L 3:#(L 22:#L 4)):#(L 2:#L 11))) 
--					   ---> ((2#(3#3))#((4#(4#11))#(22#22)))

sortT,sortTF,sortTI :: Ord a => Btree a -> Btree a

sortT t = u where (ls,u,_) = tipsReplRest t (sort ls)

tipsReplRest :: Btree a -> [a] -> ([a],Btree a,[a])
	      -- tipsReplRest t s = (leaves(t),t[take(n,s)/leaves(t)],drop(n,s))
	      --                    where n = length $ leaves t
tipsReplRest (L x) s' = ([x],L y,s) where y:s = s'
tipsReplRest (t1:#t2) s   = (ls1++ls2,u1:#u2,s2)
			    where (ls1,u1,s1) = tipsReplRest t1 s
			       	  (ls2,u2,s2) = tipsReplRest t2 s1

sortTF t = fst (f (sort s)) where (s,f) = tipsReplRestF t

tipsReplRestF :: Btree a -> ([a],[a] -> (Btree a,[a]))
tipsReplRestF (L x)    = ([x],\(y:s) -> (L y,s))
tipsReplRestF (t1:#t2) = (ls1++ls2,\s -> case f1 s of 
					 (u1,s1) -> case f2 s1 of 
						    (u2,s2) -> (u1:#u2,s2))
			 where (ls1,f1) = tipsReplRestF t1
			       (ls2,f2) = tipsReplRestF t2
			      
sortTI t = u where (ls,u,_) = tipsReplRestI t (sort ls) []

tipsReplRestI :: Btree a -> [a] -> [a] -> ([a],Btree a,[a])
    -- tipsReplRestI t s acc = (t[take(n,s)/leaves(t)],drop(n,s),leaves(t)++acc)
    --                         where n = length $ leaves t
tipsReplRestI (L x) s' acc   = (x:acc,L y,s) where y:s = s'
tipsReplRestI (t1:#t2) s acc = (ls2,u1:#u2,s2)
			       where (ls1,u1,s1) = tipsReplRestI t1 s acc
			       	     (ls2,u2,s2) = tipsReplRestI t2 s1 ls1
				     
sort :: Ord a => [a] -> [a] 
sort (x:s) = sort [z | z <- s, z <= x]++x:sort [z | z <- s, z > x]
sort s     = s

-- CLIENT/SERVER

requests = client 0 $ server requests
   
server (a:s) = mkResponse a:server s

client a s' = a:client (mkRequest b) s where b:s = s'
-- client a s' = let b:s = s' in a:client (mkRequest b) s
-- client a = \(b:s)    -> a:client (mkRequest b) s 	   -- does not terminate
-- client a = \(~(b:s)) -> a:client (mkRequest b) s   

mkRequest = (*2)
mkResponse = (+1)
			    
-- take 10 requests   ===>  [0,2,6,14,30,62,126,254,510,1022]

-- LAZY MULTIPLICATION

mulL 0 _ = 0
mulL x y = x*y

foo x = if x == 0 then 0 else foo (x-1) `mulL` foo (x+1) 	

mulR _ 0 = 0
mulR x y = x*y

goo x = if x == 0 then 0 else goo (x+1) `mulR` foo (x-1) 	

-- mul x y = unamb (mulL x y) (mulR x y)

paths :: Int -> [[Int]]		
paths i = map (i:) $ concatMap paths $ trans!!i

trans = [[2,3],[4,5,0],[2],[],[],[1,4]]

prefixes = take 2 $ map (take 2) $ paths 0	  	   -- does not terminate

