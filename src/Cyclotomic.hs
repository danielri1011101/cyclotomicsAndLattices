{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Trustworthy #-} 

-- Copyright (c) 2012-2020 Scott N. Walck
-- Copyright (c) 2026 Daniel Barrero
--
-- This file is a modified version (a rewrite) by Daniel Barrero of
-- Data.Complex.Cyclotomic from the cyclotomic package by Scott N. Walck:
--     https://github.com/walck/cyclotomic
-- Date: October 2026.
--
-- The algorithms follow the implementation of cyclotomic numbers in GAP
-- (https://www.gap-system.org)
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License version 3 as
-- published by the Free Software Foundation.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
-- GNU General Public License for more details.
import Data.List
    ( nub
    )

import Data.Ratio
    ( (%)
    , numerator
    , denominator
    )

import Data.Complex
    ( Complex(..)
    , realPart
    )

import qualified Data.Map as M
    ( Map
    , empty
    , singleton
    , lookup
    , keys
    , elems
    , size
    , fromList
    , toList
    , mapKeys
    , filter
    , insertWith
    , delete
    , map
    , unionWith
    , findWithDefault
    , fromListWith
    )
import Math.NumberTheory.ArithmeticFunctions
    ( runFunction
    , totientA
    , smallOmegaA
    , isNFreeA
    )
import Math.NumberTheory.Primes
    ( Prime
    , unPrime
    , factorise
    )

-- | @order is the order of a primitive root of unity (ROU).
--   @coeffs is a (Map k r) where k is an integer exponent and r is
--   a rational coefficient.
-- * Namely, the key-value k-r represents the summand r*e(n)^k where
--   n=@order.
data Cyclotomic= Cyclotomic { order :: Integer
                            , coeffs :: M.Map Integer Rational
                            } deriving Eq

zeroCyc :: Cyclotomic
zeroCyc= Cyclotomic 1 M.empty

fromRational :: Rational -> Cyclotomic
fromRational 0= zeroCyc
fromRational r= Cyclotomic 1 (M.singleton 0 r)

-- | Cyclotomics shown as a finite rational linear combination of
--   base e(n) powers, where e(n) is a primitive n-th root of unity.
instance Show Cyclotomic where
    show (Cyclotomic n mp)= case mpList of
        []            -> ""
        ((ex,rat):xs) -> leadingTerm rat n ex ++ followingTerms n xs
      where
        mpList= M.toList mp

-- | Display power of the base e(n).
showBaseExp :: Integer -> Integer -> String
showBaseExp n 1  = "e(" ++ show n ++ ")"
showBaseExp n ex = "e(" ++ show n ++ ")^" ++ show ex

-- | Of rational linear combination
leadingTerm :: Rational -> Integer -> Integer -> String
leadingTerm r _ 0= showRat r
leadingTerm r n ex
    | r == 1    = t
    | r == (-1) = '-':t
    | r > 0     = showRat r ++ "*" ++ t
    | r < 0     = "-" ++ showRat (abs r) ++ "*" ++ t
    | otherwise = ""
  where
    t= showBaseExp n ex

-- | Show a rational as a "/" ratio of integers
showRat :: Rational -> String
showRat r
    | d == 1    = show n
    | otherwise = show n ++ "/" ++ show d
  where
    n= numerator r
    d= denominator r

-- | When the list of the linear combination has more than one element
followingTerms :: Integer -> [(Integer, Rational)] -> String
followingTerms _ []             = ""
followingTerms n ((ex, rat):xs) = followingTerm rat n ex ++
    followingTerms n xs

-- | Base case of the function @followingTerms
followingTerm :: Rational -> Integer -> Integer -> String
followingTerm r n ex
    | r == 1    =  " + " ++ t
    | r == (-1) =  " - " ++ t
    | r > 0     =  " + " ++ showRat r ++ "*" ++ t
    | r < 0     =  " - " ++ showRat (abs r) ++ "*" ++ t
    | otherwise = ""
  where
    t= showBaseExp n ex

-- | Convert mp to its unique Zumbroich basis representation given by @n.
convertToBase :: Integer -> M.Map Integer Rational -> M.Map Integer Rational
convertToBase n mp= foldr (\(p,r) m -> replace n p r m) mp
    (extraneousPowers n)

-- | Remove all the zero summands of the linear combination
removeZeros :: M.Map Integer Rational -> M.Map Integer Rational
removeZeros mp= M.filter (/=0) mp

-- | Corresponds to GAP implementation
--   Deliberately written with both arguments, to emphasize that
-- * @mp is expected to be the result of (convertToBase ord mp')
--   for some mp'. This ensures the number is constructed from a linear combination
--   of the (@ord)-th Zumbroich basis.
cyclotomic :: Integer -> M.Map Integer Rational -> Cyclotomic
cyclotomic ord mp= tryReduce $ tryRational $ gcdReduce $ Cyclotomic ord mp

-- | Step 1 of cyclotomic is gcd reduction.
--   Obtains the correct (i.e. minimum) degree for the root of unity
gcdReduce :: Cyclotomic -> Cyclotomic
gcdReduce cyc@(Cyclotomic n mp)= case gcdCyc cyc of
    1 -> cyc
    d -> Cyclotomic (n `div` d) (M.mapKeys (`div` d) mp)

-- | Computes the gcd between the degree @ord and the powers @pows
gcdCyc :: Cyclotomic -> Integer
gcdCyc (Cyclotomic ord mp)= gcdList (ord:M.keys mp)

-- | gcd of many integers, gathered in a list
gcdList :: [Integer] -> Integer
gcdList []= error "Cannot compute the gcd of an empty list"
gcdList (n:ns)= foldr gcd n ns

-- | Step 2 of cyclotomic is reduction to a rational if possible
-- * TODO: clear ambiguity about fromRational. For now: use Main resolution.
tryRational :: Cyclotomic -> Cyclotomic
tryRational c
    | lenCyc c == fromIntegral phi && sqfree= case eqCs c of
        Nothing -> c
        Just r  -> Main.fromRational $ (-1)^(nrp `mod` 2)*r
    | otherwise= c
  where
    eqCs= equalCoefficients
    (phi,nrp,sqfree)= phiNrpSqfree (order c)

-- | Euler's phi (aka. totient) function, number of distinct prime factors,
--   and isSquareFree for the order of the ROU.
phiNrpSqfree :: Integer -> (Integer, Int, Bool)
phiNrpSqfree= runFunction $ (,,) <$> totientA <*> smallOmegaA <*>
    isNFreeA 2

equalCoefficients :: Cyclotomic -> Maybe Rational
equalCoefficients (Cyclotomic _ mp)= case ts of
    []    -> Nothing
    (x:_) -> if equal ts then Just x else Nothing
  where
    ts= M.elems mp

lenCyc :: Cyclotomic -> Int
lenCyc (Cyclotomic _ mp)= M.size $ removeZeros mp

-- | Step 3 of cyclotomic is base reduction
-- * Depends on reduceByPrime
tryReduce :: Cyclotomic -> Cyclotomic
tryReduce c= foldr reduceByPrime c squareFreeOddFactors
  where
    squareFreeOddFactors= [unPrime p | (p,m) <- factorise (order c),
                                                unPrime p > 2, m <= 1]

reduceByPrime :: Integer -> Cyclotomic -> Cyclotomic
reduceByPrime p c@(Cyclotomic n _)= case mapM eqRep [0,p..n-p] of
    Nothing  -> c
    Just cfs -> Cyclotomic (n `div` p) $ removeZeros $ M.fromList $
        zip [0..n`div`p-1] (map negate cfs)
  where
    eqRep :: Integer -> Maybe Rational
    eqRep r= equalReplacements p r c

equalReplacements :: Integer -> Integer -> Cyclotomic -> Maybe Rational
equalReplacements p r (Cyclotomic n mp)= case repList of
    []               -> error "equalReplacements generated empty list"
    (x:xs)
      | equal (x:xs) -> Just x
      | otherwise    -> Nothing
  where
    repList= [M.findWithDefault 0 k mp | k <- replacements n p r]

replacements :: Integer -> Integer -> Integer -> [Integer]
replacements n p r= takeWhile (>=0) [r-s, r-2*s..] ++
    takeWhile (<n) [r+s, r+2*s..]
  where
    s= n `div` p

replace :: Integer -> Integer -> Integer -> M.Map Integer Rational ->
    M.Map Integer Rational
replace n p r mp= case M.lookup r mp of
    Nothing  -> mp
    Just rat -> foldr (\k m -> M.insertWith (+) k (-rat) m)
        (M.delete r mp) (replacements n p r)

includeMods :: Integer -> Integer ->  Integer -> [Integer]
includeMods n q start= [start] ++ takeWhile (>=0) [start-q, start-2*q..] ++
    takeWhile (<n) [start+q, start+2*q..]

removeExps :: Integer -> Integer ->  Integer -> [Integer]
removeExps n 2 q= concatMap (includeMods n q) $
    map ((n `div` q)*) [q `div` 2..q-1]
removeExps n p q= concatMap (includeMods n q) $
    map ((n `div` q)*) [-m..m]
        where m= (q `div` p-1) `div` 2

-- | n -> [(p, p^k)] where p is a prime divisor of n and p^k is largest
--   such that it divides n.
pqPairs :: Integer -> [(Integer, Integer)]
pqPairs n= map (\(p, k) -> (unPrime p, unPrime p ^ k)) (factorise n)

extraneousPowers :: Integer -> [(Integer, Integer)]
extraneousPowers n
    | n < 1= error "extraneousPowers needs a positive integer"
    | otherwise= nub $ concat [
                               [(p,r) | r <- removeExps n p q] |
                                              (p,q) <- pqPairs n
                                                                ]

equal :: Eq a => [a] -> Bool
equal []= True
equal [_]= True
equal (x:y:ys)= x==y && equal (y:ys)

