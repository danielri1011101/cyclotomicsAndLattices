
foo :: Integer -> Integer -> [Integer]
foo t q= filter (>0) $ map bar [1..q-1]
  where
    bar= \z -> if z^t `mod` q == q-1 then z else -1

-- Example 2: {d= 64, t= 4, q= 41}
zs= foo 4 41
