module Problem
where


import Data.Array
import Control.Monad
import Control.Monad.State

data Problem a = Problem {coutsReduits :: Array Integer a,
                          contraintes :: Array (Integer, Integer) a,
                          secondsMembres :: Array Integer a}
                 
data SolType = Optimum | Infinie | Aucune                 
                                   deriving Show
instance (Show a) => Show (Problem a) where                                            
  show (Problem c a b) = show (elems c) ++ "\n" ++ show (elems a) ++ "\n" ++ show (elems b)  ++ "\n"
data Contrainte a = Contrainte {coefficients :: [a], typeContrainte :: Ordering, secondMembre :: a}

getC = State $ \p -> (coutsReduits p,p)                
getA = State $ \p -> (contraintes p, p)
getB = State $ \p -> (secondsMembres p, p)
getDim = State $ \p -> (bounds (contraintes p),p)


setC c = State $ \(Problem c' a b) -> ((),Problem c a b)
setA a = State $ \(Problem c a' b) -> ((),Problem c a b)
setB b = State $ \(Problem c a b') -> ((),Problem c a b)


recupererLigne i tab = [val | j <- [p1..p], let val = tab ! (i,j)]
         where ((_,p1),(_,p)) = bounds tab
               
               
ajouterVariable :: (Ord a, Fractional a) => State (Problem a) ()
ajouterVariable = do a <- getA
                     c <- getC
                     b <- getB
                     (b1,(m,n)) <- getDim
                     setC $ listArray (1,n+1) ((elems c) ++ [0])
                     setA $ listArray (b1,(m,n+1)) [if j == (n+1) then 0 else a ! (i,j) | i <- [1..m], j <- [1..n+1]] 


ajouterContrainte :: (Ord a,Fractional a) => Contrainte a -> State (Problem a) ()
ajouterContrainte (Contrainte coeffs LT bi) = do  ajouterVariable
                                                  a <- getA
                                                  c <- getC
                                                  b <- getB
                                                  (b1,(m,n)) <- getDim
                                                  
                                                  setB $ listArray (1,m+1) ((elems b) ++ [bi])
                                                  setA $ listArray (b1,(m+1,n)) ( (elems a) ++ coeffs ++ take (fromInteger n -  length coeffs-1) (repeat 0) ++ [1] )
ajouterContrainte (Contrainte coeffs GT bi) = ajouterContrainte $ Contrainte (map (*(-1)) coeffs) LT (-1 * bi)                                                  
ajouterContrainte (Contrainte coeffs EQ bi) = do ajouterContrainte $ Contrainte coeffs LT bi
                                                 ajouterContrainte $ Contrainte coeffs GT bi
                                                 
mkProblem obj ((Contrainte coefs LT bi):xs)  = snd (runState (foldl f (return ()) xs) (Problem c a b))
    where n  = length obj
          c = listArray (1,toInteger $ n+1) (obj ++ [0])
          a = listArray ((1,1),(1,toInteger $ n+1)) (coefs ++ [1])
          b = listArray (1,1) [bi]
          f a e = a >> ajouterContrainte e
