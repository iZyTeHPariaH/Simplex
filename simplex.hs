

import Problem
import Data.Array
import Control.Monad
import Control.Monad.State
import Data.List


toOrdering True = LT
toOrdering False = GT

{- Max cx
   sc : Ax = b
        x >= 0 -}

{- Algorithme du simplexe sur un problème de la forme
  maximiser c.x
  sous contraintes : A.x = b
 (Les variables d'écart ont déjà été introduites -}
simplexStandard :: (Ord a, Fractional a) => State (Problem a) SolType
simplexStandard =  do c <- getC
                      a <- getA
                      b <- getB
                      (_,(m,n)) <- getDim
                      -- Récupération de l'indice ayant le plus grand coût réduit
                      let (maxC,indiceC) = head $ sortBy (f (>=)) (zip (elems c) [1..n])
                      -- Si le plus grand cout réduit est négatif, alors on a atteint la solution optimale
                      if maxC <= 0 then return Optimum
                      -- Sinon, On récupère la liste des variables candidates à sortir de la base
                        else do let candidats = sortBy (f (<=)) [((b ! ligne) / (a ! (ligne,indiceC)), ligne) | ligne <-[1..m], (a ! (ligne,indiceC) ) > 0]
                                --S'il n'y a aucune variable candidate à sortir, alors il n'y a pas de solutions
                                if null candidats then return Aucune
                                  else let (val, indiceL) = head candidats 
                                           pivot = a ! (indiceL, indiceC) in
                                -- Sinon, on détermine la position et la valeur du pivot, puis nous échelonnons la matrice
                                -- A, puis le vecteur c et enfin le vecteur b. (NB : les variables a,b et c récupérées
                                -- au début de la fonction sont les valeurs originales et ne subissent pas les modifications.
                                       do setA $ echelonner (indiceL, indiceC) pivot a
                                          setC $ listArray (bounds c) [ci | i <- [1..n], let ci = (c ! i) - ((c ! indiceC)/pivot * (a ! (indiceL,i)))]
                                          setB $ updateB (indiceL, indiceC) pivot b a
                                          
                                          --Après avoir changé de base, nous itérons.
                                          simplexStandard
                                          
                                          
     where f g (a,b) (a',b') = toOrdering (g a a')
           -- Permet d'échelonner le vecteur des seconds membres à partir des indices du pivot et de la matrice des contraintes.
           updateB (pI,pJ) piv tab ct = tab // [(i,val) | i <- [n1..n],
                                                       let val = if i == pI then (tab ! i) / piv
                                                                    else (tab ! i) - (ct ! (i,pJ))/piv * (tab ! pI) ]
             where (n1,n) = bounds tab
                   
           --Permet d'échelonner la matrice des contraintes
           echelonner (pI,pJ) piv tab = tab // [((i,j),val) | i <- [n1..n2],
                                                              let li = recupererLigne i tab
                                                                  pivLigne = tab ! (i,pJ)
                                                                  li' = if (i == pI) then map (/piv) li
                                                                         else zipWith (\x pi -> x - pivLigne/piv*pi) li lpiv,
                                                              (j,val) <- zip [p1..p2] li']
             where ((n1,p1),(n2,p2)) = bounds tab
                   lpiv =  (recupererLigne pI tab)

{- Récupération des valeurs des variables de base
 Retourne un tableau contenant le couple (indice de variable, valeur) pour chaque
 variable en base (les autres ont de toutes façon 0 pour valeur). -}
extraireValeurs :: (Fractional a) => State (Problem a) [(Integer,a)]            
extraireValeurs = do c <- getC
                     a <- getA
                     b <- getB
                     (_,(m,n)) <- getDim
                     return [(var,val) | var <- range (1,n), 
                                        (c ! var) ==  0, 
                                        let val =  head [bi | i <- [1..m],
                                                              a ! (i,var) == 1,
                                                              let bi = b ! i]]
{- Max z = x1 + x2
    sc 2x1 + x2 + x3 = 14
       -x1 + 2x2 + x4 = 8
       2x1 - x2 + x5 = 10 -}




              
c1 :: Contrainte Double
c1 = Contrainte [2, 1] LT 14
c2 :: Contrainte Double
c2 = Contrainte [1, -2] GT (-8)
c3 :: Contrainte Double
c3 = Contrainte [2, -1] LT 10

test = mkProblem [1,1] [c1,c2,c3]
              
