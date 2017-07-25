-- |
module Ex where

import Prelude

import Syn
import Bi
import Tc

type Term' = Term Integer Integer
type Typ' = Typ Integer

idTerm :: Term'
idTerm = lam 1 (V 1)

idTyp :: Typ'
idTyp = fall 1 (TV 1 :-> TV 1)

idTyp' :: Typ'
idTyp' = One :-> One

id' = In idTerm idTyp

checks@[idCheck, idCheck', unitCheck, idAppCheck] = map runTc'
  [ check idTerm idTyp
  , check idTerm idTyp'
  , check Unit One
  , check (idTerm :@ Unit) One
  ]

test = all (== Right ()) $ map fst checks
